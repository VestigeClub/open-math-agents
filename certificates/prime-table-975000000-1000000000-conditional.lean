import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ975000000To1000000000

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




private def radical : ℕ := 0x6ce42a43cfcb5915ed5583ea973f79a6af8a6528fc818d18ce8d97a69d0a0e84219237c85ef5d8d76579a89867a4e60cf55a2b2516f8462409a633cb30cabbb812eb9925498a32ece37b5f0d7c8d0235e1c5ce3cb03bd56256e5670e74e39a709ca8552931e2b38aa979414c2508fc6bf6797ca039610d4a49e14f49de52d67fdc1cca2a62ab285a3df0a7605c82a6df785ebbbc1bba8b062b469c4c4fb0734f9a414cb09e5f721b4859550d54f4f62439c4321cd03152ca6c49d284ffe0934639126f90de99e61091502c7120f4e5aac6cf34304ffd6406ec387fd3b00f432b64d9aeebc733147f1aa8932b9f885eb990ac7f6c0554ad4d6b26b220194fe9db16e832a9ca35a68403968df0225c60e41b0c6c1635acf176a8a24fe86f9c1286692a0ee45e61a5d802ef4d4918c5fc945a797a1dfa232a7e27d35de1b0b537592c1b99a0e0cfbb4c51f5916b1c63f1c074e6c7fcb58f998c16d5b0a5497d655099463b456622365bb7aa90799fc15a9f40bd526682e7f15c83262b5a696ce2995277e7d08f8070c02ac5f8a9961343be897e774c33da8d2e92ace0704c15afe251898b5bd2e01d23e5998d88cebcbd355b36ed4bd846eb95ce6f2c329326857215d43b98d076b0750bc0bf9ae88786d02c4635be59d85a48f72adb37fbec94a56a9d80d908a3dedc91e101a488e2caf0754a15e37a8fc26d0e6a571e99e61885ed61854f00e485b6629a5b67b4195d3e2c0448f20a50f2ac6d2044cb53ca645289c4ef21dca8cbccd44d85c08ba0efd83200b547bfcb9f5fed2f8d96d965fca0c882ec9087219becf5484fbc32a4a7d282f020530e5579f8a1ea6d27b599bdae9dca19f4e0d76df7a47fda87e9f3b9462ac109050b05dc30c62970345ea959021d7a76a177f54305e37a5630a7d596ae63901b2230d88ef890307b4f690a98965a0bc1d34c5c92c300802b5eb096598c3c8cd36d16ef11e81dc23e1d2fed2c18234190bc31203a2b932af9cba237c2dca1b304c89971a65547038a44da5852914f4c3478083b78a73f85071961701c019a700cdb022bda90a22b93d1316d3e7a733ee285a2c972557d5d6ca3d9b86c7138056e33f2ec6efee41a5e6b1427899e3dca6b1d9415781fdb2092dedd7695102a38cc52a202230b2c792d27bf65c646f67e9a4c82cf46db4625ff8f1469ac2518db8f5e4a37f20c3cc993e04b8357ad0349b177e8306cad7e396c3b9b5fd9bf495cedf18e90679b36bde60a2cd1b17e8ccf1037236eec86a8c18cb46a835792ed8dbc794c19e0cec08de7dd5a4bbc357ee474b1a08462478128c06400e3eb6c0981b12652c28dcd1b6778dc509d75da49654e3a36493c5c5a47793b0a1156f28d887f2e004fa4fb1a9ac4d8b818ab6102d57b6d6f8724ed123a97a862df0f4ddaec862f3a1c47bbce430729e4e0d848ab212daee2d8f22eaa3efbeb171d601d08d67e822d9db128429e6302684036244b841016ab6a1b912452d84edea230c201d9ffdde3b3e1078774e835a93fa5e039e5981380fe37e1b54c6f8a3ad47efbcb6963be5936a1513b15dd24d0d047c2d5c53f88799a9aae02e167aa3117f2cbcaa76031ec75ee4b415965282caeb7dfb83970dd30006b7ee4a1619fc18526ab3347fcedfaae32b3d56dbb2c62f15efc275e1f9fba32fe85e8a30f3d35b65732fd58531f98a9810f357b8392e8935af8c41adf6d711241defddd595934237f14524895fcc96131820ff03794880b5d02d7743099df39736bbc0b09a368bb6dc6f3a9d56259a354eded3c69e1b0ea12a494e3675e0767e985b77d3cc3cfb6473d479a9f7655503774e376cb0487c25fd733fed6cefcf9635d4d36e60307ebc2c1421ce2bb6e66c09128b0215ce5f9c3b682d37bb487079a268c93227d95bf8ccacc025e3dd14e3e6189eafa963053505da95f77e4404f234938114e90e87fee6ab52202101edc78bf33d58a68e3e1ae21140251c9968c1582bcd145e5a0a0dc06a0b51588d4b19dc0f26e9c34d3acc80152e2362a3c72a72a62a07ad3f7c3a5fa28a6a6db6fcbd45002a0c72bcf0be38b50016e4cda04907a9ed0b4fd7832c463b165483c49ce5f092e89122c6111aa04bdd068324b5565501b34ecabf8a8c11aca9ad01740d3071ac4726d4d51bee7ce217984ac44957fc2d68fe83e80696b5cd98ad187f2aabf2be6de83572d2fd7d1f9145cec8b05fe027c008156111ded4bc850e797a5880abed4176f5d6f607ffc8bccf32287cdbcd55ec7f9f3be5da8723aa148b139d8bd417fee1d83da2fa443f9c058e3cab15f044a08ede9bbac8690bd5e98a884c2fdf28a1f7c036416fd74fd64552900f0f622bf31938e2b0208fc317c6d96df7243557671a986c623eed86537396625e8130e5a7f40cfe2b9bb5562e76f0620f584f6b38d435243998b5e28b3fd30bdc5541d88b5efb7b8e43a855dc318cbf6f000a8c92b37a803a1bd29c402b08b3242d4fc3784f4ad1c18b0f1c37bd3e3c8b9fc549409c074313237ef6435797910de927f432e101ace8308a54ce2ca1296836d8e3f45f159fbff6753e9911a96c7d220496776c99418b82b3e4597659013a8ef16adfa8dda265d55da9977c10cbab15d40e3e31771826b71991d1cc02e6f6480497102abf298c0421de6cce8c541be3bd9e1e52ad7e1b6928537bb261074558bc893024439bad0de3b1795e609e3e42e5f4ef269f69a67824dedf4b43d3696c31837552cecc52b989c47c4a0b1cb1854a83a3ea74f19de449afd36df6b81f3146142b33e84c91139c1b46a2e135d89da7ee5c0e902b273afea5d3deed91233e932531d809cd60bdc5f8edc9c2d15ae6573e7177dd9ec9fd41e1577db6d9a653a43bda59aa9c827cf4e80d0cb04bc22df1d3d172fc71e46b70677f85b114238293a3f01e3422715af69c7374a3e7af5e1a3fcd4f76c41ba361badf0598dd315461bcd2cdeb532738ef835cdcfd2ed2261f093e95f0d1b9b0a2b8fa19e710549ee77d2dbe16a8728e2bd9d875063728ad39ccbe8551ca004fd8ff44d1a855bb07ca758cae807a8cfb50f5eb59fe5db0eb7374e713adb765cbbb12f2b26745c05090fe70e06c092219a1de27ebd7561a6796b27afad76597982df2d775e8ef355f05f744767ed52ce1f2ff94d17a885d87e7e6135857b62b1e3ccf009d52d0e4ba26fa2749ed3cad2b792b63d5b0f9f1cca8859c6daa12bc05896db47d8e33c2a22136a408e26707c126fb6f8a8a8caa97f916743e37bcc76be0168f4490d54951cecc2bb7f91cc3c8f0d0103c32617301752c41a95eab255b1bf4feb77e3e45c8e8b76ac3a87ca91b023b2d1b43d79787e9d83eb797811e81a6c4039d4a119bc58057a177676f35461d39e2f2afb27f399179e80b70d8422b80f8e145ba81d20d5a76b711d55d0380d77568f1bbd45c3a4b885ad96f109b1e2ac3d813b97985f60f38f2fca8edac44df73099417d9cfb1210933cfabbb2fa8932b1bc766292814bf2f80656e367739aa9872ecdbdc0308b181897c470ee926b6ead918db968eb2e3aaa24ee4e54ecd9abee71d94b8d0ce03739e197bd45bea25a92c3eda792afbe8716898843db662a59edefc2ffef39d6baa3feeb6319991bf33dc32f0b8c6e1fa6de240fb2671c001fcd5408b82cf543771cbdba6703a7472b6c7a7a5d18e983a91a0517c781758bad8536957da3129be70a29d6760635da83796f2064d3b078c7827ade2e0d6ea92118dd3cb01693d632cc530a3dcf54ae392c24df2abe4c013c6c08f2dc7b4f1a50c4784133ca2093520a5a16e559a125b0660f8b47b456a68d1ee040d869d938c312b60139dd28d435bc03ad4822030a58219a6b89dd5b138acfa3f3920e59fd2a374fe38b7bb749c0563cce5bb65851f418eaad7a0688c7770648693108951f2235c5dcfcecb2f9ecb0a206768640aabd866589f9ea63fbd47d9b0da24a161db9a8bdbbf5823ec46a951a5896764ee6e42beafebb8fa3b4a569ab87ec145af5b3108274eb27092516e5154d6e355482d0e5c9ed862835ea17947d9e00daf01c33b03614ece95c844d559a30dfa24e126248c70bff241e28a3508c3cfb8855bfc7a20cdfe499541ddc86bfa27a72f08d4d31783969463588e6b179dbf81100793016f6e947901631ff56be5c115df3071073b5d9d74d75c06482c3af2ec0a198ef8779fb75155d68041bccd3011c8fb624a29e002582502a9ea1ac55962395dae660594eef7894ad4c7c5591f27c8d1b15cca8c0907ee13265575169a2371733eeef84e003418d30e545e4877a4ecd9bcb9190e5d85daa592d627b6b04bb0d317a68d11f0e6088a65f2d612b39d26439db8c25a7bc844901fd687c29f513baa20643f3423ba0b0ebaded772f1ab8dec94c92802fb2e480bc3a9200b735126cb60184157e9646bd88610a39d8a8ffb4ada694e387987670c3018c4517f6f2d44cabe0a33d0431b5996e385318d4aaa14fa2b53eb21cf40a598464a5a2d1504aebf68fcd11d9e0123f92edfe80720c16c0f7333924d036cba49abc8f80626670d2e26b0e3e094aa1dcf98dd1c443e697ef1a2debe6c03eb358d5d937de74ce8f052f297594db5516a24ae8e41f6d01dc1338e3fb3e090255a86cf3ee5c2c1879ad3e5ca9ab035a1127b41ddc166cb984c18672aab755a26cd4d9487ea0025e2effecfb310e68d8051ea6a88bbf1ee78fb489216a94dafb2b9436abd9dfc2b961819bbf55b66a55500b34413b06ce843c9fde04e0ccffa580150c3c7309f240dc50bdc7d323f0c6d21f942070812eb319705aa9d2be0d8aa7c009a0823c8b4be5ec105e951ca0fdfcb4bd15a4a98829ba3aed86c379f108f7e7db16f43e3aa5679dbb08ffa3850e31e26a35798f735963a5e180228e57c7890d347f3e7f332c2e6c358de62ad06b2e7f99fc5370749f3b87e230db43ee8deaafa5ea7fff503a2e6a58356fa765b34aa65562e48f86da87a1fff194f4e57a633ac0884dd6c92a292323888e522a49126bc1795f653db625ec2e3b4284526079508e9b67be8a950b5312b9237c274be40af49aa2fa033dc86cc92e8fc3b11807de26044595152ec592343106cf1d02d7ae2190b3769aab8755929111a1217e70626a3c9efc5535c837a619ba0e428bcae3c5780eb7df70a869eed9c2d5fe07833651a8b7aff57431be20d3c46943a90fde0bf6210a01196736cf3bc0ac99fa868b934bc4ef5163ca58d5a4258bb9d5eb95cc1636fa8feb6f0255a980227871fd86abec56e800273bbd2f52e0337a912aa91b875b2c94a95c75699c11c44fdac1661ba25b89373847820815a7664f7a21b76d5d64460f5f5c8d6ac9a7251f30107a4b68be085163fe26b547e929447e494616489d32561312bcccf588680a8c765a5bd94929364576ad34e76a165119de9b04a13232c81e18928696a0999998e16440cbc32b4df811cb954f1d33ceeee83a4b868e498855d2f56e8ff90caa48a1a292dec941ecc74513861bfb83384c69127e377c948315dded0b60840e3c4a76b2c60389d10ec014e1ccc7f3b03e9f30be5698ebe1f6110a6c70af8b0ed6fddfcc93ae68b784919eb64628051903039c6f1a95f6e1610b49151cb9278e9023ae492b9d9f881bc17a4d0c5419bff35b6af57151c61db52917437d6550cb286eecf58b9ed8a16b834731f6c343ddc6422301275759e3f836fb471c2d66e84afe9f951a6357f876a692b3af71270506c062baf5f962891c25bff1d2b7b05f44b535a7c3fc7d1ea8aa1ecb47e8d920b16bfcf5158a77d243a667845ae174788970ba4d16ad3b9755a8caa98d78cd47810cbd5199476308f20f05b37bf2b0f576d247cc547e4aa883296715d55a175a6fbeae05333b838fd3be26fca3dffca3e103afbba8661ff9c4167d553e9461dee62d5612e7c3d3e74063b09b186d63b87c9eb72c9940a37b705cf31acbe1b837ba26377ccceda022c855e4b9694e3be8286c5a0da559e8993af1c9cc815c5e0a15cada0333a064b6829bc9bfd97825c9516e8454aadc1cff002848022a255cf835773512943168bbb1811889dc80e8e7a01d55ea25da2aebea5bb2d919f190e6ad7fb60afd51a8409aa17e5a2444c349bab06d0c57f2f19fb16f4198f97f08bdce69f5b038952fe00e3a8226a6d5e7df22814b173b80d8f90e9babd770bde879902851a8bf15d732d85671779eb298531df8be3ca2e114e6a424556283e67fc983c703fce1fc064a7577c48fe06b26d3f693a5cb3d338791e0b41d3d2d1d8dace9f31bc8144460782b7f57ca53b89236d8b46f2b6953a34098f5e3365b02316d0a101687d9bdc000f93a1ec4d4af40ad5537d8cb3bf73ec18c8159926a068a825c07f8b1f10e10b0514fb92fb7773dbe4f2c7969dc81afff9dd2126a9e74c2059c0ed6e5a3942c8a585463047bd78a03908174642b0effeb3f9936ae869e9645cc3b2da0165a72ab2288a8b6dbb5f72782bff941a3bbb294291c8c2443b8a8576b141013dd48015a673894c4e48532a5f8a07f2375ced245fe077a1c353b071427c84d1dc4ad0464622b94e1af3b12d1ef5b8f3531a684038aa15ac1efc98d5441ff47c5c7abe52192bccab58fa62508437a9dbf550a587f8aaa6d854a9908593237c105d495664f96c161224a910a2ec24169df83e26fcae91bd0b50b52edb4a84b1ab3b67986bdfbce11edee540a5ff295f7bff09ef5e99546ccc972368d36223b8f936f2c21e582baf09df318848137c34a0a590008373f3fb87d6002a77dbc28c1f589752106f18b668aa6abce3b26f17902931030d25f468b7f03e9bee0fb2d80c8df12abc808a035db4bfe02a4963469c90ebfddaa12694cfff73cc776613e2beecaf9f53531498fba9d49d6c6c4c0460704fe177f3f7f4bfd680b210ac44187cda2e8629d353b1d733acf0831f8ce5775ed105324d4c147b1a662ab800faf8f069662973c1de38102bd4abdcbdac72816140668e11d2bb0034e0eb667608a9f150c9289c58098f62ccca7d282a7c45b01b3c27532240ea85ccb169db684eead97a655c4fe9ba160fd4a04413b293dfda94460a5c1b44901e34d51afbd7ba092bc7c1d522f78593c7bce83ad7f9b2a415e0e5b5a563b8abb5f5fe51418eaa4456fb2cdefca0e2fe7753e39776c50e80b03f9cc2b69f3bb9014b00d67fc6b9e3443a8b2f9464550c58aea7e9cc358ef1ef5456c38bdacc4309b47c23558335283105d8c4c728ada3443858a58567d2acd302f80994ca4a79142f82cb0c4d792a611858d2db6da9529870ccbf8a7a6ed627f8c64fff70c0da5a4d7cd1b455bca555f7dfe91c37f038f7a8c8955c5865e5a4c602aeadbf816156fb7fbb7486a0abeee092cdf7e7d1b2c42416e83e27d29dd396531104dc9902b7ab22cffc29743a6846e19c53336eff93c0a4761e1bf7ae6b36f731de8b67883a8e719f38757f5b66db5f268eaeaddd5b94eb83037774431cda571153c202fc61f222ace984e52083f0a7b2fd40528401e3f37e9a5a63f9d2ea0c774f6d96dd68979bdb3c03e7f195589160892b97cb899e48f1acfb002fee57e19cb3a68971d5d94c5ea0a86ee8ee8560efe9bc9b0ac0b7fd02dd115139a34e621f39947f1d68d7d04353700e04fec8883ee377588079b6a1b9cc50b2902ad548954c80e60fd700a8aa53cf1e0034cf2752f6de95ba26ffcb721629c2e454e3930ae6d9a46b83df9e403a1566363b4e6aa33f6ecb97e1b21f92367ac539f9a428f3ee8a178d8419d409e73c1aa4754649d7a57869c3254464e47345959a8dcba02d12120b937b8671188853756049ab5a0b5f29662aef9cf2cbe0ee8143f902ac46b236d6a52bb05c690a7127d9c685880c209c53985efa942b4a7dc2909b04f4dc0681d48848efb6f82c24aa97a4cad5ff68aeaea6abb1203889b5c2d90369e028f13d7fdd27bb53347ee458ac5e1d5979538c1d1e970b8c033a5b1935fef72

private def light (n : ℕ) : Bool :=
  if n≤177 then decide n.Prime else n.gcd 35028850546302858099329632808581946958330777310287381335557392498211882659489182680375113878618436056819965633223379924827037455308366548670588021699824718224591058237053509662339734873457437533572003084405728604488740447501223027157048421341653372149720729437766809178439438827520000000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤31622) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 177 = 35028850546302858099329632808581946958330777310287381335557392498211882659489182680375113878618436056819965633223379924827037455308366548670588021699824718224591058237053509662339734873457437533572003084405728604488740447501223027157048421341653372149720729437766809178439438827520000000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 177 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤31622 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 61 := by unfold smallValid; decide +kernel

private theorem sp61 : smallValid 61 62 := by unfold smallValid; decide +kernel

private theorem sp123 : smallValid 123 62 := by unfold smallValid; decide +kernel

private theorem sp185 : smallValid 185 62 := by unfold smallValid; decide +kernel

private theorem sp247 : smallValid 247 61 := by unfold smallValid; decide +kernel

private theorem sp308 : smallValid 308 62 := by unfold smallValid; decide +kernel

private theorem sp370 : smallValid 370 62 := by unfold smallValid; decide +kernel

private theorem sp432 : smallValid 432 62 := by unfold smallValid; decide +kernel

private theorem sp494 : smallValid 494 61 := by unfold smallValid; decide +kernel

private theorem sp555 : smallValid 555 62 := by unfold smallValid; decide +kernel

private theorem sp617 : smallValid 617 62 := by unfold smallValid; decide +kernel

private theorem sp679 : smallValid 679 62 := by unfold smallValid; decide +kernel

private theorem sp741 : smallValid 741 61 := by unfold smallValid; decide +kernel

private theorem sp802 : smallValid 802 62 := by unfold smallValid; decide +kernel

private theorem sp864 : smallValid 864 62 := by unfold smallValid; decide +kernel

private theorem sp926 : smallValid 926 62 := by unfold smallValid; decide +kernel

private theorem sp988 : smallValid 988 61 := by unfold smallValid; decide +kernel

private theorem sp1049 : smallValid 1049 62 := by unfold smallValid; decide +kernel

private theorem sp1111 : smallValid 1111 62 := by unfold smallValid; decide +kernel

private theorem sp1173 : smallValid 1173 62 := by unfold smallValid; decide +kernel

private theorem sp1235 : smallValid 1235 61 := by unfold smallValid; decide +kernel

private theorem sp1296 : smallValid 1296 62 := by unfold smallValid; decide +kernel

private theorem sp1358 : smallValid 1358 62 := by unfold smallValid; decide +kernel

private theorem sp1420 : smallValid 1420 62 := by unfold smallValid; decide +kernel

private theorem sp1482 : smallValid 1482 61 := by unfold smallValid; decide +kernel

private theorem sp1543 : smallValid 1543 62 := by unfold smallValid; decide +kernel

private theorem sp1605 : smallValid 1605 62 := by unfold smallValid; decide +kernel

private theorem sp1667 : smallValid 1667 62 := by unfold smallValid; decide +kernel

private theorem sp1729 : smallValid 1729 61 := by unfold smallValid; decide +kernel

private theorem sp1790 : smallValid 1790 62 := by unfold smallValid; decide +kernel

private theorem sp1852 : smallValid 1852 62 := by unfold smallValid; decide +kernel

private theorem sp1914 : smallValid 1914 62 := by unfold smallValid; decide +kernel

private theorem sp1976 : smallValid 1976 61 := by unfold smallValid; decide +kernel

private theorem sp2037 : smallValid 2037 62 := by unfold smallValid; decide +kernel

private theorem sp2099 : smallValid 2099 62 := by unfold smallValid; decide +kernel

private theorem sp2161 : smallValid 2161 62 := by unfold smallValid; decide +kernel

private theorem sp2223 : smallValid 2223 61 := by unfold smallValid; decide +kernel

private theorem sp2284 : smallValid 2284 62 := by unfold smallValid; decide +kernel

private theorem sp2346 : smallValid 2346 62 := by unfold smallValid; decide +kernel

private theorem sp2408 : smallValid 2408 62 := by unfold smallValid; decide +kernel

private theorem sp2470 : smallValid 2470 61 := by unfold smallValid; decide +kernel

private theorem sp2531 : smallValid 2531 62 := by unfold smallValid; decide +kernel

private theorem sp2593 : smallValid 2593 62 := by unfold smallValid; decide +kernel

private theorem sp2655 : smallValid 2655 62 := by unfold smallValid; decide +kernel

private theorem sp2717 : smallValid 2717 61 := by unfold smallValid; decide +kernel

private theorem sp2778 : smallValid 2778 62 := by unfold smallValid; decide +kernel

private theorem sp2840 : smallValid 2840 62 := by unfold smallValid; decide +kernel

private theorem sp2902 : smallValid 2902 62 := by unfold smallValid; decide +kernel

private theorem sp2964 : smallValid 2964 61 := by unfold smallValid; decide +kernel

private theorem sp3025 : smallValid 3025 62 := by unfold smallValid; decide +kernel

private theorem sp3087 : smallValid 3087 62 := by unfold smallValid; decide +kernel

private theorem sp3149 : smallValid 3149 62 := by unfold smallValid; decide +kernel

private theorem sp3211 : smallValid 3211 61 := by unfold smallValid; decide +kernel

private theorem sp3272 : smallValid 3272 62 := by unfold smallValid; decide +kernel

private theorem sp3334 : smallValid 3334 62 := by unfold smallValid; decide +kernel

private theorem sp3396 : smallValid 3396 62 := by unfold smallValid; decide +kernel

private theorem sp3458 : smallValid 3458 61 := by unfold smallValid; decide +kernel

private theorem sp3519 : smallValid 3519 62 := by unfold smallValid; decide +kernel

private theorem sp3581 : smallValid 3581 62 := by unfold smallValid; decide +kernel

private theorem sp3643 : smallValid 3643 62 := by unfold smallValid; decide +kernel

private theorem sp3705 : smallValid 3705 61 := by unfold smallValid; decide +kernel

private theorem sp3766 : smallValid 3766 62 := by unfold smallValid; decide +kernel

private theorem sp3828 : smallValid 3828 62 := by unfold smallValid; decide +kernel

private theorem sp3890 : smallValid 3890 62 := by unfold smallValid; decide +kernel

private theorem sp3952 : smallValid 3952 61 := by unfold smallValid; decide +kernel

private theorem sp4013 : smallValid 4013 62 := by unfold smallValid; decide +kernel

private theorem sp4075 : smallValid 4075 62 := by unfold smallValid; decide +kernel

private theorem sp4137 : smallValid 4137 62 := by unfold smallValid; decide +kernel

private theorem sp4199 : smallValid 4199 61 := by unfold smallValid; decide +kernel

private theorem sp4260 : smallValid 4260 62 := by unfold smallValid; decide +kernel

private theorem sp4322 : smallValid 4322 62 := by unfold smallValid; decide +kernel

private theorem sp4384 : smallValid 4384 62 := by unfold smallValid; decide +kernel

private theorem sp4446 : smallValid 4446 61 := by unfold smallValid; decide +kernel

private theorem sp4507 : smallValid 4507 62 := by unfold smallValid; decide +kernel

private theorem sp4569 : smallValid 4569 62 := by unfold smallValid; decide +kernel

private theorem sp4631 : smallValid 4631 62 := by unfold smallValid; decide +kernel

private theorem sp4693 : smallValid 4693 61 := by unfold smallValid; decide +kernel

private theorem sp4754 : smallValid 4754 62 := by unfold smallValid; decide +kernel

private theorem sp4816 : smallValid 4816 62 := by unfold smallValid; decide +kernel

private theorem sp4878 : smallValid 4878 62 := by unfold smallValid; decide +kernel

private theorem sp4940 : smallValid 4940 61 := by unfold smallValid; decide +kernel

private theorem sp5001 : smallValid 5001 62 := by unfold smallValid; decide +kernel

private theorem sp5063 : smallValid 5063 62 := by unfold smallValid; decide +kernel

private theorem sp5125 : smallValid 5125 62 := by unfold smallValid; decide +kernel

private theorem sp5187 : smallValid 5187 61 := by unfold smallValid; decide +kernel

private theorem sp5248 : smallValid 5248 62 := by unfold smallValid; decide +kernel

private theorem sp5310 : smallValid 5310 62 := by unfold smallValid; decide +kernel

private theorem sp5372 : smallValid 5372 62 := by unfold smallValid; decide +kernel

private theorem sp5434 : smallValid 5434 61 := by unfold smallValid; decide +kernel

private theorem sp5495 : smallValid 5495 62 := by unfold smallValid; decide +kernel

private theorem sp5557 : smallValid 5557 62 := by unfold smallValid; decide +kernel

private theorem sp5619 : smallValid 5619 62 := by unfold smallValid; decide +kernel

private theorem sp5681 : smallValid 5681 61 := by unfold smallValid; decide +kernel

private theorem sp5742 : smallValid 5742 62 := by unfold smallValid; decide +kernel

private theorem sp5804 : smallValid 5804 62 := by unfold smallValid; decide +kernel

private theorem sp5866 : smallValid 5866 62 := by unfold smallValid; decide +kernel

private theorem sp5928 : smallValid 5928 61 := by unfold smallValid; decide +kernel

private theorem sp5989 : smallValid 5989 62 := by unfold smallValid; decide +kernel

private theorem sp6051 : smallValid 6051 62 := by unfold smallValid; decide +kernel

private theorem sp6113 : smallValid 6113 62 := by unfold smallValid; decide +kernel

private theorem sp6175 : smallValid 6175 61 := by unfold smallValid; decide +kernel

private theorem sp6236 : smallValid 6236 62 := by unfold smallValid; decide +kernel

private theorem sp6298 : smallValid 6298 62 := by unfold smallValid; decide +kernel

private theorem sp6360 : smallValid 6360 62 := by unfold smallValid; decide +kernel

private theorem sp6422 : smallValid 6422 61 := by unfold smallValid; decide +kernel

private theorem sp6483 : smallValid 6483 62 := by unfold smallValid; decide +kernel

private theorem sp6545 : smallValid 6545 62 := by unfold smallValid; decide +kernel

private theorem sp6607 : smallValid 6607 62 := by unfold smallValid; decide +kernel

private theorem sp6669 : smallValid 6669 61 := by unfold smallValid; decide +kernel

private theorem sp6730 : smallValid 6730 62 := by unfold smallValid; decide +kernel

private theorem sp6792 : smallValid 6792 62 := by unfold smallValid; decide +kernel

private theorem sp6854 : smallValid 6854 62 := by unfold smallValid; decide +kernel

private theorem sp6916 : smallValid 6916 61 := by unfold smallValid; decide +kernel

private theorem sp6977 : smallValid 6977 62 := by unfold smallValid; decide +kernel

private theorem sp7039 : smallValid 7039 62 := by unfold smallValid; decide +kernel

private theorem sp7101 : smallValid 7101 62 := by unfold smallValid; decide +kernel

private theorem sp7163 : smallValid 7163 61 := by unfold smallValid; decide +kernel

private theorem sp7224 : smallValid 7224 62 := by unfold smallValid; decide +kernel

private theorem sp7286 : smallValid 7286 62 := by unfold smallValid; decide +kernel

private theorem sp7348 : smallValid 7348 62 := by unfold smallValid; decide +kernel

private theorem sp7410 : smallValid 7410 61 := by unfold smallValid; decide +kernel

private theorem sp7471 : smallValid 7471 62 := by unfold smallValid; decide +kernel

private theorem sp7533 : smallValid 7533 62 := by unfold smallValid; decide +kernel

private theorem sp7595 : smallValid 7595 62 := by unfold smallValid; decide +kernel

private theorem sp7657 : smallValid 7657 62 := by unfold smallValid; decide +kernel

private theorem sp7719 : smallValid 7719 62 := by unfold smallValid; decide +kernel

private theorem sp7781 : smallValid 7781 62 := by unfold smallValid; decide +kernel

private theorem sp7843 : smallValid 7843 62 := by unfold smallValid; decide +kernel

private theorem sp7905 : smallValid 7905 61 := by unfold smallValid; decide +kernel

private theorem sp7966 : smallValid 7966 62 := by unfold smallValid; decide +kernel

private theorem sp8028 : smallValid 8028 62 := by unfold smallValid; decide +kernel

private theorem sp8090 : smallValid 8090 62 := by unfold smallValid; decide +kernel

private theorem sp8152 : smallValid 8152 61 := by unfold smallValid; decide +kernel

private theorem sp8213 : smallValid 8213 62 := by unfold smallValid; decide +kernel

private theorem sp8275 : smallValid 8275 62 := by unfold smallValid; decide +kernel

private theorem sp8337 : smallValid 8337 62 := by unfold smallValid; decide +kernel

private theorem sp8399 : smallValid 8399 61 := by unfold smallValid; decide +kernel

private theorem sp8460 : smallValid 8460 62 := by unfold smallValid; decide +kernel

private theorem sp8522 : smallValid 8522 62 := by unfold smallValid; decide +kernel

private theorem sp8584 : smallValid 8584 62 := by unfold smallValid; decide +kernel

private theorem sp8646 : smallValid 8646 61 := by unfold smallValid; decide +kernel

private theorem sp8707 : smallValid 8707 62 := by unfold smallValid; decide +kernel

private theorem sp8769 : smallValid 8769 62 := by unfold smallValid; decide +kernel

private theorem sp8831 : smallValid 8831 62 := by unfold smallValid; decide +kernel

private theorem sp8893 : smallValid 8893 61 := by unfold smallValid; decide +kernel

private theorem sp8954 : smallValid 8954 62 := by unfold smallValid; decide +kernel

private theorem sp9016 : smallValid 9016 62 := by unfold smallValid; decide +kernel

private theorem sp9078 : smallValid 9078 62 := by unfold smallValid; decide +kernel

private theorem sp9140 : smallValid 9140 61 := by unfold smallValid; decide +kernel

private theorem sp9201 : smallValid 9201 62 := by unfold smallValid; decide +kernel

private theorem sp9263 : smallValid 9263 62 := by unfold smallValid; decide +kernel

private theorem sp9325 : smallValid 9325 62 := by unfold smallValid; decide +kernel

private theorem sp9387 : smallValid 9387 61 := by unfold smallValid; decide +kernel

private theorem sp9448 : smallValid 9448 62 := by unfold smallValid; decide +kernel

private theorem sp9510 : smallValid 9510 62 := by unfold smallValid; decide +kernel

private theorem sp9572 : smallValid 9572 62 := by unfold smallValid; decide +kernel

private theorem sp9634 : smallValid 9634 61 := by unfold smallValid; decide +kernel

private theorem sp9695 : smallValid 9695 62 := by unfold smallValid; decide +kernel

private theorem sp9757 : smallValid 9757 62 := by unfold smallValid; decide +kernel

private theorem sp9819 : smallValid 9819 62 := by unfold smallValid; decide +kernel

private theorem sp9881 : smallValid 9881 61 := by unfold smallValid; decide +kernel

private theorem sp9942 : smallValid 9942 62 := by unfold smallValid; decide +kernel

private theorem sp10004 : smallValid 10004 62 := by unfold smallValid; decide +kernel

private theorem sp10066 : smallValid 10066 62 := by unfold smallValid; decide +kernel

private theorem sp10128 : smallValid 10128 61 := by unfold smallValid; decide +kernel

private theorem sp10189 : smallValid 10189 62 := by unfold smallValid; decide +kernel

private theorem sp10251 : smallValid 10251 62 := by unfold smallValid; decide +kernel

private theorem sp10313 : smallValid 10313 62 := by unfold smallValid; decide +kernel

private theorem sp10375 : smallValid 10375 61 := by unfold smallValid; decide +kernel

private theorem sp10436 : smallValid 10436 62 := by unfold smallValid; decide +kernel

private theorem sp10498 : smallValid 10498 62 := by unfold smallValid; decide +kernel

private theorem sp10560 : smallValid 10560 62 := by unfold smallValid; decide +kernel

private theorem sp10622 : smallValid 10622 61 := by unfold smallValid; decide +kernel

private theorem sp10683 : smallValid 10683 62 := by unfold smallValid; decide +kernel

private theorem sp10745 : smallValid 10745 62 := by unfold smallValid; decide +kernel

private theorem sp10807 : smallValid 10807 62 := by unfold smallValid; decide +kernel

private theorem sp10869 : smallValid 10869 61 := by unfold smallValid; decide +kernel

private theorem sp10930 : smallValid 10930 62 := by unfold smallValid; decide +kernel

private theorem sp10992 : smallValid 10992 62 := by unfold smallValid; decide +kernel

private theorem sp11054 : smallValid 11054 62 := by unfold smallValid; decide +kernel

private theorem sp11116 : smallValid 11116 61 := by unfold smallValid; decide +kernel

private theorem sp11177 : smallValid 11177 62 := by unfold smallValid; decide +kernel

private theorem sp11239 : smallValid 11239 62 := by unfold smallValid; decide +kernel

private theorem sp11301 : smallValid 11301 62 := by unfold smallValid; decide +kernel

private theorem sp11363 : smallValid 11363 61 := by unfold smallValid; decide +kernel

private theorem sp11424 : smallValid 11424 62 := by unfold smallValid; decide +kernel

private theorem sp11486 : smallValid 11486 62 := by unfold smallValid; decide +kernel

private theorem sp11548 : smallValid 11548 62 := by unfold smallValid; decide +kernel

private theorem sp11610 : smallValid 11610 62 := by unfold smallValid; decide +kernel

private theorem sp11672 : smallValid 11672 62 := by unfold smallValid; decide +kernel

private theorem sp11734 : smallValid 11734 62 := by unfold smallValid; decide +kernel

private theorem sp11796 : smallValid 11796 62 := by unfold smallValid; decide +kernel

private theorem sp11858 : smallValid 11858 61 := by unfold smallValid; decide +kernel

private theorem sp11919 : smallValid 11919 62 := by unfold smallValid; decide +kernel

private theorem sp11981 : smallValid 11981 62 := by unfold smallValid; decide +kernel

private theorem sp12043 : smallValid 12043 62 := by unfold smallValid; decide +kernel

private theorem sp12105 : smallValid 12105 61 := by unfold smallValid; decide +kernel

private theorem sp12166 : smallValid 12166 62 := by unfold smallValid; decide +kernel

private theorem sp12228 : smallValid 12228 62 := by unfold smallValid; decide +kernel

private theorem sp12290 : smallValid 12290 62 := by unfold smallValid; decide +kernel

private theorem sp12352 : smallValid 12352 61 := by unfold smallValid; decide +kernel

private theorem sp12413 : smallValid 12413 62 := by unfold smallValid; decide +kernel

private theorem sp12475 : smallValid 12475 62 := by unfold smallValid; decide +kernel

private theorem sp12537 : smallValid 12537 62 := by unfold smallValid; decide +kernel

private theorem sp12599 : smallValid 12599 61 := by unfold smallValid; decide +kernel

private theorem sp12660 : smallValid 12660 62 := by unfold smallValid; decide +kernel

private theorem sp12722 : smallValid 12722 62 := by unfold smallValid; decide +kernel

private theorem sp12784 : smallValid 12784 62 := by unfold smallValid; decide +kernel

private theorem sp12846 : smallValid 12846 61 := by unfold smallValid; decide +kernel

private theorem sp12907 : smallValid 12907 62 := by unfold smallValid; decide +kernel

private theorem sp12969 : smallValid 12969 62 := by unfold smallValid; decide +kernel

private theorem sp13031 : smallValid 13031 62 := by unfold smallValid; decide +kernel

private theorem sp13093 : smallValid 13093 61 := by unfold smallValid; decide +kernel

private theorem sp13154 : smallValid 13154 62 := by unfold smallValid; decide +kernel

private theorem sp13216 : smallValid 13216 62 := by unfold smallValid; decide +kernel

private theorem sp13278 : smallValid 13278 62 := by unfold smallValid; decide +kernel

private theorem sp13340 : smallValid 13340 61 := by unfold smallValid; decide +kernel

private theorem sp13401 : smallValid 13401 62 := by unfold smallValid; decide +kernel

private theorem sp13463 : smallValid 13463 62 := by unfold smallValid; decide +kernel

private theorem sp13525 : smallValid 13525 62 := by unfold smallValid; decide +kernel

private theorem sp13587 : smallValid 13587 61 := by unfold smallValid; decide +kernel

private theorem sp13648 : smallValid 13648 62 := by unfold smallValid; decide +kernel

private theorem sp13710 : smallValid 13710 62 := by unfold smallValid; decide +kernel

private theorem sp13772 : smallValid 13772 62 := by unfold smallValid; decide +kernel

private theorem sp13834 : smallValid 13834 61 := by unfold smallValid; decide +kernel

private theorem sp13895 : smallValid 13895 62 := by unfold smallValid; decide +kernel

private theorem sp13957 : smallValid 13957 62 := by unfold smallValid; decide +kernel

private theorem sp14019 : smallValid 14019 62 := by unfold smallValid; decide +kernel

private theorem sp14081 : smallValid 14081 61 := by unfold smallValid; decide +kernel

private theorem sp14142 : smallValid 14142 62 := by unfold smallValid; decide +kernel

private theorem sp14204 : smallValid 14204 62 := by unfold smallValid; decide +kernel

private theorem sp14266 : smallValid 14266 62 := by unfold smallValid; decide +kernel

private theorem sp14328 : smallValid 14328 61 := by unfold smallValid; decide +kernel

private theorem sp14389 : smallValid 14389 62 := by unfold smallValid; decide +kernel

private theorem sp14451 : smallValid 14451 62 := by unfold smallValid; decide +kernel

private theorem sp14513 : smallValid 14513 62 := by unfold smallValid; decide +kernel

private theorem sp14575 : smallValid 14575 61 := by unfold smallValid; decide +kernel

private theorem sp14636 : smallValid 14636 62 := by unfold smallValid; decide +kernel

private theorem sp14698 : smallValid 14698 62 := by unfold smallValid; decide +kernel

private theorem sp14760 : smallValid 14760 62 := by unfold smallValid; decide +kernel

private theorem sp14822 : smallValid 14822 61 := by unfold smallValid; decide +kernel

private theorem sp14883 : smallValid 14883 62 := by unfold smallValid; decide +kernel

private theorem sp14945 : smallValid 14945 62 := by unfold smallValid; decide +kernel

private theorem sp15007 : smallValid 15007 62 := by unfold smallValid; decide +kernel

private theorem sp15069 : smallValid 15069 61 := by unfold smallValid; decide +kernel

private theorem sp15130 : smallValid 15130 62 := by unfold smallValid; decide +kernel

private theorem sp15192 : smallValid 15192 62 := by unfold smallValid; decide +kernel

private theorem sp15254 : smallValid 15254 62 := by unfold smallValid; decide +kernel

private theorem sp15316 : smallValid 15316 61 := by unfold smallValid; decide +kernel

private theorem sp15377 : smallValid 15377 62 := by unfold smallValid; decide +kernel

private theorem sp15439 : smallValid 15439 62 := by unfold smallValid; decide +kernel

private theorem sp15501 : smallValid 15501 62 := by unfold smallValid; decide +kernel

private theorem sp15563 : smallValid 15563 62 := by unfold smallValid; decide +kernel

private theorem sp15625 : smallValid 15625 62 := by unfold smallValid; decide +kernel

private theorem sp15687 : smallValid 15687 62 := by unfold smallValid; decide +kernel

private theorem sp15749 : smallValid 15749 62 := by unfold smallValid; decide +kernel

private theorem sp15811 : smallValid 15811 61 := by unfold smallValid; decide +kernel

private theorem sp15872 : smallValid 15872 62 := by unfold smallValid; decide +kernel

private theorem sp15934 : smallValid 15934 62 := by unfold smallValid; decide +kernel

private theorem sp15996 : smallValid 15996 62 := by unfold smallValid; decide +kernel

private theorem sp16058 : smallValid 16058 61 := by unfold smallValid; decide +kernel

private theorem sp16119 : smallValid 16119 62 := by unfold smallValid; decide +kernel

private theorem sp16181 : smallValid 16181 62 := by unfold smallValid; decide +kernel

private theorem sp16243 : smallValid 16243 62 := by unfold smallValid; decide +kernel

private theorem sp16305 : smallValid 16305 61 := by unfold smallValid; decide +kernel

private theorem sp16366 : smallValid 16366 62 := by unfold smallValid; decide +kernel

private theorem sp16428 : smallValid 16428 62 := by unfold smallValid; decide +kernel

private theorem sp16490 : smallValid 16490 62 := by unfold smallValid; decide +kernel

private theorem sp16552 : smallValid 16552 61 := by unfold smallValid; decide +kernel

private theorem sp16613 : smallValid 16613 62 := by unfold smallValid; decide +kernel

private theorem sp16675 : smallValid 16675 62 := by unfold smallValid; decide +kernel

private theorem sp16737 : smallValid 16737 62 := by unfold smallValid; decide +kernel

private theorem sp16799 : smallValid 16799 61 := by unfold smallValid; decide +kernel

private theorem sp16860 : smallValid 16860 62 := by unfold smallValid; decide +kernel

private theorem sp16922 : smallValid 16922 62 := by unfold smallValid; decide +kernel

private theorem sp16984 : smallValid 16984 62 := by unfold smallValid; decide +kernel

private theorem sp17046 : smallValid 17046 61 := by unfold smallValid; decide +kernel

private theorem sp17107 : smallValid 17107 62 := by unfold smallValid; decide +kernel

private theorem sp17169 : smallValid 17169 62 := by unfold smallValid; decide +kernel

private theorem sp17231 : smallValid 17231 62 := by unfold smallValid; decide +kernel

private theorem sp17293 : smallValid 17293 61 := by unfold smallValid; decide +kernel

private theorem sp17354 : smallValid 17354 62 := by unfold smallValid; decide +kernel

private theorem sp17416 : smallValid 17416 62 := by unfold smallValid; decide +kernel

private theorem sp17478 : smallValid 17478 62 := by unfold smallValid; decide +kernel

private theorem sp17540 : smallValid 17540 61 := by unfold smallValid; decide +kernel

private theorem sp17601 : smallValid 17601 62 := by unfold smallValid; decide +kernel

private theorem sp17663 : smallValid 17663 62 := by unfold smallValid; decide +kernel

private theorem sp17725 : smallValid 17725 62 := by unfold smallValid; decide +kernel

private theorem sp17787 : smallValid 17787 61 := by unfold smallValid; decide +kernel

private theorem sp17848 : smallValid 17848 62 := by unfold smallValid; decide +kernel

private theorem sp17910 : smallValid 17910 62 := by unfold smallValid; decide +kernel

private theorem sp17972 : smallValid 17972 62 := by unfold smallValid; decide +kernel

private theorem sp18034 : smallValid 18034 61 := by unfold smallValid; decide +kernel

private theorem sp18095 : smallValid 18095 62 := by unfold smallValid; decide +kernel

private theorem sp18157 : smallValid 18157 62 := by unfold smallValid; decide +kernel

private theorem sp18219 : smallValid 18219 62 := by unfold smallValid; decide +kernel

private theorem sp18281 : smallValid 18281 61 := by unfold smallValid; decide +kernel

private theorem sp18342 : smallValid 18342 62 := by unfold smallValid; decide +kernel

private theorem sp18404 : smallValid 18404 62 := by unfold smallValid; decide +kernel

private theorem sp18466 : smallValid 18466 62 := by unfold smallValid; decide +kernel

private theorem sp18528 : smallValid 18528 61 := by unfold smallValid; decide +kernel

private theorem sp18589 : smallValid 18589 62 := by unfold smallValid; decide +kernel

private theorem sp18651 : smallValid 18651 62 := by unfold smallValid; decide +kernel

private theorem sp18713 : smallValid 18713 62 := by unfold smallValid; decide +kernel

private theorem sp18775 : smallValid 18775 61 := by unfold smallValid; decide +kernel

private theorem sp18836 : smallValid 18836 62 := by unfold smallValid; decide +kernel

private theorem sp18898 : smallValid 18898 62 := by unfold smallValid; decide +kernel

private theorem sp18960 : smallValid 18960 62 := by unfold smallValid; decide +kernel

private theorem sp19022 : smallValid 19022 61 := by unfold smallValid; decide +kernel

private theorem sp19083 : smallValid 19083 62 := by unfold smallValid; decide +kernel

private theorem sp19145 : smallValid 19145 62 := by unfold smallValid; decide +kernel

private theorem sp19207 : smallValid 19207 62 := by unfold smallValid; decide +kernel

private theorem sp19269 : smallValid 19269 61 := by unfold smallValid; decide +kernel

private theorem sp19330 : smallValid 19330 62 := by unfold smallValid; decide +kernel

private theorem sp19392 : smallValid 19392 62 := by unfold smallValid; decide +kernel

private theorem sp19454 : smallValid 19454 62 := by unfold smallValid; decide +kernel

private theorem sp19516 : smallValid 19516 62 := by unfold smallValid; decide +kernel

private theorem sp19578 : smallValid 19578 62 := by unfold smallValid; decide +kernel

private theorem sp19640 : smallValid 19640 62 := by unfold smallValid; decide +kernel

private theorem sp19702 : smallValid 19702 62 := by unfold smallValid; decide +kernel

private theorem sp19764 : smallValid 19764 61 := by unfold smallValid; decide +kernel

private theorem sp19825 : smallValid 19825 62 := by unfold smallValid; decide +kernel

private theorem sp19887 : smallValid 19887 62 := by unfold smallValid; decide +kernel

private theorem sp19949 : smallValid 19949 62 := by unfold smallValid; decide +kernel

private theorem sp20011 : smallValid 20011 61 := by unfold smallValid; decide +kernel

private theorem sp20072 : smallValid 20072 62 := by unfold smallValid; decide +kernel

private theorem sp20134 : smallValid 20134 62 := by unfold smallValid; decide +kernel

private theorem sp20196 : smallValid 20196 62 := by unfold smallValid; decide +kernel

private theorem sp20258 : smallValid 20258 61 := by unfold smallValid; decide +kernel

private theorem sp20319 : smallValid 20319 62 := by unfold smallValid; decide +kernel

private theorem sp20381 : smallValid 20381 62 := by unfold smallValid; decide +kernel

private theorem sp20443 : smallValid 20443 62 := by unfold smallValid; decide +kernel

private theorem sp20505 : smallValid 20505 61 := by unfold smallValid; decide +kernel

private theorem sp20566 : smallValid 20566 62 := by unfold smallValid; decide +kernel

private theorem sp20628 : smallValid 20628 62 := by unfold smallValid; decide +kernel

private theorem sp20690 : smallValid 20690 62 := by unfold smallValid; decide +kernel

private theorem sp20752 : smallValid 20752 61 := by unfold smallValid; decide +kernel

private theorem sp20813 : smallValid 20813 62 := by unfold smallValid; decide +kernel

private theorem sp20875 : smallValid 20875 62 := by unfold smallValid; decide +kernel

private theorem sp20937 : smallValid 20937 62 := by unfold smallValid; decide +kernel

private theorem sp20999 : smallValid 20999 61 := by unfold smallValid; decide +kernel

private theorem sp21060 : smallValid 21060 62 := by unfold smallValid; decide +kernel

private theorem sp21122 : smallValid 21122 62 := by unfold smallValid; decide +kernel

private theorem sp21184 : smallValid 21184 62 := by unfold smallValid; decide +kernel

private theorem sp21246 : smallValid 21246 61 := by unfold smallValid; decide +kernel

private theorem sp21307 : smallValid 21307 62 := by unfold smallValid; decide +kernel

private theorem sp21369 : smallValid 21369 62 := by unfold smallValid; decide +kernel

private theorem sp21431 : smallValid 21431 62 := by unfold smallValid; decide +kernel

private theorem sp21493 : smallValid 21493 61 := by unfold smallValid; decide +kernel

private theorem sp21554 : smallValid 21554 62 := by unfold smallValid; decide +kernel

private theorem sp21616 : smallValid 21616 62 := by unfold smallValid; decide +kernel

private theorem sp21678 : smallValid 21678 62 := by unfold smallValid; decide +kernel

private theorem sp21740 : smallValid 21740 61 := by unfold smallValid; decide +kernel

private theorem sp21801 : smallValid 21801 62 := by unfold smallValid; decide +kernel

private theorem sp21863 : smallValid 21863 62 := by unfold smallValid; decide +kernel

private theorem sp21925 : smallValid 21925 62 := by unfold smallValid; decide +kernel

private theorem sp21987 : smallValid 21987 61 := by unfold smallValid; decide +kernel

private theorem sp22048 : smallValid 22048 62 := by unfold smallValid; decide +kernel

private theorem sp22110 : smallValid 22110 62 := by unfold smallValid; decide +kernel

private theorem sp22172 : smallValid 22172 62 := by unfold smallValid; decide +kernel

private theorem sp22234 : smallValid 22234 61 := by unfold smallValid; decide +kernel

private theorem sp22295 : smallValid 22295 62 := by unfold smallValid; decide +kernel

private theorem sp22357 : smallValid 22357 62 := by unfold smallValid; decide +kernel

private theorem sp22419 : smallValid 22419 62 := by unfold smallValid; decide +kernel

private theorem sp22481 : smallValid 22481 61 := by unfold smallValid; decide +kernel

private theorem sp22542 : smallValid 22542 62 := by unfold smallValid; decide +kernel

private theorem sp22604 : smallValid 22604 62 := by unfold smallValid; decide +kernel

private theorem sp22666 : smallValid 22666 62 := by unfold smallValid; decide +kernel

private theorem sp22728 : smallValid 22728 61 := by unfold smallValid; decide +kernel

private theorem sp22789 : smallValid 22789 62 := by unfold smallValid; decide +kernel

private theorem sp22851 : smallValid 22851 62 := by unfold smallValid; decide +kernel

private theorem sp22913 : smallValid 22913 62 := by unfold smallValid; decide +kernel

private theorem sp22975 : smallValid 22975 61 := by unfold smallValid; decide +kernel

private theorem sp23036 : smallValid 23036 62 := by unfold smallValid; decide +kernel

private theorem sp23098 : smallValid 23098 62 := by unfold smallValid; decide +kernel

private theorem sp23160 : smallValid 23160 62 := by unfold smallValid; decide +kernel

private theorem sp23222 : smallValid 23222 61 := by unfold smallValid; decide +kernel

private theorem sp23283 : smallValid 23283 62 := by unfold smallValid; decide +kernel

private theorem sp23345 : smallValid 23345 62 := by unfold smallValid; decide +kernel

private theorem sp23407 : smallValid 23407 62 := by unfold smallValid; decide +kernel

private theorem sp23469 : smallValid 23469 62 := by unfold smallValid; decide +kernel

private theorem sp23531 : smallValid 23531 62 := by unfold smallValid; decide +kernel

private theorem sp23593 : smallValid 23593 62 := by unfold smallValid; decide +kernel

private theorem sp23655 : smallValid 23655 62 := by unfold smallValid; decide +kernel

private theorem sp23717 : smallValid 23717 61 := by unfold smallValid; decide +kernel

private theorem sp23778 : smallValid 23778 62 := by unfold smallValid; decide +kernel

private theorem sp23840 : smallValid 23840 62 := by unfold smallValid; decide +kernel

private theorem sp23902 : smallValid 23902 62 := by unfold smallValid; decide +kernel

private theorem sp23964 : smallValid 23964 61 := by unfold smallValid; decide +kernel

private theorem sp24025 : smallValid 24025 62 := by unfold smallValid; decide +kernel

private theorem sp24087 : smallValid 24087 62 := by unfold smallValid; decide +kernel

private theorem sp24149 : smallValid 24149 62 := by unfold smallValid; decide +kernel

private theorem sp24211 : smallValid 24211 61 := by unfold smallValid; decide +kernel

private theorem sp24272 : smallValid 24272 62 := by unfold smallValid; decide +kernel

private theorem sp24334 : smallValid 24334 62 := by unfold smallValid; decide +kernel

private theorem sp24396 : smallValid 24396 62 := by unfold smallValid; decide +kernel

private theorem sp24458 : smallValid 24458 61 := by unfold smallValid; decide +kernel

private theorem sp24519 : smallValid 24519 62 := by unfold smallValid; decide +kernel

private theorem sp24581 : smallValid 24581 62 := by unfold smallValid; decide +kernel

private theorem sp24643 : smallValid 24643 62 := by unfold smallValid; decide +kernel

private theorem sp24705 : smallValid 24705 61 := by unfold smallValid; decide +kernel

private theorem sp24766 : smallValid 24766 62 := by unfold smallValid; decide +kernel

private theorem sp24828 : smallValid 24828 62 := by unfold smallValid; decide +kernel

private theorem sp24890 : smallValid 24890 62 := by unfold smallValid; decide +kernel

private theorem sp24952 : smallValid 24952 61 := by unfold smallValid; decide +kernel

private theorem sp25013 : smallValid 25013 62 := by unfold smallValid; decide +kernel

private theorem sp25075 : smallValid 25075 62 := by unfold smallValid; decide +kernel

private theorem sp25137 : smallValid 25137 62 := by unfold smallValid; decide +kernel

private theorem sp25199 : smallValid 25199 61 := by unfold smallValid; decide +kernel

private theorem sp25260 : smallValid 25260 62 := by unfold smallValid; decide +kernel

private theorem sp25322 : smallValid 25322 62 := by unfold smallValid; decide +kernel

private theorem sp25384 : smallValid 25384 62 := by unfold smallValid; decide +kernel

private theorem sp25446 : smallValid 25446 61 := by unfold smallValid; decide +kernel

private theorem sp25507 : smallValid 25507 62 := by unfold smallValid; decide +kernel

private theorem sp25569 : smallValid 25569 62 := by unfold smallValid; decide +kernel

private theorem sp25631 : smallValid 25631 62 := by unfold smallValid; decide +kernel

private theorem sp25693 : smallValid 25693 61 := by unfold smallValid; decide +kernel

private theorem sp25754 : smallValid 25754 62 := by unfold smallValid; decide +kernel

private theorem sp25816 : smallValid 25816 62 := by unfold smallValid; decide +kernel

private theorem sp25878 : smallValid 25878 62 := by unfold smallValid; decide +kernel

private theorem sp25940 : smallValid 25940 61 := by unfold smallValid; decide +kernel

private theorem sp26001 : smallValid 26001 62 := by unfold smallValid; decide +kernel

private theorem sp26063 : smallValid 26063 62 := by unfold smallValid; decide +kernel

private theorem sp26125 : smallValid 26125 62 := by unfold smallValid; decide +kernel

private theorem sp26187 : smallValid 26187 61 := by unfold smallValid; decide +kernel

private theorem sp26248 : smallValid 26248 62 := by unfold smallValid; decide +kernel

private theorem sp26310 : smallValid 26310 62 := by unfold smallValid; decide +kernel

private theorem sp26372 : smallValid 26372 62 := by unfold smallValid; decide +kernel

private theorem sp26434 : smallValid 26434 61 := by unfold smallValid; decide +kernel

private theorem sp26495 : smallValid 26495 62 := by unfold smallValid; decide +kernel

private theorem sp26557 : smallValid 26557 62 := by unfold smallValid; decide +kernel

private theorem sp26619 : smallValid 26619 62 := by unfold smallValid; decide +kernel

private theorem sp26681 : smallValid 26681 61 := by unfold smallValid; decide +kernel

private theorem sp26742 : smallValid 26742 62 := by unfold smallValid; decide +kernel

private theorem sp26804 : smallValid 26804 62 := by unfold smallValid; decide +kernel

private theorem sp26866 : smallValid 26866 62 := by unfold smallValid; decide +kernel

private theorem sp26928 : smallValid 26928 61 := by unfold smallValid; decide +kernel

private theorem sp26989 : smallValid 26989 62 := by unfold smallValid; decide +kernel

private theorem sp27051 : smallValid 27051 62 := by unfold smallValid; decide +kernel

private theorem sp27113 : smallValid 27113 62 := by unfold smallValid; decide +kernel

private theorem sp27175 : smallValid 27175 61 := by unfold smallValid; decide +kernel

private theorem sp27236 : smallValid 27236 62 := by unfold smallValid; decide +kernel

private theorem sp27298 : smallValid 27298 62 := by unfold smallValid; decide +kernel

private theorem sp27360 : smallValid 27360 62 := by unfold smallValid; decide +kernel

private theorem sp27422 : smallValid 27422 62 := by unfold smallValid; decide +kernel

private theorem sp27484 : smallValid 27484 62 := by unfold smallValid; decide +kernel

private theorem sp27546 : smallValid 27546 62 := by unfold smallValid; decide +kernel

private theorem sp27608 : smallValid 27608 62 := by unfold smallValid; decide +kernel

private theorem sp27670 : smallValid 27670 61 := by unfold smallValid; decide +kernel

private theorem sp27731 : smallValid 27731 62 := by unfold smallValid; decide +kernel

private theorem sp27793 : smallValid 27793 62 := by unfold smallValid; decide +kernel

private theorem sp27855 : smallValid 27855 62 := by unfold smallValid; decide +kernel

private theorem sp27917 : smallValid 27917 61 := by unfold smallValid; decide +kernel

private theorem sp27978 : smallValid 27978 62 := by unfold smallValid; decide +kernel

private theorem sp28040 : smallValid 28040 62 := by unfold smallValid; decide +kernel

private theorem sp28102 : smallValid 28102 62 := by unfold smallValid; decide +kernel

private theorem sp28164 : smallValid 28164 61 := by unfold smallValid; decide +kernel

private theorem sp28225 : smallValid 28225 62 := by unfold smallValid; decide +kernel

private theorem sp28287 : smallValid 28287 62 := by unfold smallValid; decide +kernel

private theorem sp28349 : smallValid 28349 62 := by unfold smallValid; decide +kernel

private theorem sp28411 : smallValid 28411 61 := by unfold smallValid; decide +kernel

private theorem sp28472 : smallValid 28472 62 := by unfold smallValid; decide +kernel

private theorem sp28534 : smallValid 28534 62 := by unfold smallValid; decide +kernel

private theorem sp28596 : smallValid 28596 62 := by unfold smallValid; decide +kernel

private theorem sp28658 : smallValid 28658 61 := by unfold smallValid; decide +kernel

private theorem sp28719 : smallValid 28719 62 := by unfold smallValid; decide +kernel

private theorem sp28781 : smallValid 28781 62 := by unfold smallValid; decide +kernel

private theorem sp28843 : smallValid 28843 62 := by unfold smallValid; decide +kernel

private theorem sp28905 : smallValid 28905 61 := by unfold smallValid; decide +kernel

private theorem sp28966 : smallValid 28966 62 := by unfold smallValid; decide +kernel

private theorem sp29028 : smallValid 29028 62 := by unfold smallValid; decide +kernel

private theorem sp29090 : smallValid 29090 62 := by unfold smallValid; decide +kernel

private theorem sp29152 : smallValid 29152 61 := by unfold smallValid; decide +kernel

private theorem sp29213 : smallValid 29213 62 := by unfold smallValid; decide +kernel

private theorem sp29275 : smallValid 29275 62 := by unfold smallValid; decide +kernel

private theorem sp29337 : smallValid 29337 62 := by unfold smallValid; decide +kernel

private theorem sp29399 : smallValid 29399 61 := by unfold smallValid; decide +kernel

private theorem sp29460 : smallValid 29460 62 := by unfold smallValid; decide +kernel

private theorem sp29522 : smallValid 29522 62 := by unfold smallValid; decide +kernel

private theorem sp29584 : smallValid 29584 62 := by unfold smallValid; decide +kernel

private theorem sp29646 : smallValid 29646 61 := by unfold smallValid; decide +kernel

private theorem sp29707 : smallValid 29707 62 := by unfold smallValid; decide +kernel

private theorem sp29769 : smallValid 29769 62 := by unfold smallValid; decide +kernel

private theorem sp29831 : smallValid 29831 62 := by unfold smallValid; decide +kernel

private theorem sp29893 : smallValid 29893 61 := by unfold smallValid; decide +kernel

private theorem sp29954 : smallValid 29954 62 := by unfold smallValid; decide +kernel

private theorem sp30016 : smallValid 30016 62 := by unfold smallValid; decide +kernel

private theorem sp30078 : smallValid 30078 62 := by unfold smallValid; decide +kernel

private theorem sp30140 : smallValid 30140 61 := by unfold smallValid; decide +kernel

private theorem sp30201 : smallValid 30201 62 := by unfold smallValid; decide +kernel

private theorem sp30263 : smallValid 30263 62 := by unfold smallValid; decide +kernel

private theorem sp30325 : smallValid 30325 62 := by unfold smallValid; decide +kernel

private theorem sp30387 : smallValid 30387 61 := by unfold smallValid; decide +kernel

private theorem sp30448 : smallValid 30448 62 := by unfold smallValid; decide +kernel

private theorem sp30510 : smallValid 30510 62 := by unfold smallValid; decide +kernel

private theorem sp30572 : smallValid 30572 62 := by unfold smallValid; decide +kernel

private theorem sp30634 : smallValid 30634 61 := by unfold smallValid; decide +kernel

private theorem sp30695 : smallValid 30695 62 := by unfold smallValid; decide +kernel

private theorem sp30757 : smallValid 30757 62 := by unfold smallValid; decide +kernel

private theorem sp30819 : smallValid 30819 62 := by unfold smallValid; decide +kernel

private theorem sp30881 : smallValid 30881 61 := by unfold smallValid; decide +kernel

private theorem sp30942 : smallValid 30942 62 := by unfold smallValid; decide +kernel

private theorem sp31004 : smallValid 31004 62 := by unfold smallValid; decide +kernel

private theorem sp31066 : smallValid 31066 62 := by unfold smallValid; decide +kernel

private theorem sp31128 : smallValid 31128 61 := by unfold smallValid; decide +kernel

private theorem sp31189 : smallValid 31189 62 := by unfold smallValid; decide +kernel

private theorem sp31251 : smallValid 31251 62 := by unfold smallValid; decide +kernel

private theorem sp31313 : smallValid 31313 62 := by unfold smallValid; decide +kernel

private theorem sp31375 : smallValid 31375 62 := by unfold smallValid; decide +kernel

private theorem sp31437 : smallValid 31437 62 := by unfold smallValid; decide +kernel

private theorem sp31499 : smallValid 31499 62 := by unfold smallValid; decide +kernel

private theorem sp31561 : smallValid 31561 62 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤31622) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 31623 := (joinSmall (lo:=0) (a:=15811) (b:=15812) (joinSmall (lo:=0) (a:=7905) (b:=7906) (joinSmall (lo:=0) (a:=3952) (b:=3953) (joinSmall (lo:=0) (a:=1976) (b:=1976) (joinSmall (lo:=0) (a:=988) (b:=988) (joinSmall (lo:=0) (a:=494) (b:=494) (joinSmall (lo:=0) (a:=247) (b:=247) (joinSmall (lo:=0) (a:=123) (b:=124) (joinSmall (lo:=0) (a:=61) (b:=62) sp0 sp61) (joinSmall (lo:=123) (a:=62) (b:=62) sp123 sp185)) (joinSmall (lo:=247) (a:=123) (b:=124) (joinSmall (lo:=247) (a:=61) (b:=62) sp247 sp308) (joinSmall (lo:=370) (a:=62) (b:=62) sp370 sp432))) (joinSmall (lo:=494) (a:=247) (b:=247) (joinSmall (lo:=494) (a:=123) (b:=124) (joinSmall (lo:=494) (a:=61) (b:=62) sp494 sp555) (joinSmall (lo:=617) (a:=62) (b:=62) sp617 sp679)) (joinSmall (lo:=741) (a:=123) (b:=124) (joinSmall (lo:=741) (a:=61) (b:=62) sp741 sp802) (joinSmall (lo:=864) (a:=62) (b:=62) sp864 sp926)))) (joinSmall (lo:=988) (a:=494) (b:=494) (joinSmall (lo:=988) (a:=247) (b:=247) (joinSmall (lo:=988) (a:=123) (b:=124) (joinSmall (lo:=988) (a:=61) (b:=62) sp988 sp1049) (joinSmall (lo:=1111) (a:=62) (b:=62) sp1111 sp1173)) (joinSmall (lo:=1235) (a:=123) (b:=124) (joinSmall (lo:=1235) (a:=61) (b:=62) sp1235 sp1296) (joinSmall (lo:=1358) (a:=62) (b:=62) sp1358 sp1420))) (joinSmall (lo:=1482) (a:=247) (b:=247) (joinSmall (lo:=1482) (a:=123) (b:=124) (joinSmall (lo:=1482) (a:=61) (b:=62) sp1482 sp1543) (joinSmall (lo:=1605) (a:=62) (b:=62) sp1605 sp1667)) (joinSmall (lo:=1729) (a:=123) (b:=124) (joinSmall (lo:=1729) (a:=61) (b:=62) sp1729 sp1790) (joinSmall (lo:=1852) (a:=62) (b:=62) sp1852 sp1914))))) (joinSmall (lo:=1976) (a:=988) (b:=988) (joinSmall (lo:=1976) (a:=494) (b:=494) (joinSmall (lo:=1976) (a:=247) (b:=247) (joinSmall (lo:=1976) (a:=123) (b:=124) (joinSmall (lo:=1976) (a:=61) (b:=62) sp1976 sp2037) (joinSmall (lo:=2099) (a:=62) (b:=62) sp2099 sp2161)) (joinSmall (lo:=2223) (a:=123) (b:=124) (joinSmall (lo:=2223) (a:=61) (b:=62) sp2223 sp2284) (joinSmall (lo:=2346) (a:=62) (b:=62) sp2346 sp2408))) (joinSmall (lo:=2470) (a:=247) (b:=247) (joinSmall (lo:=2470) (a:=123) (b:=124) (joinSmall (lo:=2470) (a:=61) (b:=62) sp2470 sp2531) (joinSmall (lo:=2593) (a:=62) (b:=62) sp2593 sp2655)) (joinSmall (lo:=2717) (a:=123) (b:=124) (joinSmall (lo:=2717) (a:=61) (b:=62) sp2717 sp2778) (joinSmall (lo:=2840) (a:=62) (b:=62) sp2840 sp2902)))) (joinSmall (lo:=2964) (a:=494) (b:=494) (joinSmall (lo:=2964) (a:=247) (b:=247) (joinSmall (lo:=2964) (a:=123) (b:=124) (joinSmall (lo:=2964) (a:=61) (b:=62) sp2964 sp3025) (joinSmall (lo:=3087) (a:=62) (b:=62) sp3087 sp3149)) (joinSmall (lo:=3211) (a:=123) (b:=124) (joinSmall (lo:=3211) (a:=61) (b:=62) sp3211 sp3272) (joinSmall (lo:=3334) (a:=62) (b:=62) sp3334 sp3396))) (joinSmall (lo:=3458) (a:=247) (b:=247) (joinSmall (lo:=3458) (a:=123) (b:=124) (joinSmall (lo:=3458) (a:=61) (b:=62) sp3458 sp3519) (joinSmall (lo:=3581) (a:=62) (b:=62) sp3581 sp3643)) (joinSmall (lo:=3705) (a:=123) (b:=124) (joinSmall (lo:=3705) (a:=61) (b:=62) sp3705 sp3766) (joinSmall (lo:=3828) (a:=62) (b:=62) sp3828 sp3890)))))) (joinSmall (lo:=3952) (a:=1976) (b:=1977) (joinSmall (lo:=3952) (a:=988) (b:=988) (joinSmall (lo:=3952) (a:=494) (b:=494) (joinSmall (lo:=3952) (a:=247) (b:=247) (joinSmall (lo:=3952) (a:=123) (b:=124) (joinSmall (lo:=3952) (a:=61) (b:=62) sp3952 sp4013) (joinSmall (lo:=4075) (a:=62) (b:=62) sp4075 sp4137)) (joinSmall (lo:=4199) (a:=123) (b:=124) (joinSmall (lo:=4199) (a:=61) (b:=62) sp4199 sp4260) (joinSmall (lo:=4322) (a:=62) (b:=62) sp4322 sp4384))) (joinSmall (lo:=4446) (a:=247) (b:=247) (joinSmall (lo:=4446) (a:=123) (b:=124) (joinSmall (lo:=4446) (a:=61) (b:=62) sp4446 sp4507) (joinSmall (lo:=4569) (a:=62) (b:=62) sp4569 sp4631)) (joinSmall (lo:=4693) (a:=123) (b:=124) (joinSmall (lo:=4693) (a:=61) (b:=62) sp4693 sp4754) (joinSmall (lo:=4816) (a:=62) (b:=62) sp4816 sp4878)))) (joinSmall (lo:=4940) (a:=494) (b:=494) (joinSmall (lo:=4940) (a:=247) (b:=247) (joinSmall (lo:=4940) (a:=123) (b:=124) (joinSmall (lo:=4940) (a:=61) (b:=62) sp4940 sp5001) (joinSmall (lo:=5063) (a:=62) (b:=62) sp5063 sp5125)) (joinSmall (lo:=5187) (a:=123) (b:=124) (joinSmall (lo:=5187) (a:=61) (b:=62) sp5187 sp5248) (joinSmall (lo:=5310) (a:=62) (b:=62) sp5310 sp5372))) (joinSmall (lo:=5434) (a:=247) (b:=247) (joinSmall (lo:=5434) (a:=123) (b:=124) (joinSmall (lo:=5434) (a:=61) (b:=62) sp5434 sp5495) (joinSmall (lo:=5557) (a:=62) (b:=62) sp5557 sp5619)) (joinSmall (lo:=5681) (a:=123) (b:=124) (joinSmall (lo:=5681) (a:=61) (b:=62) sp5681 sp5742) (joinSmall (lo:=5804) (a:=62) (b:=62) sp5804 sp5866))))) (joinSmall (lo:=5928) (a:=988) (b:=989) (joinSmall (lo:=5928) (a:=494) (b:=494) (joinSmall (lo:=5928) (a:=247) (b:=247) (joinSmall (lo:=5928) (a:=123) (b:=124) (joinSmall (lo:=5928) (a:=61) (b:=62) sp5928 sp5989) (joinSmall (lo:=6051) (a:=62) (b:=62) sp6051 sp6113)) (joinSmall (lo:=6175) (a:=123) (b:=124) (joinSmall (lo:=6175) (a:=61) (b:=62) sp6175 sp6236) (joinSmall (lo:=6298) (a:=62) (b:=62) sp6298 sp6360))) (joinSmall (lo:=6422) (a:=247) (b:=247) (joinSmall (lo:=6422) (a:=123) (b:=124) (joinSmall (lo:=6422) (a:=61) (b:=62) sp6422 sp6483) (joinSmall (lo:=6545) (a:=62) (b:=62) sp6545 sp6607)) (joinSmall (lo:=6669) (a:=123) (b:=124) (joinSmall (lo:=6669) (a:=61) (b:=62) sp6669 sp6730) (joinSmall (lo:=6792) (a:=62) (b:=62) sp6792 sp6854)))) (joinSmall (lo:=6916) (a:=494) (b:=495) (joinSmall (lo:=6916) (a:=247) (b:=247) (joinSmall (lo:=6916) (a:=123) (b:=124) (joinSmall (lo:=6916) (a:=61) (b:=62) sp6916 sp6977) (joinSmall (lo:=7039) (a:=62) (b:=62) sp7039 sp7101)) (joinSmall (lo:=7163) (a:=123) (b:=124) (joinSmall (lo:=7163) (a:=61) (b:=62) sp7163 sp7224) (joinSmall (lo:=7286) (a:=62) (b:=62) sp7286 sp7348))) (joinSmall (lo:=7410) (a:=247) (b:=248) (joinSmall (lo:=7410) (a:=123) (b:=124) (joinSmall (lo:=7410) (a:=61) (b:=62) sp7410 sp7471) (joinSmall (lo:=7533) (a:=62) (b:=62) sp7533 sp7595)) (joinSmall (lo:=7657) (a:=124) (b:=124) (joinSmall (lo:=7657) (a:=62) (b:=62) sp7657 sp7719) (joinSmall (lo:=7781) (a:=62) (b:=62) sp7781 sp7843))))))) (joinSmall (lo:=7905) (a:=3953) (b:=3953) (joinSmall (lo:=7905) (a:=1976) (b:=1977) (joinSmall (lo:=7905) (a:=988) (b:=988) (joinSmall (lo:=7905) (a:=494) (b:=494) (joinSmall (lo:=7905) (a:=247) (b:=247) (joinSmall (lo:=7905) (a:=123) (b:=124) (joinSmall (lo:=7905) (a:=61) (b:=62) sp7905 sp7966) (joinSmall (lo:=8028) (a:=62) (b:=62) sp8028 sp8090)) (joinSmall (lo:=8152) (a:=123) (b:=124) (joinSmall (lo:=8152) (a:=61) (b:=62) sp8152 sp8213) (joinSmall (lo:=8275) (a:=62) (b:=62) sp8275 sp8337))) (joinSmall (lo:=8399) (a:=247) (b:=247) (joinSmall (lo:=8399) (a:=123) (b:=124) (joinSmall (lo:=8399) (a:=61) (b:=62) sp8399 sp8460) (joinSmall (lo:=8522) (a:=62) (b:=62) sp8522 sp8584)) (joinSmall (lo:=8646) (a:=123) (b:=124) (joinSmall (lo:=8646) (a:=61) (b:=62) sp8646 sp8707) (joinSmall (lo:=8769) (a:=62) (b:=62) sp8769 sp8831)))) (joinSmall (lo:=8893) (a:=494) (b:=494) (joinSmall (lo:=8893) (a:=247) (b:=247) (joinSmall (lo:=8893) (a:=123) (b:=124) (joinSmall (lo:=8893) (a:=61) (b:=62) sp8893 sp8954) (joinSmall (lo:=9016) (a:=62) (b:=62) sp9016 sp9078)) (joinSmall (lo:=9140) (a:=123) (b:=124) (joinSmall (lo:=9140) (a:=61) (b:=62) sp9140 sp9201) (joinSmall (lo:=9263) (a:=62) (b:=62) sp9263 sp9325))) (joinSmall (lo:=9387) (a:=247) (b:=247) (joinSmall (lo:=9387) (a:=123) (b:=124) (joinSmall (lo:=9387) (a:=61) (b:=62) sp9387 sp9448) (joinSmall (lo:=9510) (a:=62) (b:=62) sp9510 sp9572)) (joinSmall (lo:=9634) (a:=123) (b:=124) (joinSmall (lo:=9634) (a:=61) (b:=62) sp9634 sp9695) (joinSmall (lo:=9757) (a:=62) (b:=62) sp9757 sp9819))))) (joinSmall (lo:=9881) (a:=988) (b:=989) (joinSmall (lo:=9881) (a:=494) (b:=494) (joinSmall (lo:=9881) (a:=247) (b:=247) (joinSmall (lo:=9881) (a:=123) (b:=124) (joinSmall (lo:=9881) (a:=61) (b:=62) sp9881 sp9942) (joinSmall (lo:=10004) (a:=62) (b:=62) sp10004 sp10066)) (joinSmall (lo:=10128) (a:=123) (b:=124) (joinSmall (lo:=10128) (a:=61) (b:=62) sp10128 sp10189) (joinSmall (lo:=10251) (a:=62) (b:=62) sp10251 sp10313))) (joinSmall (lo:=10375) (a:=247) (b:=247) (joinSmall (lo:=10375) (a:=123) (b:=124) (joinSmall (lo:=10375) (a:=61) (b:=62) sp10375 sp10436) (joinSmall (lo:=10498) (a:=62) (b:=62) sp10498 sp10560)) (joinSmall (lo:=10622) (a:=123) (b:=124) (joinSmall (lo:=10622) (a:=61) (b:=62) sp10622 sp10683) (joinSmall (lo:=10745) (a:=62) (b:=62) sp10745 sp10807)))) (joinSmall (lo:=10869) (a:=494) (b:=495) (joinSmall (lo:=10869) (a:=247) (b:=247) (joinSmall (lo:=10869) (a:=123) (b:=124) (joinSmall (lo:=10869) (a:=61) (b:=62) sp10869 sp10930) (joinSmall (lo:=10992) (a:=62) (b:=62) sp10992 sp11054)) (joinSmall (lo:=11116) (a:=123) (b:=124) (joinSmall (lo:=11116) (a:=61) (b:=62) sp11116 sp11177) (joinSmall (lo:=11239) (a:=62) (b:=62) sp11239 sp11301))) (joinSmall (lo:=11363) (a:=247) (b:=248) (joinSmall (lo:=11363) (a:=123) (b:=124) (joinSmall (lo:=11363) (a:=61) (b:=62) sp11363 sp11424) (joinSmall (lo:=11486) (a:=62) (b:=62) sp11486 sp11548)) (joinSmall (lo:=11610) (a:=124) (b:=124) (joinSmall (lo:=11610) (a:=62) (b:=62) sp11610 sp11672) (joinSmall (lo:=11734) (a:=62) (b:=62) sp11734 sp11796)))))) (joinSmall (lo:=11858) (a:=1976) (b:=1977) (joinSmall (lo:=11858) (a:=988) (b:=988) (joinSmall (lo:=11858) (a:=494) (b:=494) (joinSmall (lo:=11858) (a:=247) (b:=247) (joinSmall (lo:=11858) (a:=123) (b:=124) (joinSmall (lo:=11858) (a:=61) (b:=62) sp11858 sp11919) (joinSmall (lo:=11981) (a:=62) (b:=62) sp11981 sp12043)) (joinSmall (lo:=12105) (a:=123) (b:=124) (joinSmall (lo:=12105) (a:=61) (b:=62) sp12105 sp12166) (joinSmall (lo:=12228) (a:=62) (b:=62) sp12228 sp12290))) (joinSmall (lo:=12352) (a:=247) (b:=247) (joinSmall (lo:=12352) (a:=123) (b:=124) (joinSmall (lo:=12352) (a:=61) (b:=62) sp12352 sp12413) (joinSmall (lo:=12475) (a:=62) (b:=62) sp12475 sp12537)) (joinSmall (lo:=12599) (a:=123) (b:=124) (joinSmall (lo:=12599) (a:=61) (b:=62) sp12599 sp12660) (joinSmall (lo:=12722) (a:=62) (b:=62) sp12722 sp12784)))) (joinSmall (lo:=12846) (a:=494) (b:=494) (joinSmall (lo:=12846) (a:=247) (b:=247) (joinSmall (lo:=12846) (a:=123) (b:=124) (joinSmall (lo:=12846) (a:=61) (b:=62) sp12846 sp12907) (joinSmall (lo:=12969) (a:=62) (b:=62) sp12969 sp13031)) (joinSmall (lo:=13093) (a:=123) (b:=124) (joinSmall (lo:=13093) (a:=61) (b:=62) sp13093 sp13154) (joinSmall (lo:=13216) (a:=62) (b:=62) sp13216 sp13278))) (joinSmall (lo:=13340) (a:=247) (b:=247) (joinSmall (lo:=13340) (a:=123) (b:=124) (joinSmall (lo:=13340) (a:=61) (b:=62) sp13340 sp13401) (joinSmall (lo:=13463) (a:=62) (b:=62) sp13463 sp13525)) (joinSmall (lo:=13587) (a:=123) (b:=124) (joinSmall (lo:=13587) (a:=61) (b:=62) sp13587 sp13648) (joinSmall (lo:=13710) (a:=62) (b:=62) sp13710 sp13772))))) (joinSmall (lo:=13834) (a:=988) (b:=989) (joinSmall (lo:=13834) (a:=494) (b:=494) (joinSmall (lo:=13834) (a:=247) (b:=247) (joinSmall (lo:=13834) (a:=123) (b:=124) (joinSmall (lo:=13834) (a:=61) (b:=62) sp13834 sp13895) (joinSmall (lo:=13957) (a:=62) (b:=62) sp13957 sp14019)) (joinSmall (lo:=14081) (a:=123) (b:=124) (joinSmall (lo:=14081) (a:=61) (b:=62) sp14081 sp14142) (joinSmall (lo:=14204) (a:=62) (b:=62) sp14204 sp14266))) (joinSmall (lo:=14328) (a:=247) (b:=247) (joinSmall (lo:=14328) (a:=123) (b:=124) (joinSmall (lo:=14328) (a:=61) (b:=62) sp14328 sp14389) (joinSmall (lo:=14451) (a:=62) (b:=62) sp14451 sp14513)) (joinSmall (lo:=14575) (a:=123) (b:=124) (joinSmall (lo:=14575) (a:=61) (b:=62) sp14575 sp14636) (joinSmall (lo:=14698) (a:=62) (b:=62) sp14698 sp14760)))) (joinSmall (lo:=14822) (a:=494) (b:=495) (joinSmall (lo:=14822) (a:=247) (b:=247) (joinSmall (lo:=14822) (a:=123) (b:=124) (joinSmall (lo:=14822) (a:=61) (b:=62) sp14822 sp14883) (joinSmall (lo:=14945) (a:=62) (b:=62) sp14945 sp15007)) (joinSmall (lo:=15069) (a:=123) (b:=124) (joinSmall (lo:=15069) (a:=61) (b:=62) sp15069 sp15130) (joinSmall (lo:=15192) (a:=62) (b:=62) sp15192 sp15254))) (joinSmall (lo:=15316) (a:=247) (b:=248) (joinSmall (lo:=15316) (a:=123) (b:=124) (joinSmall (lo:=15316) (a:=61) (b:=62) sp15316 sp15377) (joinSmall (lo:=15439) (a:=62) (b:=62) sp15439 sp15501)) (joinSmall (lo:=15563) (a:=124) (b:=124) (joinSmall (lo:=15563) (a:=62) (b:=62) sp15563 sp15625) (joinSmall (lo:=15687) (a:=62) (b:=62) sp15687 sp15749)))))))) (joinSmall (lo:=15811) (a:=7906) (b:=7906) (joinSmall (lo:=15811) (a:=3953) (b:=3953) (joinSmall (lo:=15811) (a:=1976) (b:=1977) (joinSmall (lo:=15811) (a:=988) (b:=988) (joinSmall (lo:=15811) (a:=494) (b:=494) (joinSmall (lo:=15811) (a:=247) (b:=247) (joinSmall (lo:=15811) (a:=123) (b:=124) (joinSmall (lo:=15811) (a:=61) (b:=62) sp15811 sp15872) (joinSmall (lo:=15934) (a:=62) (b:=62) sp15934 sp15996)) (joinSmall (lo:=16058) (a:=123) (b:=124) (joinSmall (lo:=16058) (a:=61) (b:=62) sp16058 sp16119) (joinSmall (lo:=16181) (a:=62) (b:=62) sp16181 sp16243))) (joinSmall (lo:=16305) (a:=247) (b:=247) (joinSmall (lo:=16305) (a:=123) (b:=124) (joinSmall (lo:=16305) (a:=61) (b:=62) sp16305 sp16366) (joinSmall (lo:=16428) (a:=62) (b:=62) sp16428 sp16490)) (joinSmall (lo:=16552) (a:=123) (b:=124) (joinSmall (lo:=16552) (a:=61) (b:=62) sp16552 sp16613) (joinSmall (lo:=16675) (a:=62) (b:=62) sp16675 sp16737)))) (joinSmall (lo:=16799) (a:=494) (b:=494) (joinSmall (lo:=16799) (a:=247) (b:=247) (joinSmall (lo:=16799) (a:=123) (b:=124) (joinSmall (lo:=16799) (a:=61) (b:=62) sp16799 sp16860) (joinSmall (lo:=16922) (a:=62) (b:=62) sp16922 sp16984)) (joinSmall (lo:=17046) (a:=123) (b:=124) (joinSmall (lo:=17046) (a:=61) (b:=62) sp17046 sp17107) (joinSmall (lo:=17169) (a:=62) (b:=62) sp17169 sp17231))) (joinSmall (lo:=17293) (a:=247) (b:=247) (joinSmall (lo:=17293) (a:=123) (b:=124) (joinSmall (lo:=17293) (a:=61) (b:=62) sp17293 sp17354) (joinSmall (lo:=17416) (a:=62) (b:=62) sp17416 sp17478)) (joinSmall (lo:=17540) (a:=123) (b:=124) (joinSmall (lo:=17540) (a:=61) (b:=62) sp17540 sp17601) (joinSmall (lo:=17663) (a:=62) (b:=62) sp17663 sp17725))))) (joinSmall (lo:=17787) (a:=988) (b:=989) (joinSmall (lo:=17787) (a:=494) (b:=494) (joinSmall (lo:=17787) (a:=247) (b:=247) (joinSmall (lo:=17787) (a:=123) (b:=124) (joinSmall (lo:=17787) (a:=61) (b:=62) sp17787 sp17848) (joinSmall (lo:=17910) (a:=62) (b:=62) sp17910 sp17972)) (joinSmall (lo:=18034) (a:=123) (b:=124) (joinSmall (lo:=18034) (a:=61) (b:=62) sp18034 sp18095) (joinSmall (lo:=18157) (a:=62) (b:=62) sp18157 sp18219))) (joinSmall (lo:=18281) (a:=247) (b:=247) (joinSmall (lo:=18281) (a:=123) (b:=124) (joinSmall (lo:=18281) (a:=61) (b:=62) sp18281 sp18342) (joinSmall (lo:=18404) (a:=62) (b:=62) sp18404 sp18466)) (joinSmall (lo:=18528) (a:=123) (b:=124) (joinSmall (lo:=18528) (a:=61) (b:=62) sp18528 sp18589) (joinSmall (lo:=18651) (a:=62) (b:=62) sp18651 sp18713)))) (joinSmall (lo:=18775) (a:=494) (b:=495) (joinSmall (lo:=18775) (a:=247) (b:=247) (joinSmall (lo:=18775) (a:=123) (b:=124) (joinSmall (lo:=18775) (a:=61) (b:=62) sp18775 sp18836) (joinSmall (lo:=18898) (a:=62) (b:=62) sp18898 sp18960)) (joinSmall (lo:=19022) (a:=123) (b:=124) (joinSmall (lo:=19022) (a:=61) (b:=62) sp19022 sp19083) (joinSmall (lo:=19145) (a:=62) (b:=62) sp19145 sp19207))) (joinSmall (lo:=19269) (a:=247) (b:=248) (joinSmall (lo:=19269) (a:=123) (b:=124) (joinSmall (lo:=19269) (a:=61) (b:=62) sp19269 sp19330) (joinSmall (lo:=19392) (a:=62) (b:=62) sp19392 sp19454)) (joinSmall (lo:=19516) (a:=124) (b:=124) (joinSmall (lo:=19516) (a:=62) (b:=62) sp19516 sp19578) (joinSmall (lo:=19640) (a:=62) (b:=62) sp19640 sp19702)))))) (joinSmall (lo:=19764) (a:=1976) (b:=1977) (joinSmall (lo:=19764) (a:=988) (b:=988) (joinSmall (lo:=19764) (a:=494) (b:=494) (joinSmall (lo:=19764) (a:=247) (b:=247) (joinSmall (lo:=19764) (a:=123) (b:=124) (joinSmall (lo:=19764) (a:=61) (b:=62) sp19764 sp19825) (joinSmall (lo:=19887) (a:=62) (b:=62) sp19887 sp19949)) (joinSmall (lo:=20011) (a:=123) (b:=124) (joinSmall (lo:=20011) (a:=61) (b:=62) sp20011 sp20072) (joinSmall (lo:=20134) (a:=62) (b:=62) sp20134 sp20196))) (joinSmall (lo:=20258) (a:=247) (b:=247) (joinSmall (lo:=20258) (a:=123) (b:=124) (joinSmall (lo:=20258) (a:=61) (b:=62) sp20258 sp20319) (joinSmall (lo:=20381) (a:=62) (b:=62) sp20381 sp20443)) (joinSmall (lo:=20505) (a:=123) (b:=124) (joinSmall (lo:=20505) (a:=61) (b:=62) sp20505 sp20566) (joinSmall (lo:=20628) (a:=62) (b:=62) sp20628 sp20690)))) (joinSmall (lo:=20752) (a:=494) (b:=494) (joinSmall (lo:=20752) (a:=247) (b:=247) (joinSmall (lo:=20752) (a:=123) (b:=124) (joinSmall (lo:=20752) (a:=61) (b:=62) sp20752 sp20813) (joinSmall (lo:=20875) (a:=62) (b:=62) sp20875 sp20937)) (joinSmall (lo:=20999) (a:=123) (b:=124) (joinSmall (lo:=20999) (a:=61) (b:=62) sp20999 sp21060) (joinSmall (lo:=21122) (a:=62) (b:=62) sp21122 sp21184))) (joinSmall (lo:=21246) (a:=247) (b:=247) (joinSmall (lo:=21246) (a:=123) (b:=124) (joinSmall (lo:=21246) (a:=61) (b:=62) sp21246 sp21307) (joinSmall (lo:=21369) (a:=62) (b:=62) sp21369 sp21431)) (joinSmall (lo:=21493) (a:=123) (b:=124) (joinSmall (lo:=21493) (a:=61) (b:=62) sp21493 sp21554) (joinSmall (lo:=21616) (a:=62) (b:=62) sp21616 sp21678))))) (joinSmall (lo:=21740) (a:=988) (b:=989) (joinSmall (lo:=21740) (a:=494) (b:=494) (joinSmall (lo:=21740) (a:=247) (b:=247) (joinSmall (lo:=21740) (a:=123) (b:=124) (joinSmall (lo:=21740) (a:=61) (b:=62) sp21740 sp21801) (joinSmall (lo:=21863) (a:=62) (b:=62) sp21863 sp21925)) (joinSmall (lo:=21987) (a:=123) (b:=124) (joinSmall (lo:=21987) (a:=61) (b:=62) sp21987 sp22048) (joinSmall (lo:=22110) (a:=62) (b:=62) sp22110 sp22172))) (joinSmall (lo:=22234) (a:=247) (b:=247) (joinSmall (lo:=22234) (a:=123) (b:=124) (joinSmall (lo:=22234) (a:=61) (b:=62) sp22234 sp22295) (joinSmall (lo:=22357) (a:=62) (b:=62) sp22357 sp22419)) (joinSmall (lo:=22481) (a:=123) (b:=124) (joinSmall (lo:=22481) (a:=61) (b:=62) sp22481 sp22542) (joinSmall (lo:=22604) (a:=62) (b:=62) sp22604 sp22666)))) (joinSmall (lo:=22728) (a:=494) (b:=495) (joinSmall (lo:=22728) (a:=247) (b:=247) (joinSmall (lo:=22728) (a:=123) (b:=124) (joinSmall (lo:=22728) (a:=61) (b:=62) sp22728 sp22789) (joinSmall (lo:=22851) (a:=62) (b:=62) sp22851 sp22913)) (joinSmall (lo:=22975) (a:=123) (b:=124) (joinSmall (lo:=22975) (a:=61) (b:=62) sp22975 sp23036) (joinSmall (lo:=23098) (a:=62) (b:=62) sp23098 sp23160))) (joinSmall (lo:=23222) (a:=247) (b:=248) (joinSmall (lo:=23222) (a:=123) (b:=124) (joinSmall (lo:=23222) (a:=61) (b:=62) sp23222 sp23283) (joinSmall (lo:=23345) (a:=62) (b:=62) sp23345 sp23407)) (joinSmall (lo:=23469) (a:=124) (b:=124) (joinSmall (lo:=23469) (a:=62) (b:=62) sp23469 sp23531) (joinSmall (lo:=23593) (a:=62) (b:=62) sp23593 sp23655))))))) (joinSmall (lo:=23717) (a:=3953) (b:=3953) (joinSmall (lo:=23717) (a:=1976) (b:=1977) (joinSmall (lo:=23717) (a:=988) (b:=988) (joinSmall (lo:=23717) (a:=494) (b:=494) (joinSmall (lo:=23717) (a:=247) (b:=247) (joinSmall (lo:=23717) (a:=123) (b:=124) (joinSmall (lo:=23717) (a:=61) (b:=62) sp23717 sp23778) (joinSmall (lo:=23840) (a:=62) (b:=62) sp23840 sp23902)) (joinSmall (lo:=23964) (a:=123) (b:=124) (joinSmall (lo:=23964) (a:=61) (b:=62) sp23964 sp24025) (joinSmall (lo:=24087) (a:=62) (b:=62) sp24087 sp24149))) (joinSmall (lo:=24211) (a:=247) (b:=247) (joinSmall (lo:=24211) (a:=123) (b:=124) (joinSmall (lo:=24211) (a:=61) (b:=62) sp24211 sp24272) (joinSmall (lo:=24334) (a:=62) (b:=62) sp24334 sp24396)) (joinSmall (lo:=24458) (a:=123) (b:=124) (joinSmall (lo:=24458) (a:=61) (b:=62) sp24458 sp24519) (joinSmall (lo:=24581) (a:=62) (b:=62) sp24581 sp24643)))) (joinSmall (lo:=24705) (a:=494) (b:=494) (joinSmall (lo:=24705) (a:=247) (b:=247) (joinSmall (lo:=24705) (a:=123) (b:=124) (joinSmall (lo:=24705) (a:=61) (b:=62) sp24705 sp24766) (joinSmall (lo:=24828) (a:=62) (b:=62) sp24828 sp24890)) (joinSmall (lo:=24952) (a:=123) (b:=124) (joinSmall (lo:=24952) (a:=61) (b:=62) sp24952 sp25013) (joinSmall (lo:=25075) (a:=62) (b:=62) sp25075 sp25137))) (joinSmall (lo:=25199) (a:=247) (b:=247) (joinSmall (lo:=25199) (a:=123) (b:=124) (joinSmall (lo:=25199) (a:=61) (b:=62) sp25199 sp25260) (joinSmall (lo:=25322) (a:=62) (b:=62) sp25322 sp25384)) (joinSmall (lo:=25446) (a:=123) (b:=124) (joinSmall (lo:=25446) (a:=61) (b:=62) sp25446 sp25507) (joinSmall (lo:=25569) (a:=62) (b:=62) sp25569 sp25631))))) (joinSmall (lo:=25693) (a:=988) (b:=989) (joinSmall (lo:=25693) (a:=494) (b:=494) (joinSmall (lo:=25693) (a:=247) (b:=247) (joinSmall (lo:=25693) (a:=123) (b:=124) (joinSmall (lo:=25693) (a:=61) (b:=62) sp25693 sp25754) (joinSmall (lo:=25816) (a:=62) (b:=62) sp25816 sp25878)) (joinSmall (lo:=25940) (a:=123) (b:=124) (joinSmall (lo:=25940) (a:=61) (b:=62) sp25940 sp26001) (joinSmall (lo:=26063) (a:=62) (b:=62) sp26063 sp26125))) (joinSmall (lo:=26187) (a:=247) (b:=247) (joinSmall (lo:=26187) (a:=123) (b:=124) (joinSmall (lo:=26187) (a:=61) (b:=62) sp26187 sp26248) (joinSmall (lo:=26310) (a:=62) (b:=62) sp26310 sp26372)) (joinSmall (lo:=26434) (a:=123) (b:=124) (joinSmall (lo:=26434) (a:=61) (b:=62) sp26434 sp26495) (joinSmall (lo:=26557) (a:=62) (b:=62) sp26557 sp26619)))) (joinSmall (lo:=26681) (a:=494) (b:=495) (joinSmall (lo:=26681) (a:=247) (b:=247) (joinSmall (lo:=26681) (a:=123) (b:=124) (joinSmall (lo:=26681) (a:=61) (b:=62) sp26681 sp26742) (joinSmall (lo:=26804) (a:=62) (b:=62) sp26804 sp26866)) (joinSmall (lo:=26928) (a:=123) (b:=124) (joinSmall (lo:=26928) (a:=61) (b:=62) sp26928 sp26989) (joinSmall (lo:=27051) (a:=62) (b:=62) sp27051 sp27113))) (joinSmall (lo:=27175) (a:=247) (b:=248) (joinSmall (lo:=27175) (a:=123) (b:=124) (joinSmall (lo:=27175) (a:=61) (b:=62) sp27175 sp27236) (joinSmall (lo:=27298) (a:=62) (b:=62) sp27298 sp27360)) (joinSmall (lo:=27422) (a:=124) (b:=124) (joinSmall (lo:=27422) (a:=62) (b:=62) sp27422 sp27484) (joinSmall (lo:=27546) (a:=62) (b:=62) sp27546 sp27608)))))) (joinSmall (lo:=27670) (a:=1976) (b:=1977) (joinSmall (lo:=27670) (a:=988) (b:=988) (joinSmall (lo:=27670) (a:=494) (b:=494) (joinSmall (lo:=27670) (a:=247) (b:=247) (joinSmall (lo:=27670) (a:=123) (b:=124) (joinSmall (lo:=27670) (a:=61) (b:=62) sp27670 sp27731) (joinSmall (lo:=27793) (a:=62) (b:=62) sp27793 sp27855)) (joinSmall (lo:=27917) (a:=123) (b:=124) (joinSmall (lo:=27917) (a:=61) (b:=62) sp27917 sp27978) (joinSmall (lo:=28040) (a:=62) (b:=62) sp28040 sp28102))) (joinSmall (lo:=28164) (a:=247) (b:=247) (joinSmall (lo:=28164) (a:=123) (b:=124) (joinSmall (lo:=28164) (a:=61) (b:=62) sp28164 sp28225) (joinSmall (lo:=28287) (a:=62) (b:=62) sp28287 sp28349)) (joinSmall (lo:=28411) (a:=123) (b:=124) (joinSmall (lo:=28411) (a:=61) (b:=62) sp28411 sp28472) (joinSmall (lo:=28534) (a:=62) (b:=62) sp28534 sp28596)))) (joinSmall (lo:=28658) (a:=494) (b:=494) (joinSmall (lo:=28658) (a:=247) (b:=247) (joinSmall (lo:=28658) (a:=123) (b:=124) (joinSmall (lo:=28658) (a:=61) (b:=62) sp28658 sp28719) (joinSmall (lo:=28781) (a:=62) (b:=62) sp28781 sp28843)) (joinSmall (lo:=28905) (a:=123) (b:=124) (joinSmall (lo:=28905) (a:=61) (b:=62) sp28905 sp28966) (joinSmall (lo:=29028) (a:=62) (b:=62) sp29028 sp29090))) (joinSmall (lo:=29152) (a:=247) (b:=247) (joinSmall (lo:=29152) (a:=123) (b:=124) (joinSmall (lo:=29152) (a:=61) (b:=62) sp29152 sp29213) (joinSmall (lo:=29275) (a:=62) (b:=62) sp29275 sp29337)) (joinSmall (lo:=29399) (a:=123) (b:=124) (joinSmall (lo:=29399) (a:=61) (b:=62) sp29399 sp29460) (joinSmall (lo:=29522) (a:=62) (b:=62) sp29522 sp29584))))) (joinSmall (lo:=29646) (a:=988) (b:=989) (joinSmall (lo:=29646) (a:=494) (b:=494) (joinSmall (lo:=29646) (a:=247) (b:=247) (joinSmall (lo:=29646) (a:=123) (b:=124) (joinSmall (lo:=29646) (a:=61) (b:=62) sp29646 sp29707) (joinSmall (lo:=29769) (a:=62) (b:=62) sp29769 sp29831)) (joinSmall (lo:=29893) (a:=123) (b:=124) (joinSmall (lo:=29893) (a:=61) (b:=62) sp29893 sp29954) (joinSmall (lo:=30016) (a:=62) (b:=62) sp30016 sp30078))) (joinSmall (lo:=30140) (a:=247) (b:=247) (joinSmall (lo:=30140) (a:=123) (b:=124) (joinSmall (lo:=30140) (a:=61) (b:=62) sp30140 sp30201) (joinSmall (lo:=30263) (a:=62) (b:=62) sp30263 sp30325)) (joinSmall (lo:=30387) (a:=123) (b:=124) (joinSmall (lo:=30387) (a:=61) (b:=62) sp30387 sp30448) (joinSmall (lo:=30510) (a:=62) (b:=62) sp30510 sp30572)))) (joinSmall (lo:=30634) (a:=494) (b:=495) (joinSmall (lo:=30634) (a:=247) (b:=247) (joinSmall (lo:=30634) (a:=123) (b:=124) (joinSmall (lo:=30634) (a:=61) (b:=62) sp30634 sp30695) (joinSmall (lo:=30757) (a:=62) (b:=62) sp30757 sp30819)) (joinSmall (lo:=30881) (a:=123) (b:=124) (joinSmall (lo:=30881) (a:=61) (b:=62) sp30881 sp30942) (joinSmall (lo:=31004) (a:=62) (b:=62) sp31004 sp31066))) (joinSmall (lo:=31128) (a:=247) (b:=248) (joinSmall (lo:=31128) (a:=123) (b:=124) (joinSmall (lo:=31128) (a:=61) (b:=62) sp31128 sp31189) (joinSmall (lo:=31251) (a:=62) (b:=62) sp31251 sp31313)) (joinSmall (lo:=31375) (a:=124) (b:=124) (joinSmall (lo:=31375) (a:=62) (b:=62) sp31375 sp31437) (joinSmall (lo:=31499) (a:=62) (b:=62) sp31499 sp31561)))))))))
  have good : (List.range 31623).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 1000000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 31622 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 31622 := by
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


private def packet (i : ℕ) : ℕ := (if i < 254 then (if i < 127 then (if i < 63 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0 else 0) else (if i < 10 then 0 else 0)) else (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else 0)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0 else 0) else (if i < 18 then 0 else 0)) else (if i < 21 then (if i < 20 then 0 else 0) else (if i < 22 then 0 else 0))) else (if i < 27 then (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else 0)) else (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else 0))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then 0 else 0) else (if i < 34 then 0 else 0)) else (if i < 37 then (if i < 36 then 0 else 0) else (if i < 38 then 0 else 0))) else (if i < 43 then (if i < 41 then (if i < 40 then 0 else 0) else (if i < 42 then 0 else 0)) else (if i < 45 then (if i < 44 then 0 else 0) else (if i < 46 then 0 else 0)))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then 0 else 0) else (if i < 50 then 0 else 0)) else (if i < 53 then (if i < 52 then 0 else 0) else (if i < 54 then 0 else 0))) else (if i < 59 then (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else 0)) else (if i < 61 then (if i < 60 then 0 else 0) else (if i < 62 then 0 else 0)))))) else (if i < 95 then (if i < 79 then (if i < 71 then (if i < 67 then (if i < 65 then (if i < 64 then 0 else 0) else (if i < 66 then 0 else 0)) else (if i < 69 then (if i < 68 then 0 else 0) else (if i < 70 then 0 else 0))) else (if i < 75 then (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else 0)) else (if i < 77 then (if i < 76 then 0 else 0) else (if i < 78 then 0 else 0)))) else (if i < 87 then (if i < 83 then (if i < 81 then (if i < 80 then 0 else 0) else (if i < 82 then 0 else 0)) else (if i < 85 then (if i < 84 then 0 else 0) else (if i < 86 then 0 else 0))) else (if i < 91 then (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else 0)) else (if i < 93 then (if i < 92 then 0 else 0) else (if i < 94 then 0 else 0))))) else (if i < 111 then (if i < 103 then (if i < 99 then (if i < 97 then (if i < 96 then 0 else 0) else (if i < 98 then 0 else 0)) else (if i < 101 then (if i < 100 then 0 else 0) else (if i < 102 then 0 else 0))) else (if i < 107 then (if i < 105 then (if i < 104 then 0 else 0) else (if i < 106 then 0 else 0)) else (if i < 109 then (if i < 108 then 0 else 0) else (if i < 110 then 0 else 0)))) else (if i < 119 then (if i < 115 then (if i < 113 then (if i < 112 then 0 else 0) else (if i < 114 then 0 else 0)) else (if i < 117 then (if i < 116 then 0 else 0) else (if i < 118 then 0 else 0))) else (if i < 123 then (if i < 121 then (if i < 120 then 0 else 0) else (if i < 122 then 0 else 0)) else (if i < 125 then (if i < 124 then 0 else 0) else (if i < 126 then 0 else 0))))))) else (if i < 190 then (if i < 158 then (if i < 142 then (if i < 134 then (if i < 130 then (if i < 128 then 0 else (if i < 129 then 0 else 0)) else (if i < 132 then (if i < 131 then 0 else 0) else (if i < 133 then 0 else 0))) else (if i < 138 then (if i < 136 then (if i < 135 then 0 else 0) else (if i < 137 then 0 else 0)) else (if i < 140 then (if i < 139 then 0 else 0) else (if i < 141 then 0 else 0)))) else (if i < 150 then (if i < 146 then (if i < 144 then (if i < 143 then 0 else 0) else (if i < 145 then 0 else 0)) else (if i < 148 then (if i < 147 then 0 else 0) else (if i < 149 then 0 else 0))) else (if i < 154 then (if i < 152 then (if i < 151 then 0 else 0) else (if i < 153 then 0 else 0)) else (if i < 156 then (if i < 155 then 0 else 0) else (if i < 157 then 0 else 0))))) else (if i < 174 then (if i < 166 then (if i < 162 then (if i < 160 then (if i < 159 then 0 else 0) else (if i < 161 then 0 else 0)) else (if i < 164 then (if i < 163 then 0 else 0) else (if i < 165 then 0 else 0))) else (if i < 170 then (if i < 168 then (if i < 167 then 0 else 0) else (if i < 169 then 0 else 0)) else (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else 0)))) else (if i < 182 then (if i < 178 then (if i < 176 then (if i < 175 then 0 else 0) else (if i < 177 then 0 else 0)) else (if i < 180 then (if i < 179 then 0 else 0) else (if i < 181 then 0 else 0))) else (if i < 186 then (if i < 184 then (if i < 183 then 0 else 0) else (if i < 185 then 0 else 0)) else (if i < 188 then (if i < 187 then 0 else 0) else (if i < 189 then 0 else 0)))))) else (if i < 222 then (if i < 206 then (if i < 198 then (if i < 194 then (if i < 192 then (if i < 191 then 0 else 0) else (if i < 193 then 0 else 0)) else (if i < 196 then (if i < 195 then 0 else 0) else (if i < 197 then 0 else 0))) else (if i < 202 then (if i < 200 then (if i < 199 then 0 else 0) else (if i < 201 then 0 else 0)) else (if i < 204 then (if i < 203 then 0 else 0) else (if i < 205 then 0 else 0)))) else (if i < 214 then (if i < 210 then (if i < 208 then (if i < 207 then 0 else 0) else (if i < 209 then 0 else 0)) else (if i < 212 then (if i < 211 then 0 else 0) else (if i < 213 then 0 else 0))) else (if i < 218 then (if i < 216 then (if i < 215 then 0 else 0) else (if i < 217 then 0 else 0)) else (if i < 220 then (if i < 219 then 0 else 0) else (if i < 221 then 0 else 0))))) else (if i < 238 then (if i < 230 then (if i < 226 then (if i < 224 then (if i < 223 then 0 else 0) else (if i < 225 then 0 else 0)) else (if i < 228 then (if i < 227 then 0 else 0) else (if i < 229 then 0 else 0))) else (if i < 234 then (if i < 232 then (if i < 231 then 0 else 0) else (if i < 233 then 0 else 0)) else (if i < 236 then (if i < 235 then 0 else 0) else (if i < 237 then 0 else 0)))) else (if i < 246 then (if i < 242 then (if i < 240 then (if i < 239 then 0 else 0) else (if i < 241 then 0 else 0)) else (if i < 244 then (if i < 243 then 0 else 0) else (if i < 245 then 0 else 0))) else (if i < 250 then (if i < 248 then (if i < 247 then 0 else 0) else (if i < 249 then 0 else 0)) else (if i < 252 then (if i < 251 then 0 else 0) else (if i < 253 then 0 else 0)))))))) else (if i < 381 then (if i < 317 then (if i < 285 then (if i < 269 then (if i < 261 then (if i < 257 then (if i < 255 then 0 else (if i < 256 then 0 else 0)) else (if i < 259 then (if i < 258 then 0 else 0) else (if i < 260 then 0 else 0))) else (if i < 265 then (if i < 263 then (if i < 262 then 0 else 0) else (if i < 264 then 0 else 0)) else (if i < 267 then (if i < 266 then 0 else 0) else (if i < 268 then 0 else 0)))) else (if i < 277 then (if i < 273 then (if i < 271 then (if i < 270 then 0 else 0) else (if i < 272 then 0 else 0)) else (if i < 275 then (if i < 274 then 0 else 0) else (if i < 276 then 0 else 0))) else (if i < 281 then (if i < 279 then (if i < 278 then 0 else 0) else (if i < 280 then 0 else 0)) else (if i < 283 then (if i < 282 then 0 else 0) else (if i < 284 then 0 else 0))))) else (if i < 301 then (if i < 293 then (if i < 289 then (if i < 287 then (if i < 286 then 0 else 0) else (if i < 288 then 0 else 0)) else (if i < 291 then (if i < 290 then 0 else 0) else (if i < 292 then 0 else 0))) else (if i < 297 then (if i < 295 then (if i < 294 then 0 else 0) else (if i < 296 then 0 else 0)) else (if i < 299 then (if i < 298 then 0 else 0) else (if i < 300 then 0 else 0)))) else (if i < 309 then (if i < 305 then (if i < 303 then (if i < 302 then 0 else 0) else (if i < 304 then 0 else 0)) else (if i < 307 then (if i < 306 then 0 else 0) else (if i < 308 then 0 else 0))) else (if i < 313 then (if i < 311 then (if i < 310 then 0 else 0) else (if i < 312 then 0 else 0)) else (if i < 315 then (if i < 314 then 0 else 0) else (if i < 316 then 0 else 0)))))) else (if i < 349 then (if i < 333 then (if i < 325 then (if i < 321 then (if i < 319 then (if i < 318 then 0 else 0) else (if i < 320 then 0 else 0)) else (if i < 323 then (if i < 322 then 0 else 0) else (if i < 324 then 0 else 0))) else (if i < 329 then (if i < 327 then (if i < 326 then 0 else 0) else (if i < 328 then 0 else 0)) else (if i < 331 then (if i < 330 then 0 else 0) else (if i < 332 then 0 else 0)))) else (if i < 341 then (if i < 337 then (if i < 335 then (if i < 334 then 0 else 0) else (if i < 336 then 0 else 0)) else (if i < 339 then (if i < 338 then 0 else 0) else (if i < 340 then 0 else 0))) else (if i < 345 then (if i < 343 then (if i < 342 then 0 else 0) else (if i < 344 then 0 else 0)) else (if i < 347 then (if i < 346 then 0 else 0) else (if i < 348 then 0 else 0))))) else (if i < 365 then (if i < 357 then (if i < 353 then (if i < 351 then (if i < 350 then 0 else 0) else (if i < 352 then 0 else 0)) else (if i < 355 then (if i < 354 then 0 else 0) else (if i < 356 then 0 else 0))) else (if i < 361 then (if i < 359 then (if i < 358 then 0 else 0) else (if i < 360 then 0 else 0)) else (if i < 363 then (if i < 362 then 0 else 0) else (if i < 364 then 0 else 0)))) else (if i < 373 then (if i < 369 then (if i < 367 then (if i < 366 then 0 else 0) else (if i < 368 then 0 else 0)) else (if i < 371 then (if i < 370 then 0 else 0) else (if i < 372 then 0 else 0))) else (if i < 377 then (if i < 375 then (if i < 374 then 0 else 0) else (if i < 376 then 0 else 0)) else (if i < 379 then (if i < 378 then 0 else 0) else (if i < 380 then 0 else 0))))))) else (if i < 445 then (if i < 413 then (if i < 397 then (if i < 389 then (if i < 385 then (if i < 383 then (if i < 382 then 0 else 0) else (if i < 384 then 0 else 0)) else (if i < 387 then (if i < 386 then 0 else 0) else (if i < 388 then 0 else 0))) else (if i < 393 then (if i < 391 then (if i < 390 then 0 else 0) else (if i < 392 then 0 else 0)) else (if i < 395 then (if i < 394 then 0 else 0) else (if i < 396 then 0 else 0)))) else (if i < 405 then (if i < 401 then (if i < 399 then (if i < 398 then 0 else 0) else (if i < 400 then 0 else 0)) else (if i < 403 then (if i < 402 then 0 else 0) else (if i < 404 then 0 else 0))) else (if i < 409 then (if i < 407 then (if i < 406 then 0 else 0) else (if i < 408 then 0 else 0)) else (if i < 411 then (if i < 410 then 0 else 0) else (if i < 412 then 0 else 0))))) else (if i < 429 then (if i < 421 then (if i < 417 then (if i < 415 then (if i < 414 then 0 else 0) else (if i < 416 then 0 else 0)) else (if i < 419 then (if i < 418 then 0 else 0) else (if i < 420 then 0 else 0))) else (if i < 425 then (if i < 423 then (if i < 422 then 0 else 0) else (if i < 424 then 0 else 0)) else (if i < 427 then (if i < 426 then 0 else 0) else (if i < 428 then 0 else 0)))) else (if i < 437 then (if i < 433 then (if i < 431 then (if i < 430 then 0 else 0) else (if i < 432 then 0 else 0)) else (if i < 435 then (if i < 434 then 0 else 0) else (if i < 436 then 0 else 0))) else (if i < 441 then (if i < 439 then (if i < 438 then 0 else 0) else (if i < 440 then 0 else 0)) else (if i < 443 then (if i < 442 then 0 else 0) else (if i < 444 then 0 else 0)))))) else (if i < 477 then (if i < 461 then (if i < 453 then (if i < 449 then (if i < 447 then (if i < 446 then 0 else 0) else (if i < 448 then 0 else 0)) else (if i < 451 then (if i < 450 then 0 else 0) else (if i < 452 then 0 else 0))) else (if i < 457 then (if i < 455 then (if i < 454 then 0 else 0) else (if i < 456 then 0 else 0)) else (if i < 459 then (if i < 458 then 0 else 0) else (if i < 460 then 0 else 0)))) else (if i < 469 then (if i < 465 then (if i < 463 then (if i < 462 then 0 else 0) else (if i < 464 then 0 else 0)) else (if i < 467 then (if i < 466 then 0 else 0) else (if i < 468 then 0 else 0))) else (if i < 473 then (if i < 471 then (if i < 470 then 0 else 0) else (if i < 472 then 0 else 0)) else (if i < 475 then (if i < 474 then 0 else 0) else (if i < 476 then 0 else 0))))) else (if i < 493 then (if i < 485 then (if i < 481 then (if i < 479 then (if i < 478 then 0 else 0) else (if i < 480 then 0 else 0)) else (if i < 483 then (if i < 482 then 0 else 0) else (if i < 484 then 0 else 0))) else (if i < 489 then (if i < 487 then (if i < 486 then 0 else 0) else (if i < 488 then 0 else 0)) else (if i < 491 then (if i < 490 then 0 else 0) else (if i < 492 then 0 else 0)))) else (if i < 501 then (if i < 497 then (if i < 495 then (if i < 494 then 0 else 0) else (if i < 496 then 0x2f58ede2c0149499246e20d8f106c630214f89143c818208f82e00ba00002f589182b6947097c4632010e7c67e2e5141088038016708602d40ba00002f5831e2c0149c99a4622010e4c6822e8143889838417a08902d40ba00002f57d392be14a49984702090ecc6a42fd14f08f03aa17d09183000c400002f577ac299935c9124321f00e206562cd13f889838615e08502ec0b800002f571e42b414389764601ff8e846862e5148890c3cc17e09282e40c000002f56c112b6944c96e4572020eb869a2dd13b089039017908f83040ca00002f566462be148498e46a2058e8c6942f414b88d83c018209082e00ba00002f560782c394a098845f2028ea868a2e814a08d03c018309403300c800002f55a8d2cc14e09ae4702088eb86ac2f014808b839e17708c03180c800002f554c12b7143094e44e1f98e486482cd135082436615708282b40ae00002f54eeb2be149099245f2038e9c6942e414408c039c17108a02fc0ae00002f549302b293fc91e4351f48e3c6722db14008a039a17808902dc0c200002f543572c1948498046a2038e906902df14408bc3ac18209103080c000002f53d6b2c594bc9ae47b20b8ed46ae2fc14f08f03d018309403080c200002f537a32b8943494e4511f78e4c6782d713f08a037216308682cc0a200002f531c22c414889a64752078e9c67e2db14408b43b417908e030c0b400002f52c162a4139c9204371f20e5c6742de14588cc3ae17508b02d00b800002f526532b5942094c4511f70e346622d713f888c39216a08482ac0a600002f5207b2bc147498246920a0f006be30514c88dc3b218309583200b800002f51aa32b7943096444e1f78e486802e314808d83a617808d03040c800002f514db2b5947497c4571fb8e7c6902eb14608b43ac17908d03100ac00002f50f0d2bc947098846c2078eb06a62ed14b88fc3b217b08d83040c400002f5095e2ae13f09424401f78e5c6702e714308b038c16b08d82f40c400002f503b02a913cc9264341f10df465a2cd134085038616408282d80b200002f4fdd22c4949098c45a1fa0e2c6582d413d889038416908d02e40b000002f4f8092b794649844511fe8e846922e513f889838816408302bc0ac00002f4f23b2b6944895e45a1fe0e606742da143088c39217b08c82f40c400002f4ec6d2c494d89b04872168f306dc31615f09703f219509d03000b400002f4e6872c314d09a847520f0ee86b630515209303d818f09683140ce00002f4e0b82be94689884682080ebc6b42f214a88e43b217208882e40b600002f4db2329e93a890c4391f28e2065c2cd138889c3a217008b02d00bc00002f4d5312d215309d44892188f286d430315a09743e818f09203000c800002f4cf7f2b1941c95a4491f78e546802eb14588a839616b08802c80c400002f4c9bd2b694289664521fd8e7c6922ed145888437c17608a82e00b400002f4c3dc2c694a49864652080ed06bc2f814988bc39217708802b40a600002f4be122b5143096e45b1fe8ea46842ea144887039617208882e00bc00002f4b84a2b7144096445d2008e986882db13d888436a16308182a009a00002f4b27d2ba944495644e1fa8e706922f114f08e83c618309183040ca00002f4acbf2ad942095644b1f68e2865c2d8140889037215e08602e00b200002f4a6f52b9147c9864631fa0e7868e2fd14b89003ca19509302f40c400002f4a1302af143896c4551fe0eac69c2ea14a88d83b618409003140d200002f49b762ac93ec91c4331ef8e1864a2c3132084838016808682d80ac00002f495972c194a099e46c2080ec06a62ee14708cc3ac17308d02e80be00002f48fe02aa13f894c4461f58e3866c2e114588b43a8177090831c0c400002f48a0d2ba947c97e4602030ebc69e2ef14608cc3a616a08782dc0b600002f484382c1147c97a4682078e9868e2e714008603a416e08a82dc0be00002f47e6e2bc146c96444f1f80e106642d113c086037e16d08482e00ae00002f478b32aa942094e4551fd0e7068e2ed14908c039416308482b40a600002f472de2b5945095c4581f90e7c67e2dc140889038415c08582ec0b000002f46cfe2be946497645e2028ec86b22f514608f03b618c09503000cc00002f4672e2b8943096a4591ff8e886822e514708b838616908282c00a600002f461572bb947499446e2078eb069a2f615088fc3ba182095032c0ce00002f45b772c1949099a46e2090ec869c2f814d091c3d618008c82d80be00002f455ae2b9941c95c4571f98e7066e2dc13e888439416e08d02d40b400002f44f962da95649f04912140f286d430a154891c3d218209302fc0b200002f449f82a2939c92642e1e80dec62e2c1130881434e15c08082a409400002f444182bf948899446c20d8eb86ac2f515109143c817e08e82ec0c200002f43e1f2d215189c44892110ef86aa2fd14e09283de185090830c0ba00002f4385b2b514389564572010e646662e013f888038c17808e83080c600002f4329b2af142096645f2040eb06a02ed147886839a17208982e40be00002f42ceb2a613d49284441f80e206482c2138882c36016f08c82f40c000002f4270b2c294bc9a24742058eb069a2e314808c039e17708682b40a800002f4213b2bb14789924681ff0e786842e1146888038216508582b80b2000 else 0x2f7015d2b9944c9704522000e846902ed14788b43a017608b82f00c200002f6fb962ba147c99046e20e0efc6ac2f014988c83ac17308882f00d000002f6f5bf2be948c99446a2050e8c68c2e714608a83a616b08402ec0b200002f6eff42b0143497e4541fa0e846822dd13f886438a16b08602cc0a800002f6ea352a513ac91a43d1f20e2865c2d814388b83b617808f83180ce00002f6e4562bf14409584552020e906862ef14788f43b617208a02a409e00002f6de7a2c094a899a45a2060ef86ce30b15209243ca18008d02ec0cc00002f6d8b12b9946098045f2018e886a02f214388bc39e17f09483000c600002f6d2e52b7142c96e4551ff8e6067c2dc140889c38616108802cc0b800002f6cd1b2b6945895444c1fa0e486782e514508c43b017608982c00ca00002f6c73d2c514b89a847620e8ef06ce30315188f83cc17b08d03180d600002f6c1472c994c899e47b20c0ecc6b42fb14e89083b817a08982e00b800002f6bbaa29f939c92c43f1f50e546742e014208b83a617308c82f40cc00002f6b5c52c914a49a446f2058e9069c2fb14d08cc3aa17d08a03080b000002f6affe2bb143095e4551f88e646862e6142889439e16808682d40ba00002f6aa422b5145497e45e2008e906962f614788cc3c018509083180d600002f6a45a2c714b09984712088ea46942eb14988fc3c417f08902f40ac00002f69e8a2bd94749824662068e9c6942eb14a08cc3a417e08e82dc0ac00002f698c52b494089444421f18e3065e2cc138889038c16508082bc09e00002f692e62c094789924672048e986a42f214688cc3b617008a02f00b600002f68d082c214a89944712028e9468c2e214288ac38e16708602c80b200002f687462b194209584471f48e3466e2e7141089438e16d08b82d40b400002f681842af140094243e1f50e2c6542cd135086c37c16908502c40c000002f67bb62b794449504541fb0e686762de139088038416008882c40ac00002f675fe2ae143097044b1f50e3067c2d013c088837a15f07f82bc0ac00002f670402b494389624521f38e486602d313b887438a16208302ac0aa00002f66a562c6948499446d2058eac6882e313e88a439217108b82e80b400002f664652c814d09a447b2080ea86922e814688e03ba18009103080bc00002f65e992b5946097845d2060edc6a62f0150090c3b017308d83300ca00002f658db2b2942097c45d1fd0e786822e714908b43b617a09182ec0bc00002f6531f2af143495844c1fd0e786702d313b886437a16908502b80b000002f64d682af93d092c4391f28e486562cb139088038015c08202d00c800002f647802bf94889844682028e9868a2f214b88e43a417a08a03080b600002f641b22b3143c9404411f50e4066e2de141087c37816507f82bc0c000002f63bd62bf148c97e45e2030ea469e2e414708b839c17108a82b00b600002f636172b3145c9864682018ea069e2f414508a439a17808482d00ba00002f630652a993d49284341ee0e446722ce13e089837c16608782fc0be00002f62a952b5942095c4521f88e8c69e2f114788cc3b017209102f40c200002f624e42a2138891c4331f08e3065a2c5134886838416f08982f80c200002f61f3e2a393d492a43d1f48e406802e414888dc3ac17d08c02f80be00002f619692bc948c97a4601fd8e806842e914b88d03b217308982dc0c000002f613a52b194189644471f18e206502ce140089039016808b02b00a400002f60de92b194309684511fb0e546642e6145889838416208b02e40c000002f607f22cf95309e649121f8f806e8319158895c3de19009803200c600002f602422ad14289504441f28e146542c7138085438016208502dc0c400002f5fc7e2b2141c95244a1fd0e786622d113f88943a817309183000c400002f5f6a82c014c09b447e20f8f0c6c430014b09083d018808d02d00be00002f5f0e62b914349564552030e646762dd14208b43a817a08a02ec0c000002f5eb082ba944496c4602018e6c66c2e014688b43b217508f02ec0c400002f5e54a2b013f49404481f18e346722df14308a03aa16f08a82bc0a400002f5df852b514109364421f90e686802db14508a43a216d08d82e00bc00002f5d9de2aa13e09284391f40e1064e2cd13f888437c16a08c82f80b600002f5d40a2b994789824601ff0e5c65e2d914308b43a216a08502bc0a800002f5ce432b6141c95245b1f80e746842e914908cc3a817708e02e80b800002f5c8652c4149098e4722090ec86b02f614a88dc39016f08602d40a400002f5c2cc2a193688e64191e48ddc63e2be133884036016108682e40c200002f5bcfb2b614349524511ff0e6c6762e313e887c39e16308282b40b000002f5b7062c4149c98c4662018e986a22ef14c893c3e018c09203280ce00002f5b1412b8144c96a44c1fb8e586662e214588943a817708c82f40bc00002f5ab702b9143497646e2068ea069c2eb14888bc3be18c09503100c600002f5a5d52a193a892843b1ef0e7068a2e513b886437a16308a82ec0ae00002f5a01e2aa93e492c4411f20e4c67a2d413f88c43b417708f02e40c600002f59a752a393ac92043a1ea0de06522db13f887838e17008082740a200002f594bb2b3145095c45a1f60e506842e414688d039616a08882e80b2000)) else (if i < 499 then (if i < 498 then 0x2f873bb2c314c49a247520c0ec869e2f314b88c83a617808c82d80b400002f86dd72c1947897a45b1f90e746742e4142088c39e16a08702e00aa00002f8684129a13308ea40c1d68d4c61e2af12f884436c15407b027c0a000002f862612c0148899c47620d0ec46a830215489183d018e095032c0d800002f85ca42b294309744682068eb46aa2fa14a88dc3a616d08802ec0be00002f856fa2a8140494244c1f80e4066a2d7138086839a17908d82c00b600002f850fe2c814d09c847720c8ef86c030115309303d617508e03100ca00002f84b4c2ac13c89364321ea8dec6422ca131883036216a08b02fc0ba00002f8457b2bc94689824611fd8e6c6902ed14788d03ba17108902e40be00002f83f962c3949497c46820f8f146de30d15489383d218209203180ca00002f839d32b4146499446a20a8ecc6ac2fe15188ec3b417608d82f40b400002f834382a293b49124311ee0e206502cb136885037c15d08182a80a000002f82e7e2aa93fc94e4461fb0e546742dc14688c03a017708d02ec0c200002f828e029d93a492e4351f10e386642d514088a43a017108882f80c400002f8234e29e137c9344441f78e486702e414408a03a217308e030c0ca00002f81d6f2c794d49ac4852110f046ca30614b88cc3a6182092830c0c400002f817ba2b2144c9844632070e9469c2e814288ac39217108c02f00b800002f811dd2c514d09ae47e2110f206d0308157893c3c018109202e80bc00002f80c072be147898c4651ff8ea06a02eb14a88c83ac16e08b02f40c000002f806452b814249764531f88e406542d513e08943a817208502b40b600002f8006f2c214bc97c4692068eb46a62f114a88b839c17c08802cc0ae00002f7fa852c214b499c4792100ef06ba30815108fc3b417a08c02e40b400002f7f4a02c494a899847920f0ee86c830715309283d017b08f03340d800002f7eece2bb944496c4551fb0eb46a02f514788dc3a616c08b82d40b400002f7e8f82be94949984692090edc6b02f414608a838816508582c00b800002f7e34c2a613e89344411f20e146542d5139884c36a15c08282b80b200002f7dd7f2b9143c98645c2058e646882f314708c839817608f831c0b400002f7d7a82ba144496c45c2028e986922ee14408b439616908682e40c200002f7d1e62b694349644551fc8e5867a2e114408b439617408a82c00b200002f7cc102ba147498a46b2068eb469a2ed141889839a17208d83040c200002f7c65f2ab93fc9404461f78e846882ee148889439216a08d02dc0be00002f7c0c72a0939091242b1e68dc864e2c8139086437816508702c00ac00002f7bae12c094989944672058ea86a22f314388c43a417108c02e40be00002f7b5122b9942497045c1fb0e7467e2de141888836e16208602f00b400002f7af3d2bc946098645d2040e7068c2e314b089c39616d08802ec0c400002f7a9962a593c09304371ed8e106542cb13b885c36a15708482cc0a600002f7a3c82b814449784581fa8e8068e2e514388c43b217909103280d600002f79df52b8147497245c1ff0e946862e314608c43b217a08d02e80c600002f798162bf948097e4652010eb46a02f414988dc39c17508d03000c000002f7925f2af944097c46b2068ea86a22ec144889839c17208b02e40b800002f78c7e2bd94949784502008e6c67c2dd14588d43a416b08f83100b800002f786b42b2141094c4471fb8e686722e013c087c36c15808002a40a000002f781062ae94209304381e50da06042ad12d080435015808402bc0b000002f77b0e2cd94d099646920b8edc6c430915389203ba18109183180ce00002f7756e2a613b49284391eb8e086502da14008a03a617b08902f00ca00002f76fb82b113c49364461f20e246602d7141088439616e08902c80b800002f769ef2ba148c9884602000e9c6822d913a082c37016307e82b00b600002f764052bd147897445c2008ea069e2df144087c39416508702c80b200002f75e3c2b514109664552048e946962f714b08e03aa17708e82d80c000002f758942a8141096244f1fd0e906962ea143089838c16508b03080c600002f752952cb94d09ba4732068eb86ac2f914d88e83b017c08a03080b600002f74cbe2bb94849904692050ed06a42f614d890c3c418d09b03200dc00002f746e22bb146c96c45f2038ea46aa2f214809003b818309502e80b200002f7411d2b8141c95844c1f70e506642d9139883c35e15307e82a40a800002f73b3d2c014809764561fe8e606622df13d086036015507d02740a800002f7357c2b394289664602028e9c6ba30214d892c3d217e09383400ba00002f72fc62ad13f493a4441ec0dc464e2d314108b039417508982f00be00002f72a1e2a293c49284371e90e4466c2d6132882c36a15f08602b00aa00002f724652ac93fc94e45f1ff0e6c6842e214088b03a617309102d00bc00002f71e972b914309644501fb8e846862e614688d43ba17c08d83000be00002f718a82ca94d49ba47520b8ec068a2ed14a88f83b817f08a82e80b600002f712de2bb142c9524451f70e5067a2e614408ac39417308782c40c200002f70d112ba946c9744591fa8e686782e614788cc3a817408c82f80be00002f707292c694c898e46a2078ee46b22fc15188ec3bc18709302fc0b6000 else 0x2f9e6802bb947c98046a2080ed869e30215489203d419109603040ba00002f9e0b52b9943895e44f1f78e4066e2db140889439c17808c02c80ac00002f9dad72bf14a099447620a0ea86982f314888f03c217a08602fc0a600002f9d50c2b4942095c4552000ea46a82fd14e890c3c217c09682fc0c000002f9cf4b2b4943495645b1fd8ea86be2fe14d08dc3b217409103240ca00002f9c9972ae93fc93844f1f60e346702e213d887838016108502a00b000002f9c3c92b6943895c44e1f38e2465e2df14288ac39216508282a40a800002f9be1c2a793d891e4351ee8e2064e2c7135083438c17708b82d00ce00002f9b8182cc94dc9c247420d0f286e230815009203da18709202fc0c000002f9b24d2b894349764552058e8467e2de137888438417208b83080d200002f9ac962ae940893e4451f48e3c6542cb136885838816808882d40ae00002f9a70029c13749304461ef8dec65e2d313f889c39c17608f02f40bc00002f9a10d2cb94c499846b2098efc6c02fe15089003d0189095830c0d400002f99b652a513d893a43c1e90df464a2cb143888c38a16f085029009400002f9959c2b6943894844a1f20e3066a2d3136882436e16408382940aa00002f98fcb2ba948499c46c2010e686782e5144088839217608d02f00c000002f98a2c2ac140495244e1fe0e6067e2e914688b83ac17808b83100dc00002f984522c1947097c45a2018eac69c2e6141088438c17208a02f80b600002f97e8a2b2141c9544471f58e3c66a2df14588d43b617408a02ac0a400002f978ce2ac93d494844b1f08e2c6522cd139088c38416b08882cc0b000002f973032b4940094a43f1f00e3c66a2de13f088838416908302a80a600002f96d2b2c014bc9a247a20a0ed86c630815289003c217308a82ec0cc00002f967412c794c89a247c2108f286d230815689483de197097834c0d200002f961512c914c49964702118f2c6d830415489283c218409283240cc00002f95b762bf94749884622058eb06ac30415488fc3e218308f02fc0ce00002f955d429f939493043c1f18e0c6382c0138886838216d08982f40cc00002f9500f2bc946c9624581fa0e9067c2e313f08a838c16308482e40ac00002f94a432b8946497245f2010ea86962e013d088c38a16808b82c40b000002f9449a2a594049304431f90e746782e114608d03a217709082f40a400002f93ec82bb94509644541f80e6466a2d813a887c38a16208982e00b600002f9391a2ab140894a4491f98e546682db141087839617609083300d600002f9332e2c5147c99247520a8eb86a42ef14a08d83a817b08d030c0cc00002f92d682b5144496e4611fb8e486722e7147089038015c07f82900ba00002f927992c094c89904642018e9869a2f314908e83ac16f08802f40b400002f921a82cb94f49b047a2090f186e431415989443ee19209903100c000002f91bcc2be947097846c2018ec06a42eb14a88ac39616a08682b409e00002f9161d2a713bc90842e1e88dc062a2c0134082835e159080827c09600002f910642ac13b093243c1f28e3c6722d113b085436e15e08482ac0b400002f90aa12b594249544521fe8e5866c2df14908b439017908b82f80ca00002f904d62ba947896845f1fc8ea066e2ec145089c38617c09082f80b800002f8fed62d295049a447720b8f106c230a15209303d018909582ec0a800002f8f9062b4143896445d2040ec06b02fa14c08d83be17d08e02e40cc00002f8f3482b093f093a4381ee8e206582cd13988983a017508f02f40c200002f8ed7a2b794409564502000e886a42fa154893c3f21a009583240d200002f8e7852c994ac9b247d20a0eb06982f414e08e03ae17708c82d00b000002f8e1dd2aa93f494a4421f90e506642d113c08cc3a617209082ec0b600002f8dc322a713b49404511fc0e886862e814288a83a017808e03240be00002f8d6982a413c49344481fa0e5866e2d714008bc3a217108c03080c600002f8d0e22ad94009404461f48e9068a2e814688a038015708282cc0bc00002f8cafb2c814e09ae4712030e9867e2e113f889c39816408982ec0c600002f8c55a2a893e093a4411f98e546702e914b08f83b617e08e830c0d800002f8bf632d094ec9be47720c0ef46a82f814708d83a617508a82dc0ba00002f8b9972ba944896a4571f88e446622d413c086c38016508402e80c200002f8b3de2b1142094043e1ef8e146462cd13e087839816908802c00bc00002f8ae202ad13cc9324391ed0e106682da142087838c17509283200c800002f8a8702a713b893c44e1f88e5465a2d713d888438216808b82e40b800002f8a2a62b4142895244a1f60e646762db14608b03a216a08882cc0ac00002f89cc32c1148897c4621ff8e7c68e2db13e086037015e08402c40b600002f896dd2c394a498a4632080eb86a82f215108e43ba17e09203080c800002f891222b6148497645d1fc8e8468a2f414c08e83c017e08d82d40b200002f88b5f2b1940095444a1fd8e846782d913b081835014a08282e40ae00002f885692cc14d09b446f2080ee06a62fb152092c3b016e08682c40b600002f87f7d2cb94f09b246e20b0ecc6c031115689103ce17c09182f40c800002f8799e2bd947898c46c2040ec869e2f714f88f03aa17108c82d80c0000) else (if i < 500 then 0x2fb59fa2be949c97645e2028ea06862ea14308bc3a017308482b00a800002fb54462ab93c892443e1ee8df865c2c6132881035616008882c00ba00002fb4e6f2b9944896e4511ff0e686682d913d888c39c17b09183200c000002fb488a2c314b098e45f1fd8e646802eb14988c83b217a08d02cc0ae00002fb42942cf14f89ac47320b0ed46922eb14608b439618109502f80c000002fb3cb32bf946c9664571fb0e406802d9140889c39e17508982e00aa00002fb36eb2b8944c9604581ff8e8c6862e714888d83ba17b08d831c0c200002fb31032c814d89a84752030e906842db139886c39a16f08a02dc0aa00002fb2b252b7143895c45c1fe0e846662d614108a03b017608c02d80c000002fb255d2b5940c9564451f08e286722de14308c43a817908d030c0b600002fb1f952b9145897645f2000e886a22f014b08d43ae17108982dc0ac00002fb19d82b0141093e4451f28e006602dd14308b438e17308d83040aa00002fb14082ba943c97a45f2030e906942ef14808e43a016f09183300ce00002fb0e6a2a093b891042e1e88db06382c3135084c36c15607f82ac0ae00002fb08822c494d89b24712078ecc6982f415589203cc18b09383180ba00002fb02c42af93e893e4532000e746702dc13d087437816508102980ac00002fafce72b7141c9504511fd0e906862e714188ac3ba18608e83080c600002faf70f2c2949899647a2130f006ae2fa14988c838a16708482a809c00002faf1502b5143c9784612000e706862e2143089838e17108482b009e00002faeb632cd94f09c647b2128f346c42fc15108f83be18b09082f80b600002fae5952b7141894043a1eb8dd863a2c3135084837816408902cc0b200002fadfb32c194989724602028ebc6a42f414a08f43c618109382f80c200002fad9d72b9145496844d1fa8e5067e2d613b888c38017008b82f00b200002fad4112b7145898245f2018eb06be2fa14c88f83c618509382e80be00002face382b5145497445c1f90e5c6742e214308ac38617008682f00b800002fac85d2c114a898c4712090eec6aa2f114888cc38e16208182c40ac00002fac2732c794c89a44702088ebc6b42f414a88a83a217608982fc0be00002fabcda2a413c49204371ee0ddc6242b212d882837015b07d02a00ae00002fab7062bd144895a44f1ff0ea068a2f114888d43b217908a82d40ba00002fab14b2b2943895045a1ff8e5c6802e214c88c039417308d03080b200002faab7e2b3141895644b1f68e706742dd141087c36a15607b028808a00002faa5a52bc145898245f2048e8068e2ef14c88c43a416e08c02d40a400002fa9ff92a993e092c43b1f00e406662d913f085037e15a08682c409a00002fa9a342b6143495e44e1f40e2c6422c9135884837616108402cc0b800002fa947d2ac13f494244d1fc0e546662d714008c83ba17a08d02f40b400002fa8eb72b5143495a4561fb0e7466e2e214688bc3aa17708f02fc0b600002fa890a2a893f49244361e68dd862e2c0136887c39a16a08b02ec0aa00002fa831d2ca94e09aa4712060eac69c2e914a08dc3a017008902fc0b400002fa7d582b3942895444d1f88e506702e3148087c37e15708502d00aa00002fa77922b494489744591fc0e9469a2ee14608bc39216c08e82dc0a800002fa71ab2c094a09b247d2108eac6982fd14c88dc3b217808d03100ce00002fa6be52b9944495e4591fe0e8867e2f114f08d03a017608e03100c600002fa665529d939890442f1ea8e086542cc137885838616908382c40b000002fa60832c2148098646f2038e906922e814008a839617508a02b409a00002fa5b0029413348e64241e70df863e2bc133883835814b081829c0aa00002fa554e2a893e89424461ed0e1c6582dd14388bc39a17909103100d600002fa4f692bd94689864692058eb069a2f014408bc3ba17b08e03200cc00002fa496f2d1950c9ce48c2100eec6b02f615088d039617308302b40ac00002fa43b42af13d492c4481fa0e3865a2d413e889c39616808a02f80b200002fa3db92cb94e89c047520f0f186c62fe15209143c018509803100b000002fa37f02b294489744571f98e6867e2e914608d03ae18b08c02ec0ae00002fa32372af940894a44d1fd8e8469e2ee14588cc3c818709503300be00002fa2c5d2b714489484441f30e2065e2e013f88ac37816608682b00b400002fa26882b8943494844d1f90e606642de141888c3a017208582e40b000002fa20bd2b2943896c45b2008e786922e914708cc3a217908a02e40c200002fa1aff2b6145895c4531ff8e606662d313e88cc39a17408c83080c200002fa15322b994709784682038ec46b62f914a08e83c017608882e00b400002fa0f332d095449d44852148f286ca30c15289083be17708a82d80be00002fa09722b594589684562008e806882e214388e03b417a08e82fc0ce00002fa039e2c094709744611fe8e6c66e2d313a885838a16b08b82f40c400002f9fdd02bd948097c4652028e786822e114488b039e16a08c82e80c000002f9f7fb2c194a09964692030e8c6862e214688ec3a216d08a02e00c600002f9f2412b5144496445b2010e846842e714708bc38416108502e00b600002f9ec5f2bb144096844a1f80e5066a2d613c883836616108602b00a2000 else 0x2fccd952be147498e45f2040e946802e214288983a017208b82bc0b200002fcc7e42aa93dc92e43f1ef8e146562d2140089837016008382c80b400002fcc2062bb145c9744571f60e246602d213e087c38e17608c82d00a800002fcbc502ae13f894c4461fa8e606662e3140088439217308802fc0ba00002fcb6702bd945898c46a2070ecc6a82f514988cc3ac17809083080c400002fcb0872be14909804602008e606862e614c88c43a417808b82bc0ae00002fcaa9a2c594d49c44882158f106ce2f714b89083d018108c03180d400002fca4c42b9144896c4581fc0e846922e814b88d83a817408902d40b600002fc9f41295135890a4231e50dbc61e2b8134086c38616b08082980a200002fc99762b5941c95c44c1f28e546762de143889839c17008982e00c400002fc93a82ba14689664531fb8e946722e314588b839217a08702c40a200002fc8de22b6143494e4471ef8dc86362b912b881835a15007e02a80a400002fc88062c414d09984632068ebc68c2e9140089038e16b08a02e40bc00002fc82302bd94789804632038e686882f214908a439816f09083000c400002fc7c702b5142c95044d1fa8e6c6882e514788cc3a817109403280d400002fc76b32af93fc94e4481ef0e2864a2c9137884838616a08b82d40b800002fc70f72ad94389584551f88e686762e213d886038c16108482d80a600002fc6b232b6943c95a44c1fd8e9c6822f014988cc3c417f08e82fc0be00002fc651c2df15689f448920e8eec6bc30515288e83a417008502c80ae00002fc5f532b8142894c4531fb0e7465e2d213d086038a16208582dc0c400002fc59b02a113c091842d1e78db861a2ae12a081436415807e029409e00002fc53eb2bb146898045c1fa8e6868c2ea14608d03aa16b081829c0ac00002fc4e042c0949897a4622078ecc6ba2ff15109103d818809483280d000002fc483d2b7943c97a4571fe8e7866e2d3139885c37816308703000c200002fc42812aa93d092a4451f50e406662db13c887838616508982f00bc00002fc3cb12b8141894e45e2010ea867c2de143888839417708e02e40c600002fc36f02ae13f89544531fc0e9469a2f514788a83ac17608b83040b200002fc31452ac13dc93e44b1f68e3866c2db13e0894388169088030c0d600002fc2b6e2bb946897445b2068ec46a42f314488c439a16b08702c00b200002fc25a82b8945497244f1fc0ea868c2ea14988ec3c418109103300d600002fc1fa32ca95089bc4852100f086c02f715108fc3a617508802980bc00002fc19dc2ba94889924632018e9068e2e914a08c03ae18509182dc0ac00002fc13f82c794c09a44732050ec869c2ee14808d83a216d08b82d00b200002fc0dfc2cf14e09d04902188f7470431f15f09583f6198095832c0c600002fc081f2c314889704632078eb468e2ee14288b039c17708c82e40be00002fc02382c694ec9a846b2058ebc6aa2f914c08c839617508882cc0c800002fbfc5c2bd14849904642008eb46822e814708dc3b417f09003040c600002fbf69b2b4942094e4592030e9c6902f014588b839c17108902ac0b400002fbf0912d9952c9d84942168f2c6d831115e09583fa1aa0a1034c0c800002fbeaa92c514ac99e46d2060ea869c2e814608d839a17408982bc0aa00002fbe4f52b1144c95c4551fd8e8c69c2eb143089038e16908902e40b200002fbdf302b8143c95a4531fd8e7867c2df14488ac3a017408802e40b400002fbd96a2b6944897045f2000e8c6942f814e88e83be17c08d02f00cc00002fbd3882c194a09aa4681fe8e5867a2df14488bc39a17608e02e00ac00002fbcdde2a9940095a4451f58e246642e114508b838e17008402b80aa00002fbc80e2b4947498045c1fe8e7466e2dc13c884837e16b08702d80b000002fbc2422b0141494c4501fe0e9c6882e714308c039617208902d80b600002fbbc822af13fc9624561fd8e3c67c2de140089039a17408882cc0a200002fbb6cd2af142496a4511fa0e606742d513c889439416608702c80a400002fbb0f22ba146c98a4632038e946882ea13f888836e16308002c80ae00002fbab432af13c49184261ec8e246682df14588cc3ac17e08902e80be00002fba5672c094449564511f78e386702dc140088839016b08a82e80a600002fb9f9e2be14709784631fa0e3c66a2dc139886c38016908682c00a800002fb99b42c794d89a246d20d0ef86ce30315189083be17f09103040b800002fb93e02bc14689904702060edc6aa2f514a08f43c617a08f03100ce00002fb8e312aa93f89304421fa0e646842e114408bc39a17408902e80bc00002fb88422c4946c9744602018eb068c2e414608d43ac16508582ec0b400002fb82822af941095444c1f88e5c68c2e214308b43a417e08b83080c600002fb7cd12ac139091642b1ec8e0465a2df14188843a216208682b80b400002fb771a2b0140894e4581f90e8c68c2e914a88b03b017808e82d40b600002fb71312c694c09a247a2068ee46b630214f08a039c17608b83000b400002fb6b5b2bd148c98c4712060ef46a22ee14988d83a217208b03180d000002fb65862ba94809904632058f006b22fc15209003c218008d82ec0c600002fb5fdc2a413fc93643f1f10e086462ca13b887037c16e08b02ec0be000))) else (if i < 505 then (if i < 503 then (if i < 502 then 0x2fe40992a493b092e4361ef0de464e2cc139086439216f08a02d40be00002fe3acd2bf14649824682020e8c6962ea145888c38616908682e40ce00002fe354329a13388fe42c1e90de06462ca139086839217408d02ec0c600002fe2f642c114b89a64802130ee06be2f8151891c3ea18c09503180b200002fe29a72b314409624521fa8e606722ec14688f03ac18108f03100bc00002fe23ed2b014389524471f30e2864e2c8135083c37415e083029c0b200002fe1dde2d795149c848120e0f106c830415789283e219209383080ce00002fe180d2bf148c99246b2090eb868c2f214808d83b017f08f030c0c400002fe124b2b6146097845d1ff0e8868a2e014588f83b618209083100c400002fe0c612c6949099446b2080ed86b630715188ec3aa17308c82d80ce00002fe06a62ae13e095444b1f70e5c67c2e6141088039016808082a00a400002fe00ca2bc94809824642000e946922e814708e03be18509083200dc00002fdfaf82bb149c99c46d2070ecc6ac2f114808ac39617208402e40bc00002fdf51c2bf94989aa4672020ea46a62f914d09003a817908c82f00ae00002fdef452bf947c9744511fc0eb46942f515109183ae17709002f40cc00002fde95d2bf948097a46c2078eb468a2e7142887036e16308a02bc0aa00002fde38c2b5142c94a4461f90e686802da14388a03a417708c82dc0c400002fddde22ae13f494a4401f08e2065c2d3138088038c16708502d40aa00002fdd8122b6947898e45c2028eac6802d9140088c38a16708502c80b600002fdd24b2b2140c9444511fe0e746962f114588c43aa18109203280da00002fdcca62ac941094043b1ef8e306622db14208bc3b017508e02f00c000002fdc6bf2be948c9724582038eb46a82ea14788ec3b0175086029409800002fdc0fb2b1141494c44b1f38e486682db13b885837416a08602e00b800002fdbb232c794a49744602020ea86862ed14708a839816f08b82d00c400002fdb55e2b0943c95844d1f30e5067a2dd140886039c17408f82d80bc00002fdaf732c4148c97e45e1fd0e4c6682e0142087038016b08482bc0b600002fda9ad2b9147097c46a2040e886982ed14a89143ae17708b82ec0b000002fda40a2a513a893243e1ef8df064e2d113d885c38a16608a82d00b600002fd9e1f2c794c499c47520b0ec86ac2fa15208e43ae18408c02cc0b000002fd98702a613fc93243c1eb8e086562c6133884036415d08782c00b400002fd92942c1948498a46b20a0ee46c030a157092c3cc18509403240cc00002fd8cd22b394109504491fa0e5c6842ee14d88f43a416908682d00b000002fd86ea2c414c89984652038e9c6922f915089103b817e09182f00b800002fd810d2bd14549664581fd0e5c6522ca135882436a16008782ac0b000002fd7b542ad13f89504471f88e646702ec145888c3a617a09182f40ba00002fd758e2b594449564572000e8c69c2f014708f83b617a08c82e40ac00002fd6fa62c014ac98a4652008ea46a62f214708bc3a6184091034c0d400002fd69fe2aa13d893c43f1f30e4064c2c813f086838217008a82b80ae00002fd64442ad143494c4461f28e386682d713c887036c15a08002ac0c400002fd5e932ab13f894644a1f18dfc64a2d2137885036a16408a02e40b600002fd58da2b013f09284481f48e486782d513d08a838c16d08b82fc0c200002fd53312aa93f09544521f80e5466c2dd13e887838816d08882d80ba00002fd4d4b2c4148c98e47d2110ef46b830214f89003c818f09683200d600002fd47612c414a89a446d2058eac6a82fc15109043ac17c08e83300c200002fd41a92ac13ec94e44d1f98e4466a2de14288c839c16b08982ec0bc00002fd3bb42ce95009b44752120eec6b22ef144889c38616808482d00b800002fd35fb2b214209684531fb8e8c6862e5143087037a16b08b02e40c200002fd300c2c8949c98e4602090ec46aa2ff15009043ba17808b02f80bc00002fd2a542ab13f893a4491f78e586722e814208c43b817508d830c0c000002fd24952b494449804612088ea06942e814788bc3ae17508b02d00b000002fd1ecb2b3943c94844d1fa8e7867c2e313f08b03a816d08c82e40bc00002fd19092ac940c94843a1ea0e3065c2e214788c03a616f08a02f40c200002fd13272c594a097e45d2008ea068e2e714408b03a417408d03100b800002fd0d102dd958c9ee4962168f706e630615388f83d2191095031c0c200002fd07402bc147c97a45c2010ea46942f114408c03b017208282c00c400002fd018f2ad13dc92e4401f38e4066a2de13f087037415908002c80bc00002fcfbcb2b4142c9444461f70e2866e2e1142089037c16a08582a80ac00002fcf5e72be947498446f2050ec86982f014c89143c218108f02e00ac00002fcf02b2b714609764531fd0e7c6922e214508c83a617208c02e00b400002fcea4f2bb141895e44f1fb0e7c68e2e513d88a838a16108982940a600002fce4892b214209584521fe0e6c6842dd13e887439616e08b02f80b600002fcdee82a593c89284401f28e4866a2d813d887839a16f08c02b40ac00002fcd9372ae13fc9544491f78e7c6662e514588a83a017509103000cc00002fcd37d2af13f894e44a1f90e746882ec14688a43a017f09183180ce000 else 0x2ffb3332bd94a899a47320b8ed06a82eb14488dc3a017008c82ec0b000002ffad702b314189584461fe0e8467c2ed14508c03a417e08982f80ca00002ffa7aa2b3141895845d2048ea867c2de13d88ac38616908182bc0a800002ffa1b62cc94dc9aa47820d0ef86c42f914d09043b217c08e02ec0aa00002ff9c062b013fc96c4591fa0e4c6642da14208b438a16d08202ac09800002ff96122cb94e499446c2058e986962f014f88ec3b417c09402e40cc00002ff904b2b0943c96245f1fc8e7c66c2cf137085836e15f08082a80b800002ff8a9a2ab140493a43e1f30e0c6462c513a888438816a08802e00ac00002ff84c02c4147c98045c1ff8ea46922f314288ac39c17008a02d80b800002ff7f052a993d09344331eb8e346642d213a88a439017309083040c800002ff79392bb146c96a4591fd8e8469e2f314b08d03aa17508682ec0bc00002ff73662b614589684541fd0e8c67a2dc14208c03a217509003100ca00002ff6db92a593e093c44e1f90e446642de13d08a83b017e09483080b200002ff68062b0942895c4491f90e5c66e2ea14488c03ba18409403100ce00002ff624f2b2940092c4381f40e3866a2cb136085036c15a07f82b80ac00002ff5c822ba14689804632010ea068c2f514d08f83ca185098033c0e600002ff56b12c614a49a046c20b8ee06942f214a88ac3a217a08882ac0ae00002ff50c92c794d89a44672008ea06842df144889839216c08a82d40b800002ff4b012b114149524501f70e4c6662e314808e43ca18008e02f00c000002ff451a2c494c49b646f2098ed86b82f915289003ca18a09683440d200002ff3f4f2b9946c9844682050e8c6802e414988c43a217e090831c0d400002ff39b22a293a492443c1f78e486602d613c087c38816308882d00b200002ff33e52b9949898a47a20c0f0c6e230e156091c3ca18809303180c800002ff2e1f2b3143497245d2080ea86802e214408a438e16408602c80b400002ff28622b0942096845a2020ea06842de141089c3a217109083000c200002ff22b02aa93b892843f1f30e0c6542d313d089439a17508d82dc0ba00002ff1cd72be949898845e1fe0e806722e113e889038816d08982f00bc00002ff171a2b1143096845f2050eac68a2f114e89183d418908a830c0c600002ff113c2c2149c99646e2010eac6ae2f014d08e43b016f08a82d40be00002ff0b612c394a09964772120efc6ba30215689403d6186090031c0ce00002ff05962b314489604521f80e4466a2d713a085437c16508382940a000002feffac2c814c09ae4742080ec06902e014588a839e17408682b80ac00002fef9ee2ae14049684491f68e506722d513e88b43a416e08802e00ba00002fef46929c13989164281eb8df863a2c6135883438a17608a02cc0bc00002feee9e2b7143c97046b2068edc6b82fb14809103c618009083080be00002fee8b32c594b49aa4692070ec069c2ed14988f03cc18909583000cc00002fee2fa2b314149504561fc8e786782dd141088c39016908782d40b400002fedd1b2bd948098445a2010ebc6982e713d086837c15e08302b00b800002fed7302cc14d49aa47520c0ed86982f914d88f43b417e08e03240d200002fed14e2bf949098246d20f0f086bc30214e88e83ba17709082f00c400002fecb752bc948c9744591fc8e5867c2e514688a839a16608782d40b400002fec58a2c894bc99e47320d8f186b62f414988d43b617808902d00b200002febff129d936491242d1e98df06302ba12e081836e15f08302c00b000002feba0d2c5148498846d2038e8c6902dd14108c83aa17908a82d40bc00002feb48f292931c8b64041d70d6c6002b412e880c35415608182a80b000002feae792d415109c248220e8f206bc2fd14c88ec3b617108903000c200002fea8ca2a613c894843b1f18e2c66c2e113f888c39c16d08482bc0a800002fea3002b5943c97245b1fc0e8467e2e413e887837816b08902d80ba00002fe9d322b2942493e44c2008e9c6902f614608c43a017408e03000c200002fe976c2b7145897245e1fe0e886982f615008fc3c618308c03040c200002fe91ba2ab94349604471f98e5465c2c9133884836815307b828009c00002fe8bdc2bf94889964662038eac68e2e614488a83c8185093832c0d800002fe86312a593b09384411f58e3065e2d814408cc3c8190099035c0e400002fe80782b2942c9584511f90e6c6962f214a88ac3b0175091834c0e200002fe7ab22b093f892c4441ed0dd86502d914308a03ac16d08b02f80a800002fe74eb2b594609744541fd0e806882ee14809083c818b09182f40c200002fe6f3b2aa13e491c4391ee0ddc6382ca134883c36016708402c00a600002fe69502c0147898045c2028e9869c2fd14f88dc3ae17f09103200ba00002fe63872b6945c98a46b2088ed46942fb15089143ca17a09083200be00002fe5dc02b8145c96c44d1f28e286462d013c087038815b08402c80b000002fe57e32bf94a499646a2068ea068e2e213e887c37e16308302b80b600002fe51f92c3948898846e20b8ec86b42f014c88e43ba17d08d83280c200002fe4c192c694c49a647920c8ef86ca30815489003be17e09383240d600002fe46442bc146496a4662000e9c6982e513f08a039616c08482dc0ae000) else (if i < 504 then 0x30126162be14709704582000e7c6682d2138086037c16b08482d00b4000030120322c1946c97c45f1ff8e786882e1140886838416b083029c0b600003011a662bd149098846820a0ee06b430214f08f03d818909882fc0b4000030114c72a293d09264401f38dfc6382c1137085437415d08582d80bc00003010f052ad93dc92243d1f50e106602df141887c38616608402c40ac0000301091a2c594b09aa47220d8f086ca30d15589103de18209203180c8000030103122d515109de4882130f146c030214988d03ac17208882c80a80000300fd742a0136c91842e1ee0e146462c6135885838416a08802ec0b40000300f7872c1949899846f2048e9068e2e114608cc3ae18109003080b60000300f1ca2b5942c95044d1f70e486622d413e889c38e16808282bc0aa0000300ebfa2b994749824541fa0e506722e1141088839017208b82d80bc0000300e62b2b9144497445d2078ec46bc30415409043d217e09303100c80000300e0712af93e892443a1ef8e246522d1139083c38416208202c40c20000300daae2b6945095e4511f90e3466c2d613f088039a16c08582cc0be0000300d4bc2cc95049cc48c2100f106c630315089343ec19209382fc0c80000300cf052a7140895e4501fb0e6c69a2f714d89203ca18409283100bc0000300c93d2b113f093e4491f50e186662d814088943ac17908f82f40c20000300c37b2b8946897c45e2030ed86aa2f914988b83a817508b02dc0ac0000300bdd32a313b892e4411fa8e586702d713b884c34e14e07f82a00b60000300b7ed2c694cc9a64812118f186ca2fc15189103c817d09102e40b80000300b2242b614449464481f48e286442d413f88c03aa17508a02d40b20000300ac5a2ba146c9824601fe8e786862ed13f887837e17008b82dc0b80000300a69b2af942c95a4501f90e506762da13d08ac3aa17208682f40c20000300a0d12bb145c99447220c8ed06b630615109083c218809403500cc00003009b082ba94689784622000e7c6742de13d085837815e08102c80b40000300954e2af93d49324401f28e1463c2c1136085036e15d08282bc0ac00003008f622c5147898a46620d8ee06bc30915609443de18e09002fc0cc000030089892bc146c96a4561f58e506682df141089c38416e08c02e40ca000030083a52bf946096c45b2048e8c68e2e814388ac39e17508c82ec0be00003007de02b7142c96244f1fa0e646842eb14408c03aa18008e82ec0b4000030078182b4942095445c1f90e606782dd141087839217a09283180c0000030072612ad14189664511f80e986aa2f614888c43aa17e09003280dc00003006cb32aa13f09444541f98e5c6742db139887037616408682e80b4000030066fc2a913c092a4401f38e4466e2de142888c39217708a82bc0b6000030061302b6142096e4582018e8868a2f014608ec3b417a09003180c000003005b632b5145c97a45c1ff8ea86a02ec14988e03a017308902d40b00000300559c2b514289624501f50e5c6922e6143089c3a417108b82ec0be00003004fd12b5146896c45f2058ec469e2ee14b08d439416a08882d80be00003004a292a293a490c42f1ec8dc463a2c6132881836a16108482ac0b2000030044482c814f49ca48a2168f306e030915a09403d017e09183080c200003003e832b5943495444d1ff0e806702e614808d43b618009002e00a4000030038a52c2949899a47220c8ec868e2ef14788c83b017d08a82dc0b0000030032a22d415049c24782058eb068e2ee14708bc37a16108302a009e00003002cd62b5143c9684551fc8e5c67a2e413e08b03b217208a02f80c2000030026e62c914c49a44852168f106cc30315108d43b017d08f83040c60000300213a2a513c091442b1f08e3064e2d0136083437c16808702b80c200003001b6e2bb148498e4662020ebc6a02f414e09003ce18009003140b8000030015b62ac13d893443f1ee0df46362c3132084837416808582b80a600003000ff82b014049444491f38e106382ce13b085838616d08982bc0b400003000a2d2b7943894c4451f20e1c6522ce138086c37e15c07c828c09e0000300046a2b4942c9604431f58e246602d313e088038616408302b80be00002fffec82a613c09264381eb0e0c64c2c7133085437215d08382ac0a000002fff8f32be14849864662030e9068c2ed14708ac39a17b09303340ca00002fff3162c4148c99046a2068ed06c02fb14b88bc3ae17e08a82e40d200002ffed432be14949924632050ecc6942e114488bc3a017608682c00aa00002ffe7612be147498046a2090ed86ac2fb14d08c03a217508d83300d800002ffe18d2bb147c96c4621fd0e986862e3141088c39216b08702a80ae00002ffdbb62b8948497e4612040ea069c2ef14508d83a616d08602d80b800002ffd5ec2bc947c9844652098ecc6be30315089003c418409282d80c400002ffd0262b594649924601fe8e786842e814488bc3a418008d82d00a000002ffca422c214ac9a047c20e0ee06a82ee14608ac39216e08a82f00ae00002ffc47e2af13fc95844d1f68e4066e2dc14208d83a017a08d82e00c400002ffbecf2b0941c94844e1fb0e6c6842ea14788e83b418a09983240ca00002ffb9072b7946099a46f20b0eac68a2e814988b83a217008b02dc0b8000 else 0x30298e72b013f49584541fa8e4067c2f414d09143d018b09583280da000030292f02cb94b499e47620b0f006c62ff14c88f83ba18308e82f00c400003028d292b3944897645d1fe0e706962ec14908ec38c16b08582b80a60000302875f2b7942493e4471f20e286702dd14708c83a417608b02b40ac0000302816f2cd14d89ac47620a8eb46ac2ef14808fc3aa17708982d40bc00003027ba62b4943497244e1fc0e946942e714688ac3a416b08702e80b40000302760e2a093949004261e20dd46402ce13c88a83a617708582e80ca0000302704b2b414349604511fb0e3c65e2d6140888038216608382d80ba00003026a6d2c2948096e4571ff0e346542d413e888839817408c82f40be000030264b82aa13f495044d1fa8e646742de144888839c16c08282ac0ae00003025eb82cf15089d24832110efc6ce30914c89283ba17a08f82e00ba000030258eb2b914989944762060ea46982f014c08c83c418a08d83140c000003025363297936490a4211ea8db86342ca139088039a17108a82d80ce00003024d742c794bc9ae4822120f486ec31715a09483ec18d092833c0c8000030247a72b9945c9684591ff8e906862eb14c89043a216f08902ec0ca000030241f82ae141c9524431f60e506682d1138886037616208602d00c400003023c2a2ba94649764541fe0e7c6762e314788c03ae17a092030c0d60000302366e2ab942094e43b1ee8e2065e2cc13d088438416008582ec0bc0000302309c2b814649944601fd8e7c6822d4139087c37c16708a02f00c000003022ac12bb146499046f2018e9069a2e5142889037816708d03000aa000030224f72b9946497c4511fe0e906842e514508a83a416f081829c0ac00003021f352b514089564591fc8e5867a2dd14108cc3a417108402c00b00000302197d2b194189584491fa8e6c66a2d4143888838c17609283140b8000030213842cf153c9c847f2118ef06ae2f014788983aa18008f83140ba00003020d992cb14c89a04642008e986782e613f889438e16f08d02f00be000030207dc2ac94189584511f70e7067c2df13f08c03a017508f03000ca000030202142b4143894c4561f80e5866e2da140888037e16c08a02e00ae0000301fc622aa93ec93243e1f00e386502c8132082c36a15e08382b40ba0000301f6a72b0941095a4561f90e4066c2ec14788e03ae17b08f83180ba0000301f0db2b614689744662020e7c68a2f814d88e43b617b09083080ce0000301eb262aa13dc9304401f38e206562d714108b03a417508b02e80c80000301e55e2b414609824642008e946982e214308cc39416a08882c40ac0000301dfb32ac93f49444401f10e146522c9135084437816108482bc0ae0000301d9e22b8147098447020b8ee06a62ed14808d83b217108d03000b80000301d4072c214a89a246b2098ed86bc2fd15489283d218309603000c60000301ce662a493b491c43b1ec0e0866a2e314188b83b817d08f02f80b60000301c8992bb945898445d1fd8e806782e714688bc38616008302c40ae0000301c2e92a713a49204341e78de86322c8139888c39217308d03000c00000301bd102bf148c9864662040eb86be30314c88dc3b818308d82dc0c20000301b7612ab13e49264341e58db462c2c012e87e434214907b026c0a20000301b1bd2a0938491242a1e50dbc6382c5139088437616208a82c40b00000301abe42c314d09a046e2048e9c6a02f314a88e03ba17508b82fc0be0000301a6302a994049504531fa8e686782d714088b039817208f02f80c20000301a09a2a293e094244c1f58e486742df13a886c37c16008202d40a200003019ae62b4945c9784632050ed86b02f214888d43b217308782e00bc000030194c92e495809f249721f8f706ee31015a89583ce19109783180ca00003018ee52c4149497a45e1fc0e6c6842e214488b839c17a08c02e40cc000030189132b7946096c45b1fe8e8c6882ed147888038e16908b82cc0b20000301834e2ad14189544481f98e7c68c2df14108b038e15d08382c409a00003017d732bd94989a24762090efc6d430d15389303bc18008c83040ca000030177a72bb946c98a4632020e9467c2e614888ec3a817408b02e40ac000030171c02c894e89aa46f2098edc6b62fd14a08c03ae17a09082e40cc00003016bfe2b2947095a44d1fd8e7469a2f114808d43bc17908d83180c0000030166222c0147896a45e1ff0e7c6742e214088a038416208982b00a4000030160462c2149099246920f0ed86b62f614d892c3ce18609683280d400003015a5b2ca14d499c4651ff0ecc6922ef14e08e83b817d08d82e80b40000301548b2bb942094e44a1f70e686862d913d884837816c08702d40b800003014ec42b714389704551fc0ea46b22f514d08c03be17908e02ec0d0000030148e92bf14709804551fc0e786802e213f889838816d08882d40b0000030143092c714f49aa4832148f206b02f714c08f03b417d08e82e409600003013d472b514489524541f90e706842dc141089438e17308b02d80b0000030137642be948096e4681fd0e746902e314688b43be17d09203200ce000030131b52aa93cc9304421ed8e106502c7136085037215c08a82f40bc00003012bed2b7945096e45c2020e9c69c2ee14a08ac39617008a82dc0be000)) else (if i < 507 then (if i < 506 then 0x3040b922ae941c95044c1ff0e886822e114388b439816c08582cc0b4000030405db2a693d09244431f88e546662cf138083435616008602e00ba0000303fff42be147898e4622030ea86962f214c88c838816b08682e40ca0000303fa332ad93fc94a4391f30e7c6802d614788903a016e08702e00a80000303f4732b2143098245e1fb8e806882e314888dc3b817a08a83000d00000303eeb12b3940094844f1f30e2c66c2c8137883836616008602f80be0000303e8e02c1949498446b2048e9467c2e714a08bc39216c08a82dc0cc0000303e3332a613c892c42e1eb0df06622d413f88ac3b617c09482e40c60000303dd682b9947c98245b1fc0e686762dc142089838617208c02c809c0000303d76c2cc94d89ce48820f8f006cc30715209403e2188093031c0c60000303d1932ba147496e4651fb8e806702ec14a88c439817208c03100d80000303cbcc2b8146096a4531fc0e906982f314508a03b017908d82e00ac0000303c6072b0943894c4431f70e546682d813a087c38c17508b82c80b60000303c03e2b6141c9564501f80e2c6642e014288ac39e17008d02e00c00000303ba932ab13a491843d1f20e3466c2d913b087c38016508582b80b20000303b4b02c614c09984622078eb06982f214b890c3de18e09482fc0b80000303aeec2b6142496044a1fa8e686702dc13b086838216408882c80b00000303a9152b414589764602020e946922e014108bc3a817b08e03140be0000303a31d2cc95109b647820f8f146b42f814f08f03b617808982d00a000003039d702a513a490c42f1e80dd46382c5136083837016208482b00ae000030397802c594c899e46b2048eb068c2e914708b839617b08f02f00a40000303919e2c394809904732090f046d630815689543ea19409d83700de00003038c0c29d13a092e43f1e80df064a2c1136885036615f07f8288094000030386302b9947c97645f1fd0e986942e714908bc39416808682c80c0000030380632bb14789764652020e806802e013b086c3ae17508782cc0ac00003037a942ba145096445a1ff8e6c66c2e014488b03aa16708903080be000030374c02bc146896a4642058ec46902f014308c839c17608c030c0d000003036f3429993689164391ef0e6c6802e6143089038e16f08382c40b2000030369572c514989844652060ecc6b430815008e03ca17f08b02ec0c80000303634a2d595289ce4852128ef86cc30215208ec3b617808f83280d200003035da02a613a892e4391f80e706802ea14e08f03ac17408d03000ca000030357da2b5942494443d1f28e306622e014208a439817809383080da0000303522f2a513dc9284311ed0df464c2d513d886038817308982e80b600003034c6f2b594209504441f28e0c6462d013a085837816f08782ec0bc0000303469b2be949899645a1ff8ea06902e914c08e03ba17e09183080c2000030340e22b014089444421f88e4066c2d1139887c37416b08982e40a600003033b182b614209524591fe8e946902f3144088c3a417408903000a6000030335282c794c899c47120b0f006d430515289243e017e092832c0c800003032f8929c937490242b1f38e2c6502d913d887838a16b08a03140ac000030329c42b914549724592068e746842e514808d03ba17c08e82d40b2000030323f02bb14489764611fc8e7c67a2ea142086c38616308382b80b600003031e2d2b5143c94e43e1f00e2c6502c7135081037215c08502900b00000303186d2ab93cc94044a1f48e1865c2dc138086c38015a08282d40b6000030312912c2149897a45a1f60e606782e1143088c3a617908c82e40ba00003030cd82b0941c9624501fc0e8c69e2f214488a43b218209102e40b8000030307282a493d093a4451f88e6066c2e014688c439c17908f02f00d20000303015b2b7143c97245b1fd0e7067e2dc13f889839c17408402c80ba0000302fb882bf946897645b2058eb86a42fe15389043c818509003080bc0000302f5d72ac13c893243c1f00e146622d713c087838615c08082ac0aa0000302f0132aa94149424451ef8e2064e2d613c887037817108c02c00ae0000302ea3c2be14b89a447d2100eec6c430b15409303d218b094031c0d00000302e45d2c2148499a46f2020ec86b42fa14a08c83b618209182e80c60000302dea62b0143896845d1fe0e6867e2e0144088439617608d03100c60000302d8bc2c794cc9a84822140f246dc30b15a89543e019209703100c80000302d2f62b6140c94844c1fc0e6c6742e314508b839616e08482c00ae0000302cd1b2c1148496e4602060eb069a2ec14888b43ae18108f03080b40000302c7662aa13989284411f30e046482c4132087838816c08d82e00ac0000302c15c2d815349ce4822118ef46b42f614c89043a617508d02f80c40000302bbb22ab93ec92243b1f30e346642db13c886c38c16908c030c0cc0000302b5c82c614d89ac47d2118f386f831d16089603f019009b83600d80000302b03529e93648fe4261e70ddc6442c7132883038016c080829c0a60000302aa672b5142c9564491f70e4867c2e314988b83a816808182d80b40000302a4722cb94b49ac4742080ed06a02e814a08d83c618c09683300c200003029ea12ba148098c4682050e946722ea13d887036615907f82980ac000 else 0x3057ebd2b1140894644d1fc0e606702d413d088439a18009483100c4000030578e62bd949898445a1fe8e7c68c2e614788cc3ac17808982f40ba000030572ff2c614c49ca4822088ed06ac30415608f03a816d08702dc0bc00003056d252b894589784591fe0eac6942ee14b88ac3b618409683180c8000030567612b094389684561fb0e5c67e2e9144088839416d08a03180ca000030561982bf94809864632050ebc6a82f114808e43bc17308c02dc0b600003055bcb2b694209604501fc8e8c6a82f914808c43a417708f02fc0c80000305562f2a513dc9324361f10e1c6622da13f884c36a16708282ac0a20000305503a2ca94c499a4632020ec06a42f314b08f03d218609583140d400003054a652ba942c9544551fe8e4c6622cf13a88a039016b08902c80a2000030544972b6144098246c20c0ed46cc2fd14788d83c8187097032c0d400003053ebd2ba943093a44a1fa8e706882e9143886c3a017308b02ec0b60000305392729d93a89144341f50e0c66a2d813c089039617508d82f40ca0000305334e2b8944896a44d1f88e446822db140086038616a08382b80b600003052d682c2948c97a45d1ff8ec06a42f914d08f83ac17208a02dc0ae000030527922ba947c9804511f80e8868a2e714588d03b817208982e00aa000030521d92af13f894c44d1f48e406582c6139887c37c15d08382d80ae00003051be32c6149899846a2060e906962ef14808d43b818909583280d00000305161f2b194389664632050ec86b22f714c08e03aa16e089030c0be000030510842a213a490242c1e70dd86502d513888a83aa171091830c0cc00003050acb2ab13e093643d1f68e5066a2d9140087038816c08582b00a2000030504d12cb94b09ac47c2088ec06a42f115289003d4187094831c0c20000304ff0a2ba948c98c46d2010e6466a2e314908b43ac17709103000c60000304f94b2b4142894a4471f70e406722de13b087837816908582dc0ce0000304f3772b9145c96445b1ff0e806762e114708ac3a616608902dc0b00000304ed6d2d395109ae47e20f0ec86a22e514308a039416b08d82d40b40000304e7a42ba14649704622060ebc6a22f814c08f83b817c09283140b20000304e1e52b113f093e4421f28e006582d313d086c36215907f028c0960000304dc412a193ac9164381e88df86462d113a087439016508802bc0a20000304d6672bc94809704511f90e5868a2ef14888dc3a417208d02f00b00000304d08d2c2149c9864692070ed86a02ec14688e83aa17609082d00b60000304cade2ad142496845b1fa8e406622d4139086438215f08482dc0ac0000304c5052c2149c99445c2040ebc69e2ed143088838816f08b82fc0c60000304bf152c7149898c46e2058ea868e2f214b08c03a617308d03000ba0000304b9372c194889864662080eb46922fa14988f03c218809083000ca0000304b37d2b214649804521f90e446582d3140089838c16708402a40ae0000304ada22b9143095a4662040e7867e2de14208803a017708e02c80ae0000304a7dd2b894689804602040eb46942f114588e83ba18509183140b80000304a2262ae14089464481f80e346722e714508c83ae17309083080c200003049c7b2a893d09204321f50e486822eb14a88c43a617d09602f80bc000030496ae2bd147499447520b8ebc6a62f614d08d03b217709302fc0ba000030490cc2c194a49924742098ef06a82f715209483e418409582fc0b600003048b1a2aa93e893c44e1fb8e8868e2ea14108903a017108a82ec0c60000304853f2bd14589664591ff0e986762e3142889c3a617e09202dc0ce00003047f9b2a413b09184311ea0dfc6522c7131883436415207b82700a4000030479bd2be948899446920e8ec46a22f614e09043ca187093832c0cc000030474002b394349664601fe8e6466e2e114488d43a617b09082f00c200003046e4e2b2142895e44d1f68e7067e2db13e086438216408582c40b4000030468812b3943897045a1fe8e7c6762e513f886837c16608802b80b8000030462982c314ac9a647b20e0ee06b22ff15489203f619a09c834c0d000003045cf72a713ec9444391f10e106522c8137884036a16b08502c40c6000030457442ac140895e4471f18de863e2c4136085838016408602e00c4000030451842b0141896e4591fd0e8c68c2ed14488c83ae18009282f00ae00003044ba62bb147c9704662060ec46a02f414b08b83ac18508e02f80ba000030445c92c314dc9ae4762060ebc6ac2eb142887c37e17208982f00be00003043fe12c214c89ae4702090ed46b62fa14a88cc3b618108f02e40c4000030439ec2c894a899646d2048e9c6822eb14e89003a217808b82b809e000030433df2d995309d648f2128f186c030e157092c3d018209382f40c600003042e392a793c09504481f68e406602d914488a43b216e08982e80ae0000304287e2b5940495c4541f90e5c6722e013f08b038a16908582b40b0000030422a62be94989a246f2068eb86a62ff15009143de17d08902ec0b800003041cf62a593cc93e44a1f80e2c6662db141889439c16f08b02c00bc000030417382af94249544511f90e486682d713d087037216208402d40c6000030411502c414cc99846d1ff0e886922f014508a83b017c08e02fc0c2000) else (if i < 508 then 0x306f2412bb94ac99e46620a8eac6ae2f314d08ec3b417708e02e40c40000306ec812b214009604572000e886962f214c09003cc18709082e00ae0000306e6ad2bb94509764501fb0e546782d614208b039016408382d80c40000306e0bb2cc14c899c46a2038ec46922f114708b43a016808802ac0b20000306dae92b9143c9604591fd0e706782dd13e887038a16008602d80a00000306d5262ba142095e44e1f68e446602cb13b885c37815f07f82a40a60000306cf432c3149c98c46d2040ec46a02f614a88ec3c418709383100ac0000306c9832b2944897a45e2058ecc6962f114588c438416908a02d40bc0000306c38e2c914bc9a447720e0ea86aa2f814f08c839817708f83280ba0000306bdd62b0144094044b1fb8eb06a02f214b88b03b217b08502ec0c60000306b7f52c614a099a46a2078ee86b22fd14a88f83b217808c82ec0c40000306b2432ae13ec9404461f50e4868a2f414e08c83b817708682d40b80000306ac502cc94f49c04772100ee46ac30415089203be18308d82e40b80000306a6632c3147097e4612038e806742db13f886438015608002b00ac0000306a09f2b1942495e4581fb0e5866c2de14588d83b017508b82f00c800003069abc2c4146496e4571fb0e8067e2ed14508e43a417408402a80a6000030694db2c214b49ac4742060ee06ba2f714988a839e18008e830c0d000003068f0a2b614349604572048eb86a42f3150094c3e418d09c03300b2000030689242c414949864712090ec46a82f914c08d83c418208e02f80bc0000306837d2ad93f893c4491f20e286562cf139885437616208502d40b000003067d962c4148099a46f2050ebc68e2ee14688ac39817208b02cc0a8000030677d42b6145096e45f2048ee46ac2ee14808dc3b017b08e82f80b0000030672272ac93c09424451f50e106522cf13c885036416208102b40b200003066c642b3941893a4411f08e286662e214088983a417708682bc0ba000030666c22a3939c92a4361ee0e206562d713a088438616208302d00c0000030660e32ba146096045b1fd0e5c6682d313988783a217b08e83080c400003065b2d2ac14209664581fa0e9068a2e713d08983a017508f83140c00000306553c2cf94c899c4661ff0e806622dd14308ac3a217308f030c0c600003064f712b4941894e4511fc0e686882e314088ac38216808902d00b2000030649712d395009ca48a2188f346c6303152090c3c217f08f02e00aa000030643b02af141894c4511fc0e586762e114408c83c417308a03000c800003063dd02c014bc99e4732078ec068e2f114f88d03a817908f83000c0000030637e92c814c09a646a2048e9468e2f514988e83ac17b08802e40ba0000306321a2b914509824652050eb069630114988f83ba181090831c0c400003062c692ad13d89404421f88e286622d313c886c38816208682e00b4000030626972be943495a4581fe0e646742d914088a43a416a08502b40b4000030620c02b7946097e4601fd8e8c6882f114a88cc3b017d09583100c200003061afd2b394109544491f80e8c68c2e814508b03ae17408e82f80c2000030615472a994009504471f30e306602d714088d039e17208c03000c600003060f6b2c514e49984612008ec06982ee14688ac39016f08983140c00000306097a2c714c89b447320a8ef46d42fa146889039e16b08a82d80a8000030603ab2b9147c97c45a2010e746842f014888e43c818008d82f80c00000305fdf72af93f89304441f08e5866e2dc13e087439416808482e80aa0000305f8092c915149d648c2158f446ee31615189143c817e091830c0be0000305f2472b2941c95e44c1f88e486462cf140887c38816b08582d00ae0000305ec882b0943095444d1f80e2866e2dc13b088838c16b08702dc0c00000305e6db2b013fc94444c1f90e2c66c2da13f888839017108802d00ba0000305e0d82cb94e89b648020c0ec46a02f814c88e43a817409002ec0bc0000305db3f29d93909124311e90dc862c2bb135083436c15b08302d00ac0000305d5712b2143895a4531fe0e946682cf13d087c39016e08902e00d40000305cf8f2c614d89a047120b8edc6c630415389283f219609383180c80000305c9eb2a693cc9504491f78e2c6542d313c888038616a08a02e80ba0000305c4072c194b49944702078ec46ae2f814d88d43a216608802f00bc0000305be452b0144096e45b2000e6c6702e014288d43ba18808f02f80c60000305b8a52a313ac9144391ee0db061a2b8135084038816e08482b40a00000305b2c72bd94c49964692038e8c68a2e014608b03ac16c08b03080c20000305ad052b1940494243d1f58e486682d613f087838e16408302c009c0000305a71a2cc15109c447a2110ed86b830315789183ce180093030c0bc0000305a1542b414349624521fa0e706702db142089038e16e08a82f40b400003059b762be945c96e4551fd8e9c69a2ef14b08f43b417909082f80b0000030595d72a1139491442a1e60dc86362c1136885838a16408302900a4000030590352a213a090c4291e50dd46242b612c87f436415707c827409c00003058a572bf14ac9a447d2138f0c6c82fa15108dc3b417808f82e40b2000030584842bf946896e45c2040ecc6aa2f314a08e83a816d09002f40c6000 else 0x307deb100000000000000000000000000000000000000000002e40c60000307d8eb2b6141c97445d2008e8467e2e714588ac3b418309003000be0000307d3222bc143c95e44d1fa0e3c6602d914408c83b417a08e02ec0bc0000307cd402cb94c89a447a20d8ec06922f214909003c018509a03240cc0000307c7802b3145895c4542018ea46a62f014a890c3c818509303180cc0000307c1b42b3144c94a4451f40e2c6502d113a884c38617209082d80c00000307bbdd2bc94649864632040e886842df14488cc3b217409003100b80000307b6392a193a49224361ef8de86402c7139888838816608782c00a80000307b0902a2139490c42f1ea0e106582d0138885c37215e08602a00a40000307aae02aa93ec93c4421f88e6067e2e314008883a017608b82f80ca0000307a5272aa13f093e44b1f30e146682d513b087c38a17308a02e80c200003079f6d2af13f89484481f38dec6442c0131882035015108102a40aa000030799bf2a513d092443b1f28e3c6822e613f088837e16508302c40b0000030793ee2bd947096844f1f88e5866c2d2136888038a16c08902dc0ac00003078e0f2ba945495644b1fb8e9c6922e514688d839e17508a02e80ba0000307889a28d13088e84151db8d9061c2bf132083836015207d02a00a8000030782d12b7943095844d1f90e1c66c2d613f08a438a16c08982f00b800003077d312a3139c9324431ef0e286762d613d085036a16308402c40a40000307774c2c5948c9864662030eb86982e314988cc3b417e09103180be000030771862b4941c94e44b1f58e406562d013f089c38c17208a02f80c600003076bb72b794509784642040ed46d430e15b891c3cc18c098832c0da000030765d72be147897645b2000e9469a2f014808a439a17208b82d80b8000030760122b8145c98646f20a8ec86ba2f814708c83bc180096835c0cc00003075a462b7944c96c4622018ea869c2ec14888fc3b217e08e03000c2000030754812bd94789964652038ed46ac2ef14c89243c018108a82f40c600003074ebb2b514149644581fe0e7069e2e914288803ae17408f83000b6000030748eb2b794709704672080ec86982f414188a839616f08602e40b60000307432a2b2142096045c2000e786862e514088a039016f08682bc09e00003073d6c2b113e89504421ef8e106562c8138088437c17008a02cc0bc000030737b12ae943096a45c2000e5c66c2d813c886438a16708602c00b0000030731df2bb145c96a4531fd8e706822e914788d03a817c090031c0c600003072c242b614149484521fa0e5c67e2e514508bc39817508d02e00b00000307267b2a213889044211ea8dec63c2cd13b087c36c161084829c0ac000030720c42ab93f494c44b1f98e386742e714608b83ae17508d03000d800003071ac92c814d89ac47020c0f1c6b62fd15188fc3be17c08d03340da000030714f12bd948c98e46c20d8eec6a42e114708cc39e16d08a02d40cc00003070f482a293b49344391f20e006642d514088c43be18608f02f40c4000030709762bb947897646a2040ea46822e0145888037e162084029c09c0000307039d2ba948097a4591ff0e586762e314408ac3aa17708d02d40c60000306fde02b1142c9524481f98e606742d913b0880396167084829809c0000306f81d2b5940c94e4441f30e486682d714188d439e17208702c00a6000)))))))))

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



private theorem b507735 : covered 507735 507862 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b507862 : covered 507862 507989 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b507989 : covered 507989 508117 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b508117 : covered 508117 508244 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b508244 : covered 508244 508371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b508371 : covered 508371 508498 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b508498 : covered 508498 508626 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b508626 : covered 508626 508753 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b508753 : covered 508753 508880 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b508880 : covered 508880 509007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b509007 : covered 509007 509134 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b509134 : covered 509134 509261 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b509261 : covered 509261 509388 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b509388 : covered 509388 509515 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b509515 : covered 509515 509643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b509643 : covered 509643 509770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b509770 : covered 509770 509897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b509897 : covered 509897 510024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b510024 : covered 510024 510151 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b510151 : covered 510151 510278 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b510278 : covered 510278 510405 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b510405 : covered 510405 510532 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b510532 : covered 510532 510660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b510660 : covered 510660 510787 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b510787 : covered 510787 510914 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b510914 : covered 510914 511041 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b511041 : covered 511041 511168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b511168 : covered 511168 511295 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b511295 : covered 511295 511422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b511422 : covered 511422 511549 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b511549 : covered 511549 511677 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b511677 : covered 511677 511804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b511804 : covered 511804 511931 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b511931 : covered 511931 512058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b512058 : covered 512058 512186 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b512186 : covered 512186 512313 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b512313 : covered 512313 512440 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b512440 : covered 512440 512567 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b512567 : covered 512567 512695 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b512695 : covered 512695 512822 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b512822 : covered 512822 512949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b512949 : covered 512949 513076 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b513076 : covered 513076 513203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b513203 : covered 513203 513330 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b513330 : covered 513330 513457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b513457 : covered 513457 513584 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b513584 : covered 513584 513712 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b513712 : covered 513712 513839 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b513839 : covered 513839 513966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b513966 : covered 513966 514093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b514093 : covered 514093 514220 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b514220 : covered 514220 514347 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b514347 : covered 514347 514474 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b514474 : covered 514474 514601 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b514601 : covered 514601 514729 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b514729 : covered 514729 514856 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b514856 : covered 514856 514983 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b514983 : covered 514983 515110 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b515110 : covered 515110 515237 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b515237 : covered 515237 515364 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b515364 : covered 515364 515491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b515491 : covered 515491 515618 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b515618 : covered 515618 515746 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b515746 : covered 515746 515873 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b515873 : covered 515873 516000 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b516000 : covered 516000 516127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b516127 : covered 516127 516255 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b516255 : covered 516255 516382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b516382 : covered 516382 516509 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b516509 : covered 516509 516636 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b516636 : covered 516636 516764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b516764 : covered 516764 516891 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b516891 : covered 516891 517018 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b517018 : covered 517018 517145 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b517145 : covered 517145 517272 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b517272 : covered 517272 517399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b517399 : covered 517399 517526 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b517526 : covered 517526 517653 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b517653 : covered 517653 517781 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b517781 : covered 517781 517908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b517908 : covered 517908 518035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b518035 : covered 518035 518162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b518162 : covered 518162 518290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b518290 : covered 518290 518417 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b518417 : covered 518417 518544 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b518544 : covered 518544 518671 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b518671 : covered 518671 518799 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b518799 : covered 518799 518926 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b518926 : covered 518926 519053 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b519053 : covered 519053 519180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b519180 : covered 519180 519307 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b519307 : covered 519307 519434 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b519434 : covered 519434 519561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b519561 : covered 519561 519688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b519688 : covered 519688 519816 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b519816 : covered 519816 519943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b519943 : covered 519943 520070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b520070 : covered 520070 520197 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b520197 : covered 520197 520325 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b520325 : covered 520325 520452 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b520452 : covered 520452 520579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b520579 : covered 520579 520706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b520706 : covered 520706 520834 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 507735 520834 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b507735 (joinCoverage b507862 b507989)) (joinCoverage b508117 (joinCoverage b508244 b508371))) (joinCoverage (joinCoverage b508498 (joinCoverage b508626 b508753)) (joinCoverage b508880 (joinCoverage b509007 b509134)))) (joinCoverage (joinCoverage (joinCoverage b509261 (joinCoverage b509388 b509515)) (joinCoverage b509643 (joinCoverage b509770 b509897))) (joinCoverage (joinCoverage b510024 (joinCoverage b510151 b510278)) (joinCoverage (joinCoverage b510405 b510532) (joinCoverage b510660 b510787))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b510914 (joinCoverage b511041 b511168)) (joinCoverage b511295 (joinCoverage b511422 b511549))) (joinCoverage (joinCoverage b511677 (joinCoverage b511804 b511931)) (joinCoverage (joinCoverage b512058 b512186) (joinCoverage b512313 b512440)))) (joinCoverage (joinCoverage (joinCoverage b512567 (joinCoverage b512695 b512822)) (joinCoverage b512949 (joinCoverage b513076 b513203))) (joinCoverage (joinCoverage b513330 (joinCoverage b513457 b513584)) (joinCoverage (joinCoverage b513712 b513839) (joinCoverage b513966 b514093)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b514220 (joinCoverage b514347 b514474)) (joinCoverage b514601 (joinCoverage b514729 b514856))) (joinCoverage (joinCoverage b514983 (joinCoverage b515110 b515237)) (joinCoverage (joinCoverage b515364 b515491) (joinCoverage b515618 b515746)))) (joinCoverage (joinCoverage (joinCoverage b515873 (joinCoverage b516000 b516127)) (joinCoverage b516255 (joinCoverage b516382 b516509))) (joinCoverage (joinCoverage b516636 (joinCoverage b516764 b516891)) (joinCoverage (joinCoverage b517018 b517145) (joinCoverage b517272 b517399))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b517526 (joinCoverage b517653 b517781)) (joinCoverage b517908 (joinCoverage b518035 b518162))) (joinCoverage (joinCoverage b518290 (joinCoverage b518417 b518544)) (joinCoverage (joinCoverage b518671 b518799) (joinCoverage b518926 b519053)))) (joinCoverage (joinCoverage (joinCoverage b519180 (joinCoverage b519307 b519434)) (joinCoverage b519561 (joinCoverage b519688 b519816))) (joinCoverage (joinCoverage b519943 (joinCoverage b520070 b520197)) (joinCoverage (joinCoverage b520325 b520452) (joinCoverage b520579 b520706)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 507735 ≤ index 975000000/512 := by decide +kernel
private theorem starting_value : fast 975000000=49640342 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 975000000=49640342) (n : ℕ) (low : 975000000≤n) (bound : n≤1000000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=975000000
    · rw [first,anchor]
      exact starting_value
    · have past : 975000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤1000000000 by omega)
        have within : index n / 512 < 520834 := by omega
        have lower : index 975000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤1000000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ975000000To1000000000
