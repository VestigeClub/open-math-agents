import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ1050000000To1075000000

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




private def radical : ℕ := 0x3f64282159270f0a9cf332cc4a3ba35eaa0d466ae15f84e8d480f57e32bdb1acfc6c97dc29fdab47eba45dc826205152e4cec2bbb014bd364effca9c907385a5b32e8764cf5fab24b89455060126be16ab3b1f3b1ca9e4ab61716d08a63cd08d9beba0b6ec218718d09d00159ed4a46861126cc6d49e127b07233a1403bbc1eb5aa0436f057e69934addaa3838a8cd645e22925f6fd3458d9cbe4c07d46b50a4176d002be911fe43f6d259fe2551e0aae8990e775098664287eeec857a6cdb5496e33073cc7114f6e9c5c6c3e3d5e5bed3a92b1830222ec506316936a383ebb3bbdb27ffa8cf4889b260ab78f982efc536b8ec6e8127b96b0e4f94e0c7f33d0cd1b608a6f18b5c70f9857f8bafda7b55e25c45092ad74d2fee5bf102cb810e5f6629f63c702c95380590c9141da9db46d488b52c4764e9e5d8827bb6383310ecaf042eb40779a7c361914a89d6ed9b504b9719e4683cda682d3f793a96e5863242de960212ab5278482d7dbfc287a9ee1dedadc81df00eec868cef9294f6154d887c05d999b10379980cbb957bf26d88543f48bb6f3b59777ab09c14b8bd6a0cdc6da0d75534a170549f5d610ff9cc58d6b9a0a24fe24faf24a10525d76f019d0d95e603d082b89a2925e1a90eb2bc413343d1422d982109b8aaf348a83f9e31f33874fa7c166e3aed59da855a7242cca3014f0322101082f8211da7ba692cc62d03582d972e1ade9af32a72000049eccdcda48784afa91fc0199ae2376aa7fc31913e53363c98bec30f44ba126df1c1b8712f4646368a138d8dab1d41de65e231f4628d041f2da185674fc2396fff155a9557564b1245b85bcf6af4cc95e281450d191ea14e2d2364675d16c20e450bbeb846ab67e34c0a31fb4e3b0ab119356f2ae7df82b0288e9efdbac0a5b64df09afba33e72eb3c70d8d40a57be2001c8acdf51525dc3d7ce75e1e371bc60043ad8ceca3562cde75cf465aa4de3a2200ea1d38a24a2d23fdebdb0a32b0bf1cc09f641944e2da1907c1bf09da9d2aebdc7d7e7dc2ddbb0311c64661626bf0a832421dce060f446b9446b6cc0f1de785a5928b27e511b39b239e41826aa1cae281bd8a375591fca8be92d8e68eef590080fa6ad55e416be531569db3c0b9dc0b8e4f08035ce50b508fb3427052d76e83ee6ce1b1415162ed4ca1fdb2f7965d02515cea6eaada9544c372c35fd2c03ef31740e67708d01d570f0cf3710d34e44f44c8badf510637b541294cf62ad92289020ae60793ce2ab1dbd1fe04605b030478177ca13a54a1351ef0ae57efdaebc1085830c223b802e07e62074750ae8f1e577f88fa79e8acb2440366bbc05bde72b8f5b7af87cf3ca5adfe82d37eac5ee60c26e9ab2ea3976c6284051336ad462336ff19b49b1b15345917ba0d95196c1c636db4cc120bf547dbe812d526311325bf37ec0d071a4985f4eb23d6a0c1271f8d592950199d7d5fa5e15add3e3a3eb2565e75a7ea867f2debabadd91631308553ef4e6da51e7368c38a3610a94dcd5fa2d61b64b5b29e01aafc9056dc59d40423cb26d4ea934b2ab26632aea3dce5b23361fa9fa769d191ebc7b060c66b047282c3f019c02d5dca5e4d1bffb8b6d3019931cd2ddb453e77acbe2c7ade29ab1b21c0487897e425f58b564cd8f7167754f7f096ee08bb57b955b3fecbdcad19ccca1cd9955e0b3f2950873c860850187c22f05238167dcb03eaed3258b01cf1f1a656e31115e6c9aa3222ae01fde264164049156c2aa13a29eb9ddd7dddebef34e30d09560e6a3c8d5ae5ddf250408738d996f1045c2c224550921ece8afeb446bcce3e117f16718483ebd5dfcbd7857fcfd916b4a3bed1e5a8adf77ee83dbe723d54c74c0ac163e707bec4006723598936d152110eb6dbcdd50f00d3f461136ebe16dae9f71da803ac90facd375331480cb0b37cf96f97bd5272bd7b4786f08d54ac923f259353685be4324b78f0c8fc22d39c1d4d6c58bfad1e797204a53fbba8b440d97ca358a6e98bb2179dd1194d59fd1438991b0427913573f64b4750846c0e64c7fad236ee93e5c743a0ee0f84cd52bff3967620650370598eaed69a0eeecab8a47f28bacca366f77c8dfa7e656d20f85ba878db3a0448d143aed255c14d92e7fd4be9b39cfc0364ee282fd21772cf4946f17f9e30bcde3aafbc55bb620a17961c47cfd5463cb260b847f5fa6f8dc04b9c98a3178b783218dc4d995f2dbcb8334c88b72b616fbed74990249d1ec6f751581bbc250a7ab54f59dcd9f80210f1bac5c5d0451bb65eb31e6b42548c902f9851abdd37a31b73a28432db82c8607c2aecb18baccd91aa482a74014611e48d3daa7107868c69dd018b9f9a214f42abeded6c1657835652069eeb422bab4dbc53bc91c035297e091b5d18d928a2fd9ea3cb3545fe9d121116bd5af44fb71157463150dab0f51398ad6cc3bfe3c4b8577a1293bdee2be9681639aa026487de57639009de777077b9f1762811b4a01f5c596da035257704699764c59a8ed1ffd3d257fe90ced26fcc6b8bbe690b8d924ca7fde9a27fdbc1672ec5698da7ce58dc110f5194cc5d969afe47c5088d9e23d295c02846b745eaa0a7590e79609922ff18e39520dbeef7890764ab5091bf1cafff147894dc1d8b13eb0a91eeaecc641b24f364b22fdbe30249192c4c16384d3d451072fb696eb8cb49f49f0ce7cf735d236b3cc4ba21bb57f6224fff50311301389e6c8d649ac58e8cc546e13ddf450cbc06b90283bb35e5d75c0515f6444e192fd75bc346c875215763fd10f5b535b9e99e767798ad8c5c34c509df93b48a481a4c68770ef10c584b8d142862dbf368fab8a24e29caabcc700667e5908a230fe321893a1869712462e63036aa575889b06a4486efb8c5acb407ddce1fc5a18e1cc7785f9ae26070b6978ad26e836f9e71a949432135cdc7e0fc8a59ca6c120efc1cb7aabf29b2aad47ebc5bfbe168f1a7607ddf062568e94dcd835c58a92c405f9583b2eac18e310bd9a82ab4aaf7bd513a236522f727a904f94139bdabc09ee11cd111f01ca51bd25a0b654f3ffa9312d8b779106401fa6cfd255bb7bceeaec53b5ab0a4d9d6eb76fe55104dfa48809dd80c200437ce606fee1ae8682d248c1366a396abc6ac3656ce2d637903c6cdc017c39a632f149eace56682d8b9ca2fb03be7fec8d5e8a59a35e8ede8a024c3abf22bf27cbe3944b37d16f475b3af805ba179e1811d601ae05d4079ac79f29518a439236a6440cc8f4caa0c410f8f3a03ca4adae6c24c05115e66cb7b954050ef22fd20bec951f3a74b1b920687880f22c8dbb9e36da678e0221b942cf82949daae648c6b396404b61318c22b36d03d2cece358d1eb38517aa2f4c7cf194c90740a44b2ba89a70ce5f642b16dcd51233eaa722a67119280d87a33bb5a3e0fd028351e6fbaeed37b56224f4ca73fa132efac8d6c9c2055e7d6244c5d32c18a9c26cdbe58f12cecf3146948e188bc339c0f5519e5629882fbef737c0fda9a7b460341834d6437127e5a9d6bf72085d391d5b563be37f2697546b0215959d72327e6e0319fbf34fbac483bb0bf2081a63b75611c7447af2baf96f04557ae1d405257e6882bb042903479cad3f9941d6be62d1309a5111326f27de16fd6a076b66b8c6959612ab5298e630735d32097be521bf7ede5e1afcf64d3727db3a077970f2060ebcb6b04033e02662f102a8731a314815928776099378dbfe68c7f08e4cdaeb6402a3cb9fa5235c9b29731ee3e2fe4c289e9bf78f2efab3f9043c74f620762318593c14c0b7e174d98e26f6898539a2cda9a3215e47f6503778d45111e429550a9fd402a415ae47fa3cad50c40ebfcd32acf14cdc9a2e85b1f2c167f80095baa68c24996082b4a2606645c8427dcbdb15522338752c9d8387fb19a1f4bf00a555df3a910317c3a043c4213fc34885b9b9ede8ef8a5024b283a02a42104f27e0e4194ad3a083912b833a1d6e3b6d25558f715be219b84d4273d83e76dc7ea5df4185250f4353c98cfd070004f2fc376c98dcbcdb88ad1afc17a4f11d7ab01667e8f91cef43131d922b7159d101c0a908a8277d8afa4fab492aacf65232583dbc53d4c4e6bc007e4645f22e556ca91c3e50b8fec103e285acdad8f3f4c449c9f94e4d10599188d0da59f8d35c041fea6d9da061ca1c2294b7645667603bd71b220558951e91736bcb679c4c2f9d377a9e60b06e2c60b5f27a3de5930c4c9dd5b38fccb6c55ea3cc7c9774d89485fb21a903bc21a259a502f4c32b5e0004d125b663cc06cf7bd5339a018baf5f02a7b8b5d5ec3c58038979ab57aa50b42276fd1e1c7841a3404228c96ed205938402719d86be065156c46dd4fbc8c3c625c331b5d04370b9ec0689102669eafe00982d7052d6167bd7622be5ee2664b5b0216368ad7f71cfce388096808753d9f8c1c1e5f7204f1d544fff07f2fe13660b2573bfc6a74806abf37dbec24f33d738c0b8e2a024daba5cf40174926c1aacc54709d0c015fbe4b20dddb724ee9ca223fed8defa0ac336fa633e4cf5999ace9138016eaf5d579073a8c8841f371b5cb876a2e4ea5df850d0d97b0ca2d2aac36cf7dc4a236a8923b605aa8c122b4276ad84852c0c4b165a46bec73d1e35c5e65b145ac6fb90119ec895a75d3457e9fbf042757cb756d189aaa150031630dc899af8bedccb1fbf12b737c8c68df1e9c7e209e787ad7d43eb96bc403abc1e2b28f082d97c3d0f12e6ae8158ad394a0131c02697b7bdf3980f8193dfa5a3e856343186ea362a0783274097ff9c6fe25066af882d0fb5bb2ae9148c95ca413db235736a1c87a439408edcc1aee1645d2d1a2f6d551aa780ba50a8dc2d920e33b3a884b7b5793eef7cc35a3bde7739587b446d493f5c8ebecd8160a6c279d7039a0c03a1a71c5cd50e11f23bb06e399ea223448808e05d82fe299220837404b74c9706b1ea893d61fb974887ffc69bcefd458a3d711578e5723e67c13bf0de09be8e9d45c0d91b53e476fc16c38d60889e8d4066625cd4ec6a76844aca7449cadcadd07539f6bfcf9ac11b4dc62b1c9c03923f2ae757548a4f37ad1fc5d3155e38e1b1428746411cb2b2446e16acdf6c2f6d7ed01159462e5d998653d001a3f2027cc31dfcc8421c297bcc5dbb48930e6c732b5472e5ba23cac15d12439333b93ef203b2ec2b307e48a24b682ebc33d5c8db7d796a25d9a02392abd456a0f470ed7d0c051524dddc3f629813550e8339066946b53d95451e89a600b246411e0020d063d93e96035b533407763be7cece7f67c28e4f536216cf7bf153f2dfe6a3a53cf69c0979919aa637da9eed563d76df0dfa043921b69242f136911266facade0cfc33ee65c29bbc9c90a0501944d576428542c747acbd64e59edcdf4e53f6dbced69faf39eb1156d398021271671d1db1b6f21cd614dbee091d3dc52de2f727c39f250b0f8b6ff5fa6a06cb90a0425578e9da714938b10dd5d994e5df223e7194c86352a2527b7699c80ac1b4b9c6fe09c59a7d082b7e9abf3a04de5fa39d5c7c0dc4bfe5a364699c0609c55f2de4c204fca36429c59d1b2457721a300d348a355557845462cfb385276d16dccee9863cc793842d59b53b4e550ce1797d88d2e04e3ba7139f2e26fec3d3b85573adf217a6d2754aec307473f813e365ee1fd28a7bcc943d87fb9b4dd612716b279ee5db0a048f8a44411cee220abacc418f4ee6af7fea6b11800a90d5056e646c369a5f51e432525dc07bf58012cbd0042535dec3d7a9da233424cc0ce0ddd07ed77510503ef2bb5bc51bd955ad2ea2a2b8070caf17d6202fa9d77e3d35c76e3d99eea0334d574cfec3f62e00ce2fc49eccfa96e6f9fa2d8d33843221d584547f8fe9fd6bac506c6f1d9bc934b52a17a437ec5ef4b8e6d443b4a78828bd18fe40ce1a05e37aa665a05e2616a7c2f08f0fdd8168adaf0855b7b9016ae10c728461b72b3c2efa224d0067616347de1a7a6fd5ecfebbac2362ba9a5e567f258f42ce2f3533de229032d467f548621a60d7d9158e3d4eb16cd488345afdc8cc678e0f1c417688e05982375284cd7e9ae592e3952c6913cd91b8d002850362d2f0664d3f3b97c068d51d9dc5230f3b36f6cd23334f8627b06b14e61e704e3e739bf07ab447f051392918122c801a84535d672f4194a66992b607e422dc252877579520c5825631ca21fa74bb6ec9e869924170756f9449ba65597ca015b6da10c48dbf339c9756be0657b5a0af00c84273c5400a4af7dfa8921b9ed1914f2c0f70a06f6af85ffaf23a5146a00bbe15bb7e9d03653df0fc0ef95f4ac6bf58a16e799a82bf08b5d05b86c9b85de26e837e67a88cc7a08ea4f89bd106538cf53455dbff073dfa4b41e4e524cdcf34bd4624b407c88ed8dfc7b42a3530736f557fa061c24aa6ef11a97a2540c571ebd46534e9038dee8b6d07a5a869a6b11df5bd9b805c311cbe7dbd2ffc98a3c3cc38a4fa0c7242831b8226c3ba67438772a2be814b36e6ec92e253c28d642e7d8675b4b69ec6e89781fda1c6f6d6bd5fca6db8144839cdf7416fce0e385d864b6f08f0df2465bd42633e2967a4f24575d15a536065016f31332d09ed97f6f9c8a1d08b1de792bb41c724b3a87ef1ab2da2518ef116b3dae48a11b4d9bf5f9ce278df370059d464ce3fcfd4f72067c0b82c72605acaac644135b0947d890432abd083939c97fd0bbaf4eac11fa29b4dbc2821757498d28201c5e6e26a33e6bce1acdf69b0221cb326c5e61207fc9a69e72cafc09f0dfca0c56b172266e095784cc56f9c530b007aad7342806c761c45a6f71e4bbbf342fdc16c2ecbb851c18c8342afe3e8fb262acff3a65b88eb99bbcc8760444c548db741a8918509fceec3382feb981845ff49fa4cc61982a18ea3f0f5d1e20a3d7c237dfb66bfe6e735aeea0ec74aba2438e4072ab9297775b56c3be5db35705bb2ec06a53dece158796a3ef60d2e16ef45fd2a923b1f215541afcfbb98299817c740d579c55da5ce3ca3f96c353a67a72476915357c1dce617d3f0c574357097acd1faf3a67bc21108681a5eb7b0b7db72fda69e59a84d98c52aed9aee336adfff4558f7e003bb1d7c63531845f0f1bceb4a4693a5eab1a2bf6263a96a3a51037617f8a6d44b239adfbcf8bd9b9e1ffa36d8f308e9bfb651c7a111814dbae611230e258574e7e46d28c4667c06b486aef1b6b0c7117dc39d684c1753f06e9969dfcf924582eb35cbdbf383a2f3ceb7f1fc9f9415617ce00cd7d9eb47ab7bf9ceb03c0ceef19d91b03bd7eefd99c0ef2c8d8ea5ccfb90ad107f41181f3bb57e2f4163f0e49b023186147bcb9b1936aee414f1c4c5b1e0ea889dfff5259f80b2b64d4b4abe30e6e886559e16473e433654114f084c14fc108031818cead09e4fc009220310a9e36757e318ac7ab463e3b96a22c53bc5a2b40deed74875091d99d10acd219eda98021a36c02be6670340f42aa95d013f1a8068b9e6cf27fe543bf7e2f9ca6038e32063d7b4e074f015d4885d0ed62de1044ee6d20b87127675490efcee65ebd8bfcc07ff3dd9b396c0ce9ab32f5025befae5a7776340f191dad3014e3c65be115576e1f28339c51179f1f1d47c6a5136ed21d8e2d5cddad3a12d737d9318f9f6722622d4495872ba74141bd6c48adde28d0a52c791e922f38043d15b1b286e67d621e2e1f5c20a8bfdf109602cddf61e616e597ebd755f88306d7954a35155cda0857652549f8456702b38d2f93754a3f4f99ab3ce2ecda9b3b8e70d66fc618e23bbf6d764e6221d5676f89794719f3ddf36077c8b392efe335c71f27fcac111d39959122e9b9395d2f98849f8b2eca265ff9db4b5ee1dc4cca7e20166436e2d28bb4d8d98553d7b78429d10f94d81c2b175b9eda174105c51ea023bf5fe08eddb98c665f7f6d63f63d623a93726489f7e1b2884cde3f4260b6996c51fe1407aebb7f43e9f2a0d80361bae56766a541ca48fd8d927cdd6090ce79cb535e80189d3a300ef194b119da950447541ffe477001d141fae36b726193c7ad35f23a9f4b063412d5a4167554cb6f37ec7507d901cda0882b241bbc79d490094da27faf16e3d3d8f418ae5d5490cc95e8719b46a8f00e258f949a098a610c072efc870b480793aac5ebdb73d860128bfc9dcbbbcf56d28d68abd722bfd4fae377be0c707a3da92a5ccfed67502c4906f6c42ad53c9f6527797d4752edbda702553b04f381fe7e4c0128ded302476e6cb91516774938bd2a428ca54dc6142bf23b727eea

private def light (n : ℕ) : Bool :=
  if n≤181 then decide n.Prime else n.gcd 36362187312343308237908191978622497844074801684595067807218795663968119832564672550353604998289613062149318532287769329350456815925726000644523337334285978306103163294146384971986648048091326497552386466930424881860855684345291680413833226169665212441092813294256787492335190489473168179200000000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤32787) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 181 = 36362187312343308237908191978622497844074801684595067807218795663968119832564672550353604998289613062149318532287769329350456815925726000644523337334285978306103163294146384971986648048091326497552386466930424881860855684345291680413833226169665212441092813294256787492335190489473168179200000000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 181 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤32787 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 64 := by unfold smallValid; decide +kernel

private theorem sp64 : smallValid 64 64 := by unfold smallValid; decide +kernel

private theorem sp128 : smallValid 128 64 := by unfold smallValid; decide +kernel

private theorem sp192 : smallValid 192 64 := by unfold smallValid; decide +kernel

private theorem sp256 : smallValid 256 64 := by unfold smallValid; decide +kernel

private theorem sp320 : smallValid 320 64 := by unfold smallValid; decide +kernel

private theorem sp384 : smallValid 384 64 := by unfold smallValid; decide +kernel

private theorem sp448 : smallValid 448 64 := by unfold smallValid; decide +kernel

private theorem sp512 : smallValid 512 64 := by unfold smallValid; decide +kernel

private theorem sp576 : smallValid 576 64 := by unfold smallValid; decide +kernel

private theorem sp640 : smallValid 640 64 := by unfold smallValid; decide +kernel

private theorem sp704 : smallValid 704 64 := by unfold smallValid; decide +kernel

private theorem sp768 : smallValid 768 64 := by unfold smallValid; decide +kernel

private theorem sp832 : smallValid 832 64 := by unfold smallValid; decide +kernel

private theorem sp896 : smallValid 896 64 := by unfold smallValid; decide +kernel

private theorem sp960 : smallValid 960 64 := by unfold smallValid; decide +kernel

private theorem sp1024 : smallValid 1024 64 := by unfold smallValid; decide +kernel

private theorem sp1088 : smallValid 1088 64 := by unfold smallValid; decide +kernel

private theorem sp1152 : smallValid 1152 64 := by unfold smallValid; decide +kernel

private theorem sp1216 : smallValid 1216 64 := by unfold smallValid; decide +kernel

private theorem sp1280 : smallValid 1280 64 := by unfold smallValid; decide +kernel

private theorem sp1344 : smallValid 1344 64 := by unfold smallValid; decide +kernel

private theorem sp1408 : smallValid 1408 64 := by unfold smallValid; decide +kernel

private theorem sp1472 : smallValid 1472 64 := by unfold smallValid; decide +kernel

private theorem sp1536 : smallValid 1536 64 := by unfold smallValid; decide +kernel

private theorem sp1600 : smallValid 1600 64 := by unfold smallValid; decide +kernel

private theorem sp1664 : smallValid 1664 64 := by unfold smallValid; decide +kernel

private theorem sp1728 : smallValid 1728 64 := by unfold smallValid; decide +kernel

private theorem sp1792 : smallValid 1792 64 := by unfold smallValid; decide +kernel

private theorem sp1856 : smallValid 1856 64 := by unfold smallValid; decide +kernel

private theorem sp1920 : smallValid 1920 64 := by unfold smallValid; decide +kernel

private theorem sp1984 : smallValid 1984 32 := by unfold smallValid; decide +kernel

private theorem sp2016 : smallValid 2016 33 := by unfold smallValid; decide +kernel

private theorem sp2049 : smallValid 2049 64 := by unfold smallValid; decide +kernel

private theorem sp2113 : smallValid 2113 64 := by unfold smallValid; decide +kernel

private theorem sp2177 : smallValid 2177 64 := by unfold smallValid; decide +kernel

private theorem sp2241 : smallValid 2241 64 := by unfold smallValid; decide +kernel

private theorem sp2305 : smallValid 2305 64 := by unfold smallValid; decide +kernel

private theorem sp2369 : smallValid 2369 64 := by unfold smallValid; decide +kernel

private theorem sp2433 : smallValid 2433 64 := by unfold smallValid; decide +kernel

private theorem sp2497 : smallValid 2497 64 := by unfold smallValid; decide +kernel

private theorem sp2561 : smallValid 2561 64 := by unfold smallValid; decide +kernel

private theorem sp2625 : smallValid 2625 64 := by unfold smallValid; decide +kernel

private theorem sp2689 : smallValid 2689 64 := by unfold smallValid; decide +kernel

private theorem sp2753 : smallValid 2753 64 := by unfold smallValid; decide +kernel

private theorem sp2817 : smallValid 2817 64 := by unfold smallValid; decide +kernel

private theorem sp2881 : smallValid 2881 64 := by unfold smallValid; decide +kernel

private theorem sp2945 : smallValid 2945 64 := by unfold smallValid; decide +kernel

private theorem sp3009 : smallValid 3009 64 := by unfold smallValid; decide +kernel

private theorem sp3073 : smallValid 3073 64 := by unfold smallValid; decide +kernel

private theorem sp3137 : smallValid 3137 64 := by unfold smallValid; decide +kernel

private theorem sp3201 : smallValid 3201 64 := by unfold smallValid; decide +kernel

private theorem sp3265 : smallValid 3265 64 := by unfold smallValid; decide +kernel

private theorem sp3329 : smallValid 3329 64 := by unfold smallValid; decide +kernel

private theorem sp3393 : smallValid 3393 64 := by unfold smallValid; decide +kernel

private theorem sp3457 : smallValid 3457 64 := by unfold smallValid; decide +kernel

private theorem sp3521 : smallValid 3521 64 := by unfold smallValid; decide +kernel

private theorem sp3585 : smallValid 3585 64 := by unfold smallValid; decide +kernel

private theorem sp3649 : smallValid 3649 64 := by unfold smallValid; decide +kernel

private theorem sp3713 : smallValid 3713 64 := by unfold smallValid; decide +kernel

private theorem sp3777 : smallValid 3777 64 := by unfold smallValid; decide +kernel

private theorem sp3841 : smallValid 3841 64 := by unfold smallValid; decide +kernel

private theorem sp3905 : smallValid 3905 64 := by unfold smallValid; decide +kernel

private theorem sp3969 : smallValid 3969 64 := by unfold smallValid; decide +kernel

private theorem sp4033 : smallValid 4033 32 := by unfold smallValid; decide +kernel

private theorem sp4065 : smallValid 4065 33 := by unfold smallValid; decide +kernel

private theorem sp4098 : smallValid 4098 64 := by unfold smallValid; decide +kernel

private theorem sp4162 : smallValid 4162 64 := by unfold smallValid; decide +kernel

private theorem sp4226 : smallValid 4226 64 := by unfold smallValid; decide +kernel

private theorem sp4290 : smallValid 4290 64 := by unfold smallValid; decide +kernel

private theorem sp4354 : smallValid 4354 64 := by unfold smallValid; decide +kernel

private theorem sp4418 : smallValid 4418 64 := by unfold smallValid; decide +kernel

private theorem sp4482 : smallValid 4482 64 := by unfold smallValid; decide +kernel

private theorem sp4546 : smallValid 4546 64 := by unfold smallValid; decide +kernel

private theorem sp4610 : smallValid 4610 64 := by unfold smallValid; decide +kernel

private theorem sp4674 : smallValid 4674 64 := by unfold smallValid; decide +kernel

private theorem sp4738 : smallValid 4738 64 := by unfold smallValid; decide +kernel

private theorem sp4802 : smallValid 4802 64 := by unfold smallValid; decide +kernel

private theorem sp4866 : smallValid 4866 64 := by unfold smallValid; decide +kernel

private theorem sp4930 : smallValid 4930 64 := by unfold smallValid; decide +kernel

private theorem sp4994 : smallValid 4994 64 := by unfold smallValid; decide +kernel

private theorem sp5058 : smallValid 5058 64 := by unfold smallValid; decide +kernel

private theorem sp5122 : smallValid 5122 64 := by unfold smallValid; decide +kernel

private theorem sp5186 : smallValid 5186 64 := by unfold smallValid; decide +kernel

private theorem sp5250 : smallValid 5250 64 := by unfold smallValid; decide +kernel

private theorem sp5314 : smallValid 5314 64 := by unfold smallValid; decide +kernel

private theorem sp5378 : smallValid 5378 64 := by unfold smallValid; decide +kernel

private theorem sp5442 : smallValid 5442 64 := by unfold smallValid; decide +kernel

private theorem sp5506 : smallValid 5506 64 := by unfold smallValid; decide +kernel

private theorem sp5570 : smallValid 5570 64 := by unfold smallValid; decide +kernel

private theorem sp5634 : smallValid 5634 64 := by unfold smallValid; decide +kernel

private theorem sp5698 : smallValid 5698 64 := by unfold smallValid; decide +kernel

private theorem sp5762 : smallValid 5762 64 := by unfold smallValid; decide +kernel

private theorem sp5826 : smallValid 5826 64 := by unfold smallValid; decide +kernel

private theorem sp5890 : smallValid 5890 64 := by unfold smallValid; decide +kernel

private theorem sp5954 : smallValid 5954 64 := by unfold smallValid; decide +kernel

private theorem sp6018 : smallValid 6018 64 := by unfold smallValid; decide +kernel

private theorem sp6082 : smallValid 6082 32 := by unfold smallValid; decide +kernel

private theorem sp6114 : smallValid 6114 33 := by unfold smallValid; decide +kernel

private theorem sp6147 : smallValid 6147 64 := by unfold smallValid; decide +kernel

private theorem sp6211 : smallValid 6211 64 := by unfold smallValid; decide +kernel

private theorem sp6275 : smallValid 6275 64 := by unfold smallValid; decide +kernel

private theorem sp6339 : smallValid 6339 64 := by unfold smallValid; decide +kernel

private theorem sp6403 : smallValid 6403 64 := by unfold smallValid; decide +kernel

private theorem sp6467 : smallValid 6467 64 := by unfold smallValid; decide +kernel

private theorem sp6531 : smallValid 6531 64 := by unfold smallValid; decide +kernel

private theorem sp6595 : smallValid 6595 64 := by unfold smallValid; decide +kernel

private theorem sp6659 : smallValid 6659 64 := by unfold smallValid; decide +kernel

private theorem sp6723 : smallValid 6723 64 := by unfold smallValid; decide +kernel

private theorem sp6787 : smallValid 6787 64 := by unfold smallValid; decide +kernel

private theorem sp6851 : smallValid 6851 64 := by unfold smallValid; decide +kernel

private theorem sp6915 : smallValid 6915 64 := by unfold smallValid; decide +kernel

private theorem sp6979 : smallValid 6979 64 := by unfold smallValid; decide +kernel

private theorem sp7043 : smallValid 7043 64 := by unfold smallValid; decide +kernel

private theorem sp7107 : smallValid 7107 32 := by unfold smallValid; decide +kernel

private theorem sp7139 : smallValid 7139 33 := by unfold smallValid; decide +kernel

private theorem sp7172 : smallValid 7172 64 := by unfold smallValid; decide +kernel

private theorem sp7236 : smallValid 7236 64 := by unfold smallValid; decide +kernel

private theorem sp7300 : smallValid 7300 64 := by unfold smallValid; decide +kernel

private theorem sp7364 : smallValid 7364 64 := by unfold smallValid; decide +kernel

private theorem sp7428 : smallValid 7428 64 := by unfold smallValid; decide +kernel

private theorem sp7492 : smallValid 7492 64 := by unfold smallValid; decide +kernel

private theorem sp7556 : smallValid 7556 64 := by unfold smallValid; decide +kernel

private theorem sp7620 : smallValid 7620 64 := by unfold smallValid; decide +kernel

private theorem sp7684 : smallValid 7684 64 := by unfold smallValid; decide +kernel

private theorem sp7748 : smallValid 7748 64 := by unfold smallValid; decide +kernel

private theorem sp7812 : smallValid 7812 64 := by unfold smallValid; decide +kernel

private theorem sp7876 : smallValid 7876 64 := by unfold smallValid; decide +kernel

private theorem sp7940 : smallValid 7940 64 := by unfold smallValid; decide +kernel

private theorem sp8004 : smallValid 8004 64 := by unfold smallValid; decide +kernel

private theorem sp8068 : smallValid 8068 64 := by unfold smallValid; decide +kernel

private theorem sp8132 : smallValid 8132 32 := by unfold smallValid; decide +kernel

private theorem sp8164 : smallValid 8164 33 := by unfold smallValid; decide +kernel

private theorem sp8197 : smallValid 8197 64 := by unfold smallValid; decide +kernel

private theorem sp8261 : smallValid 8261 64 := by unfold smallValid; decide +kernel

private theorem sp8325 : smallValid 8325 64 := by unfold smallValid; decide +kernel

private theorem sp8389 : smallValid 8389 64 := by unfold smallValid; decide +kernel

private theorem sp8453 : smallValid 8453 64 := by unfold smallValid; decide +kernel

private theorem sp8517 : smallValid 8517 64 := by unfold smallValid; decide +kernel

private theorem sp8581 : smallValid 8581 64 := by unfold smallValid; decide +kernel

private theorem sp8645 : smallValid 8645 64 := by unfold smallValid; decide +kernel

private theorem sp8709 : smallValid 8709 64 := by unfold smallValid; decide +kernel

private theorem sp8773 : smallValid 8773 64 := by unfold smallValid; decide +kernel

private theorem sp8837 : smallValid 8837 64 := by unfold smallValid; decide +kernel

private theorem sp8901 : smallValid 8901 64 := by unfold smallValid; decide +kernel

private theorem sp8965 : smallValid 8965 64 := by unfold smallValid; decide +kernel

private theorem sp9029 : smallValid 9029 64 := by unfold smallValid; decide +kernel

private theorem sp9093 : smallValid 9093 64 := by unfold smallValid; decide +kernel

private theorem sp9157 : smallValid 9157 64 := by unfold smallValid; decide +kernel

private theorem sp9221 : smallValid 9221 64 := by unfold smallValid; decide +kernel

private theorem sp9285 : smallValid 9285 64 := by unfold smallValid; decide +kernel

private theorem sp9349 : smallValid 9349 64 := by unfold smallValid; decide +kernel

private theorem sp9413 : smallValid 9413 64 := by unfold smallValid; decide +kernel

private theorem sp9477 : smallValid 9477 64 := by unfold smallValid; decide +kernel

private theorem sp9541 : smallValid 9541 64 := by unfold smallValid; decide +kernel

private theorem sp9605 : smallValid 9605 64 := by unfold smallValid; decide +kernel

private theorem sp9669 : smallValid 9669 64 := by unfold smallValid; decide +kernel

private theorem sp9733 : smallValid 9733 64 := by unfold smallValid; decide +kernel

private theorem sp9797 : smallValid 9797 64 := by unfold smallValid; decide +kernel

private theorem sp9861 : smallValid 9861 64 := by unfold smallValid; decide +kernel

private theorem sp9925 : smallValid 9925 64 := by unfold smallValid; decide +kernel

private theorem sp9989 : smallValid 9989 64 := by unfold smallValid; decide +kernel

private theorem sp10053 : smallValid 10053 64 := by unfold smallValid; decide +kernel

private theorem sp10117 : smallValid 10117 64 := by unfold smallValid; decide +kernel

private theorem sp10181 : smallValid 10181 32 := by unfold smallValid; decide +kernel

private theorem sp10213 : smallValid 10213 33 := by unfold smallValid; decide +kernel

private theorem sp10246 : smallValid 10246 64 := by unfold smallValid; decide +kernel

private theorem sp10310 : smallValid 10310 64 := by unfold smallValid; decide +kernel

private theorem sp10374 : smallValid 10374 64 := by unfold smallValid; decide +kernel

private theorem sp10438 : smallValid 10438 64 := by unfold smallValid; decide +kernel

private theorem sp10502 : smallValid 10502 64 := by unfold smallValid; decide +kernel

private theorem sp10566 : smallValid 10566 64 := by unfold smallValid; decide +kernel

private theorem sp10630 : smallValid 10630 64 := by unfold smallValid; decide +kernel

private theorem sp10694 : smallValid 10694 64 := by unfold smallValid; decide +kernel

private theorem sp10758 : smallValid 10758 64 := by unfold smallValid; decide +kernel

private theorem sp10822 : smallValid 10822 64 := by unfold smallValid; decide +kernel

private theorem sp10886 : smallValid 10886 64 := by unfold smallValid; decide +kernel

private theorem sp10950 : smallValid 10950 64 := by unfold smallValid; decide +kernel

private theorem sp11014 : smallValid 11014 64 := by unfold smallValid; decide +kernel

private theorem sp11078 : smallValid 11078 64 := by unfold smallValid; decide +kernel

private theorem sp11142 : smallValid 11142 64 := by unfold smallValid; decide +kernel

private theorem sp11206 : smallValid 11206 64 := by unfold smallValid; decide +kernel

private theorem sp11270 : smallValid 11270 64 := by unfold smallValid; decide +kernel

private theorem sp11334 : smallValid 11334 64 := by unfold smallValid; decide +kernel

private theorem sp11398 : smallValid 11398 64 := by unfold smallValid; decide +kernel

private theorem sp11462 : smallValid 11462 64 := by unfold smallValid; decide +kernel

private theorem sp11526 : smallValid 11526 64 := by unfold smallValid; decide +kernel

private theorem sp11590 : smallValid 11590 64 := by unfold smallValid; decide +kernel

private theorem sp11654 : smallValid 11654 64 := by unfold smallValid; decide +kernel

private theorem sp11718 : smallValid 11718 64 := by unfold smallValid; decide +kernel

private theorem sp11782 : smallValid 11782 64 := by unfold smallValid; decide +kernel

private theorem sp11846 : smallValid 11846 64 := by unfold smallValid; decide +kernel

private theorem sp11910 : smallValid 11910 64 := by unfold smallValid; decide +kernel

private theorem sp11974 : smallValid 11974 64 := by unfold smallValid; decide +kernel

private theorem sp12038 : smallValid 12038 64 := by unfold smallValid; decide +kernel

private theorem sp12102 : smallValid 12102 64 := by unfold smallValid; decide +kernel

private theorem sp12166 : smallValid 12166 64 := by unfold smallValid; decide +kernel

private theorem sp12230 : smallValid 12230 32 := by unfold smallValid; decide +kernel

private theorem sp12262 : smallValid 12262 33 := by unfold smallValid; decide +kernel

private theorem sp12295 : smallValid 12295 64 := by unfold smallValid; decide +kernel

private theorem sp12359 : smallValid 12359 64 := by unfold smallValid; decide +kernel

private theorem sp12423 : smallValid 12423 64 := by unfold smallValid; decide +kernel

private theorem sp12487 : smallValid 12487 64 := by unfold smallValid; decide +kernel

private theorem sp12551 : smallValid 12551 64 := by unfold smallValid; decide +kernel

private theorem sp12615 : smallValid 12615 64 := by unfold smallValid; decide +kernel

private theorem sp12679 : smallValid 12679 64 := by unfold smallValid; decide +kernel

private theorem sp12743 : smallValid 12743 64 := by unfold smallValid; decide +kernel

private theorem sp12807 : smallValid 12807 64 := by unfold smallValid; decide +kernel

private theorem sp12871 : smallValid 12871 64 := by unfold smallValid; decide +kernel

private theorem sp12935 : smallValid 12935 64 := by unfold smallValid; decide +kernel

private theorem sp12999 : smallValid 12999 64 := by unfold smallValid; decide +kernel

private theorem sp13063 : smallValid 13063 64 := by unfold smallValid; decide +kernel

private theorem sp13127 : smallValid 13127 64 := by unfold smallValid; decide +kernel

private theorem sp13191 : smallValid 13191 64 := by unfold smallValid; decide +kernel

private theorem sp13255 : smallValid 13255 64 := by unfold smallValid; decide +kernel

private theorem sp13319 : smallValid 13319 64 := by unfold smallValid; decide +kernel

private theorem sp13383 : smallValid 13383 64 := by unfold smallValid; decide +kernel

private theorem sp13447 : smallValid 13447 64 := by unfold smallValid; decide +kernel

private theorem sp13511 : smallValid 13511 64 := by unfold smallValid; decide +kernel

private theorem sp13575 : smallValid 13575 64 := by unfold smallValid; decide +kernel

private theorem sp13639 : smallValid 13639 64 := by unfold smallValid; decide +kernel

private theorem sp13703 : smallValid 13703 64 := by unfold smallValid; decide +kernel

private theorem sp13767 : smallValid 13767 64 := by unfold smallValid; decide +kernel

private theorem sp13831 : smallValid 13831 64 := by unfold smallValid; decide +kernel

private theorem sp13895 : smallValid 13895 64 := by unfold smallValid; decide +kernel

private theorem sp13959 : smallValid 13959 64 := by unfold smallValid; decide +kernel

private theorem sp14023 : smallValid 14023 64 := by unfold smallValid; decide +kernel

private theorem sp14087 : smallValid 14087 64 := by unfold smallValid; decide +kernel

private theorem sp14151 : smallValid 14151 64 := by unfold smallValid; decide +kernel

private theorem sp14215 : smallValid 14215 64 := by unfold smallValid; decide +kernel

private theorem sp14279 : smallValid 14279 32 := by unfold smallValid; decide +kernel

private theorem sp14311 : smallValid 14311 33 := by unfold smallValid; decide +kernel

private theorem sp14344 : smallValid 14344 64 := by unfold smallValid; decide +kernel

private theorem sp14408 : smallValid 14408 64 := by unfold smallValid; decide +kernel

private theorem sp14472 : smallValid 14472 64 := by unfold smallValid; decide +kernel

private theorem sp14536 : smallValid 14536 64 := by unfold smallValid; decide +kernel

private theorem sp14600 : smallValid 14600 64 := by unfold smallValid; decide +kernel

private theorem sp14664 : smallValid 14664 64 := by unfold smallValid; decide +kernel

private theorem sp14728 : smallValid 14728 64 := by unfold smallValid; decide +kernel

private theorem sp14792 : smallValid 14792 64 := by unfold smallValid; decide +kernel

private theorem sp14856 : smallValid 14856 64 := by unfold smallValid; decide +kernel

private theorem sp14920 : smallValid 14920 64 := by unfold smallValid; decide +kernel

private theorem sp14984 : smallValid 14984 64 := by unfold smallValid; decide +kernel

private theorem sp15048 : smallValid 15048 64 := by unfold smallValid; decide +kernel

private theorem sp15112 : smallValid 15112 64 := by unfold smallValid; decide +kernel

private theorem sp15176 : smallValid 15176 64 := by unfold smallValid; decide +kernel

private theorem sp15240 : smallValid 15240 64 := by unfold smallValid; decide +kernel

private theorem sp15304 : smallValid 15304 32 := by unfold smallValid; decide +kernel

private theorem sp15336 : smallValid 15336 33 := by unfold smallValid; decide +kernel

private theorem sp15369 : smallValid 15369 64 := by unfold smallValid; decide +kernel

private theorem sp15433 : smallValid 15433 64 := by unfold smallValid; decide +kernel

private theorem sp15497 : smallValid 15497 64 := by unfold smallValid; decide +kernel

private theorem sp15561 : smallValid 15561 64 := by unfold smallValid; decide +kernel

private theorem sp15625 : smallValid 15625 64 := by unfold smallValid; decide +kernel

private theorem sp15689 : smallValid 15689 64 := by unfold smallValid; decide +kernel

private theorem sp15753 : smallValid 15753 64 := by unfold smallValid; decide +kernel

private theorem sp15817 : smallValid 15817 64 := by unfold smallValid; decide +kernel

private theorem sp15881 : smallValid 15881 64 := by unfold smallValid; decide +kernel

private theorem sp15945 : smallValid 15945 64 := by unfold smallValid; decide +kernel

private theorem sp16009 : smallValid 16009 64 := by unfold smallValid; decide +kernel

private theorem sp16073 : smallValid 16073 64 := by unfold smallValid; decide +kernel

private theorem sp16137 : smallValid 16137 64 := by unfold smallValid; decide +kernel

private theorem sp16201 : smallValid 16201 64 := by unfold smallValid; decide +kernel

private theorem sp16265 : smallValid 16265 64 := by unfold smallValid; decide +kernel

private theorem sp16329 : smallValid 16329 32 := by unfold smallValid; decide +kernel

private theorem sp16361 : smallValid 16361 33 := by unfold smallValid; decide +kernel

private theorem sp16394 : smallValid 16394 64 := by unfold smallValid; decide +kernel

private theorem sp16458 : smallValid 16458 64 := by unfold smallValid; decide +kernel

private theorem sp16522 : smallValid 16522 64 := by unfold smallValid; decide +kernel

private theorem sp16586 : smallValid 16586 64 := by unfold smallValid; decide +kernel

private theorem sp16650 : smallValid 16650 64 := by unfold smallValid; decide +kernel

private theorem sp16714 : smallValid 16714 64 := by unfold smallValid; decide +kernel

private theorem sp16778 : smallValid 16778 64 := by unfold smallValid; decide +kernel

private theorem sp16842 : smallValid 16842 64 := by unfold smallValid; decide +kernel

private theorem sp16906 : smallValid 16906 64 := by unfold smallValid; decide +kernel

private theorem sp16970 : smallValid 16970 64 := by unfold smallValid; decide +kernel

private theorem sp17034 : smallValid 17034 64 := by unfold smallValid; decide +kernel

private theorem sp17098 : smallValid 17098 64 := by unfold smallValid; decide +kernel

private theorem sp17162 : smallValid 17162 64 := by unfold smallValid; decide +kernel

private theorem sp17226 : smallValid 17226 64 := by unfold smallValid; decide +kernel

private theorem sp17290 : smallValid 17290 64 := by unfold smallValid; decide +kernel

private theorem sp17354 : smallValid 17354 64 := by unfold smallValid; decide +kernel

private theorem sp17418 : smallValid 17418 64 := by unfold smallValid; decide +kernel

private theorem sp17482 : smallValid 17482 64 := by unfold smallValid; decide +kernel

private theorem sp17546 : smallValid 17546 64 := by unfold smallValid; decide +kernel

private theorem sp17610 : smallValid 17610 64 := by unfold smallValid; decide +kernel

private theorem sp17674 : smallValid 17674 64 := by unfold smallValid; decide +kernel

private theorem sp17738 : smallValid 17738 64 := by unfold smallValid; decide +kernel

private theorem sp17802 : smallValid 17802 64 := by unfold smallValid; decide +kernel

private theorem sp17866 : smallValid 17866 64 := by unfold smallValid; decide +kernel

private theorem sp17930 : smallValid 17930 64 := by unfold smallValid; decide +kernel

private theorem sp17994 : smallValid 17994 64 := by unfold smallValid; decide +kernel

private theorem sp18058 : smallValid 18058 64 := by unfold smallValid; decide +kernel

private theorem sp18122 : smallValid 18122 64 := by unfold smallValid; decide +kernel

private theorem sp18186 : smallValid 18186 64 := by unfold smallValid; decide +kernel

private theorem sp18250 : smallValid 18250 64 := by unfold smallValid; decide +kernel

private theorem sp18314 : smallValid 18314 64 := by unfold smallValid; decide +kernel

private theorem sp18378 : smallValid 18378 32 := by unfold smallValid; decide +kernel

private theorem sp18410 : smallValid 18410 33 := by unfold smallValid; decide +kernel

private theorem sp18443 : smallValid 18443 64 := by unfold smallValid; decide +kernel

private theorem sp18507 : smallValid 18507 64 := by unfold smallValid; decide +kernel

private theorem sp18571 : smallValid 18571 64 := by unfold smallValid; decide +kernel

private theorem sp18635 : smallValid 18635 64 := by unfold smallValid; decide +kernel

private theorem sp18699 : smallValid 18699 64 := by unfold smallValid; decide +kernel

private theorem sp18763 : smallValid 18763 64 := by unfold smallValid; decide +kernel

private theorem sp18827 : smallValid 18827 64 := by unfold smallValid; decide +kernel

private theorem sp18891 : smallValid 18891 64 := by unfold smallValid; decide +kernel

private theorem sp18955 : smallValid 18955 64 := by unfold smallValid; decide +kernel

private theorem sp19019 : smallValid 19019 64 := by unfold smallValid; decide +kernel

private theorem sp19083 : smallValid 19083 64 := by unfold smallValid; decide +kernel

private theorem sp19147 : smallValid 19147 64 := by unfold smallValid; decide +kernel

private theorem sp19211 : smallValid 19211 64 := by unfold smallValid; decide +kernel

private theorem sp19275 : smallValid 19275 64 := by unfold smallValid; decide +kernel

private theorem sp19339 : smallValid 19339 64 := by unfold smallValid; decide +kernel

private theorem sp19403 : smallValid 19403 64 := by unfold smallValid; decide +kernel

private theorem sp19467 : smallValid 19467 64 := by unfold smallValid; decide +kernel

private theorem sp19531 : smallValid 19531 64 := by unfold smallValid; decide +kernel

private theorem sp19595 : smallValid 19595 64 := by unfold smallValid; decide +kernel

private theorem sp19659 : smallValid 19659 64 := by unfold smallValid; decide +kernel

private theorem sp19723 : smallValid 19723 64 := by unfold smallValid; decide +kernel

private theorem sp19787 : smallValid 19787 64 := by unfold smallValid; decide +kernel

private theorem sp19851 : smallValid 19851 64 := by unfold smallValid; decide +kernel

private theorem sp19915 : smallValid 19915 64 := by unfold smallValid; decide +kernel

private theorem sp19979 : smallValid 19979 64 := by unfold smallValid; decide +kernel

private theorem sp20043 : smallValid 20043 64 := by unfold smallValid; decide +kernel

private theorem sp20107 : smallValid 20107 64 := by unfold smallValid; decide +kernel

private theorem sp20171 : smallValid 20171 64 := by unfold smallValid; decide +kernel

private theorem sp20235 : smallValid 20235 64 := by unfold smallValid; decide +kernel

private theorem sp20299 : smallValid 20299 64 := by unfold smallValid; decide +kernel

private theorem sp20363 : smallValid 20363 64 := by unfold smallValid; decide +kernel

private theorem sp20427 : smallValid 20427 32 := by unfold smallValid; decide +kernel

private theorem sp20459 : smallValid 20459 33 := by unfold smallValid; decide +kernel

private theorem sp20492 : smallValid 20492 64 := by unfold smallValid; decide +kernel

private theorem sp20556 : smallValid 20556 64 := by unfold smallValid; decide +kernel

private theorem sp20620 : smallValid 20620 64 := by unfold smallValid; decide +kernel

private theorem sp20684 : smallValid 20684 64 := by unfold smallValid; decide +kernel

private theorem sp20748 : smallValid 20748 64 := by unfold smallValid; decide +kernel

private theorem sp20812 : smallValid 20812 64 := by unfold smallValid; decide +kernel

private theorem sp20876 : smallValid 20876 64 := by unfold smallValid; decide +kernel

private theorem sp20940 : smallValid 20940 64 := by unfold smallValid; decide +kernel

private theorem sp21004 : smallValid 21004 64 := by unfold smallValid; decide +kernel

private theorem sp21068 : smallValid 21068 64 := by unfold smallValid; decide +kernel

private theorem sp21132 : smallValid 21132 64 := by unfold smallValid; decide +kernel

private theorem sp21196 : smallValid 21196 64 := by unfold smallValid; decide +kernel

private theorem sp21260 : smallValid 21260 64 := by unfold smallValid; decide +kernel

private theorem sp21324 : smallValid 21324 64 := by unfold smallValid; decide +kernel

private theorem sp21388 : smallValid 21388 64 := by unfold smallValid; decide +kernel

private theorem sp21452 : smallValid 21452 64 := by unfold smallValid; decide +kernel

private theorem sp21516 : smallValid 21516 64 := by unfold smallValid; decide +kernel

private theorem sp21580 : smallValid 21580 64 := by unfold smallValid; decide +kernel

private theorem sp21644 : smallValid 21644 64 := by unfold smallValid; decide +kernel

private theorem sp21708 : smallValid 21708 64 := by unfold smallValid; decide +kernel

private theorem sp21772 : smallValid 21772 64 := by unfold smallValid; decide +kernel

private theorem sp21836 : smallValid 21836 64 := by unfold smallValid; decide +kernel

private theorem sp21900 : smallValid 21900 64 := by unfold smallValid; decide +kernel

private theorem sp21964 : smallValid 21964 64 := by unfold smallValid; decide +kernel

private theorem sp22028 : smallValid 22028 64 := by unfold smallValid; decide +kernel

private theorem sp22092 : smallValid 22092 64 := by unfold smallValid; decide +kernel

private theorem sp22156 : smallValid 22156 64 := by unfold smallValid; decide +kernel

private theorem sp22220 : smallValid 22220 64 := by unfold smallValid; decide +kernel

private theorem sp22284 : smallValid 22284 64 := by unfold smallValid; decide +kernel

private theorem sp22348 : smallValid 22348 64 := by unfold smallValid; decide +kernel

private theorem sp22412 : smallValid 22412 64 := by unfold smallValid; decide +kernel

private theorem sp22476 : smallValid 22476 32 := by unfold smallValid; decide +kernel

private theorem sp22508 : smallValid 22508 33 := by unfold smallValid; decide +kernel

private theorem sp22541 : smallValid 22541 64 := by unfold smallValid; decide +kernel

private theorem sp22605 : smallValid 22605 64 := by unfold smallValid; decide +kernel

private theorem sp22669 : smallValid 22669 64 := by unfold smallValid; decide +kernel

private theorem sp22733 : smallValid 22733 64 := by unfold smallValid; decide +kernel

private theorem sp22797 : smallValid 22797 64 := by unfold smallValid; decide +kernel

private theorem sp22861 : smallValid 22861 64 := by unfold smallValid; decide +kernel

private theorem sp22925 : smallValid 22925 64 := by unfold smallValid; decide +kernel

private theorem sp22989 : smallValid 22989 64 := by unfold smallValid; decide +kernel

private theorem sp23053 : smallValid 23053 64 := by unfold smallValid; decide +kernel

private theorem sp23117 : smallValid 23117 64 := by unfold smallValid; decide +kernel

private theorem sp23181 : smallValid 23181 64 := by unfold smallValid; decide +kernel

private theorem sp23245 : smallValid 23245 64 := by unfold smallValid; decide +kernel

private theorem sp23309 : smallValid 23309 64 := by unfold smallValid; decide +kernel

private theorem sp23373 : smallValid 23373 64 := by unfold smallValid; decide +kernel

private theorem sp23437 : smallValid 23437 64 := by unfold smallValid; decide +kernel

private theorem sp23501 : smallValid 23501 32 := by unfold smallValid; decide +kernel

private theorem sp23533 : smallValid 23533 33 := by unfold smallValid; decide +kernel

private theorem sp23566 : smallValid 23566 64 := by unfold smallValid; decide +kernel

private theorem sp23630 : smallValid 23630 64 := by unfold smallValid; decide +kernel

private theorem sp23694 : smallValid 23694 64 := by unfold smallValid; decide +kernel

private theorem sp23758 : smallValid 23758 64 := by unfold smallValid; decide +kernel

private theorem sp23822 : smallValid 23822 64 := by unfold smallValid; decide +kernel

private theorem sp23886 : smallValid 23886 64 := by unfold smallValid; decide +kernel

private theorem sp23950 : smallValid 23950 64 := by unfold smallValid; decide +kernel

private theorem sp24014 : smallValid 24014 64 := by unfold smallValid; decide +kernel

private theorem sp24078 : smallValid 24078 64 := by unfold smallValid; decide +kernel

private theorem sp24142 : smallValid 24142 64 := by unfold smallValid; decide +kernel

private theorem sp24206 : smallValid 24206 64 := by unfold smallValid; decide +kernel

private theorem sp24270 : smallValid 24270 64 := by unfold smallValid; decide +kernel

private theorem sp24334 : smallValid 24334 64 := by unfold smallValid; decide +kernel

private theorem sp24398 : smallValid 24398 64 := by unfold smallValid; decide +kernel

private theorem sp24462 : smallValid 24462 64 := by unfold smallValid; decide +kernel

private theorem sp24526 : smallValid 24526 32 := by unfold smallValid; decide +kernel

private theorem sp24558 : smallValid 24558 33 := by unfold smallValid; decide +kernel

private theorem sp24591 : smallValid 24591 64 := by unfold smallValid; decide +kernel

private theorem sp24655 : smallValid 24655 64 := by unfold smallValid; decide +kernel

private theorem sp24719 : smallValid 24719 64 := by unfold smallValid; decide +kernel

private theorem sp24783 : smallValid 24783 64 := by unfold smallValid; decide +kernel

private theorem sp24847 : smallValid 24847 64 := by unfold smallValid; decide +kernel

private theorem sp24911 : smallValid 24911 64 := by unfold smallValid; decide +kernel

private theorem sp24975 : smallValid 24975 64 := by unfold smallValid; decide +kernel

private theorem sp25039 : smallValid 25039 64 := by unfold smallValid; decide +kernel

private theorem sp25103 : smallValid 25103 64 := by unfold smallValid; decide +kernel

private theorem sp25167 : smallValid 25167 64 := by unfold smallValid; decide +kernel

private theorem sp25231 : smallValid 25231 64 := by unfold smallValid; decide +kernel

private theorem sp25295 : smallValid 25295 64 := by unfold smallValid; decide +kernel

private theorem sp25359 : smallValid 25359 64 := by unfold smallValid; decide +kernel

private theorem sp25423 : smallValid 25423 64 := by unfold smallValid; decide +kernel

private theorem sp25487 : smallValid 25487 64 := by unfold smallValid; decide +kernel

private theorem sp25551 : smallValid 25551 64 := by unfold smallValid; decide +kernel

private theorem sp25615 : smallValid 25615 64 := by unfold smallValid; decide +kernel

private theorem sp25679 : smallValid 25679 64 := by unfold smallValid; decide +kernel

private theorem sp25743 : smallValid 25743 64 := by unfold smallValid; decide +kernel

private theorem sp25807 : smallValid 25807 64 := by unfold smallValid; decide +kernel

private theorem sp25871 : smallValid 25871 64 := by unfold smallValid; decide +kernel

private theorem sp25935 : smallValid 25935 64 := by unfold smallValid; decide +kernel

private theorem sp25999 : smallValid 25999 64 := by unfold smallValid; decide +kernel

private theorem sp26063 : smallValid 26063 64 := by unfold smallValid; decide +kernel

private theorem sp26127 : smallValid 26127 64 := by unfold smallValid; decide +kernel

private theorem sp26191 : smallValid 26191 64 := by unfold smallValid; decide +kernel

private theorem sp26255 : smallValid 26255 64 := by unfold smallValid; decide +kernel

private theorem sp26319 : smallValid 26319 64 := by unfold smallValid; decide +kernel

private theorem sp26383 : smallValid 26383 64 := by unfold smallValid; decide +kernel

private theorem sp26447 : smallValid 26447 64 := by unfold smallValid; decide +kernel

private theorem sp26511 : smallValid 26511 64 := by unfold smallValid; decide +kernel

private theorem sp26575 : smallValid 26575 32 := by unfold smallValid; decide +kernel

private theorem sp26607 : smallValid 26607 33 := by unfold smallValid; decide +kernel

private theorem sp26640 : smallValid 26640 64 := by unfold smallValid; decide +kernel

private theorem sp26704 : smallValid 26704 64 := by unfold smallValid; decide +kernel

private theorem sp26768 : smallValid 26768 64 := by unfold smallValid; decide +kernel

private theorem sp26832 : smallValid 26832 64 := by unfold smallValid; decide +kernel

private theorem sp26896 : smallValid 26896 64 := by unfold smallValid; decide +kernel

private theorem sp26960 : smallValid 26960 64 := by unfold smallValid; decide +kernel

private theorem sp27024 : smallValid 27024 64 := by unfold smallValid; decide +kernel

private theorem sp27088 : smallValid 27088 64 := by unfold smallValid; decide +kernel

private theorem sp27152 : smallValid 27152 64 := by unfold smallValid; decide +kernel

private theorem sp27216 : smallValid 27216 64 := by unfold smallValid; decide +kernel

private theorem sp27280 : smallValid 27280 64 := by unfold smallValid; decide +kernel

private theorem sp27344 : smallValid 27344 64 := by unfold smallValid; decide +kernel

private theorem sp27408 : smallValid 27408 64 := by unfold smallValid; decide +kernel

private theorem sp27472 : smallValid 27472 64 := by unfold smallValid; decide +kernel

private theorem sp27536 : smallValid 27536 64 := by unfold smallValid; decide +kernel

private theorem sp27600 : smallValid 27600 64 := by unfold smallValid; decide +kernel

private theorem sp27664 : smallValid 27664 64 := by unfold smallValid; decide +kernel

private theorem sp27728 : smallValid 27728 64 := by unfold smallValid; decide +kernel

private theorem sp27792 : smallValid 27792 64 := by unfold smallValid; decide +kernel

private theorem sp27856 : smallValid 27856 64 := by unfold smallValid; decide +kernel

private theorem sp27920 : smallValid 27920 64 := by unfold smallValid; decide +kernel

private theorem sp27984 : smallValid 27984 64 := by unfold smallValid; decide +kernel

private theorem sp28048 : smallValid 28048 64 := by unfold smallValid; decide +kernel

private theorem sp28112 : smallValid 28112 64 := by unfold smallValid; decide +kernel

private theorem sp28176 : smallValid 28176 64 := by unfold smallValid; decide +kernel

private theorem sp28240 : smallValid 28240 64 := by unfold smallValid; decide +kernel

private theorem sp28304 : smallValid 28304 64 := by unfold smallValid; decide +kernel

private theorem sp28368 : smallValid 28368 64 := by unfold smallValid; decide +kernel

private theorem sp28432 : smallValid 28432 64 := by unfold smallValid; decide +kernel

private theorem sp28496 : smallValid 28496 64 := by unfold smallValid; decide +kernel

private theorem sp28560 : smallValid 28560 64 := by unfold smallValid; decide +kernel

private theorem sp28624 : smallValid 28624 32 := by unfold smallValid; decide +kernel

private theorem sp28656 : smallValid 28656 33 := by unfold smallValid; decide +kernel

private theorem sp28689 : smallValid 28689 64 := by unfold smallValid; decide +kernel

private theorem sp28753 : smallValid 28753 64 := by unfold smallValid; decide +kernel

private theorem sp28817 : smallValid 28817 64 := by unfold smallValid; decide +kernel

private theorem sp28881 : smallValid 28881 64 := by unfold smallValid; decide +kernel

private theorem sp28945 : smallValid 28945 64 := by unfold smallValid; decide +kernel

private theorem sp29009 : smallValid 29009 64 := by unfold smallValid; decide +kernel

private theorem sp29073 : smallValid 29073 64 := by unfold smallValid; decide +kernel

private theorem sp29137 : smallValid 29137 64 := by unfold smallValid; decide +kernel

private theorem sp29201 : smallValid 29201 64 := by unfold smallValid; decide +kernel

private theorem sp29265 : smallValid 29265 64 := by unfold smallValid; decide +kernel

private theorem sp29329 : smallValid 29329 64 := by unfold smallValid; decide +kernel

private theorem sp29393 : smallValid 29393 64 := by unfold smallValid; decide +kernel

private theorem sp29457 : smallValid 29457 64 := by unfold smallValid; decide +kernel

private theorem sp29521 : smallValid 29521 64 := by unfold smallValid; decide +kernel

private theorem sp29585 : smallValid 29585 64 := by unfold smallValid; decide +kernel

private theorem sp29649 : smallValid 29649 64 := by unfold smallValid; decide +kernel

private theorem sp29713 : smallValid 29713 64 := by unfold smallValid; decide +kernel

private theorem sp29777 : smallValid 29777 64 := by unfold smallValid; decide +kernel

private theorem sp29841 : smallValid 29841 64 := by unfold smallValid; decide +kernel

private theorem sp29905 : smallValid 29905 64 := by unfold smallValid; decide +kernel

private theorem sp29969 : smallValid 29969 64 := by unfold smallValid; decide +kernel

private theorem sp30033 : smallValid 30033 64 := by unfold smallValid; decide +kernel

private theorem sp30097 : smallValid 30097 64 := by unfold smallValid; decide +kernel

private theorem sp30161 : smallValid 30161 64 := by unfold smallValid; decide +kernel

private theorem sp30225 : smallValid 30225 64 := by unfold smallValid; decide +kernel

private theorem sp30289 : smallValid 30289 64 := by unfold smallValid; decide +kernel

private theorem sp30353 : smallValid 30353 64 := by unfold smallValid; decide +kernel

private theorem sp30417 : smallValid 30417 64 := by unfold smallValid; decide +kernel

private theorem sp30481 : smallValid 30481 64 := by unfold smallValid; decide +kernel

private theorem sp30545 : smallValid 30545 64 := by unfold smallValid; decide +kernel

private theorem sp30609 : smallValid 30609 64 := by unfold smallValid; decide +kernel

private theorem sp30673 : smallValid 30673 32 := by unfold smallValid; decide +kernel

private theorem sp30705 : smallValid 30705 33 := by unfold smallValid; decide +kernel

private theorem sp30738 : smallValid 30738 64 := by unfold smallValid; decide +kernel

private theorem sp30802 : smallValid 30802 64 := by unfold smallValid; decide +kernel

private theorem sp30866 : smallValid 30866 64 := by unfold smallValid; decide +kernel

private theorem sp30930 : smallValid 30930 64 := by unfold smallValid; decide +kernel

private theorem sp30994 : smallValid 30994 64 := by unfold smallValid; decide +kernel

private theorem sp31058 : smallValid 31058 64 := by unfold smallValid; decide +kernel

private theorem sp31122 : smallValid 31122 64 := by unfold smallValid; decide +kernel

private theorem sp31186 : smallValid 31186 64 := by unfold smallValid; decide +kernel

private theorem sp31250 : smallValid 31250 64 := by unfold smallValid; decide +kernel

private theorem sp31314 : smallValid 31314 64 := by unfold smallValid; decide +kernel

private theorem sp31378 : smallValid 31378 64 := by unfold smallValid; decide +kernel

private theorem sp31442 : smallValid 31442 64 := by unfold smallValid; decide +kernel

private theorem sp31506 : smallValid 31506 64 := by unfold smallValid; decide +kernel

private theorem sp31570 : smallValid 31570 64 := by unfold smallValid; decide +kernel

private theorem sp31634 : smallValid 31634 64 := by unfold smallValid; decide +kernel

private theorem sp31698 : smallValid 31698 32 := by unfold smallValid; decide +kernel

private theorem sp31730 : smallValid 31730 33 := by unfold smallValid; decide +kernel

private theorem sp31763 : smallValid 31763 64 := by unfold smallValid; decide +kernel

private theorem sp31827 : smallValid 31827 64 := by unfold smallValid; decide +kernel

private theorem sp31891 : smallValid 31891 64 := by unfold smallValid; decide +kernel

private theorem sp31955 : smallValid 31955 64 := by unfold smallValid; decide +kernel

private theorem sp32019 : smallValid 32019 64 := by unfold smallValid; decide +kernel

private theorem sp32083 : smallValid 32083 64 := by unfold smallValid; decide +kernel

private theorem sp32147 : smallValid 32147 64 := by unfold smallValid; decide +kernel

private theorem sp32211 : smallValid 32211 64 := by unfold smallValid; decide +kernel

private theorem sp32275 : smallValid 32275 64 := by unfold smallValid; decide +kernel

private theorem sp32339 : smallValid 32339 64 := by unfold smallValid; decide +kernel

private theorem sp32403 : smallValid 32403 64 := by unfold smallValid; decide +kernel

private theorem sp32467 : smallValid 32467 64 := by unfold smallValid; decide +kernel

private theorem sp32531 : smallValid 32531 64 := by unfold smallValid; decide +kernel

private theorem sp32595 : smallValid 32595 64 := by unfold smallValid; decide +kernel

private theorem sp32659 : smallValid 32659 64 := by unfold smallValid; decide +kernel

private theorem sp32723 : smallValid 32723 32 := by unfold smallValid; decide +kernel

private theorem sp32755 : smallValid 32755 33 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤32787) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 32788 := (joinSmall (lo:=0) (a:=16394) (b:=16394) (joinSmall (lo:=0) (a:=8197) (b:=8197) (joinSmall (lo:=0) (a:=4098) (b:=4099) (joinSmall (lo:=0) (a:=2049) (b:=2049) (joinSmall (lo:=0) (a:=1024) (b:=1025) (joinSmall (lo:=0) (a:=512) (b:=512) (joinSmall (lo:=0) (a:=256) (b:=256) (joinSmall (lo:=0) (a:=128) (b:=128) (joinSmall (lo:=0) (a:=64) (b:=64) sp0 sp64) (joinSmall (lo:=128) (a:=64) (b:=64) sp128 sp192)) (joinSmall (lo:=256) (a:=128) (b:=128) (joinSmall (lo:=256) (a:=64) (b:=64) sp256 sp320) (joinSmall (lo:=384) (a:=64) (b:=64) sp384 sp448))) (joinSmall (lo:=512) (a:=256) (b:=256) (joinSmall (lo:=512) (a:=128) (b:=128) (joinSmall (lo:=512) (a:=64) (b:=64) sp512 sp576) (joinSmall (lo:=640) (a:=64) (b:=64) sp640 sp704)) (joinSmall (lo:=768) (a:=128) (b:=128) (joinSmall (lo:=768) (a:=64) (b:=64) sp768 sp832) (joinSmall (lo:=896) (a:=64) (b:=64) sp896 sp960)))) (joinSmall (lo:=1024) (a:=512) (b:=513) (joinSmall (lo:=1024) (a:=256) (b:=256) (joinSmall (lo:=1024) (a:=128) (b:=128) (joinSmall (lo:=1024) (a:=64) (b:=64) sp1024 sp1088) (joinSmall (lo:=1152) (a:=64) (b:=64) sp1152 sp1216)) (joinSmall (lo:=1280) (a:=128) (b:=128) (joinSmall (lo:=1280) (a:=64) (b:=64) sp1280 sp1344) (joinSmall (lo:=1408) (a:=64) (b:=64) sp1408 sp1472))) (joinSmall (lo:=1536) (a:=256) (b:=257) (joinSmall (lo:=1536) (a:=128) (b:=128) (joinSmall (lo:=1536) (a:=64) (b:=64) sp1536 sp1600) (joinSmall (lo:=1664) (a:=64) (b:=64) sp1664 sp1728)) (joinSmall (lo:=1792) (a:=128) (b:=129) (joinSmall (lo:=1792) (a:=64) (b:=64) sp1792 sp1856) (joinSmall (lo:=1920) (a:=64) (b:=65) sp1920 (joinSmall (lo:=1984) (a:=32) (b:=33) sp1984 sp2016)))))) (joinSmall (lo:=2049) (a:=1024) (b:=1025) (joinSmall (lo:=2049) (a:=512) (b:=512) (joinSmall (lo:=2049) (a:=256) (b:=256) (joinSmall (lo:=2049) (a:=128) (b:=128) (joinSmall (lo:=2049) (a:=64) (b:=64) sp2049 sp2113) (joinSmall (lo:=2177) (a:=64) (b:=64) sp2177 sp2241)) (joinSmall (lo:=2305) (a:=128) (b:=128) (joinSmall (lo:=2305) (a:=64) (b:=64) sp2305 sp2369) (joinSmall (lo:=2433) (a:=64) (b:=64) sp2433 sp2497))) (joinSmall (lo:=2561) (a:=256) (b:=256) (joinSmall (lo:=2561) (a:=128) (b:=128) (joinSmall (lo:=2561) (a:=64) (b:=64) sp2561 sp2625) (joinSmall (lo:=2689) (a:=64) (b:=64) sp2689 sp2753)) (joinSmall (lo:=2817) (a:=128) (b:=128) (joinSmall (lo:=2817) (a:=64) (b:=64) sp2817 sp2881) (joinSmall (lo:=2945) (a:=64) (b:=64) sp2945 sp3009)))) (joinSmall (lo:=3073) (a:=512) (b:=513) (joinSmall (lo:=3073) (a:=256) (b:=256) (joinSmall (lo:=3073) (a:=128) (b:=128) (joinSmall (lo:=3073) (a:=64) (b:=64) sp3073 sp3137) (joinSmall (lo:=3201) (a:=64) (b:=64) sp3201 sp3265)) (joinSmall (lo:=3329) (a:=128) (b:=128) (joinSmall (lo:=3329) (a:=64) (b:=64) sp3329 sp3393) (joinSmall (lo:=3457) (a:=64) (b:=64) sp3457 sp3521))) (joinSmall (lo:=3585) (a:=256) (b:=257) (joinSmall (lo:=3585) (a:=128) (b:=128) (joinSmall (lo:=3585) (a:=64) (b:=64) sp3585 sp3649) (joinSmall (lo:=3713) (a:=64) (b:=64) sp3713 sp3777)) (joinSmall (lo:=3841) (a:=128) (b:=129) (joinSmall (lo:=3841) (a:=64) (b:=64) sp3841 sp3905) (joinSmall (lo:=3969) (a:=64) (b:=65) sp3969 (joinSmall (lo:=4033) (a:=32) (b:=33) sp4033 sp4065))))))) (joinSmall (lo:=4098) (a:=2049) (b:=2050) (joinSmall (lo:=4098) (a:=1024) (b:=1025) (joinSmall (lo:=4098) (a:=512) (b:=512) (joinSmall (lo:=4098) (a:=256) (b:=256) (joinSmall (lo:=4098) (a:=128) (b:=128) (joinSmall (lo:=4098) (a:=64) (b:=64) sp4098 sp4162) (joinSmall (lo:=4226) (a:=64) (b:=64) sp4226 sp4290)) (joinSmall (lo:=4354) (a:=128) (b:=128) (joinSmall (lo:=4354) (a:=64) (b:=64) sp4354 sp4418) (joinSmall (lo:=4482) (a:=64) (b:=64) sp4482 sp4546))) (joinSmall (lo:=4610) (a:=256) (b:=256) (joinSmall (lo:=4610) (a:=128) (b:=128) (joinSmall (lo:=4610) (a:=64) (b:=64) sp4610 sp4674) (joinSmall (lo:=4738) (a:=64) (b:=64) sp4738 sp4802)) (joinSmall (lo:=4866) (a:=128) (b:=128) (joinSmall (lo:=4866) (a:=64) (b:=64) sp4866 sp4930) (joinSmall (lo:=4994) (a:=64) (b:=64) sp4994 sp5058)))) (joinSmall (lo:=5122) (a:=512) (b:=513) (joinSmall (lo:=5122) (a:=256) (b:=256) (joinSmall (lo:=5122) (a:=128) (b:=128) (joinSmall (lo:=5122) (a:=64) (b:=64) sp5122 sp5186) (joinSmall (lo:=5250) (a:=64) (b:=64) sp5250 sp5314)) (joinSmall (lo:=5378) (a:=128) (b:=128) (joinSmall (lo:=5378) (a:=64) (b:=64) sp5378 sp5442) (joinSmall (lo:=5506) (a:=64) (b:=64) sp5506 sp5570))) (joinSmall (lo:=5634) (a:=256) (b:=257) (joinSmall (lo:=5634) (a:=128) (b:=128) (joinSmall (lo:=5634) (a:=64) (b:=64) sp5634 sp5698) (joinSmall (lo:=5762) (a:=64) (b:=64) sp5762 sp5826)) (joinSmall (lo:=5890) (a:=128) (b:=129) (joinSmall (lo:=5890) (a:=64) (b:=64) sp5890 sp5954) (joinSmall (lo:=6018) (a:=64) (b:=65) sp6018 (joinSmall (lo:=6082) (a:=32) (b:=33) sp6082 sp6114)))))) (joinSmall (lo:=6147) (a:=1025) (b:=1025) (joinSmall (lo:=6147) (a:=512) (b:=513) (joinSmall (lo:=6147) (a:=256) (b:=256) (joinSmall (lo:=6147) (a:=128) (b:=128) (joinSmall (lo:=6147) (a:=64) (b:=64) sp6147 sp6211) (joinSmall (lo:=6275) (a:=64) (b:=64) sp6275 sp6339)) (joinSmall (lo:=6403) (a:=128) (b:=128) (joinSmall (lo:=6403) (a:=64) (b:=64) sp6403 sp6467) (joinSmall (lo:=6531) (a:=64) (b:=64) sp6531 sp6595))) (joinSmall (lo:=6659) (a:=256) (b:=257) (joinSmall (lo:=6659) (a:=128) (b:=128) (joinSmall (lo:=6659) (a:=64) (b:=64) sp6659 sp6723) (joinSmall (lo:=6787) (a:=64) (b:=64) sp6787 sp6851)) (joinSmall (lo:=6915) (a:=128) (b:=129) (joinSmall (lo:=6915) (a:=64) (b:=64) sp6915 sp6979) (joinSmall (lo:=7043) (a:=64) (b:=65) sp7043 (joinSmall (lo:=7107) (a:=32) (b:=33) sp7107 sp7139))))) (joinSmall (lo:=7172) (a:=512) (b:=513) (joinSmall (lo:=7172) (a:=256) (b:=256) (joinSmall (lo:=7172) (a:=128) (b:=128) (joinSmall (lo:=7172) (a:=64) (b:=64) sp7172 sp7236) (joinSmall (lo:=7300) (a:=64) (b:=64) sp7300 sp7364)) (joinSmall (lo:=7428) (a:=128) (b:=128) (joinSmall (lo:=7428) (a:=64) (b:=64) sp7428 sp7492) (joinSmall (lo:=7556) (a:=64) (b:=64) sp7556 sp7620))) (joinSmall (lo:=7684) (a:=256) (b:=257) (joinSmall (lo:=7684) (a:=128) (b:=128) (joinSmall (lo:=7684) (a:=64) (b:=64) sp7684 sp7748) (joinSmall (lo:=7812) (a:=64) (b:=64) sp7812 sp7876)) (joinSmall (lo:=7940) (a:=128) (b:=129) (joinSmall (lo:=7940) (a:=64) (b:=64) sp7940 sp8004) (joinSmall (lo:=8068) (a:=64) (b:=65) sp8068 (joinSmall (lo:=8132) (a:=32) (b:=33) sp8132 sp8164)))))))) (joinSmall (lo:=8197) (a:=4098) (b:=4099) (joinSmall (lo:=8197) (a:=2049) (b:=2049) (joinSmall (lo:=8197) (a:=1024) (b:=1025) (joinSmall (lo:=8197) (a:=512) (b:=512) (joinSmall (lo:=8197) (a:=256) (b:=256) (joinSmall (lo:=8197) (a:=128) (b:=128) (joinSmall (lo:=8197) (a:=64) (b:=64) sp8197 sp8261) (joinSmall (lo:=8325) (a:=64) (b:=64) sp8325 sp8389)) (joinSmall (lo:=8453) (a:=128) (b:=128) (joinSmall (lo:=8453) (a:=64) (b:=64) sp8453 sp8517) (joinSmall (lo:=8581) (a:=64) (b:=64) sp8581 sp8645))) (joinSmall (lo:=8709) (a:=256) (b:=256) (joinSmall (lo:=8709) (a:=128) (b:=128) (joinSmall (lo:=8709) (a:=64) (b:=64) sp8709 sp8773) (joinSmall (lo:=8837) (a:=64) (b:=64) sp8837 sp8901)) (joinSmall (lo:=8965) (a:=128) (b:=128) (joinSmall (lo:=8965) (a:=64) (b:=64) sp8965 sp9029) (joinSmall (lo:=9093) (a:=64) (b:=64) sp9093 sp9157)))) (joinSmall (lo:=9221) (a:=512) (b:=513) (joinSmall (lo:=9221) (a:=256) (b:=256) (joinSmall (lo:=9221) (a:=128) (b:=128) (joinSmall (lo:=9221) (a:=64) (b:=64) sp9221 sp9285) (joinSmall (lo:=9349) (a:=64) (b:=64) sp9349 sp9413)) (joinSmall (lo:=9477) (a:=128) (b:=128) (joinSmall (lo:=9477) (a:=64) (b:=64) sp9477 sp9541) (joinSmall (lo:=9605) (a:=64) (b:=64) sp9605 sp9669))) (joinSmall (lo:=9733) (a:=256) (b:=257) (joinSmall (lo:=9733) (a:=128) (b:=128) (joinSmall (lo:=9733) (a:=64) (b:=64) sp9733 sp9797) (joinSmall (lo:=9861) (a:=64) (b:=64) sp9861 sp9925)) (joinSmall (lo:=9989) (a:=128) (b:=129) (joinSmall (lo:=9989) (a:=64) (b:=64) sp9989 sp10053) (joinSmall (lo:=10117) (a:=64) (b:=65) sp10117 (joinSmall (lo:=10181) (a:=32) (b:=33) sp10181 sp10213)))))) (joinSmall (lo:=10246) (a:=1024) (b:=1025) (joinSmall (lo:=10246) (a:=512) (b:=512) (joinSmall (lo:=10246) (a:=256) (b:=256) (joinSmall (lo:=10246) (a:=128) (b:=128) (joinSmall (lo:=10246) (a:=64) (b:=64) sp10246 sp10310) (joinSmall (lo:=10374) (a:=64) (b:=64) sp10374 sp10438)) (joinSmall (lo:=10502) (a:=128) (b:=128) (joinSmall (lo:=10502) (a:=64) (b:=64) sp10502 sp10566) (joinSmall (lo:=10630) (a:=64) (b:=64) sp10630 sp10694))) (joinSmall (lo:=10758) (a:=256) (b:=256) (joinSmall (lo:=10758) (a:=128) (b:=128) (joinSmall (lo:=10758) (a:=64) (b:=64) sp10758 sp10822) (joinSmall (lo:=10886) (a:=64) (b:=64) sp10886 sp10950)) (joinSmall (lo:=11014) (a:=128) (b:=128) (joinSmall (lo:=11014) (a:=64) (b:=64) sp11014 sp11078) (joinSmall (lo:=11142) (a:=64) (b:=64) sp11142 sp11206)))) (joinSmall (lo:=11270) (a:=512) (b:=513) (joinSmall (lo:=11270) (a:=256) (b:=256) (joinSmall (lo:=11270) (a:=128) (b:=128) (joinSmall (lo:=11270) (a:=64) (b:=64) sp11270 sp11334) (joinSmall (lo:=11398) (a:=64) (b:=64) sp11398 sp11462)) (joinSmall (lo:=11526) (a:=128) (b:=128) (joinSmall (lo:=11526) (a:=64) (b:=64) sp11526 sp11590) (joinSmall (lo:=11654) (a:=64) (b:=64) sp11654 sp11718))) (joinSmall (lo:=11782) (a:=256) (b:=257) (joinSmall (lo:=11782) (a:=128) (b:=128) (joinSmall (lo:=11782) (a:=64) (b:=64) sp11782 sp11846) (joinSmall (lo:=11910) (a:=64) (b:=64) sp11910 sp11974)) (joinSmall (lo:=12038) (a:=128) (b:=129) (joinSmall (lo:=12038) (a:=64) (b:=64) sp12038 sp12102) (joinSmall (lo:=12166) (a:=64) (b:=65) sp12166 (joinSmall (lo:=12230) (a:=32) (b:=33) sp12230 sp12262))))))) (joinSmall (lo:=12295) (a:=2049) (b:=2050) (joinSmall (lo:=12295) (a:=1024) (b:=1025) (joinSmall (lo:=12295) (a:=512) (b:=512) (joinSmall (lo:=12295) (a:=256) (b:=256) (joinSmall (lo:=12295) (a:=128) (b:=128) (joinSmall (lo:=12295) (a:=64) (b:=64) sp12295 sp12359) (joinSmall (lo:=12423) (a:=64) (b:=64) sp12423 sp12487)) (joinSmall (lo:=12551) (a:=128) (b:=128) (joinSmall (lo:=12551) (a:=64) (b:=64) sp12551 sp12615) (joinSmall (lo:=12679) (a:=64) (b:=64) sp12679 sp12743))) (joinSmall (lo:=12807) (a:=256) (b:=256) (joinSmall (lo:=12807) (a:=128) (b:=128) (joinSmall (lo:=12807) (a:=64) (b:=64) sp12807 sp12871) (joinSmall (lo:=12935) (a:=64) (b:=64) sp12935 sp12999)) (joinSmall (lo:=13063) (a:=128) (b:=128) (joinSmall (lo:=13063) (a:=64) (b:=64) sp13063 sp13127) (joinSmall (lo:=13191) (a:=64) (b:=64) sp13191 sp13255)))) (joinSmall (lo:=13319) (a:=512) (b:=513) (joinSmall (lo:=13319) (a:=256) (b:=256) (joinSmall (lo:=13319) (a:=128) (b:=128) (joinSmall (lo:=13319) (a:=64) (b:=64) sp13319 sp13383) (joinSmall (lo:=13447) (a:=64) (b:=64) sp13447 sp13511)) (joinSmall (lo:=13575) (a:=128) (b:=128) (joinSmall (lo:=13575) (a:=64) (b:=64) sp13575 sp13639) (joinSmall (lo:=13703) (a:=64) (b:=64) sp13703 sp13767))) (joinSmall (lo:=13831) (a:=256) (b:=257) (joinSmall (lo:=13831) (a:=128) (b:=128) (joinSmall (lo:=13831) (a:=64) (b:=64) sp13831 sp13895) (joinSmall (lo:=13959) (a:=64) (b:=64) sp13959 sp14023)) (joinSmall (lo:=14087) (a:=128) (b:=129) (joinSmall (lo:=14087) (a:=64) (b:=64) sp14087 sp14151) (joinSmall (lo:=14215) (a:=64) (b:=65) sp14215 (joinSmall (lo:=14279) (a:=32) (b:=33) sp14279 sp14311)))))) (joinSmall (lo:=14344) (a:=1025) (b:=1025) (joinSmall (lo:=14344) (a:=512) (b:=513) (joinSmall (lo:=14344) (a:=256) (b:=256) (joinSmall (lo:=14344) (a:=128) (b:=128) (joinSmall (lo:=14344) (a:=64) (b:=64) sp14344 sp14408) (joinSmall (lo:=14472) (a:=64) (b:=64) sp14472 sp14536)) (joinSmall (lo:=14600) (a:=128) (b:=128) (joinSmall (lo:=14600) (a:=64) (b:=64) sp14600 sp14664) (joinSmall (lo:=14728) (a:=64) (b:=64) sp14728 sp14792))) (joinSmall (lo:=14856) (a:=256) (b:=257) (joinSmall (lo:=14856) (a:=128) (b:=128) (joinSmall (lo:=14856) (a:=64) (b:=64) sp14856 sp14920) (joinSmall (lo:=14984) (a:=64) (b:=64) sp14984 sp15048)) (joinSmall (lo:=15112) (a:=128) (b:=129) (joinSmall (lo:=15112) (a:=64) (b:=64) sp15112 sp15176) (joinSmall (lo:=15240) (a:=64) (b:=65) sp15240 (joinSmall (lo:=15304) (a:=32) (b:=33) sp15304 sp15336))))) (joinSmall (lo:=15369) (a:=512) (b:=513) (joinSmall (lo:=15369) (a:=256) (b:=256) (joinSmall (lo:=15369) (a:=128) (b:=128) (joinSmall (lo:=15369) (a:=64) (b:=64) sp15369 sp15433) (joinSmall (lo:=15497) (a:=64) (b:=64) sp15497 sp15561)) (joinSmall (lo:=15625) (a:=128) (b:=128) (joinSmall (lo:=15625) (a:=64) (b:=64) sp15625 sp15689) (joinSmall (lo:=15753) (a:=64) (b:=64) sp15753 sp15817))) (joinSmall (lo:=15881) (a:=256) (b:=257) (joinSmall (lo:=15881) (a:=128) (b:=128) (joinSmall (lo:=15881) (a:=64) (b:=64) sp15881 sp15945) (joinSmall (lo:=16009) (a:=64) (b:=64) sp16009 sp16073)) (joinSmall (lo:=16137) (a:=128) (b:=129) (joinSmall (lo:=16137) (a:=64) (b:=64) sp16137 sp16201) (joinSmall (lo:=16265) (a:=64) (b:=65) sp16265 (joinSmall (lo:=16329) (a:=32) (b:=33) sp16329 sp16361))))))))) (joinSmall (lo:=16394) (a:=8197) (b:=8197) (joinSmall (lo:=16394) (a:=4098) (b:=4099) (joinSmall (lo:=16394) (a:=2049) (b:=2049) (joinSmall (lo:=16394) (a:=1024) (b:=1025) (joinSmall (lo:=16394) (a:=512) (b:=512) (joinSmall (lo:=16394) (a:=256) (b:=256) (joinSmall (lo:=16394) (a:=128) (b:=128) (joinSmall (lo:=16394) (a:=64) (b:=64) sp16394 sp16458) (joinSmall (lo:=16522) (a:=64) (b:=64) sp16522 sp16586)) (joinSmall (lo:=16650) (a:=128) (b:=128) (joinSmall (lo:=16650) (a:=64) (b:=64) sp16650 sp16714) (joinSmall (lo:=16778) (a:=64) (b:=64) sp16778 sp16842))) (joinSmall (lo:=16906) (a:=256) (b:=256) (joinSmall (lo:=16906) (a:=128) (b:=128) (joinSmall (lo:=16906) (a:=64) (b:=64) sp16906 sp16970) (joinSmall (lo:=17034) (a:=64) (b:=64) sp17034 sp17098)) (joinSmall (lo:=17162) (a:=128) (b:=128) (joinSmall (lo:=17162) (a:=64) (b:=64) sp17162 sp17226) (joinSmall (lo:=17290) (a:=64) (b:=64) sp17290 sp17354)))) (joinSmall (lo:=17418) (a:=512) (b:=513) (joinSmall (lo:=17418) (a:=256) (b:=256) (joinSmall (lo:=17418) (a:=128) (b:=128) (joinSmall (lo:=17418) (a:=64) (b:=64) sp17418 sp17482) (joinSmall (lo:=17546) (a:=64) (b:=64) sp17546 sp17610)) (joinSmall (lo:=17674) (a:=128) (b:=128) (joinSmall (lo:=17674) (a:=64) (b:=64) sp17674 sp17738) (joinSmall (lo:=17802) (a:=64) (b:=64) sp17802 sp17866))) (joinSmall (lo:=17930) (a:=256) (b:=257) (joinSmall (lo:=17930) (a:=128) (b:=128) (joinSmall (lo:=17930) (a:=64) (b:=64) sp17930 sp17994) (joinSmall (lo:=18058) (a:=64) (b:=64) sp18058 sp18122)) (joinSmall (lo:=18186) (a:=128) (b:=129) (joinSmall (lo:=18186) (a:=64) (b:=64) sp18186 sp18250) (joinSmall (lo:=18314) (a:=64) (b:=65) sp18314 (joinSmall (lo:=18378) (a:=32) (b:=33) sp18378 sp18410)))))) (joinSmall (lo:=18443) (a:=1024) (b:=1025) (joinSmall (lo:=18443) (a:=512) (b:=512) (joinSmall (lo:=18443) (a:=256) (b:=256) (joinSmall (lo:=18443) (a:=128) (b:=128) (joinSmall (lo:=18443) (a:=64) (b:=64) sp18443 sp18507) (joinSmall (lo:=18571) (a:=64) (b:=64) sp18571 sp18635)) (joinSmall (lo:=18699) (a:=128) (b:=128) (joinSmall (lo:=18699) (a:=64) (b:=64) sp18699 sp18763) (joinSmall (lo:=18827) (a:=64) (b:=64) sp18827 sp18891))) (joinSmall (lo:=18955) (a:=256) (b:=256) (joinSmall (lo:=18955) (a:=128) (b:=128) (joinSmall (lo:=18955) (a:=64) (b:=64) sp18955 sp19019) (joinSmall (lo:=19083) (a:=64) (b:=64) sp19083 sp19147)) (joinSmall (lo:=19211) (a:=128) (b:=128) (joinSmall (lo:=19211) (a:=64) (b:=64) sp19211 sp19275) (joinSmall (lo:=19339) (a:=64) (b:=64) sp19339 sp19403)))) (joinSmall (lo:=19467) (a:=512) (b:=513) (joinSmall (lo:=19467) (a:=256) (b:=256) (joinSmall (lo:=19467) (a:=128) (b:=128) (joinSmall (lo:=19467) (a:=64) (b:=64) sp19467 sp19531) (joinSmall (lo:=19595) (a:=64) (b:=64) sp19595 sp19659)) (joinSmall (lo:=19723) (a:=128) (b:=128) (joinSmall (lo:=19723) (a:=64) (b:=64) sp19723 sp19787) (joinSmall (lo:=19851) (a:=64) (b:=64) sp19851 sp19915))) (joinSmall (lo:=19979) (a:=256) (b:=257) (joinSmall (lo:=19979) (a:=128) (b:=128) (joinSmall (lo:=19979) (a:=64) (b:=64) sp19979 sp20043) (joinSmall (lo:=20107) (a:=64) (b:=64) sp20107 sp20171)) (joinSmall (lo:=20235) (a:=128) (b:=129) (joinSmall (lo:=20235) (a:=64) (b:=64) sp20235 sp20299) (joinSmall (lo:=20363) (a:=64) (b:=65) sp20363 (joinSmall (lo:=20427) (a:=32) (b:=33) sp20427 sp20459))))))) (joinSmall (lo:=20492) (a:=2049) (b:=2050) (joinSmall (lo:=20492) (a:=1024) (b:=1025) (joinSmall (lo:=20492) (a:=512) (b:=512) (joinSmall (lo:=20492) (a:=256) (b:=256) (joinSmall (lo:=20492) (a:=128) (b:=128) (joinSmall (lo:=20492) (a:=64) (b:=64) sp20492 sp20556) (joinSmall (lo:=20620) (a:=64) (b:=64) sp20620 sp20684)) (joinSmall (lo:=20748) (a:=128) (b:=128) (joinSmall (lo:=20748) (a:=64) (b:=64) sp20748 sp20812) (joinSmall (lo:=20876) (a:=64) (b:=64) sp20876 sp20940))) (joinSmall (lo:=21004) (a:=256) (b:=256) (joinSmall (lo:=21004) (a:=128) (b:=128) (joinSmall (lo:=21004) (a:=64) (b:=64) sp21004 sp21068) (joinSmall (lo:=21132) (a:=64) (b:=64) sp21132 sp21196)) (joinSmall (lo:=21260) (a:=128) (b:=128) (joinSmall (lo:=21260) (a:=64) (b:=64) sp21260 sp21324) (joinSmall (lo:=21388) (a:=64) (b:=64) sp21388 sp21452)))) (joinSmall (lo:=21516) (a:=512) (b:=513) (joinSmall (lo:=21516) (a:=256) (b:=256) (joinSmall (lo:=21516) (a:=128) (b:=128) (joinSmall (lo:=21516) (a:=64) (b:=64) sp21516 sp21580) (joinSmall (lo:=21644) (a:=64) (b:=64) sp21644 sp21708)) (joinSmall (lo:=21772) (a:=128) (b:=128) (joinSmall (lo:=21772) (a:=64) (b:=64) sp21772 sp21836) (joinSmall (lo:=21900) (a:=64) (b:=64) sp21900 sp21964))) (joinSmall (lo:=22028) (a:=256) (b:=257) (joinSmall (lo:=22028) (a:=128) (b:=128) (joinSmall (lo:=22028) (a:=64) (b:=64) sp22028 sp22092) (joinSmall (lo:=22156) (a:=64) (b:=64) sp22156 sp22220)) (joinSmall (lo:=22284) (a:=128) (b:=129) (joinSmall (lo:=22284) (a:=64) (b:=64) sp22284 sp22348) (joinSmall (lo:=22412) (a:=64) (b:=65) sp22412 (joinSmall (lo:=22476) (a:=32) (b:=33) sp22476 sp22508)))))) (joinSmall (lo:=22541) (a:=1025) (b:=1025) (joinSmall (lo:=22541) (a:=512) (b:=513) (joinSmall (lo:=22541) (a:=256) (b:=256) (joinSmall (lo:=22541) (a:=128) (b:=128) (joinSmall (lo:=22541) (a:=64) (b:=64) sp22541 sp22605) (joinSmall (lo:=22669) (a:=64) (b:=64) sp22669 sp22733)) (joinSmall (lo:=22797) (a:=128) (b:=128) (joinSmall (lo:=22797) (a:=64) (b:=64) sp22797 sp22861) (joinSmall (lo:=22925) (a:=64) (b:=64) sp22925 sp22989))) (joinSmall (lo:=23053) (a:=256) (b:=257) (joinSmall (lo:=23053) (a:=128) (b:=128) (joinSmall (lo:=23053) (a:=64) (b:=64) sp23053 sp23117) (joinSmall (lo:=23181) (a:=64) (b:=64) sp23181 sp23245)) (joinSmall (lo:=23309) (a:=128) (b:=129) (joinSmall (lo:=23309) (a:=64) (b:=64) sp23309 sp23373) (joinSmall (lo:=23437) (a:=64) (b:=65) sp23437 (joinSmall (lo:=23501) (a:=32) (b:=33) sp23501 sp23533))))) (joinSmall (lo:=23566) (a:=512) (b:=513) (joinSmall (lo:=23566) (a:=256) (b:=256) (joinSmall (lo:=23566) (a:=128) (b:=128) (joinSmall (lo:=23566) (a:=64) (b:=64) sp23566 sp23630) (joinSmall (lo:=23694) (a:=64) (b:=64) sp23694 sp23758)) (joinSmall (lo:=23822) (a:=128) (b:=128) (joinSmall (lo:=23822) (a:=64) (b:=64) sp23822 sp23886) (joinSmall (lo:=23950) (a:=64) (b:=64) sp23950 sp24014))) (joinSmall (lo:=24078) (a:=256) (b:=257) (joinSmall (lo:=24078) (a:=128) (b:=128) (joinSmall (lo:=24078) (a:=64) (b:=64) sp24078 sp24142) (joinSmall (lo:=24206) (a:=64) (b:=64) sp24206 sp24270)) (joinSmall (lo:=24334) (a:=128) (b:=129) (joinSmall (lo:=24334) (a:=64) (b:=64) sp24334 sp24398) (joinSmall (lo:=24462) (a:=64) (b:=65) sp24462 (joinSmall (lo:=24526) (a:=32) (b:=33) sp24526 sp24558)))))))) (joinSmall (lo:=24591) (a:=4098) (b:=4099) (joinSmall (lo:=24591) (a:=2049) (b:=2049) (joinSmall (lo:=24591) (a:=1024) (b:=1025) (joinSmall (lo:=24591) (a:=512) (b:=512) (joinSmall (lo:=24591) (a:=256) (b:=256) (joinSmall (lo:=24591) (a:=128) (b:=128) (joinSmall (lo:=24591) (a:=64) (b:=64) sp24591 sp24655) (joinSmall (lo:=24719) (a:=64) (b:=64) sp24719 sp24783)) (joinSmall (lo:=24847) (a:=128) (b:=128) (joinSmall (lo:=24847) (a:=64) (b:=64) sp24847 sp24911) (joinSmall (lo:=24975) (a:=64) (b:=64) sp24975 sp25039))) (joinSmall (lo:=25103) (a:=256) (b:=256) (joinSmall (lo:=25103) (a:=128) (b:=128) (joinSmall (lo:=25103) (a:=64) (b:=64) sp25103 sp25167) (joinSmall (lo:=25231) (a:=64) (b:=64) sp25231 sp25295)) (joinSmall (lo:=25359) (a:=128) (b:=128) (joinSmall (lo:=25359) (a:=64) (b:=64) sp25359 sp25423) (joinSmall (lo:=25487) (a:=64) (b:=64) sp25487 sp25551)))) (joinSmall (lo:=25615) (a:=512) (b:=513) (joinSmall (lo:=25615) (a:=256) (b:=256) (joinSmall (lo:=25615) (a:=128) (b:=128) (joinSmall (lo:=25615) (a:=64) (b:=64) sp25615 sp25679) (joinSmall (lo:=25743) (a:=64) (b:=64) sp25743 sp25807)) (joinSmall (lo:=25871) (a:=128) (b:=128) (joinSmall (lo:=25871) (a:=64) (b:=64) sp25871 sp25935) (joinSmall (lo:=25999) (a:=64) (b:=64) sp25999 sp26063))) (joinSmall (lo:=26127) (a:=256) (b:=257) (joinSmall (lo:=26127) (a:=128) (b:=128) (joinSmall (lo:=26127) (a:=64) (b:=64) sp26127 sp26191) (joinSmall (lo:=26255) (a:=64) (b:=64) sp26255 sp26319)) (joinSmall (lo:=26383) (a:=128) (b:=129) (joinSmall (lo:=26383) (a:=64) (b:=64) sp26383 sp26447) (joinSmall (lo:=26511) (a:=64) (b:=65) sp26511 (joinSmall (lo:=26575) (a:=32) (b:=33) sp26575 sp26607)))))) (joinSmall (lo:=26640) (a:=1024) (b:=1025) (joinSmall (lo:=26640) (a:=512) (b:=512) (joinSmall (lo:=26640) (a:=256) (b:=256) (joinSmall (lo:=26640) (a:=128) (b:=128) (joinSmall (lo:=26640) (a:=64) (b:=64) sp26640 sp26704) (joinSmall (lo:=26768) (a:=64) (b:=64) sp26768 sp26832)) (joinSmall (lo:=26896) (a:=128) (b:=128) (joinSmall (lo:=26896) (a:=64) (b:=64) sp26896 sp26960) (joinSmall (lo:=27024) (a:=64) (b:=64) sp27024 sp27088))) (joinSmall (lo:=27152) (a:=256) (b:=256) (joinSmall (lo:=27152) (a:=128) (b:=128) (joinSmall (lo:=27152) (a:=64) (b:=64) sp27152 sp27216) (joinSmall (lo:=27280) (a:=64) (b:=64) sp27280 sp27344)) (joinSmall (lo:=27408) (a:=128) (b:=128) (joinSmall (lo:=27408) (a:=64) (b:=64) sp27408 sp27472) (joinSmall (lo:=27536) (a:=64) (b:=64) sp27536 sp27600)))) (joinSmall (lo:=27664) (a:=512) (b:=513) (joinSmall (lo:=27664) (a:=256) (b:=256) (joinSmall (lo:=27664) (a:=128) (b:=128) (joinSmall (lo:=27664) (a:=64) (b:=64) sp27664 sp27728) (joinSmall (lo:=27792) (a:=64) (b:=64) sp27792 sp27856)) (joinSmall (lo:=27920) (a:=128) (b:=128) (joinSmall (lo:=27920) (a:=64) (b:=64) sp27920 sp27984) (joinSmall (lo:=28048) (a:=64) (b:=64) sp28048 sp28112))) (joinSmall (lo:=28176) (a:=256) (b:=257) (joinSmall (lo:=28176) (a:=128) (b:=128) (joinSmall (lo:=28176) (a:=64) (b:=64) sp28176 sp28240) (joinSmall (lo:=28304) (a:=64) (b:=64) sp28304 sp28368)) (joinSmall (lo:=28432) (a:=128) (b:=129) (joinSmall (lo:=28432) (a:=64) (b:=64) sp28432 sp28496) (joinSmall (lo:=28560) (a:=64) (b:=65) sp28560 (joinSmall (lo:=28624) (a:=32) (b:=33) sp28624 sp28656))))))) (joinSmall (lo:=28689) (a:=2049) (b:=2050) (joinSmall (lo:=28689) (a:=1024) (b:=1025) (joinSmall (lo:=28689) (a:=512) (b:=512) (joinSmall (lo:=28689) (a:=256) (b:=256) (joinSmall (lo:=28689) (a:=128) (b:=128) (joinSmall (lo:=28689) (a:=64) (b:=64) sp28689 sp28753) (joinSmall (lo:=28817) (a:=64) (b:=64) sp28817 sp28881)) (joinSmall (lo:=28945) (a:=128) (b:=128) (joinSmall (lo:=28945) (a:=64) (b:=64) sp28945 sp29009) (joinSmall (lo:=29073) (a:=64) (b:=64) sp29073 sp29137))) (joinSmall (lo:=29201) (a:=256) (b:=256) (joinSmall (lo:=29201) (a:=128) (b:=128) (joinSmall (lo:=29201) (a:=64) (b:=64) sp29201 sp29265) (joinSmall (lo:=29329) (a:=64) (b:=64) sp29329 sp29393)) (joinSmall (lo:=29457) (a:=128) (b:=128) (joinSmall (lo:=29457) (a:=64) (b:=64) sp29457 sp29521) (joinSmall (lo:=29585) (a:=64) (b:=64) sp29585 sp29649)))) (joinSmall (lo:=29713) (a:=512) (b:=513) (joinSmall (lo:=29713) (a:=256) (b:=256) (joinSmall (lo:=29713) (a:=128) (b:=128) (joinSmall (lo:=29713) (a:=64) (b:=64) sp29713 sp29777) (joinSmall (lo:=29841) (a:=64) (b:=64) sp29841 sp29905)) (joinSmall (lo:=29969) (a:=128) (b:=128) (joinSmall (lo:=29969) (a:=64) (b:=64) sp29969 sp30033) (joinSmall (lo:=30097) (a:=64) (b:=64) sp30097 sp30161))) (joinSmall (lo:=30225) (a:=256) (b:=257) (joinSmall (lo:=30225) (a:=128) (b:=128) (joinSmall (lo:=30225) (a:=64) (b:=64) sp30225 sp30289) (joinSmall (lo:=30353) (a:=64) (b:=64) sp30353 sp30417)) (joinSmall (lo:=30481) (a:=128) (b:=129) (joinSmall (lo:=30481) (a:=64) (b:=64) sp30481 sp30545) (joinSmall (lo:=30609) (a:=64) (b:=65) sp30609 (joinSmall (lo:=30673) (a:=32) (b:=33) sp30673 sp30705)))))) (joinSmall (lo:=30738) (a:=1025) (b:=1025) (joinSmall (lo:=30738) (a:=512) (b:=513) (joinSmall (lo:=30738) (a:=256) (b:=256) (joinSmall (lo:=30738) (a:=128) (b:=128) (joinSmall (lo:=30738) (a:=64) (b:=64) sp30738 sp30802) (joinSmall (lo:=30866) (a:=64) (b:=64) sp30866 sp30930)) (joinSmall (lo:=30994) (a:=128) (b:=128) (joinSmall (lo:=30994) (a:=64) (b:=64) sp30994 sp31058) (joinSmall (lo:=31122) (a:=64) (b:=64) sp31122 sp31186))) (joinSmall (lo:=31250) (a:=256) (b:=257) (joinSmall (lo:=31250) (a:=128) (b:=128) (joinSmall (lo:=31250) (a:=64) (b:=64) sp31250 sp31314) (joinSmall (lo:=31378) (a:=64) (b:=64) sp31378 sp31442)) (joinSmall (lo:=31506) (a:=128) (b:=129) (joinSmall (lo:=31506) (a:=64) (b:=64) sp31506 sp31570) (joinSmall (lo:=31634) (a:=64) (b:=65) sp31634 (joinSmall (lo:=31698) (a:=32) (b:=33) sp31698 sp31730))))) (joinSmall (lo:=31763) (a:=512) (b:=513) (joinSmall (lo:=31763) (a:=256) (b:=256) (joinSmall (lo:=31763) (a:=128) (b:=128) (joinSmall (lo:=31763) (a:=64) (b:=64) sp31763 sp31827) (joinSmall (lo:=31891) (a:=64) (b:=64) sp31891 sp31955)) (joinSmall (lo:=32019) (a:=128) (b:=128) (joinSmall (lo:=32019) (a:=64) (b:=64) sp32019 sp32083) (joinSmall (lo:=32147) (a:=64) (b:=64) sp32147 sp32211))) (joinSmall (lo:=32275) (a:=256) (b:=257) (joinSmall (lo:=32275) (a:=128) (b:=128) (joinSmall (lo:=32275) (a:=64) (b:=64) sp32275 sp32339) (joinSmall (lo:=32403) (a:=64) (b:=64) sp32403 sp32467)) (joinSmall (lo:=32531) (a:=128) (b:=129) (joinSmall (lo:=32531) (a:=64) (b:=64) sp32531 sp32595) (joinSmall (lo:=32659) (a:=64) (b:=65) sp32659 (joinSmall (lo:=32723) (a:=32) (b:=33) sp32723 sp32755))))))))))
  have good : (List.range 32788).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 1075000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 32787 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 32787 := by
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


private def packet (i : ℕ) : ℕ := (if i < 273 then (if i < 136 then (if i < 68 then (if i < 34 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else 0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0 else 0) else (if i < 11 then 0 else 0)) else (if i < 14 then (if i < 13 then 0 else 0) else (if i < 15 then 0 else (if i < 16 then 0 else 0))))) else (if i < 25 then (if i < 21 then (if i < 19 then (if i < 18 then 0 else 0) else (if i < 20 then 0 else 0)) else (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else 0))) else (if i < 29 then (if i < 27 then (if i < 26 then 0 else 0) else (if i < 28 then 0 else 0)) else (if i < 31 then (if i < 30 then 0 else 0) else (if i < 32 then 0 else (if i < 33 then 0 else 0)))))) else (if i < 51 then (if i < 42 then (if i < 38 then (if i < 36 then (if i < 35 then 0 else 0) else (if i < 37 then 0 else 0)) else (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0))) else (if i < 46 then (if i < 44 then (if i < 43 then 0 else 0) else (if i < 45 then 0 else 0)) else (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else (if i < 50 then 0 else 0))))) else (if i < 59 then (if i < 55 then (if i < 53 then (if i < 52 then 0 else 0) else (if i < 54 then 0 else 0)) else (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else 0))) else (if i < 63 then (if i < 61 then (if i < 60 then 0 else 0) else (if i < 62 then 0 else 0)) else (if i < 65 then (if i < 64 then 0 else 0) else (if i < 66 then 0 else (if i < 67 then 0 else 0))))))) else (if i < 102 then (if i < 85 then (if i < 76 then (if i < 72 then (if i < 70 then (if i < 69 then 0 else 0) else (if i < 71 then 0 else 0)) else (if i < 74 then (if i < 73 then 0 else 0) else (if i < 75 then 0 else 0))) else (if i < 80 then (if i < 78 then (if i < 77 then 0 else 0) else (if i < 79 then 0 else 0)) else (if i < 82 then (if i < 81 then 0 else 0) else (if i < 83 then 0 else (if i < 84 then 0 else 0))))) else (if i < 93 then (if i < 89 then (if i < 87 then (if i < 86 then 0 else 0) else (if i < 88 then 0 else 0)) else (if i < 91 then (if i < 90 then 0 else 0) else (if i < 92 then 0 else 0))) else (if i < 97 then (if i < 95 then (if i < 94 then 0 else 0) else (if i < 96 then 0 else 0)) else (if i < 99 then (if i < 98 then 0 else 0) else (if i < 100 then 0 else (if i < 101 then 0 else 0)))))) else (if i < 119 then (if i < 110 then (if i < 106 then (if i < 104 then (if i < 103 then 0 else 0) else (if i < 105 then 0 else 0)) else (if i < 108 then (if i < 107 then 0 else 0) else (if i < 109 then 0 else 0))) else (if i < 114 then (if i < 112 then (if i < 111 then 0 else 0) else (if i < 113 then 0 else 0)) else (if i < 116 then (if i < 115 then 0 else 0) else (if i < 117 then 0 else (if i < 118 then 0 else 0))))) else (if i < 127 then (if i < 123 then (if i < 121 then (if i < 120 then 0 else 0) else (if i < 122 then 0 else 0)) else (if i < 125 then (if i < 124 then 0 else 0) else (if i < 126 then 0 else 0))) else (if i < 131 then (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else 0)) else (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else (if i < 135 then 0 else 0)))))))) else (if i < 204 then (if i < 170 then (if i < 153 then (if i < 144 then (if i < 140 then (if i < 138 then (if i < 137 then 0 else 0) else (if i < 139 then 0 else 0)) else (if i < 142 then (if i < 141 then 0 else 0) else (if i < 143 then 0 else 0))) else (if i < 148 then (if i < 146 then (if i < 145 then 0 else 0) else (if i < 147 then 0 else 0)) else (if i < 150 then (if i < 149 then 0 else 0) else (if i < 151 then 0 else (if i < 152 then 0 else 0))))) else (if i < 161 then (if i < 157 then (if i < 155 then (if i < 154 then 0 else 0) else (if i < 156 then 0 else 0)) else (if i < 159 then (if i < 158 then 0 else 0) else (if i < 160 then 0 else 0))) else (if i < 165 then (if i < 163 then (if i < 162 then 0 else 0) else (if i < 164 then 0 else 0)) else (if i < 167 then (if i < 166 then 0 else 0) else (if i < 168 then 0 else (if i < 169 then 0 else 0)))))) else (if i < 187 then (if i < 178 then (if i < 174 then (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else 0)) else (if i < 176 then (if i < 175 then 0 else 0) else (if i < 177 then 0 else 0))) else (if i < 182 then (if i < 180 then (if i < 179 then 0 else 0) else (if i < 181 then 0 else 0)) else (if i < 184 then (if i < 183 then 0 else 0) else (if i < 185 then 0 else (if i < 186 then 0 else 0))))) else (if i < 195 then (if i < 191 then (if i < 189 then (if i < 188 then 0 else 0) else (if i < 190 then 0 else 0)) else (if i < 193 then (if i < 192 then 0 else 0) else (if i < 194 then 0 else 0))) else (if i < 199 then (if i < 197 then (if i < 196 then 0 else 0) else (if i < 198 then 0 else 0)) else (if i < 201 then (if i < 200 then 0 else 0) else (if i < 202 then 0 else (if i < 203 then 0 else 0))))))) else (if i < 238 then (if i < 221 then (if i < 212 then (if i < 208 then (if i < 206 then (if i < 205 then 0 else 0) else (if i < 207 then 0 else 0)) else (if i < 210 then (if i < 209 then 0 else 0) else (if i < 211 then 0 else 0))) else (if i < 216 then (if i < 214 then (if i < 213 then 0 else 0) else (if i < 215 then 0 else 0)) else (if i < 218 then (if i < 217 then 0 else 0) else (if i < 219 then 0 else (if i < 220 then 0 else 0))))) else (if i < 229 then (if i < 225 then (if i < 223 then (if i < 222 then 0 else 0) else (if i < 224 then 0 else 0)) else (if i < 227 then (if i < 226 then 0 else 0) else (if i < 228 then 0 else 0))) else (if i < 233 then (if i < 231 then (if i < 230 then 0 else 0) else (if i < 232 then 0 else 0)) else (if i < 235 then (if i < 234 then 0 else 0) else (if i < 236 then 0 else (if i < 237 then 0 else 0)))))) else (if i < 255 then (if i < 246 then (if i < 242 then (if i < 240 then (if i < 239 then 0 else 0) else (if i < 241 then 0 else 0)) else (if i < 244 then (if i < 243 then 0 else 0) else (if i < 245 then 0 else 0))) else (if i < 250 then (if i < 248 then (if i < 247 then 0 else 0) else (if i < 249 then 0 else 0)) else (if i < 252 then (if i < 251 then 0 else 0) else (if i < 253 then 0 else (if i < 254 then 0 else 0))))) else (if i < 264 then (if i < 259 then (if i < 257 then (if i < 256 then 0 else 0) else (if i < 258 then 0 else 0)) else (if i < 261 then (if i < 260 then 0 else 0) else (if i < 262 then 0 else (if i < 263 then 0 else 0)))) else (if i < 268 then (if i < 266 then (if i < 265 then 0 else 0) else (if i < 267 then 0 else 0)) else (if i < 270 then (if i < 269 then 0 else 0) else (if i < 271 then 0 else (if i < 272 then 0 else 0))))))))) else (if i < 410 then (if i < 341 then (if i < 307 then (if i < 290 then (if i < 281 then (if i < 277 then (if i < 275 then (if i < 274 then 0 else 0) else (if i < 276 then 0 else 0)) else (if i < 279 then (if i < 278 then 0 else 0) else (if i < 280 then 0 else 0))) else (if i < 285 then (if i < 283 then (if i < 282 then 0 else 0) else (if i < 284 then 0 else 0)) else (if i < 287 then (if i < 286 then 0 else 0) else (if i < 288 then 0 else (if i < 289 then 0 else 0))))) else (if i < 298 then (if i < 294 then (if i < 292 then (if i < 291 then 0 else 0) else (if i < 293 then 0 else 0)) else (if i < 296 then (if i < 295 then 0 else 0) else (if i < 297 then 0 else 0))) else (if i < 302 then (if i < 300 then (if i < 299 then 0 else 0) else (if i < 301 then 0 else 0)) else (if i < 304 then (if i < 303 then 0 else 0) else (if i < 305 then 0 else (if i < 306 then 0 else 0)))))) else (if i < 324 then (if i < 315 then (if i < 311 then (if i < 309 then (if i < 308 then 0 else 0) else (if i < 310 then 0 else 0)) else (if i < 313 then (if i < 312 then 0 else 0) else (if i < 314 then 0 else 0))) else (if i < 319 then (if i < 317 then (if i < 316 then 0 else 0) else (if i < 318 then 0 else 0)) else (if i < 321 then (if i < 320 then 0 else 0) else (if i < 322 then 0 else (if i < 323 then 0 else 0))))) else (if i < 332 then (if i < 328 then (if i < 326 then (if i < 325 then 0 else 0) else (if i < 327 then 0 else 0)) else (if i < 330 then (if i < 329 then 0 else 0) else (if i < 331 then 0 else 0))) else (if i < 336 then (if i < 334 then (if i < 333 then 0 else 0) else (if i < 335 then 0 else 0)) else (if i < 338 then (if i < 337 then 0 else 0) else (if i < 339 then 0 else (if i < 340 then 0 else 0))))))) else (if i < 375 then (if i < 358 then (if i < 349 then (if i < 345 then (if i < 343 then (if i < 342 then 0 else 0) else (if i < 344 then 0 else 0)) else (if i < 347 then (if i < 346 then 0 else 0) else (if i < 348 then 0 else 0))) else (if i < 353 then (if i < 351 then (if i < 350 then 0 else 0) else (if i < 352 then 0 else 0)) else (if i < 355 then (if i < 354 then 0 else 0) else (if i < 356 then 0 else (if i < 357 then 0 else 0))))) else (if i < 366 then (if i < 362 then (if i < 360 then (if i < 359 then 0 else 0) else (if i < 361 then 0 else 0)) else (if i < 364 then (if i < 363 then 0 else 0) else (if i < 365 then 0 else 0))) else (if i < 370 then (if i < 368 then (if i < 367 then 0 else 0) else (if i < 369 then 0 else 0)) else (if i < 372 then (if i < 371 then 0 else 0) else (if i < 373 then 0 else (if i < 374 then 0 else 0)))))) else (if i < 392 then (if i < 383 then (if i < 379 then (if i < 377 then (if i < 376 then 0 else 0) else (if i < 378 then 0 else 0)) else (if i < 381 then (if i < 380 then 0 else 0) else (if i < 382 then 0 else 0))) else (if i < 387 then (if i < 385 then (if i < 384 then 0 else 0) else (if i < 386 then 0 else 0)) else (if i < 389 then (if i < 388 then 0 else 0) else (if i < 390 then 0 else (if i < 391 then 0 else 0))))) else (if i < 401 then (if i < 396 then (if i < 394 then (if i < 393 then 0 else 0) else (if i < 395 then 0 else 0)) else (if i < 398 then (if i < 397 then 0 else 0) else (if i < 399 then 0 else (if i < 400 then 0 else 0)))) else (if i < 405 then (if i < 403 then (if i < 402 then 0 else 0) else (if i < 404 then 0 else 0)) else (if i < 407 then (if i < 406 then 0 else 0) else (if i < 408 then 0 else (if i < 409 then 0 else 0)))))))) else (if i < 478 then (if i < 444 then (if i < 427 then (if i < 418 then (if i < 414 then (if i < 412 then (if i < 411 then 0 else 0) else (if i < 413 then 0 else 0)) else (if i < 416 then (if i < 415 then 0 else 0) else (if i < 417 then 0 else 0))) else (if i < 422 then (if i < 420 then (if i < 419 then 0 else 0) else (if i < 421 then 0 else 0)) else (if i < 424 then (if i < 423 then 0 else 0) else (if i < 425 then 0 else (if i < 426 then 0 else 0))))) else (if i < 435 then (if i < 431 then (if i < 429 then (if i < 428 then 0 else 0) else (if i < 430 then 0 else 0)) else (if i < 433 then (if i < 432 then 0 else 0) else (if i < 434 then 0 else 0))) else (if i < 439 then (if i < 437 then (if i < 436 then 0 else 0) else (if i < 438 then 0 else 0)) else (if i < 441 then (if i < 440 then 0 else 0) else (if i < 442 then 0 else (if i < 443 then 0 else 0)))))) else (if i < 461 then (if i < 452 then (if i < 448 then (if i < 446 then (if i < 445 then 0 else 0) else (if i < 447 then 0 else 0)) else (if i < 450 then (if i < 449 then 0 else 0) else (if i < 451 then 0 else 0))) else (if i < 456 then (if i < 454 then (if i < 453 then 0 else 0) else (if i < 455 then 0 else 0)) else (if i < 458 then (if i < 457 then 0 else 0) else (if i < 459 then 0 else (if i < 460 then 0 else 0))))) else (if i < 469 then (if i < 465 then (if i < 463 then (if i < 462 then 0 else 0) else (if i < 464 then 0 else 0)) else (if i < 467 then (if i < 466 then 0 else 0) else (if i < 468 then 0 else 0))) else (if i < 473 then (if i < 471 then (if i < 470 then 0 else 0) else (if i < 472 then 0 else 0)) else (if i < 475 then (if i < 474 then 0 else 0) else (if i < 476 then 0 else (if i < 477 then 0 else 0))))))) else (if i < 512 then (if i < 495 then (if i < 486 then (if i < 482 then (if i < 480 then (if i < 479 then 0 else 0) else (if i < 481 then 0 else 0)) else (if i < 484 then (if i < 483 then 0 else 0) else (if i < 485 then 0 else 0))) else (if i < 490 then (if i < 488 then (if i < 487 then 0 else 0) else (if i < 489 then 0 else 0)) else (if i < 492 then (if i < 491 then 0 else 0) else (if i < 493 then 0 else (if i < 494 then 0 else 0))))) else (if i < 503 then (if i < 499 then (if i < 497 then (if i < 496 then 0 else 0) else (if i < 498 then 0 else 0)) else (if i < 501 then (if i < 500 then 0 else 0) else (if i < 502 then 0 else 0))) else (if i < 507 then (if i < 505 then (if i < 504 then 0 else 0) else (if i < 506 then 0 else 0)) else (if i < 509 then (if i < 508 then 0 else 0) else (if i < 510 then 0 else (if i < 511 then 0 else 0)))))) else (if i < 529 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 0 else 0) else (if i < 515 then 0 else 0)) else (if i < 518 then (if i < 517 then 0 else 0) else (if i < 519 then 0 else 0))) else (if i < 524 then (if i < 522 then (if i < 521 then 0 else 0) else (if i < 523 then 0 else 0)) else (if i < 526 then (if i < 525 then 0 else 0) else (if i < 527 then 0 else (if i < 528 then 0 else 0))))) else (if i < 538 then (if i < 533 then (if i < 531 then (if i < 530 then 0 else 0) else (if i < 532 then 0 else 0)) else (if i < 535 then (if i < 534 then 0 else 0x32dfb802ca14c09b647d20f8edc6ae2f614b88fc3c418008b02d80c4000032df5c92b1143896a4602008e7c6802e013d889439616a08982c40b0000032df0162af940c97a4682050eb869a2e9142889438816208a02e00b8000032dea552b0944096c4581ff0e686702d113a086439016e08b03000c0000032de45c2d215349d448d2198f446e230b15489083c218409583380d2000032dde9e2ac93ec93c4411ed8e086642c913a084c37c16708982d40b4000032dd8ec2ab93d093e44e1fa8e386622e4140088c39c17409203380c8000032dd31b2bd94749884691fc0e7c67c2e9147889c3a816f08602b80ac000032dcd732a613b493243d1ed0dd46342c613a085437c16208a02d80c0000032dc7962bd94449684582008e646782dc13f88ac38a16208382e40b8000032dc1d92b094349544471f58e7c6902e9143089439e17408b82d80c0000032dbbfd2bf149098e47320b0f086bc30014a89083ca18508e83080d0000032db6302be147097a46c20d0efc6c82fb14d08e83ca17908c83080b4000032db0762ab93e094c43a1f00e1c66a2e514788c03b017109203100c8000032daaa72b014489584501fb0e3c65c2c6135887c39417008a02e00b0000032da50b2a313d89104341ec0de46422c3132083436a15907d827c0a6000032d9f272be946097e45a2000ea46a22ef14a08ec3bc17e08e02cc0c8000032d99752aa13ec93a43c1ed0e386562cf14008b43b017208d02d40ba000032d93752cc94dc9a44842078ee86b430615209103cc18409203040b0000032d8db32b5144c95c4491f60e2464e2cd135886439017008a82e80ba000032d87c82c1948c99c46d2068ecc67e2e314b08e839c17008a82d80bc000032d820a2b7143496845b1fe0e4c6722d913c088438416508682b80ac000032d7c402b9148497245e2018ea468a2e914588a438c16f08402a80a8000032d76802b3143497045e2010e7c6802df13c083c37616b08782ac0ae000032d70962c514909824582000ea867a2e414408c03a417708d82d009e000032d6ae52aa93b892e4321e98dfc63a2c4136084036015d08302cc0b0000032d65272ad140495644f1fe8e846822e414608b039217709103040d0000032d5f512bf948c98845c1fd0e6c6922e4142889439e17208702f80b0000032d59912b7942c9544451f10e106282c11320830384167086829c0b0000032d53d82ab13ec95644a1f78e706662ed14788ac39616808882d00ae000032d4e2d2a513e89384401f18e0865a2da141889438016508582a80ac000032d484b2c094849864622018e8c6882ee149890c3d218c09383180c6000032d42982ad140895a44a1f80e7c68a302153890c3bc18108d02e80ce000032d3ccd2b5944496a4682050ef86c62fe14d88d03a616d08a82e00ac000032d36f92b9945c9764571fb8e5067c2e713e889839816a08582d40c0000032d30fb2cb14e09c048c2150f2c6ca2fb15209083c217708a02b40a4000032d2b622a713b892c4361ee0e0c6382bd131881836215a08302b80ac000032d256c2ce14fc9b24832118f386b42fd152090c3ac17908d830c0c4000032d1ff6294933c8e24141db8db06222ba133883037415407d829409c000032d1a092c5148497c45c2030eb86b22f914b88c039817608482d40ac000032d14302bb946c9964702020eac6b42f814d88d43a617508a02cc0aa000032d0e5b2bd94b89a646d20d0edc6bc2ef14e08f83a2178090832c0c6000032d08bf29f93d091a42d1e80dd86462c0130083c35e15808382a40aa000032d03032ae941095a4581ff8e9067e2e714488ac3a617208982c00b4000032cfd4f2aa13e09304411f28df46322c413d086037616608302b00a8000032cf76e2c5149898c4652080ed06ac2f914588b43aa17c08c82e80c0000032cf1802c814b098846d2078ecc6b62fd14f08cc3a016d08902d80b2000032ceb9b2c3949099a46a20d8ee46bc2fa14a08a439a16808882d80b0000032ce5d32b0143095a44d1f88e586542df141086038416708b82e80a8000032cdff62c394749944702100f286d031015989543ea19d09c83300bc000032cda312b714089524421f30e186482ca138081c35215808082bc09a000032cd4742ad13f093c4471f50e106562d513d085836615b08382b80ae000032ccec62a1937891242b1ec0e006522d513c888c37616908602c00b4000032cc8ee2be946497645a1fc0e5c6742dd144889839016508402c00a0000032cc3392b094209724682000e906802e114108903a417008282ec0b8000032cbd772b293f495a44c1f50e106562ce13c089039416408302a809e000032cb7ce2a713d49324341ed8de06422cc13a886839017308682d40ae000032cb1f72c0948c97645c1ff0e806882e314308c03a017308882c40aa000032cac2f2af14089504491f50e5068e2e414308a438e16808882d80b4000032ca6692b194109524491fa0e906982e2145089838c16508302d40ae000032ca0722cc14f89b847b2088eec6b02fc15209143ce18509183140be000032c9ad42a413f49424491f28e286562d113f088438c16908582900b0000032c952f2a213d493643c1f28e406622d514208bc3a217a08c82e00b8000032c8f652b9146498c4752058ea46962e0145889c39216b08702f40c8000) else (if i < 536 then 0x32f6cf92be94709644551f78e3866e2e213e086c37416308682cc0ba000032f67192bd946c9924662088ee46a82ea14608d83b017408a02fc0bc000032f61432c1948c9a04752090ee06a82f514d08e43ce17e09003380d8000032f5b9f2a613949184211eb8e246542d114108b839816808682d40b6000032f562129013088e44181dd0d7c60e2ad12707dc34814807f82b809e000032f50652b1143096c4592010ea06ac2e914508cc3b417b09083180cc000032f4ab02ae14149604581fc0e5c6722d8141087c38416b08a02d80b4000032f45072a293bc92842c1ec0db46242c6137085838616408502cc0c2000032f3f352bd94789804662028ec06a62f614d08c439a17208d02d00c6000032f398c2a013989164331ee0df86482cd141086438e17208b82f00be000032f33e12a594009564601fc0e946882f714a08dc3ac17208902d80b4000032f2e232b214509724541fb0e8c6762e714a08e03ac16e08d02f00be000032f28732aa940095a44d1f98e646902ec14408b439816e08702c80b2000032f22a72b8945497845c2030ea06a42f614908ec3ba17608b83040c6000032f1cc42bf94ac99c47720b8ec86902e113f088c39016308602e00b6000032f171c2a913e092e43d1f50e506582c5133082436616107f0288094000032f11612a793d893844d1f78e606722e413f889037e16008582cc09c000032f0b842c0147c9804672080ef06cc307152892c3d618109403280c2000032f05a32bd14809924662058e946782e514888cc3a817508a03100bc000032effc12c694e09a847320a8ef86ba2f914c88d83bc17c091031c0c0000032efa062ac13d493e43b1ee0e006382bf135881836e15c08102b80a8000032ef4142c794ec9b64812138f406e632115d09603ec19509203000c8000032eee3c2b9947498046820c0ec86ba30b15309283d818709383280c0000032ee84f2c914c09c048120f8efc6aa2f314888f03ba18209002fc0d0000032ee2912ad13f895444e1f88e646802ee14808a839216408602bc096000032edcf22a493b892443e1ef0de86382d413a088c3a416c08582ac0bc000032ed7452ae140894844a1f90e506722e414288c439e17908d82c40b6000032ed1882b3144095a4461f38e5467a2df14588ac39c17a08782d80bc000032ecbdc2a993e49364321ec8db06342bf131083836215607e82a40ae000032ec5f82c4148898847420d8ee86a02ed14e88f03b017f09803240d6000032ec03f2ac13dc9504591fe8e806922f214a88e43b217308902e40bc000032eba782b594709664611fc8ea06a62f114988c83a417508802fc0b6000032eb4b72b614349544501fd0e8c67e2eb14588b439616808882f40b6000032eaeef2b3142c9764561ff8e6c6762da14088a037e15c08502cc0ac000032ea94d2a013ac92242b1ee0e0c65c2d713c085037e16808882e40a6000032ea38d2bc145496445e1ff8e9868a2df14688c43b817c08d02e40ae000032e9daf2ba144c9764642008e986902df14888c83b817909002e00be000032e97d92bc147098a46420b0eec6ba2f814788dc3b417608b82cc0a8000032e91f32c0149499246d2070ed86ca30a14f09043be17e08a02d80ac000032e8c0a2c314909964692080ea86a02f015009083b817b08f02d00b8000032e86232c5949c98a4672060ebc69a2e814608a038216e08b02e00c0000032e80412bd946897a45a1fa0e846a42f114e88f83a617709003140c4000032e7a6d2b9943496e45e2010e686802e2143889839816d08983000c2000032e74c42a9940c94c4431fb8e246542cb13b088c38a16b08a82f40d0000032e6f152a993c89304351ed8dd06502d513b086037c15f08182bc0b6000032e69292cc15149b847e2138f086c02f914f893c3c2189094832c0e4000032e632d2ce14f89d048120d8ef86cc2ff15408e83a818008c030c0c0000032e5d4d2c294949a04692038e846922eb14488a039417008482f80c6000032e57762ba14609704581fd0e646862e113f88c03b017b08f02ec0ae000032e51c42a913cc93443d1f20e0c6682dd14288b83ac17008982e00c4000032e4bfb2b5140c9444491f80e1c65a2cf13c087c39416e08b02b40c4000032e46442aa93f894e4471f50df86302c3134887838e16f08302b00a8000032e40882b2142095044c1fc8e646662ca13c086437815f08202ac0ac000032e3ad92ab93e893242e1e80dd46362bb12f081c35615e08202940b6000032e35272b0942095c45d1fc8e4066e2e014208b039016d08402c40c2000032e2f532bc14689824622018e946982ed14908e03a416908982e40b0000032e29812bb14689824612028ebc6b22fe14f091c3ba18f09302f40c4000032e23cb2ad140c94c4491f08e306662e214789083ac17a08d83000b8000032e1e0c2ad142894a4441f48e3464a2cc13d88a83aa16f08902e40b6000032e186b2a193d493c43d1ed8e0c6462d7140887039217308a82cc0bc000032e12b62a813f09464511fd0e406662d914008d03a817208702d40b4000032e0cf92ab13e49524441f20e4c6702e9140887837e16b08902d80bc000032e07352b614349604511fc8e546782e514488b839c16508382c00c4000032e01722ba140493e4451fa0e706822dd14408c03a217609083040d4000 else (if i < 537 then 0x330de332bf148099246b2050ea86a42f415188fc3d418d09483000c00000330d8632b6142896e45f1fd0e906902e713f086438e16507f82840900000330d29f2b0142895845d2018e9468c2e0141089c38a16308c82e40bc0000330ccff2a413bc9304381f20e1864e2ce138884437c16708602ec0bc0000330c7662a593b094043e1f50e3066c2d2139085c36c15708502d00b80000330c1b42aa13d49184391f10e506842e8144888439017408b82bc0ac0000330bbfb2af93e49444431f10e0c6602cf139088839416b08902d80b60000330b6272b8144c9604541fa0e446702d313a087438e174090030c0ca0000330b0722ab140495a45820b0ec06b42f114708bc3aa17508f83040b20000330aabc2ad13ec93c4411f58e706862f914b08f43b418409102f00ac0000330a4fb2b193d09244461fc8e746842e814908d83ac17c09182f80a800003309f232bb14589724672020e6c6942e814688b83a416908a82b809e0000330992b2cc94dc9b84742080ea868e2e013d886038c17508f03200c4000033093732b0943096a4501f88e7c6802d413e888c37816208702e80b400003308d8d2c394b89b247520c8ed06a22f914d88c839c17408902b00a8000033087ce2b8943c97245f2048ea869e2fe15188e03b617c09103140d2000033082312a493a091e43c1f20e2c6742d913e888438e17109083180c400003307c5d2c2144c97045a1fe0e746922f214488a839816808482d00a80000330768c2b994689784682040ea06a82f014408b439e17b08f82dc0c4000033070be2b8145097a45d2048ed06a82eb14608d43b617908d03100b200003306b1b2a493b893043b1ee8e186522c412e882036215807d82b00a6000033065622af942096644e1f30e1464e2cf13e088438415a07e029c09c00003305f692d295289da49421b8f646e631416009503ec18b09583280c2000033059b82aa940495c4511fd8e786802db13f888438416908582cc0b8000033053e12c614bc9ba4752060e986802dd14288a83a216c08482ec0ca00003304e092bb94449564501fe0e7068e2e414908dc3c217f08d82d80b2000033048632a9140895a4491fa8e8868e2f314b88d83a617909002f40a4000033042be2a5139490a4281ec0dd86362c6139086c37016a08582dc0b200003303d262a2139c9384441f50e0c6602d5139887838e17308f02e00be000033037552ba94649564521fb0e8c6a42fb14e08f43b017708a03080bc000033031b42a613b09224391f30e046642db141086438216308702e00c800003302bd02be947097245d2008ea06862e414488e43ae16a08b82d80bc0000330263c29d137c9084351e68e0065c2c913b889c39016808882dc0b60000330208a2a693c493e4471f60e606822ee14a88cc3a016408b82f80bc00003301a922ca14e89aa46a20b0ec06942f214688d43ba18308f82f80aa000033014cf2b6944895c4511f78e746822e414a08d43be17e09082d40ae00003300f0d2b6945096e4612030e786722d814108b038216f08f02d00c20000330095f2aa13dc94a43e1f30e0065e2e1141089c3a216c08402dc0b2000033003a92aa13f09464421f68e1c6662d513f089038216708682d40c0000032ffdf22ac940c95444e1f70e546742de14608c839816708082900a2000032ff82f2b8142495e4471f30e446662d814108b839616b08802e00b2000032ff2892ae13dc93a4361ef0e146582ce133884038c17308b82b80aa000032fec6c2d9151c9b848621a8f3c6f831a16009543ce19409382f80ca000032fe6962ba944c96645b1fc8e306462c713e087836a15808002940a6000032fe0c42bc144c96044c2030eb468a2ee14988b83a417808d02dc0a8000032fdae02c2948c9724542048eac6ac2ef14888c83bc18109383300c2000032fd5362a413c091642f1e98de46322bb12d881c36814c07702a40ac000032fcf652bb946097245f2020e8c6a22f914f88e03aa17308c02d40b4000032fc9bb2a293c892e43d1f00e386622d4139887838a16e08f03100be000032fc4012b9942494e4441f50e346622e614588a439216608402b80b6000032fbe2a2bc14949824591ff0e9468c2e414888c43be17908d82f00c0000032fb8492bf949099c4722068ea06a82fd14a88e43ae17c08b83000b2000032fb2422d795189b647c2100f286c2307157091c3ca18209503300d2000032fac632c614d89b647120a0ed06a02e714488dc39c17508802bc0bc000032fa6972ba146c97845d1fd0e906922ef14c08e83bc18909182f40b0000032fa0c22bf148c98845e1fe8e646942f514a88dc3c018c09603180d6000032f9b062b1141c95e44c1f38e406722eb14508943a017809282e00ba000032f95542ad941096c4571fb8e7468a2ee14708ac39e16b08702d00ae000032f8f9a2ac14049544431f40e146662db14889143d6187091832c0d0000032f89bb2bd14689684622010e7c67c2dd13f88a438816c08d02c80ac000032f84072a8940094e4571f98e5866c2e214388e43b017808302b80a2000032f7e522a913d89384381ee8e106602d0136886036815e08102c80b4000032f78bd2a313ac91a4301ed0df86502cd13a088c38a16708782d80b0000032f72d52c314cc9a447920b0ec469a2ee14c08f03b618409683300c4000 else 0x3324f4d2b4142896044d1f58e5867a2e0143886438616708d82f00c00000332499c2ae940c95644d1f70e546922ee14608e43a618209383540ea000033243dc2b513f09464441f78e3c6682d5140088038217008a02f00c000003323e1a2b494389664531fa8e806782df13e08a039816b08a82b80a20000332383b2be947c99e46e2088ea46902e314288843a816f08802dc0aa000033232982a313c893a4451f70e506742e014388b83a817f09183140e600003322cf02a2139892843a1f28e286622da13e888038016408902c40aa0000332271d2bf14a898e45f2000eac6942ec14488c43a217508e02dc0ba0000332217f29d137c8f842d1e40dc463c2cb13a087c38e17108382c40ba00003321baa2b894289684521fa0e7468e2f414d08dc3ca18809202e80bc000033215c52c1949098245b1f98e5466e2dd13f88883a417808982ec0ba00003320ffc2b6946898246a20a0ed46c42fb14c88dc3b018409703280d200003320a1c2c014789884602028ed86c02fe14888cc3c618809482fc0cc0000332043e2c394809904661fe0e806922f0145889838c16708782bc0a20000331fe972aa941494843a1f08e446782da13c888c38a16a086029c0a60000331f8c22b994749764601fe0e8c68c2da142889438816908a82d80a60000331f3142a493cc9464531f88e1867a2e314388b839816b08482b40a20000331ed502b4143494a4461f68e486822e213f08cc3b417e09282e80c80000331e78c2b7143c9504431f78e846842e014108b038816708482d00b00000331e1f12a093548fa4301ea0e086522ce139086436e16008482d00bc0000331dc372b0140495844d1f68e586682e013c08883ac17308d83040ce0000331d67f2aa13d893a4491f98e446702da13c087838c16308502a40b40000331d0d22a613c092043f1f08e186522d513a08803a017208c82f80ca0000331cb122af93f893843e1ef0e3864c2d413e889039017308682d00c00000331c5312be14789824692060ec468a2ea14588cc3a418009503140c20000331bf592bd147497045b2018e8868e2e114408c03a817208d03100d20000331b9852ba148498e46c2078ee46a62fb14d88b83aa17f09202f00b60000331b3a92bd947099646d20c0ed46b02f8151092c3e619509302e80ce0000331adeb2b494489604581f90e6c6722e0142088838217108c02f40ae0000331a8392ac93f494c44c1f88e5c6602db13d087437a16808a03180c40000331a2682be94749724581fa0e4c66c2d714388ac39a17208a02e80b600003319c7e2c314a099247120e0ef06c830215389203ca17d09283000b4000033196a12bd147c9824662020ebc6a02ea14988cc3ba17a08982e80b2000033190fa2a713bc9184341e48de46322c613a084837015e08782cc0c400003318b0c2c894ac99246c2068eb06982f715209243b218409383000c60000331854d2b2142898445d1f98e4c6682d413b089838c17908e03000c200003317f822bd14809764592020eb46ac2f714a08ac3aa17c09783300c2000033179bd2af943896c4591f58e346722da14388ac3a416f08982cc0bc0000331742d29993a092e4331f00dd862e2c0135083438216808582c00b000003316e672bc94989864602000e8c6882da13d087039c17708e02f80c0000033168cc2a4138c91c43a1f00e0864a2ba132083837615b08182bc0ae000033163052b314009404471f50e6068c2ee14488ac39617608882e00be00003315d7b29793408f041c1e30da86282c0135083c36415608182a80a4000033157822ca94e099a4672010ea469e2f1147889039417608982cc0b40000331519d2c314a097e4622030e9868a2ee14488a83ae17208602cc0be00003314bbf2c614b89a04792000e9c6982ea14708cc3ac16f08602c00a0000033145ec2bc944096a4602068e7866e2da142088039618208e03000b20000331403a2ae140493e4411f50e146422d614308b03a817e09102c80b400003313a682ba94bc9a24712070ee06a82fa15089103e018808c02c80ac000033134a02b7946497a4591fe8e9c68c2eb14588d43a817808d82f80c000003312ef32ac141094c4581fe0e746622d314108ac39416b08802f40c20000331292b2b814349664541f80e6069c2f414a88cc39e16808a82e80bc000033123682b5144896044f1fa8e786882e414808b83a0177091830c0c000003311d912ba94809864622028eac69a2e5143889839c17208a82cc0b0000033117c72b1142894c4431f30e2c64a2ca137083837015807f82b00960000331120a2ae94109524491f90e506722d913c085c37616408902d80bc00003310c3f2b6142894a4431f78e3865a2d013d88c83aa17608e03200ca000033106782b214149404441f40e3066e2d7139886c38c16b08702bc0ae000033100db2a493b093643c1ee8df864e2cd138885c37c16608682d00c20000330fb212ac93ec94a44b1f70e6c6882f314708ec3aa17108d02e80cc0000330f55d2ae140494043d1f30e146682d513f08a43a417a09083140ca0000330ef5d2d3151c9c24812108f006b02fa14a08bc39417408b82d00be0000330e9c929e137c9164311eb0de86402c7134884436c15e08582bc09e0000330e3f02be145095c4501fa0e5466c2ea14888c439a16e08402d00ac000)))) else (if i < 542 then (if i < 540 then (if i < 539 then 0x333c1482cc14c899c46c2058ed069c2f315008f03b017608702e80b00000333bb992a713d093443e1ef0e286582d613c887438216a08682e00be0000333b5ff29c93748f84241e10de46402c1132882c36e16608a02f80cc0000333b02c2b8946c97c4632038eac69e2ff14e88f03d218009002f40d20000333aa3b2c894ec9ae4772098ee46b22fb14988c039e16908a82e80c00000333a44d2c294a899246c20c8ef06b8303154090c3ae17c09003340c600003339e892b6945496244d1f48e3c6642d513e888837816108782ec0b8000033398c22b3942c95845c1fe0e6c68a2ea14588a039416a08582e00bc000033393222a6938c91e4301f08e286642e0142088039a17908e82f80d600003338d692ae140895643f1f10e1c6602d013a086c38216a08702b40b4000033387ad2b214309564591fe8ea069a2ed146889437c16007e82ac0a8000033381ca2c5149898e4722090ec86a02fb14d890c3c217d09083200c600003337be82c1946c97c46f20b0eec6bc30814f08fc3c818009303140b2000033376202b6942495a4501ff8e986942f414588cc3a017808f03000c8000033370532bb14789724601fe8e586642d813e886438015a08302c40b200003336ab62a593ac91642e1e68dcc6442b9137087437815c08282a40b4000033364fe2b193f093643a1f50e406602d5136883035615407d82900b000003335f402af942c94c44d1f80e6468a2ee14908f83ac17308b82f00b60000333596a2bb145896e4652030e7068a2e414508a83a017a08c82e40ae000033353ba2ab141095c4501fe0ea868c2e513f085037815e08602ec0ca00003334e0a2a813ac91642e1e90de865a2d2139087038216a08a02e80be0000333483f2b2143897645b1fc8e7466c2d413d889439817909003000ba000033342802b8142c95244e1f40e4466c2db13e08ac3a016b08e02f00b800003333cd22aa13cc93243d1ef8e1865e2e414588b439816908902f00b8000033336d82c894d499646a2080ec86982e414608bc39a16e08802c80b2000033330ec2c514809a44732050e9c68e2ef14b88e43b618008e82f80b800003332b232b4142895e4501fc0e706882e814988c039216f08a02d40ba000033325732aa93e89364391eb0e106522cd133885c38817808e82e80b600003331fbc2ac940494444f1f78e4466c2df14208ac38817508c02dc0b6000033319fa2b0941c94c4461f80e2064c2d513d087838416c08902bc09c0000333143a2b2141495e44c1f98e6c6a42f914988dc3c418409583100ce00003330e3b2c814bc9a447320a8ed86ba30615209243da19009d83340d20000333086f2b5943c9584592020e886862df14388b439e17608902c40b6000033302a82c0946896e45d2048eb06922e414588a03aa17108982c40b60000332fcf42ac93c892442e1e68da86242c9134888038216608702d40b00000332f73d2ae940895a4551f60e506822e114308b439616f08582c80ae0000332f1822a994109584451f58e306582d713c886c38816d08e82c80c00000332eb9b2c094649744612058ebc68a2ed14a88b83b417608382e40c40000332e5df2b1142895244c1fa0e5c67c2e213d886437415a08102c80c40000332dff72c794d899a47d20a0ee46aa2f815009143ca17d08e83340ce0000332da322b6140c97245e2008e6c6882ea14b09043d218d09803180b80000332d4642b914509604552008ea468c2ec14708a43a216c08e83000cc0000332ceb72a893bc93a43e1ec8de86262bc12f882c37616208482bc0900000332c8bb2cf94cc9be4912140f446dc30a15409143b217d09083200cc0000332c2f02b7143c96a44e1f60e7467e2e514608c039e17808202c00a40000332bd032c614cc99a4622038ea868c2f014c090c3be17208d03040bc0000332b75f2a513d094e44a1f98e7067a2de14408b83ae17708f02f00ac0000332b1c02a6939c90e42a1ea0e1065a2d113b886836e16608502bc0aa0000332ac022b714749824632040ecc6b62f514c88d43be17d09102e80ba0000332a6222c494c89b247d2130f206d830314e88e03ae17208382b00ca0000332a05c2b1942094844d1ff0e986942f314788f03bc17c08a02ec0be00003329a952b294149584471f60e7c68a2e013f887837615b08302c40b4000033294c62bc94949a446a2038e906942f014d09083b817408a82fc0be00003328f102ac13bc9164371eb0df864a2d513d088037816808602d409c000033289322be948097045d2028e8467a2e414408c038c16a08682a80b40000332834d2bb94509544491fb0e6c6582c1137884038016507e82a00a200003327d602c8948c97246c2080ed06b02f715188dc39a178091031c0b60000332779a2b914349644501fc0e586982f714b88cc3a617608b02f00ba000033271da2b5942896a45b2000e8468e2d813a0858376167080829c09800003326c2a2a7940094c4421f40e5466a2dd13f88a43a617d08e02ec0be000033266592ba946c98c46b2088ebc6a42f714888ec3bc17d08f83040bc0000332608e2b3142495c4511fd0e9869a2ef14c88d83bc17e08c82f00b200003325ae22a793e09444411f88e506582db14208a03b417e09303040ba0000332550f2ba944c9624501f88e5066a2df14a88f43ce18609283280c8000 else 0x33532232af93e09424451ef8e1465c2e114288ac3a617208982e40ae00003352c762ab93dc92643e1f40e546762d014188943a016e08c831c0bc000033526c12b4142c9524581fa0e846882df14808b039817308d83000d4000033520e42c094909964702090eb068e2e714808c43b417108902c00a800003351b2e2aa13d094e44c1fe8e686742dd14408bc3aa17909202e40b6000033515872a393889064381f28e1c63e2d013d088839e17308102c00b600003350fc72b3940893e44f1f80e486642db13f089c38216d08702d00b6000033509fd2b6143c98045f2028eb46b62fb14b08e43aa17108c02e80ba000033504322bd14489644571fa0e7868a2e714708b839e16608682cc0ba0000334fe872a513b493c44c1f28e486802e114788cc3b617f08e82fc0c00000334f8ae2c014ac9924651fa8e706862eb14708a03a217609102f80ba0000334f2fe2ad141496c44f1f98e286662e5139086c36c16008382ac0a60000334ed3a2b694489644552000eb46942e714988dc3ba18809583040c60000334e7782b214449624541fa8e786702da13d88b439417008c82dc0be0000334e1c72ac93ec9364411f08e2065a2d513a887437e15f08402c80a40000334dc072b4945096c4672048eb86a42f514e08f83be17f08e83100be0000334d6432ba144c9664571fd8e646742ec14b08fc3d418909303300d20000334d0632c1149c9744662088ec46ae2fa14d08cc39417408a82f00b60000334cab22ac93cc93a4451f78e346682d013e887c39216308582f40ce0000334c4f12ac14089324401f00e2c65e2d1139886c37e16c08a02ec0be0000334bf0d2be947897045c1ff0eb869e2f314808dc3b018108f82f00ca0000334b9562ad940895a4531fd8e4467e2f114d88ec3b817908e831c0d40000334b3a82a913e094644e1fb8e4865c2cb13a887839016b08a82b40a80000334add22ba146497044f1f98e486762e013f088039016c08b82f00ce0000334a81c2ad13f093443e1f70e2066a2e214488ac38416b08983100b80000334a2482bd947898c46a2090ef869c2f014c08f03ae17e09102ec0c000003349c6a2c414a899c47b20c8ef46ac2f314f08c03a617508802d00b4000033496b72aa93dc93443b1f18e0c64e2c813a886037e16308302ac09c000033490d12c1149c9924742038ec069a2f914f09003b617b08f03140cc00003348b122b3142c95a4561fc8e7c67c2eb14e08dc3b218109183240d6000033485442b3944496e46b2060ec06a82f714c08ec3ba18209202e00b000003347f842b3145096c45a2030e646762df144089438e16a08a82e40aa000033479cb2ae94249644581fd0e886982e314488d83aa17008883180ca00003347441297936490e42f1ed8df864c2d213d085c38c16f08c02dc0b600003346e702bb14789844561f60e6866c2d6144089c39016a08602f00c0000033468de29d936c91242a1e98dec6402ca133082835014e07e025809a0000334630f2bc946098645e2040eb469c2ed14508ac3a6186092830c0c600003345d3e2bb146097a4622048ec06b82fe14b88e43c218d09082fc0b2000033457652bb94549684572020e886742e113e087c37216f08a82dc0be000033451882c1948896c4591ff8e8c69a2e714488a439617008902dc0b600003344be62a193c094843e1f40e3c6622de13b888439416908a02c00aa000033446192bb946c98847220a8ec46a42f014808c43ba17908e830c0d40000334404a2b7947897645c1fc0e4866e2e0140888c39618209003100c600003343a762be145c97c46b2040e806762ec14b08e43b817f09403000be000033434d32a993d494043f1ed0e146522cf13c089c39816b08702c00ac00003342f0a2b093f49464421f70e706762da142889c39616408702bc0a8000033429472b494009564451f78e5867c2e814708ec3a617508c030c0c4000033423722b914609804561fd0e806842ea14b88cc3b017f09203180b400003341da82b5142894c4461f60e2864c2ce136885438216708602c80a6000033417e12ad141c9584481fa8e9869a2f114408ac39216c08382a40b20000334120d2b9143496e45a1ff0eb86ac2f114708a839616e08982b40ac00003340c612a713ec92c43a1ef8e2c6562cd13f088837015307a82980a40000334069a2b614249604541fc0e786802dc14488c43b017a08d82f40b6000033400d02b8143497e45e1fc8e7068e2f114408c03ac17408e02dc0ba0000333faff2bd946497a4672088ec46982e814a88e43a617808b82a00a40000333f53a2b8945897845a2018eb06a62f314b08f03bc18109383280d60000333ef792b1944c95444b1f80e546622cd13a886038616c08782bc09a0000333e9c92ae93f493e4431f40e3c67c2dd14088b83a017008c032c0cc0000333e40c2b4943896c46b2008ec86c230215009043ca18709503300cc0000333de6f2a293a89304381eb0e206522c9138084438416408602c80a20000333d8a42b4942c97044f1f98e7467c2dd14008bc3a617a08e031c0ca0000333d2c62c0948099a46a2028ea469c2ec14d89003be17508e82fc0ca0000333cd092b1943896044f1f98e7068a2e9146088438216d08a02e80bc0000333c7432b1943095044b1f38e186622da140885c38a17308902f00bc000) else (if i < 541 then 0x336a3dc2cc94fc9ca4842158f246b62f714d88d83b417408c82e00ca00003369ddd2d695309de48b2190f546ec31115a89483e618609283180d6000033697f12c8149c9904702020e7c68c2e714c88ec3b417f093830c0c2000033692022c694a499c47220b8f006b830114f09083b817a08d82c80b200003368c282bb94749784642038e506642cf13a885437816408802c40b2000033686602ba145c95e4522010ea868c2e614508a837e16d08702c80c2000033680bb2a213ac91e4351ec0e106642d413c885036e15a08002ac0a200003367ae02bd146497e4652038ea068a2f2142889837616508482e00c0000033675362a593d49444451f08df46402d01348858378164083829c0a600003366f6a2b6144c96a4501f98e4c65e2cd137887c39216c08883080c00000336698f2c294b499e47520a0eb86b62fe150091c3c218709a032c0dc000033663f32a694049504481f88e4465a2d113e885037215f07c82840a800003365e2e2b013fc93a4391ef0e286622da13f089439c16c08702e40a40000336587e2b1941894c4592000eb06962ef14a88b83a417609003040c8000033652df2a213a892a4381ef0e0c6642ea14a08c839416f08d03100b000003364d012b814349684542050ea469e2f014688fc3b217108782c40b80000336470f2cd14dc9b047c20e8ee06b82fe14e88d83b417008d02f80b00000336419129593048d241d1dd0dc86182c3135885037e16b08902d40c400003363bc52b714309584511f68e5067c2dc14408a43a016c08e02fc0ac000033636032b3940c9384471f18e106642d613c086838816b08502b809c000033630332bc94ac98847020b8f086b030015509183c818408e830c0da00003362a642b8146c9a648020a8ecc6962f714e08dc3ba18409283380d0000033624bb2aa13e093043d1f00e1c65e2d113e087439017008b03100b800003361f102a893cc91643d1f18e1463e2ce13a885837416308b82f80be000033619312bf94849a04702118f306e031015d09543f419909d83680ce0000336138f2a4137c91643c1ef8dec6362b7130882036815f08102a00b000003360dc82b7945096a4601ff0e8c6882dc14188c038816a08782cc0a60000336081e29b93a091843a1eb8df86502c5131883836615c078828c09a000033602492b8945097c4662020e946822dd14508983a617508d82f00c40000335fccb29a93548f04221eb8e086302b512d881435015508382cc0b40000335f6ed2bb945897c45d1fc8e706722db14788c03a016f08882f40b60000335f1142c014809904672050eb46b02fa15689183d218d09883240ca0000335eb5e2a893f094a4481fb0e6c6762de146087c39015e08182c40b00000335e59b2b4143896e4581fa8e606802ea14788bc3b618309003080bc0000335dfaf2c814d49ac46e2080ea06882db141087c38617308902e80ca0000335d9f22b014149484582020e806862e714188a43ae17908682c00c80000335d4472a713dc93443b1f00e1c6542ce13a088838e17208882d00b80000335ce7a2b5143495c4501fc0e6467e2e814288a839e16d08c82e80b40000335c8c52ac13dc93a44a1fa0e606782db13f888c38016e08782c80b00000335c2fc2b594049484431f80e286562d213a087039c17008d030c0cc0000335bd6129e93988f04151e08dac6302b512e881036615e08202cc0b40000335b7892b8145496645d1ff0e7c6962f614808e43b217709302e00ba0000335b1d22a993d092242e1eb8dd06462c2137082c37815d07f82ac0980000335abf12be94a099447320d8f146bc2fa14708c43b817a08b83100ba0000335a6272b294289524562018ea46a02e4143089438a16608702ac09e0000335a0292c994bc9a246e2040ec468e2ea14708c83a217008b02d00c000003359a432c794b89944742098ee86ba2f814d08e43b617508e02f40cc000033594972a893f89284491f78e546862e214588a439e17509003080c400003358eb62c714d499a47020a8ec46982f2143087837e16a08382ac0ae000033588f02b2941495044e1fa8e806962e814888d03b417408c82ec0c4000033583302b1942c9684521fa0e846a22f314788cc39817208582d80ac00003357d902a193b892c43b1f40e246642d4138085836415607c82a80a4000033577ac2bf146897045e2070e9c6862e914508b039e17008a82d40c2000033571ed2b694109504411f40e306502cb138081835414d07b82a80a800003356c302ad144495e4541fa8e486622e114888dc39817008982f80c6000033566502bd148c98a45e1fc8e8068c2f214808dc3ba17809302f40c00000335606a2c514c09b447b2100ee86a630314e88e039c17108a82f80ac00003355ab22ac941094a43e1f08e146402d013a886438e16b08e02f80b8000033554c22c414989aa47b2108ef86c430115709043c818308c83080c600003354ef12b9946c97e46d2078e986aa2e814708d039e17408702fc0b4000033549392ad93f893a4471fb0e606942ee140889039a17509002fc0ca0000335437b2ae940895e44a1f90e546762de14588b039416f08602d40a800003353dd62a313b091842b1e70db06222c1136086037816908a02bc0b4000033537dc2ce95089bc4882150f2c6da30615008d83b417908d83140c6000 else 0x33815d22bd947499247120a0ee46d030915489183c018609082f80b8000033810082bb947499e47320c8ef06b430314c88fc3ce18d09683180c800003380a4a2b2943896e4551f90e6c6842ea14d08bc3ba17709103200ce000033804b729f93c49264361ec0dfc6542cc13e089c38016308a02b80ac0000337feeb2c0148498e4742098ea869230315389243f619b09c83380ce0000337f90e2c194a099a47a20c0edc6be2ff14c88d83ac17b08c02f40aa0000337f3642aa13cc9364401f78e586702e3143089c3a016e08b02e40a80000337eda92af94049464511f40e0063e2c8132082036015707d82940a00000337e7e12b494349744542020eb06a62ee14b08d83b618108f82f40a20000337e2172b3946898a4551fa0e7868c2e5140088838416c08b82bc0c20000337dc3f2bb94849744561fe8e846a42ef14788fc3c018208d02ec0b60000337d6722b794409824642048ea06b62f814f08e83bc18209283100c00000337d0cb2a713d49484531fa0e506742d1139884837416708202940a00000337cae32c914b09a846f20a0edc6b62fd14e09003c418708f82f40ac0000337c5132b494609724591fc8e806862e214208883a217308782e40ba0000337bf8329513448f041d1e80e006562c7133083437415e08582ec0ce0000337b9e42a093989184351f58e1863e2d213b085837a16508b82fc0c60000337b43a2a1139c9204331e38dd861e2b9134886437c16808682cc0ae0000337ae672c1945898846720b0ed86b82f314d08d83ac17108b02c00ac0000337a8af2ad93d09244321ec0dbc62c2bd135883437616008202bc0920000337a2ca2c694e49ca48120c0edc6b830615109343c617608a02c80c000003379d262a693d89224351eb0df86582bb139887837815808382b80ba000033797852ac141c9564571fe0e7068c2e314288903a217a08a82f80ba000033791c52ae93f89444411f78e6867e2e413c0860382163082029c0aa00003378bfc2b593fc96a45d2030e9c6a22e714688e03ac17b08e83080c8000033786042cc14f89bc47d20f0ed46c62f914f08e43b017b08d830c0d8000033780392ba144c95a44c1f98e8468c2f714e88b039c17f094034c0be00003377a682ba14949884612000ea86862f214608ac38e16d08482c00ae000033774922b7942896444f1f78e646822ed14788cc3a417e09202f40b000003376ebc2b514289604511fb8e606862eb14908d83b218709103180d2000033768ea2bf94789844652080ecc6b4302153093c3cc19a09b831c0b8000033763082bf14cc9b447820f0ed86b22fb14988e039617108e03000ba00003375d1f2c594c09a047620a8eb06a82f414d08e83ac17108c830c0ca0000337578629d938892c4431f58e3066e2d613e886039417208d82e80b6000033751a62bf94889804652020ec468c2ef14688b438a16308602bc0b400003374bc22c414849a84742070e986862e914508c83a417608882c40a0000033745cf2ce95209c04882178f046c830615109243c818909502f80d400003373fe72c3948899246c20a0ec46a82ee14608e43ac17b094030c0c600003373a5229a93708fc4291ed0df46522d8140088439015e08402940ae000033734962ab93e49464481f70e586882ee14588bc39c16b08882e80b600003372efc29b13708f84261e68ddc6362ca138085837616108302b80ae000033729242be946c97c4652040e686862e1147088c38816f08782f00c2000033723362c614b499a4682088ebc6aa2f214788c839a16a08982d80bc00003371d652ba147897e4692058e8468e2f014888d83a617408702e80b60000337177e2c214a49744672060ea469e2fd14e09183ca18509202d80a8000033711992c5947c9824611ff0e5c6762e3140888c38c16c08902c00b000003370bcb2b6943c9624571fb0e6c67e2e614a08d039e17108882d40bc000033705ed2c014a898046e20b0ef46c22fb151890c3ba17d08d03100c40000336ffe72cf94fc9cc48520b8ef86b62f314a88c83be18008d03040c40000336fa0b2bb14609784682080ebc6a22f414988c43a617208e83140c60000336f43e2b9145898446a2090ec86ae2ee14208d839217408782c00b80000336ee872b5143895a45f1fd0e9c6a02e614588cc3ae18308f02e40d20000336e8e12a693c492e4391ee8e3065e2d614688f83b417608c02b00ac0000336e3342a613c492843d1f48e4867e2dc13d086038a16b08b02e40bc0000336dd8f2a693b890a42e1e88e046442cc13c889439016508502a40a60000336d7e12ab93cc94244e1f50e5865e2d113d085836a15d08202a80bc0000336d21f2b1142493e4381ea0df464a2ca138083836215308082a00ae0000336cc5b2b4141c96a4521fa0e6467a2e814888e03a817a08b02e00b00000336c6842bc94b897a4642028e9068a2e5140885037c16108382dc0a80000336c0a72ba946496445d2020e8c6822e4142887839617908902d00b00000336bae72b0144496644e1f48e4468a2e714608d03a617809283240de0000336b54a2a513ac92a4391f30e146402c913a088437a17008882c40ba0000336af872b4942c9664662058ec86ae2e814408ac39017008d02d00b40000336a9d52ad13f89204331e70dc46282c1137083c37817409002fc0ba000)) else (if i < 544 then (if i < 543 then 0x339888e2ae93ec93c43f1f70e5066c2dc13f889438e16508682dc0c4000033982b82be147899446e2068eb46aa2f8147089438416908782c80b600003397cf72b7944896c4581fe8e6c6722d613a886438c16f08b83040c00000339772f2b7146097a4501f70e2c6582cb13d0858382168080026409c000033971532be947498046b2080ec86a02e5141089c38a17108702e40ba00003396b6c2bd144c9724622040ee06be2f614908ac3a817608602dc0b2000033965852bd94789884612000e9866e2de13c88a039416308602d80ac00003395fa52bf14a099a47d2140f006da31015789183d418509003280cc000033959d92b9145098e4712070eb469a2e314988e03b616c08802f00ce000033954242ab141494e4491fa0e706762e2140888c39c17308982dc0be00003394e5a2b694609724591fa0e446822e5149090c3bc18409282fc0b80000339488c2bc948c99a4692088e9468c2e514388c839816e08d03000c8000033942f129f139891442e1ec0dfc63a2c7134083837e16808782c40aa00003393d392ac13cc92843c1ed0de46422d413d087837c15808682b00a8000033937472ce94d89b24762078ed06b22fd14989003ae17608c82f80cc0000339316d2b9148c9a446e2008e9068a2ed14588e43b6187097030c0d000003392baa2b114189484491f30e2c65c2d913b888038216c08682c80cc000033925d72bc948c9844652040eac6942e614308a839416f08782c80b6000033920222a813f094e4441fa0e8c6802e113e086038417108d82c40ac00003391a802a493d09204381f50e5866a2da14588c43a217508a02c00ae000033914c32b2943096244d1f80e2c65a2c9134886438e15c084028409800003390f052b194409584501f98e786882de14488ac3a017808882b40ac000033909582af93ec94c4551fe8e746742e914508a039c17708c83000ba0000339036e2c9950c9da48b2158f186b830415088c03a017308b82ec0b40000338fdb22ae943496e45a2038eb46b62fc14e08f43ca18d08e03040be0000338f7b42ce94f89c84882160f0c6c430b155891c3ce18309403080be0000338f1ee2b7945c9824672020e9c69a2f714a88b43ae17f09183080d20000338ec172bf946895e4481fb8e6c6762e714888b83a217d08c82e40ac0000338e6622af141c9504441fc8e5466c2de13c889037e15d08382c00ba0000338e0912b614349644541fe8ea46a62ef141888438416c08c82e40ce0000338dad32b3945496c4592010ea06962f214a08b83a617608f83000b40000338d5092b714689804651ff8e906882ef14c88cc3a016f08782ec0ae0000338cf7629c939490242e1ea8dd062a2c112f082435415407e829809a0000338c9c52ae141c9664551fb8e746742e514308c439016908983080b60000338c3df2c1948897c4622018e906942eb148889039e16608582d00c40000338be1b2b094309644522010e9c6982f114908e83b2186094830c0ce0000338b85c2ad941895243f1ef8df464a2c3136883836215e08703000cc0000338b2a42b294309684541f30e146462d413a886837215c08182c80b00000338acd52b4942896844a1f38e0c6482cb13c886837616308282c00b60000338a6f32c1146c97446a2080eac6ae2ff14f08f83d419609383100c40000338a1102c3945496845b1fc0e846882e714688d03a617908b02fc0aa00003389b7a29c13809084351eb0df06422ce13b089039217008b02e80b00000338958a2cc94dc9a647120c0ef46b02ea15308f43dc18709503080c800003388fa62c494d09be4802110ee46a22f314c08e03a817508c02e40c4000033889e42b4141c93a4421ee8e2865e2e013d088439817408f82e40ba000033884272af14049504541fc0e606882eb13f888838215808102d80ba00003387e2c2cf94e89a64752138f286cc30e15509403ea19009383080cc000033878502c614c89ac4702070eb86a02f614a08dc3b417b08c03040ca000033872662c294b89a247020a0ecc6c630315088f03ca18509503140c200003386c9e2b7946095844e1f80e3865a2d013f088437e17208b02f80ce000033866e92ad140495a45e1f90e446562da13c885c38a15b08302d40b4000033861222b814509584491f38df86522cc136880834e15a07c02980ae00003385b8329d934c8ea4131dd8d6c5fc2bf134886438e16608b82e80b8000033855b72b8145c9644601ff0e606782df14208903ae17808e82e80c600003384fdd2bc94409924722010e886842e6143888c39616a08882c80c600003384a1a2b6142c9524511fd0e6c6802d613f089c39e17a08c82cc0b4000033844422b9945c9904752070ec06962e214208c03b417d09102dc0aa00003383e842b3143096044e1f90e306742d914208a039616808402cc0a6000033838a72bd14609804511f38e386602e014308a03a016c08582dc0ba000033832ea2ae13f494c4461f48e346722e714508e03c818209183140ba00003382d002c314a098c4662040ec46b22f114608b43b217b08d82fc0cc000033827332bb94609724501f98e4c6582dc13e086838816707f02c40b40000338217a2ad93f093a4511fe8e806862ee144088038c16608682ec0d000003381bac2bd143c9684572058ed86942ea14e09083cc180090030c0c2000 else 0x33afa4b2a413d492e43a1ea8df464c2cf141889439c17108b82f00ba000033af4a22a513d893a43e1f08e006402c1135882837015107e02940ae000033aeecc2be147497e4601f90e5867a2e0143888038e17d08f82dc0aa000033ae9192ab141894a4421f88e6c6802e314788c43b017d09183040c4000033ae3522b994549844691ff8e906aa2ff14e09083d218509503480e0000033add6c2c494909b047a2100eec6b830014b09203d418d09483300c6000033ad7aa2af94089524561fd0ea86a82fb15088f03c218909583440d4000033ad1b52cc94d49b047b2100eb86a62f914d08d83b417608d83000b6000033acbf92ad14049504511fa8e7c66e2d914208b83a016608702d80be000033ac6452ad943895a4491f80e7466c2df13f887c38216b08d82e40ac000033ac06c2c0946c98845a2060ec06a62f714a88d03ac16e08c83040cc000033ababa2a793f894e4491fb8e6468e2eb14588e03b818809702d40bc000033ab4f72b9140894a4471f90e586722d813f089c39a16808482a00bc000033aaf0d2ca94a09a846c20a0eec6bc2f614888cc39616808783100c0000033aa95c2ad940c9424461f90e546782d513b885c37416b08202d40b0000033aa3a72ab93fc9444491fa8e506702e6143088c39c17a08602d40aa000033a9dd42b714609824632038ea06942e1143888838a16c08a82a40b0000033a980f2b4943096045c1fc0e6c67e2e314608b038816308602c80a4000033a927729b13789224341eb0dfc65a2d913d088c38416808902c80ac000033a8cac2b794409464491f28e086542c9137085c37415b08182880a4000033a86c82c214bc99446f2038ea068e2e214a88fc3c218209503040b6000033a80ee2bf94809704612028e986742e8140887839a16608882c80bc000033a7b332b0141897646b2040eb46922e914088983a217d08982e00b4000033a75772b614509624471f80e206522d813c087837015d08502c00ae000033a6faf2b6942094e4561f68e446642cd136086838216c08702c80a2000033a6a0f2a493c090c42f1e60d9c6062ba132885c37e16408882ec0a4000033a643b2b9947c97c46c2030ecc6a82ec14608c83aa17508b02fc0b2000033a5e4d2c794b099047020d0ef06c230314e08e43c418109683380da000033a58922ae943497a4631ff0e6067e2e013f88903a017308b02dc0be000033a52ca2b614749584421f58e646782e014108a039416908302b40a2000033a4ce82c7148c9944632030ea46962de13d08a039016c08f82dc0b4000033a46ec2cc94dc9a447820c8eac69a2e514708b03a017808e82cc0b8000033a41392af944c95c44c1fc8e5c6642d513f088839017208a82e40d0000033a3b6b2b7144497245a2078ea869e2e914688d43c2187093031c0ba000033a359e2bb146496e4561ff0e7467c2e214608d03b017c08d03040c8000033a2fc62ba94649664561f48e0064e2d713b888837416708602c00b0000033a2a252a893d493e43d1f40e3c65c2d413d08b03a617808982dc0a4000033a247b2a913d09244321eb8dfc6562cc136886838c16e08a02e40c8000033a1e982c594b49a246d2018ebc6a42f915108f83b418309403280c8000033a18f82a313a09224401f18e506722e714408c03be17c08c82ac0b8000033a13532a013a092043b1f50e1c66a2d813e08b83a417a08c82e80b0000033a0d922b9943c9624501f98e706902ef14a08b439617109183300ca000033a07af2bf14689864682050e9c68a2e914188783aa17408e02d80b8000033a01dc2bc946497445d1fe8e746702e3145088039017108882bc0a80000339fbeb2c714c89944702038ec06b82ff15089143ce181093032c0de0000339f6432af13f49564421f10e306622d813d08a43a816d08882d80a80000339f0622bc147c97a4592020ecc6b430315009103d418a09102d80c80000339eab82a493e89464491f68e146502c313908a039c17d08d02f40b60000339e4ed2bc145c9744561fc0e6c6702de141889c39c16a08902f40b20000339df372b1142495c44a1f60e6c6882ea14508c83b617a08a82f00c00000339d9582bd14609824682070ec86b02fb15188f03b417e08f03200ca0000339d38e2b5942c96a4631fd8e7c6962f014a08e43a617108682c80980000339cdb42bd947099046e2038ebc69a2e814b89043be17208d02e40c00000339c7f72ae93dc9304381ef0e406882e214088c038e16208502c00a60000339c2442af943097245a1fc8e906a62e814308a039016508582d40b40000339bc762b4142c95e4552000e706822e114308b83ae17a08c83040be0000339b6ac2b194149664662048ee46bc30615489303e019309483040ce0000339b1032a513a09164361f30e2865e2dd141088c39417509002e00bc0000339ab1f2c2149c98245d1fe0e7867c2eb14808903a817208c02e80c40000339a5682ae94149544471f90e7466e2dd14188c039c16708402bc0b000003399fbc2a993d493a4461f60e4865c2d113b086c38416c08782b80ba000033999e22c294bc9884662068eb468c2e514188b43a017f08c82d00b4000033994282ab13d093443c1f40e486762e4142088039a16c08902e40c000003398e4e2bf948897e4612068eb86a82f314e09003c618508f031c0c2000) else (if i < 545 then 0x33c6c252ba944c9784642048eac6a42ed14788f03ba17708a82d80b6000033c66722a593d892c4351ef8e0c6522cf13f088c39c16808a02d80bc000033c606a2d215009ba4852100ef06ca30e15589243d218408f83080b6000033c5a752ca15049d04872108ee86b02ed14d88fc3ce17608c82fc0c0000033c54d02ad93ec92e43a1f40e6068a2e514988dc3c6186092831c0dc000033c4f092b6943c9624581fc0e8069a2e7141089039016c08b82ac0b6000033c49612a493c89304391ef8e0463a2bb132883036015a08502bc0a0000033c43d4298134c8f842e1e80dcc62e2c8137884436816307e82ac0a2000033c3e0f2b7944096445c1fd8e4c6702e614208ac39416a08782d80bc000033c38412b9943c96045f1fb8eac6a22f214808c43a817a08a02e40b6000033c32732bd147c97e4612040eac6882ee14988f83be17808b83040b4000033c2cc02ae13f495e4551f78e4067a2e0140887839216608702cc0ac000033c26f02ba143c97045b1fa0e3465e2cf13e086838416608a02e80c0000033c210e2c2147c96e4591fc0e5866c2de14088b03a217d08c02ec0b6000033c1b482b294209544491f70e5867c2df14908d03c017808b02cc0ac000033c157a2bd947498a4662048eb86b22f114708d43a017909603180c4000033c0fba2b0143895c4561fa0e606722e814788d83b616d08d83040ba000033c09d22cb14f09c047c20e0ee46b22fb147889c3aa17a090830c0d2000033c04012b9146496e45e2038ec86ac2f514808ac38a16808502c009a000033bfe5a2a613e892842e1ea0e006422cd13a888c39216108102d00ba000033bf82f2de95609f84a721f0f6470431b16089603ee19709782fc0c4000033bf2692b2941496444d1fd8e7c6922eb14688e03b617608b82f40c2000033becc429f138c91642e1ed8e0c63a2cb13e884c35e16108202c00a2000033be6cc2cc14f49be47520b0ec46a02f714888bc39416808782e80b2000033be12929f93ec94e44f1f68e6c6602dc13f087837216408602c80a6000033bdb7c2ac13c091a4321ef0e2866a2d413d089038216108502bc0aa000033bd5772cc95009c248120c0eb86922f313d089839417208902cc0bc000033bcf902c614ac99e4682038eb46a22f014988f03b418209283140c2000033bc9ca2b6944096c45b1fb8e7867e2e414188b839216c08702cc0a2000033bc4352a2939890e42d1ea0dc062a2c3133083837015b07e02900aa000033bbe702b0941094e44d1f80e646782e314408ac39617508d83180ce000033bb8ae2b213f09484461f90e446562d913f888037e16b08802cc0b4000033bb2dd2bb144c95a44e1fa0e7c68e2e013f888437e16c089030c0be000033bad0e2bf948c99e4681fe8e7c69c2ea14888f03a217508a82e40b4000033ba7542b1141c95444c1fb0e446582cf13a887037415507c82c00b0000033ba1b229f93b09324341f18dd86422c2134885838e17908882b80ac000033b9bc92c394bc9b046e2070ee46aa2ef14789043ba18208e82f40b6000033b95ed2c2946098045c1ff8ea068a2ec14588b439817c09002c80c6000033b900c2c714e09bc47d2108ed469a2e914588c43aa17108902cc0ca000033b8a352b614609824591fb8e886962e514108a43a417209082e40ba000033b845f2b9948497c4622068eb069a2ee14488a43a818008d02e40a8000033b7e972b8943c96e4612058eb46a42f614808d039c16d08f82f80c4000033b78e22a993e89464421f78e486662c9135885837215907d02a00b4000033b73102bf145c97444f1fc8e606862e614688d43b017e08f82d40c2000033b6d5d2b094209464481f68e406602d314188a038a16808602bc0b4000033b679f2b1142494844f1f70e3866c2d1135084438015e08002ac0bc000033b61d62b8945097845c2028eb468a2eb143889439216408902f40d0000033b5c2c2ab93e892443a1ee8df865c2d2139885c37c16008082b00a2000033b566d2b3142096445e1fd0e6867c2e2144887c38c17108f02e80b0000033b50c929e13ac91442f1ec0dcc63a2b912e080035c15d08402b40b2000033b4b0b2b414289544431f28e3c6702e4144888c37c16508102b40bc000033b45202c4948c9824641fd0ebc6b62f714e88fc3c218309183180c6000033b3f462c114949604531fd0e5467c2dd13f087c38416208402d40b6000033b39682bd147497e4672038ea069e30215288e43b8184098032c0c0000033b33b22ad941c94043d1f38e386662dc14188983a016908b82fc0ac000033b2e1229e93b094244b1f58e406762e414608e43a617709203040c2000033b28552b1143c9524461f68e706862db140887c38c17708e030c0b6000033b22542d695209e64942128f046bc2f914f09203c817f093031c0c6000033b1ca92a993b89244381ee8df86402be134886439817009082f80c8000033b16f62a993f094c44f1f80e5467c2e213e889038a16308802e80c8000033b116f291932c8ee4211e10dac6322b41328838386164080829809e000033b0b922be94509544411f70e786862ed14608a439616708b82ec0b4000033b05b82ba945497646a2048ee069e2f814b88c439817208a02c40bc000033afff02b714249544501f28e1064c2d213908903aa17c08f02dc0be000 else (if i < 546 then 0x33ddd662a493f894a4471f28e506602df14108a43a617808f030c0bc000033dd7bc2ae14009344431f30e306642d913f088037a16a08582b80b2000033dd2052ae93e093243a1f18e1865e2d1136084036e16308202ac0ac000033dcc432b5943498045c2060e986982e2141887837e16308282bc0c0000033dc6412d415149c44842110f086e0308158092c3cc18708e83140c4000033dc0962a913e49204361ef8e0464a2d213d088038a16408782cc0ac000033dbac62bb142c96445c1f78e786962f314d88f03ae17b090031c0ce000033db4fa2b9145497a45c1f78e2c64a2ce138085c38816508c82f40c6000033daf532a713e894e4511f70e286602ce13a087038016f08782d80b4000033da9782bf94a89a246f20a0ed06be30a15589203da18c09603080c2000033da3842d0152c9f24952178f6c6fa30f15889443cc18508f830c0cc000033d9d9b2c4148c9604461f80e686942e413c087038016408482b40a8000033d97fc2a293808f842c1e60dfc6382bc12c080836816008382a80a8000033d92312b0140c97445f2000e8c6a02fe14a88d839e17308902bc0ae000033d8c832a9140c93643f1ec8e2466e2de14288a439217708f82f40c2000033d86db2a793a09024351ee8e1865c2da143889c39a17308c02ec0ac000033d81252af140893c4451f68e5c6882d713b887039016f08c02f40c6000033d7b552bb14509844612020e886822eb144888c39a17608982d40ba000033d759b2b194489704521f48e306682d714208c43b817c090830c0c8000033d700529c13b890e4301ef8de86382bb133884837416d08a82e00be000033d6a3f2b3943497445f1ff8ea06882f614888a438a16608702d00bc000033d646a2b8944896c4572008e9868c2e914c08d439c16c08c82e80c4000033d5e952bf94889804622070ea06a42eb14a08d03c017d08982f40aa000033d58ca2b8146497e4541f88e406802df14408a43a217408702cc0ac000033d52e72c214b89924602028eb06bc2f414989043c418409002ec0c2000033d4d1e2b514749924672028eb86a02ed14808e43c618108e82f00ba000033d47502b7944895a44c1fc8e7067c2da13a087037c16708582d40ac000033d418a2b2946c98845d2060ed46c830414e08c83ac16f08c82f00c2000033d3be62a9141093c4501f98e646662d613c887438c16408a83180be000033d36272aa93d893643f1f28e2c65a2d7139887439616b08582b80ae000033d30582b594489684562038e9c68a2ef14988c03a217708902ec0b2000033d2a902b9948898a4672008e6467e2e2140087c38217008a030c0bc000033d24de2a513dc94e4491f68e7468c2ea147089c3a216d08582b80ae000033d1f1a2b1142094844b1f80e4465c2de14088b83a016d09002fc0b4000033d19702a993e493e4381ef0e286422be134085436015e08482c40ac000033d13b02b7946496845b1fc0e6c6822e914508a039616508402d80ae000033d0de12b9146c97e4672048e8c6922eb14888cc39c16d08b02f00bc000033d08112bb147098246a20a8f006c630014f08d43ae17708c82e00ca000033d02342c794b09ac47b20f8ed86a630014d88e83bc17909203200cc000033cfc6a2c2949499a46c20c8eec6bc300154092c3d017f08e02f00c6000033cf6ba2a593e49444481f80e646882f714c892c3c018308d02e80c2000033cf1022b2140893c43d1ee8e286582d0137084836816608502cc0b0000033ceb562a913bc9164371ee0ddc6522d413f08a83a616e08782d00b6000033ce5682c894b898a4622040e806862e214688d03b018108c82f80bc000033cdfa42b7947498446b2028eb869e2f614988b839016e08902fc0bc000033cd9d72b694689784611fd8e586822ec14988c839c16908a82e40bc000033cd4062b794549844692058ea06982eb14488d03b817608f03040b8000033cce7029713608fc41b1e00da861c2ba133884c35815e08302b0098000033cc8a52b9146c97245d2020eb86a630515189083bc17908e03040bc000033cc30429f93b89184381ee8e3865a2d113b086438216808482a00a0000033cbd4e2ab940c92e43e1f08e2064c2d413e086838216508a82f40c2000033cb7862b393f494243c1eb0dd862c2c0136888839416208582c00a2000033cb1c82b0141494e44f1fb8e646682d4141088c39a16808482b40b8000033cabfc2bd94ac99e4732098ed86b42f414d88dc3be18308e02e00ae000033ca60f2c694b499046a2080ec06ae302153892c3e218509102f00b6000033ca03e2b4145497845b1f88e586782d5141888039217908d02e40be000033c9a4b2cb94c49a847a20a8f246e231015b894c3d418809603340ca000033c948e2ab944097e46820c0ed06962ea140888c39016b08782f40b8000033c8ec72b7944896646b2020e906922ea143889c38816e08b02d40b0000033c88f72ba94649864672010e946862eb14408d039e16908282a80ae000033c832d2b714349724571fe0e8069c2f014488c439017e08f02fc0b6000033c7d762af141c94044a1fa8e5c68a2f0140887038616b08782f80cc000033c77c72a913f094244e1fa0e5c6902ee141886838016408502b00b4000033c71f92b4142496045b1fd0e706862f114f88f83be17e08f02f80ba000 else 0x33efd9a000000000000000000000002d4134882836816008582b80ac000033ef7d92b513f894e4511f88e4868c2df141889038c16a07e82b80b8000033ef1fc2c2146497c4622078ed069a2f714e08e039416808702dc0be000033eec4b2a793e093e44a1f98e506762df140088839016308282d00b2000033ee6942ae14209684561f90e486622dd14108ac3a617a08f02ec0d2000033ee0ee2a713d892a4381f10e146582cc136084037816408402c40b8000033edb1e2b9144495c44f1fd0e8468a2ea14988e83ca18509083340c8000033ed5562b4142495044e1fa8e6468c2e314388c43a616f08982f00c4000033ecfaa2ac13c49384451f10dec6482d7137886038a16308282900a4000033ec9e82b4142c95a4461fc0e706642ce13c083436815007e82980b6000033ec4162bb94549624581fc8ea06962ef14908cc39a17108982ec0c0000033ebe302c494c49b047c20f0ef06b42fc15589383d618209103180c2000033eb86d2b914449624592008eac6a42fe15109003b417708e02c00ca000033eb2c02ac93f092a43b1f18e0c64c2cd13a886035e15c083029809c000033eace02c514c49904652048e806922f614c88c83b017a08d03040c4000033ea7102bc947498845f1fc0e7c68a2d413a886c38c16a08882d80be000033ea1582ac93c89344431f78e446482cb137885037a15f08602cc0c0000033e9bbd2a413b492e4391f00e1c6522d5137084436e15907d82ac0a2000033e960a2aa140094a44b1fd0e6c6882df143887c376164082029c09c000033e90472b193fc95e44b1f50e4866a2da13f086437016008582d00ac000033e8a742bd144c9644561ff0e7c6882dd140888839617108b829c0aa000033e84d22a393a08fc4211e58db062a2ba131882c37215c08182c40a4000033e7ed92c814989a047020c0efc6ba2fd15489343e418f09803140c0000033e78f72c414b498a4672068ebc6b02f214b89343d218408e02ec0ba000033e73372b1943896245d1fb0e486782d914408cc3a217408c83080d2000033e6d792b7142c94c4531fc0e646722e814608a839a16d08802e80b2000033e67872c894c49ac4792110ee06d230a15689303da18109202fc0c2000033e61972c294cc9c44882108f206dc30d14d88c43b818108902d40ae000033e5bdc2a913e893c4461f40e3c65e2cc137887838c16f08a83000c6000033e562b2af13f094c4441f68e506642d8140887438c17008b03040c2000033e50652b0140896a4561fe8e7c6782e714988e43b017408e02f00be000033e4a8d2bd145c96845e1ff8e9868e2f214c09003c017908c83100d4000033e449a2ca94a49784622060eac6882e414408a839c17708702a00ae000033e3eda2a9140c94a43c1f50e4066e2cc13d086036815207e02b40b4000033e39262b094149424491fa0e606722df142088438016a08782d80b6000033e33702ac93f093e43e1f68e746582d713e087c38616408302d80c0000033e2db92ab13e09384411ef0e2c6642cc137086c36816908602c80b8000033e280d2ae140c9504501fa0e5c67c2ea14688d03ac18408d02f80ca000033e22392be948097a4692058e806942ed14a88c83a016508682e80c4000033e1c892a7938091e4371ef0de86542d4140088c38a16c08782ec0b2000033e16cf2ae13fc94a44c1f70e2c65e2d313b088038817008c02dc0b0000033e10f62c1948098e4652060eb869e2f714a88e03b618209103100c2000033e0b262b6144897245e1fe8ea46922fa14c08c83a416c08982c00b0000033e05562b4943c96e4591fd8e746802ec14308bc3c417e08e82f40b4000033dffaa2a8942096a4602018e846842e714888d83b217208982f00a4000033dfa092a093989124341e78dcc6362c5133884838016908702d80b6000033df4572a313ac9264371ef0e3c65a2d3133882836415f08002c00ac000033dee6d2c6948497a4581fa8e686782e413e08883a016c08902e00a8000033de8b92b0144895e4521fd0e9868a2e113f88783a016e08b82e40c2000033de3102a613d493443c1ef8e146482cd139085837416c08702f40ba000))))))))))

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



private theorem b546841 : covered 546841 546909 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546909 : covered 546909 546977 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b546977 : covered 546977 547046 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547046 : covered 547046 547114 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547114 : covered 547114 547182 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547182 : covered 547182 547250 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547250 : covered 547250 547319 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547319 : covered 547319 547387 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547387 : covered 547387 547455 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547455 : covered 547455 547523 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547523 : covered 547523 547592 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547592 : covered 547592 547660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547660 : covered 547660 547729 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547729 : covered 547729 547797 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547797 : covered 547797 547866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547866 : covered 547866 547934 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b547934 : covered 547934 548002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548002 : covered 548002 548070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548070 : covered 548070 548139 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548139 : covered 548139 548207 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548207 : covered 548207 548276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548276 : covered 548276 548344 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548344 : covered 548344 548413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548413 : covered 548413 548481 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548481 : covered 548481 548549 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548549 : covered 548549 548617 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548617 : covered 548617 548686 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548686 : covered 548686 548754 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548754 : covered 548754 548823 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548823 : covered 548823 548891 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548891 : covered 548891 548960 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b548960 : covered 548960 549028 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549028 : covered 549028 549096 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549096 : covered 549096 549164 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549164 : covered 549164 549233 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549233 : covered 549233 549301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549301 : covered 549301 549369 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549369 : covered 549369 549437 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549437 : covered 549437 549506 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549506 : covered 549506 549574 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549574 : covered 549574 549642 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549642 : covered 549642 549710 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549710 : covered 549710 549779 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549779 : covered 549779 549847 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549847 : covered 549847 549916 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549916 : covered 549916 549984 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b549984 : covered 549984 550053 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550053 : covered 550053 550121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550121 : covered 550121 550189 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550189 : covered 550189 550257 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550257 : covered 550257 550326 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550326 : covered 550326 550394 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550394 : covered 550394 550463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550463 : covered 550463 550531 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550531 : covered 550531 550600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550600 : covered 550600 550668 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550668 : covered 550668 550736 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550736 : covered 550736 550804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550804 : covered 550804 550873 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550873 : covered 550873 550941 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b550941 : covered 550941 551010 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551010 : covered 551010 551078 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551078 : covered 551078 551147 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551147 : covered 551147 551215 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551215 : covered 551215 551283 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551283 : covered 551283 551351 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551351 : covered 551351 551420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551420 : covered 551420 551488 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551488 : covered 551488 551556 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551556 : covered 551556 551624 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551624 : covered 551624 551693 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551693 : covered 551693 551761 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551761 : covered 551761 551829 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551829 : covered 551829 551897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551897 : covered 551897 551966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b551966 : covered 551966 552034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552034 : covered 552034 552103 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552103 : covered 552103 552171 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552171 : covered 552171 552240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552240 : covered 552240 552308 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552308 : covered 552308 552376 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552376 : covered 552376 552444 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552444 : covered 552444 552513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552513 : covered 552513 552581 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552581 : covered 552581 552650 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552650 : covered 552650 552718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552718 : covered 552718 552787 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552787 : covered 552787 552855 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552855 : covered 552855 552923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552923 : covered 552923 552991 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b552991 : covered 552991 553060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553060 : covered 553060 553128 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553128 : covered 553128 553197 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553197 : covered 553197 553265 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553265 : covered 553265 553334 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553334 : covered 553334 553402 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553402 : covered 553402 553470 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553470 : covered 553470 553538 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553538 : covered 553538 553607 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553607 : covered 553607 553675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553675 : covered 553675 553743 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553743 : covered 553743 553811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553811 : covered 553811 553880 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553880 : covered 553880 553948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b553948 : covered 553948 554016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554016 : covered 554016 554084 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554084 : covered 554084 554153 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554153 : covered 554153 554221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554221 : covered 554221 554290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554290 : covered 554290 554358 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554358 : covered 554358 554427 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554427 : covered 554427 554495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554495 : covered 554495 554563 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554563 : covered 554563 554631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554631 : covered 554631 554700 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554700 : covered 554700 554768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554768 : covered 554768 554837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554837 : covered 554837 554905 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554905 : covered 554905 554974 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b554974 : covered 554974 555042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555042 : covered 555042 555110 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555110 : covered 555110 555178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555178 : covered 555178 555247 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555247 : covered 555247 555315 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555315 : covered 555315 555384 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555384 : covered 555384 555452 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555452 : covered 555452 555521 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555521 : covered 555521 555589 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555589 : covered 555589 555657 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555657 : covered 555657 555725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555725 : covered 555725 555794 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555794 : covered 555794 555862 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555862 : covered 555862 555930 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555930 : covered 555930 555998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b555998 : covered 555998 556067 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556067 : covered 556067 556135 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556135 : covered 556135 556203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556203 : covered 556203 556271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556271 : covered 556271 556340 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556340 : covered 556340 556408 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556408 : covered 556408 556477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556477 : covered 556477 556545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556545 : covered 556545 556614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556614 : covered 556614 556682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556682 : covered 556682 556750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556750 : covered 556750 556818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556818 : covered 556818 556887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556887 : covered 556887 556955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b556955 : covered 556955 557024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557024 : covered 557024 557092 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557092 : covered 557092 557161 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557161 : covered 557161 557229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557229 : covered 557229 557297 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557297 : covered 557297 557365 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557365 : covered 557365 557434 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557434 : covered 557434 557502 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557502 : covered 557502 557571 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557571 : covered 557571 557639 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557639 : covered 557639 557708 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557708 : covered 557708 557776 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557776 : covered 557776 557844 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557844 : covered 557844 557912 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557912 : covered 557912 557981 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b557981 : covered 557981 558049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558049 : covered 558049 558118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558118 : covered 558118 558186 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558186 : covered 558186 558255 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558255 : covered 558255 558323 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558323 : covered 558323 558391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558391 : covered 558391 558459 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558459 : covered 558459 558528 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558528 : covered 558528 558596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558596 : covered 558596 558665 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558665 : covered 558665 558733 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558733 : covered 558733 558802 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558802 : covered 558802 558870 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558870 : covered 558870 558938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b558938 : covered 558938 559006 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559006 : covered 559006 559075 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559075 : covered 559075 559143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559143 : covered 559143 559212 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559212 : covered 559212 559280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559280 : covered 559280 559349 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559349 : covered 559349 559417 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559417 : covered 559417 559485 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559485 : covered 559485 559553 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559553 : covered 559553 559622 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559622 : covered 559622 559690 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559690 : covered 559690 559759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559759 : covered 559759 559827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b559827 : covered 559827 559896 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 546841 559896 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b546841 b546909) (joinCoverage b546977 (joinCoverage b547046 b547114))) (joinCoverage (joinCoverage b547182 (joinCoverage b547250 b547319)) (joinCoverage b547387 (joinCoverage b547455 b547523)))) (joinCoverage (joinCoverage (joinCoverage b547592 (joinCoverage b547660 b547729)) (joinCoverage b547797 (joinCoverage b547866 b547934))) (joinCoverage (joinCoverage b548002 (joinCoverage b548070 b548139)) (joinCoverage b548207 (joinCoverage b548276 b548344))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b548413 (joinCoverage b548481 b548549)) (joinCoverage b548617 (joinCoverage b548686 b548754))) (joinCoverage (joinCoverage b548823 (joinCoverage b548891 b548960)) (joinCoverage b549028 (joinCoverage b549096 b549164)))) (joinCoverage (joinCoverage (joinCoverage b549233 (joinCoverage b549301 b549369)) (joinCoverage b549437 (joinCoverage b549506 b549574))) (joinCoverage (joinCoverage b549642 (joinCoverage b549710 b549779)) (joinCoverage b549847 (joinCoverage b549916 b549984)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b550053 (joinCoverage b550121 b550189)) (joinCoverage b550257 (joinCoverage b550326 b550394))) (joinCoverage (joinCoverage b550463 (joinCoverage b550531 b550600)) (joinCoverage b550668 (joinCoverage b550736 b550804)))) (joinCoverage (joinCoverage (joinCoverage b550873 (joinCoverage b550941 b551010)) (joinCoverage b551078 (joinCoverage b551147 b551215))) (joinCoverage (joinCoverage b551283 (joinCoverage b551351 b551420)) (joinCoverage b551488 (joinCoverage b551556 b551624))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b551693 (joinCoverage b551761 b551829)) (joinCoverage b551897 (joinCoverage b551966 b552034))) (joinCoverage (joinCoverage b552103 (joinCoverage b552171 b552240)) (joinCoverage b552308 (joinCoverage b552376 b552444)))) (joinCoverage (joinCoverage (joinCoverage b552513 (joinCoverage b552581 b552650)) (joinCoverage b552718 (joinCoverage b552787 b552855))) (joinCoverage (joinCoverage b552923 (joinCoverage b552991 b553060)) (joinCoverage b553128 (joinCoverage b553197 b553265))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b553334 (joinCoverage b553402 b553470)) (joinCoverage b553538 (joinCoverage b553607 b553675))) (joinCoverage (joinCoverage b553743 (joinCoverage b553811 b553880)) (joinCoverage b553948 (joinCoverage b554016 b554084)))) (joinCoverage (joinCoverage (joinCoverage b554153 (joinCoverage b554221 b554290)) (joinCoverage b554358 (joinCoverage b554427 b554495))) (joinCoverage (joinCoverage b554563 (joinCoverage b554631 b554700)) (joinCoverage b554768 (joinCoverage b554837 b554905))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b554974 (joinCoverage b555042 b555110)) (joinCoverage b555178 (joinCoverage b555247 b555315))) (joinCoverage (joinCoverage b555384 (joinCoverage b555452 b555521)) (joinCoverage b555589 (joinCoverage b555657 b555725)))) (joinCoverage (joinCoverage (joinCoverage b555794 (joinCoverage b555862 b555930)) (joinCoverage b555998 (joinCoverage b556067 b556135))) (joinCoverage (joinCoverage b556203 (joinCoverage b556271 b556340)) (joinCoverage b556408 (joinCoverage b556477 b556545)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b556614 (joinCoverage b556682 b556750)) (joinCoverage b556818 (joinCoverage b556887 b556955))) (joinCoverage (joinCoverage b557024 (joinCoverage b557092 b557161)) (joinCoverage b557229 (joinCoverage b557297 b557365)))) (joinCoverage (joinCoverage (joinCoverage b557434 (joinCoverage b557502 b557571)) (joinCoverage b557639 (joinCoverage b557708 b557776))) (joinCoverage (joinCoverage b557844 (joinCoverage b557912 b557981)) (joinCoverage b558049 (joinCoverage b558118 b558186))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b558255 (joinCoverage b558323 b558391)) (joinCoverage b558459 (joinCoverage b558528 b558596))) (joinCoverage (joinCoverage b558665 (joinCoverage b558733 b558802)) (joinCoverage b558870 (joinCoverage b558938 b559006)))) (joinCoverage (joinCoverage (joinCoverage b559075 (joinCoverage b559143 b559212)) (joinCoverage b559280 (joinCoverage b559349 b559417))) (joinCoverage (joinCoverage b559485 (joinCoverage b559553 b559622)) (joinCoverage b559690 (joinCoverage b559759 b559827))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 546841 ≤ index 1050000000/512 := by decide +kernel
private theorem starting_value : fast 1050000000=53257350 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 1050000000=53257350) (n : ℕ) (low : 1050000000≤n) (bound : n≤1075000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=1050000000
    · rw [first,anchor]
      exact starting_value
    · have past : 1050000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤1075000000 by omega)
        have within : index n / 512 < 559896 := by omega
        have lower : index 1050000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤1075000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ1050000000To1075000000
