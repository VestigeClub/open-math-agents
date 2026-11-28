import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ550000000To575000000

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




private def radical : ℕ := 0xe72c85cde45e6ca786d87b2b0b05c100596a0c87ee8cfcb73df44c921fdb0af340b30c4671b0236ece952bac7e183e2956b8bf030e473360ca921e8c69d55e6d6c8082b30e4563165765be610dc31bbc3bc9290f8c4eab04a8fa408a472c8b31b36a473c877de98074013bfede42cae414a963aa0a83b9fa4881cec6f3e3b087d6ba98b7e9e1bbed485ceb9af87ec8f4eaf64b754e46d71ece4299cfc557cd4bdb53e84c158c85a309fa0b118fa64a4ed23230bf2f237ef3312bc7ab1b64a23708279cedb48a2b695cb7d70724e893ac7eaa769fa72bdfab2734465446eb6f1e254dc389a7bb5a7411105c8a95abe2619cca3ca32b006aa620d938036ba2cd844f74399e8ee291a30689e912ceb73815e7016128f5c3ae3d6f20f41c0e1ebffd4a98502df79e30c00163243ee9f307e5827e3ccf884e0b0541bb8f9f51a40f6606ae8bf29babf99a21c29c422a2721f78e861a79a56d4f4495694a3036f7fc8baf6dc205d80df672134df2ab0ff5e086236e018165b516ba6a0cc873a27e110f96b002b7105397e126fb4064dc9a3ba5c1339f00d9f9af6c7f7182655463a5242761bc0d89d505448c590e9845e59b337faa703e59c91ced075c515ab0772c10a328f0ee19b1575c6c18cf69e9fe25e1691014602a470bc3394054626682cdaf36bcbfed58b8ecd26943f8a41defb73908e642806ed28f7259c27dc29adb29b7d58862c1be1909a2a7ceb943aa0362839961c4188c74f120941229e99d5b2385152367fbbdfbc32a5a791fac2fa3f8ebfd35c5215793ae10f71129204e92621fffaef87e033336820aa5377f7c466347640e3a53d86b3c4b7279630a6af7fcd400f7f0a0b9e52489871f46712ea69087d9fca16d982d8607038cda806d9996ecbaea799ff181576718c105e27d529459d9bde68797c3a54dbf032f7eed7ff3f15678e60869ba46c2cb575addb65646e404392e1f7c3e4752225e0491c1ec8d803710c956b39f9cc44621dd3d3596556e1176a9be2adadf505273c3f910e10e44e84f26f1fbcc5c39d86166d22fc3c1dc8432f2f1ba9c6919cf441e4c161f78d6ad4090019022944cd83831d7668be0e64feab81b7e1aa3dec99d73f1f64a7451cdc50b6b3b49a566b27487852121511e6ce4ac17429efc92fdb4d5b49b7923143718343170f64416818cdc0acd4348ec7abac0f2dc154e8a96a7db4c43994600188e659ad38b90b053edfa0d86f98b05402236aec8f464a608b42ca976d0f5192267cb7b21d54d0633944ba558afc39474e4009c1e98ba1718ca54b35360dea99437fca387094bb7c66269c83d74e880b8797b3de8a2b7678bc48592517d5368685517ef3ae0cb12ce555ad22bb864472e2cf392f0a35699241b27f968d80c4c1156736eda262e1b3c6b42a011e39859eb77c65280c683dae0d164f0571dd10dafeac6962760cf967d520d1d88bc4237de3074afa319c05adf6a88c240bed68c45d32dd78ba3dd82d0c046a62d81e5c906f972700873c2e267c5f4bac00d607353e1776a5be40d2d91a9c42b3e07c13e92660022b5b8ea9b37cb211e4af7fca1c6b3222460b5e7beb1752e3481faf56dd213cb70d5d8322f161fd5a01bcf3ed1e9becbbf5bfa1e91fcdcba52d53f63cca46d586a732d780e7e2764ba8198117cc3ad6114e3fe145b6823a1f169bda6bb66ed8dfa52002052299899e4b143538b77b5ec79fc2a2214431aded28a2507d3d4682d95c6241f46ae089d928a33b2f38305f380bd9f28cfdf5fe044f69ffcd99eda596349468e70c54ccbc483b75cb7aadafbef5d4bb702b95470e39dbefadca9a10da2d6fb1e44e532fcad4f5763ca3563d670dd4b7a9bc17c8719537f69ff0ec4a52eca79f5a22386902d4ca08ce3a22b734e7f4f335d5e7d546cebb842a496c61f263e9860ef0e49b4f5d374310f843f355f4f84b83afbb4710e38e6ba8ed920523d3a1737eb8791f1ffdd69b3df6e6d7e2adfc6e5bbb1f36e596d8c208023b5ae6cfdef5ab11950601d12bb30dee311d72f6085f8c845ec21de2041baaaeda67d4e273a92abbb6623ecd92ef32c41f2bfb92e8f39fd93b4d6fc452feb6e5357f97a8c328dc19ac1fe631557ce0cf3420aab21fc3c25716e612ded787662f4229e36cdb1fe88d6f249bd07c409a8b970e1d9fd6a578d8fe8b5f26f4acd7f725b41ee9acec18a64e888f11a70b6dcb0b23010ea175aae0bddc563c4167c7d4b89522884f841bff9a94c147c84441461ccf55a209dfb44a30c632131a4031035c787a960f0cc8ce7c15afd33063ac4dcdfd584f308c7f2c0511375ca1e1a7d1a253ff67ef422092c1f9ad7946eb35bca345fdbfcc9dc143b07c041c4903efbc57f9df3ba853e72871bf2a252938cf6ce31d1ced01949f1aa8d838c587ef9980917b858f93373ce17f178d34fc17f7236cd3ab42eae6211fc538f04753cdf8d74ef0017329a56825441a65c3c6a9f27151cd0813ebaf555e7464101bf63f6e874fd2404d1cacabdc047912314fee058ea72503c8a40b31fc5c22576339bd3e4e8daa5774fdd919b427308d0f8d08eb7aec12bed27db86cce09fdef72b732b7f791b6e66aa2ef62890e700ff4ec900756f08c12e24302dbd8ab605de36c1140da2d1be1181711bafea3a1f08b2c52ff6a23eaa427b0175ecb6bc30e4929916d30266799a3a8f2fb7831c1005e480c1fcec46daa5e97f001d72a76b41c52b4835b4f3924a6e59183cd84cb9a83cf791b0f84a3f50d2abc1511b66a2dece4e237752ccd2eaaa78acd86a896b2f2b585f74cfaad0328dc4a3fdd8a23b7bb8847eea0cf01814036099bc03213cb9d63650e8812fc7d79629f48427c7eb32dcd4aa5f6e63b1aeb219ba709da50d447937ac7e599e82b036c391600a1bba6333e265331714675b0347590783840691a979bc50921f9b1c247eb37697e685fbf594ceb99e3332f57b9498d3ed68f554617cb4cfe9ec13d4691ccdfac54393c0117c9e249b2fa6985b57ed7ae6a9950db516a5483fb7c315f34a25c51f04775d0dd6f02244f738f8ca0f48abd0745908e3988507f78534b16f381a72de7134de111c6b1f67be84acbce17628ab9a267e8964a23d3cfc27eb51f36ad1f529a212934720063b5e291c696055184748e49e163020ef45062c47125df1e2135da0066821f1c3522ef30a7d9aea1ec1f135988007ee2ffb188f6d9569dfef44f90ed66ec9a5482be045f6d775775a2a8405b95c602430d5c5cdc803d9bc1d5baee3276c44d8173487ab3ef59c3a8e29625abf9d36249dfd9fc47f2a5f3a5ab606e71515195c6d29ed208fa0dee9cc14357c0950051f10292ff06da0d2bee07572df4b236775ce12a64a1b5d21ebda2bb6180b4837a31e91e069bfb21775fdd0f1f514995a2ab8560de7d21d66507898cf43ccf7b0e461c89b689733e46a83549418ddf9b639d0c434e522d7599770f2c679ca84f1aec28a62f700bd3e4016dfba3de976ef6e22a98cbd9eff3c3240c7bb58eaa9be3a86637773f22917db0540866d7d1a68e670ad734473ed0a260ca9e0b6284f82a85aab9e25be53d35700d50d0af1234f1f9147c24e0e70864bc6fb348fc6d32adf0d5205b17942a0dae3fe194f0144587aac2ec0db364974d8d2ce8d018c256c2548e3f8a3c24483011acf8c9861791d2e013655ed37c7f6604aec5549cc9b0908ec82c8b49ccf5331b8ea70ad7b271ab48c0a9ff042d54175e2f7daa4ab910c37a5c48758da94d1b1dbd0a9c573f6983787d5831a120134ef26bcda55e78c31c4480f339d50bdba95e53243b6a09e2aa35627fa35e2346518cd7c5345e7d2be8c33b52370964f94dbf35749476a5f2ef2d4ee7d67edd58eade8efaeaa980be471a0b5e16bdeea5ad18529d6e6f7bf192b2496f3c911d6e8ddbde9aadd1352b2fdc94641fe9fb00af80caccbcdd84a92338a81cf92b3c825953ffd276c8efd1ac0f2dec25792abe27e8af76c0711eca88bbbc531066b8401b44180f3ab0a391397a691aae468fb41085ee9bfc47e67d6bb42953527bfd97b9dbbf855a18d14df16f629b96f480166c4c312b4ed91b39d5d9071b9022d11a46869d1d123bcd60160e44883e484a559474153883e8789648910bc047a6f836a29b39507d64c72cdb3d5f19c0fd6d9de1db7718d0c8a3a3336ba82023035e6cc18072e504dc0571a850c674576df2ccf264273e526479c2cdb6f9bfbe8cc1e2586857b566c184e71fb04948c2d587d00f44d3c107916951563bd84198924081a421994d4b8c5166c12cb921e73f32517c361321d0a76976a872e4eb3ddec6d1eb99e04da0426a0d9254489669d31ef2eaa349bc23f2b99a14f056d81248426fdb900dbc6be7dde5fe3611223de135faceda46f9d28eaf3d781c1804eb2e21404d83d9ac3fb94dcf1aeb9f2c74af0dbbe3fe8338b53ec2a39e5de30e6ef506ecd34ee147de3e8cf859412fa35a5fe566036623f524c1cc87cd47e18e5a82f88bcfdd589cf9722b993ac1c135f5749b44c525f63a929c3396ee5d4c92fe82cc5c28fde7e78f406647ec26219907573cb4bd106660a788fa7df216955bf0d9e98578f9ea4bd4c3ef9261b18db14d1af6f4354bbca9ef6f83c0f7b99c9b73d1548d82f8edd4f5dbf1918089e39d6a01421933576d37d2c4fe5aa7c456ae15ceff6f34275f576343bbc5d6b07169305e106a00d57f39ecde5547c77dbd7db644251d27073adda15d504803dc67ce60c51ffc768baf6f9e93cfeb0ca4f0f920988fdfe813c8075ae76abe217b12e4013fe568a5a3e02ecb218d872b0ce2094fbc008dd59529dc7d00f9b21c1bb1336b9e252ed91a4e2af2711a6cdd5645a51c8dda0ac8f1dd3319497f4f061e7272c56fbcb858b44466bfa6d963e05470ff53407545846897a655109772d123d587812f1337e5283bcb549ab6423046cf0020136ae3822363d6097f67b300214372779d4aef782c955869a70bc70bee4ab7f5b00f0fb44aeb7a11a0ab4049eeba21ea3d4fe83fa91ba6a5a7898a60cc07791817ff41096aee5961225bba1b99772ab303f98c7f3e3fa4bb6979763693facb9d612808b882694a4ce9437a8260f74da9de70cae782287cc2a893fdf4473ac48c7ccdc25cd0957dd64bab56d0af9352be6c1a50ee907f51a9118a23600493564a5b46202a97ad7e11ae32909958260e0d8b9df1290c79c964e19efb4eb0366fd90f9269aa92d9061587e86793686ab4c7bda4bed5c6d8de18eeaa37a7fb6c82e68433b599fd48180b5ec6d5cf4f34b7b81f7ca1097ab56ec84e9cf048fe8ac3fb4252b5c7666c56fa1dab96a33d9fdd7a716d70b51c0a49c4e56581d7a6ff322ff964263758598e6f0485ad261baaf82df271439f898f6c5da192121f2c00b2cdc157022b0a1cb2810faba1b4b0e9d8fa3a7f8bf0459a6291b2943444c1ac5de507871a0de6a4d25a066770a3c242f2b1a607731a906b4c58e9fa41957ba0def0b414f169dbb07eb5c8108689560300c5baab82c4712dfeff6ace2b8461d18fed972aad7fe976a1c22319d21f1d1dfa026cf4c67447979b1e661272b4c566f4e94bb086021a80d7512e11460fbecc8bd4a4139d80756c3775a1b0edc5bbb7b9e4ad63917a8ce009bc82e9eaf82220abc8334a2c5eb0644a552f57e4996ad1b1530e0c4c1c7e07dea6d8c603ad10fcfae9abdc6813d8bfef62191fb8e66fa10c6310f88964e1f5e421acdd0bdee571d5c093edec7736486a02ea1bb79fcf53c18384db180507888fb8dd71c86e72dd2448972315c9da20195d151c67f8bc7ab1dad0f92afbcd5de78996a5e59249b556d60a9e09f3666c93aba01c685615a229a096ddf800f82f99837f5fd60eed0626b6a7804c848b024b3bee3b001f865a82eec31b41c85899fad57e1aa82992d9f26178b72ad9e25bd2f7e3707711183f870385b0030bc9b5f6d2ea8dd39cec8829deaa1946e3fc473c7b7a8190ef01f93dbe21f3fffabb49fa58edc98c1c57d934c2b598096be3e19a76f44fa96d509e03515d141d5d8e7aeecee28af0bb9f85098c487ee40b3882db2526a

private def light (n : ℕ) : Bool :=
  if n≤154 then decide n.Prime else n.gcd 30897696138473508879585646703632404659201907040888820477871589289865505687886666220300447285640952619071680544337494109264649994680187591361311072737951454695525676891035640863743200899694758450943586711068571022031011228320107310612480000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤23979) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 154 = 30897696138473508879585646703632404659201907040888820477871589289865505687886666220300447285640952619071680544337494109264649994680187591361311072737951454695525676891035640863743200899694758450943586711068571022031011228320107310612480000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 154 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤23979 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 46 := by unfold smallValid; decide +kernel

private theorem sp46 : smallValid 46 47 := by unfold smallValid; decide +kernel

private theorem sp93 : smallValid 93 47 := by unfold smallValid; decide +kernel

private theorem sp140 : smallValid 140 47 := by unfold smallValid; decide +kernel

private theorem sp187 : smallValid 187 46 := by unfold smallValid; decide +kernel

private theorem sp233 : smallValid 233 47 := by unfold smallValid; decide +kernel

private theorem sp280 : smallValid 280 47 := by unfold smallValid; decide +kernel

private theorem sp327 : smallValid 327 47 := by unfold smallValid; decide +kernel

private theorem sp374 : smallValid 374 46 := by unfold smallValid; decide +kernel

private theorem sp420 : smallValid 420 47 := by unfold smallValid; decide +kernel

private theorem sp467 : smallValid 467 47 := by unfold smallValid; decide +kernel

private theorem sp514 : smallValid 514 47 := by unfold smallValid; decide +kernel

private theorem sp561 : smallValid 561 47 := by unfold smallValid; decide +kernel

private theorem sp608 : smallValid 608 47 := by unfold smallValid; decide +kernel

private theorem sp655 : smallValid 655 47 := by unfold smallValid; decide +kernel

private theorem sp702 : smallValid 702 47 := by unfold smallValid; decide +kernel

private theorem sp749 : smallValid 749 46 := by unfold smallValid; decide +kernel

private theorem sp795 : smallValid 795 47 := by unfold smallValid; decide +kernel

private theorem sp842 : smallValid 842 47 := by unfold smallValid; decide +kernel

private theorem sp889 : smallValid 889 47 := by unfold smallValid; decide +kernel

private theorem sp936 : smallValid 936 46 := by unfold smallValid; decide +kernel

private theorem sp982 : smallValid 982 47 := by unfold smallValid; decide +kernel

private theorem sp1029 : smallValid 1029 47 := by unfold smallValid; decide +kernel

private theorem sp1076 : smallValid 1076 47 := by unfold smallValid; decide +kernel

private theorem sp1123 : smallValid 1123 46 := by unfold smallValid; decide +kernel

private theorem sp1169 : smallValid 1169 47 := by unfold smallValid; decide +kernel

private theorem sp1216 : smallValid 1216 47 := by unfold smallValid; decide +kernel

private theorem sp1263 : smallValid 1263 47 := by unfold smallValid; decide +kernel

private theorem sp1310 : smallValid 1310 47 := by unfold smallValid; decide +kernel

private theorem sp1357 : smallValid 1357 47 := by unfold smallValid; decide +kernel

private theorem sp1404 : smallValid 1404 47 := by unfold smallValid; decide +kernel

private theorem sp1451 : smallValid 1451 47 := by unfold smallValid; decide +kernel

private theorem sp1498 : smallValid 1498 46 := by unfold smallValid; decide +kernel

private theorem sp1544 : smallValid 1544 47 := by unfold smallValid; decide +kernel

private theorem sp1591 : smallValid 1591 47 := by unfold smallValid; decide +kernel

private theorem sp1638 : smallValid 1638 47 := by unfold smallValid; decide +kernel

private theorem sp1685 : smallValid 1685 46 := by unfold smallValid; decide +kernel

private theorem sp1731 : smallValid 1731 47 := by unfold smallValid; decide +kernel

private theorem sp1778 : smallValid 1778 47 := by unfold smallValid; decide +kernel

private theorem sp1825 : smallValid 1825 47 := by unfold smallValid; decide +kernel

private theorem sp1872 : smallValid 1872 46 := by unfold smallValid; decide +kernel

private theorem sp1918 : smallValid 1918 47 := by unfold smallValid; decide +kernel

private theorem sp1965 : smallValid 1965 47 := by unfold smallValid; decide +kernel

private theorem sp2012 : smallValid 2012 47 := by unfold smallValid; decide +kernel

private theorem sp2059 : smallValid 2059 47 := by unfold smallValid; decide +kernel

private theorem sp2106 : smallValid 2106 47 := by unfold smallValid; decide +kernel

private theorem sp2153 : smallValid 2153 47 := by unfold smallValid; decide +kernel

private theorem sp2200 : smallValid 2200 47 := by unfold smallValid; decide +kernel

private theorem sp2247 : smallValid 2247 46 := by unfold smallValid; decide +kernel

private theorem sp2293 : smallValid 2293 47 := by unfold smallValid; decide +kernel

private theorem sp2340 : smallValid 2340 47 := by unfold smallValid; decide +kernel

private theorem sp2387 : smallValid 2387 47 := by unfold smallValid; decide +kernel

private theorem sp2434 : smallValid 2434 47 := by unfold smallValid; decide +kernel

private theorem sp2481 : smallValid 2481 47 := by unfold smallValid; decide +kernel

private theorem sp2528 : smallValid 2528 47 := by unfold smallValid; decide +kernel

private theorem sp2575 : smallValid 2575 47 := by unfold smallValid; decide +kernel

private theorem sp2622 : smallValid 2622 46 := by unfold smallValid; decide +kernel

private theorem sp2668 : smallValid 2668 47 := by unfold smallValid; decide +kernel

private theorem sp2715 : smallValid 2715 47 := by unfold smallValid; decide +kernel

private theorem sp2762 : smallValid 2762 47 := by unfold smallValid; decide +kernel

private theorem sp2809 : smallValid 2809 47 := by unfold smallValid; decide +kernel

private theorem sp2856 : smallValid 2856 47 := by unfold smallValid; decide +kernel

private theorem sp2903 : smallValid 2903 47 := by unfold smallValid; decide +kernel

private theorem sp2950 : smallValid 2950 47 := by unfold smallValid; decide +kernel

private theorem sp2997 : smallValid 2997 46 := by unfold smallValid; decide +kernel

private theorem sp3043 : smallValid 3043 47 := by unfold smallValid; decide +kernel

private theorem sp3090 : smallValid 3090 47 := by unfold smallValid; decide +kernel

private theorem sp3137 : smallValid 3137 47 := by unfold smallValid; decide +kernel

private theorem sp3184 : smallValid 3184 46 := by unfold smallValid; decide +kernel

private theorem sp3230 : smallValid 3230 47 := by unfold smallValid; decide +kernel

private theorem sp3277 : smallValid 3277 47 := by unfold smallValid; decide +kernel

private theorem sp3324 : smallValid 3324 47 := by unfold smallValid; decide +kernel

private theorem sp3371 : smallValid 3371 46 := by unfold smallValid; decide +kernel

private theorem sp3417 : smallValid 3417 47 := by unfold smallValid; decide +kernel

private theorem sp3464 : smallValid 3464 47 := by unfold smallValid; decide +kernel

private theorem sp3511 : smallValid 3511 47 := by unfold smallValid; decide +kernel

private theorem sp3558 : smallValid 3558 47 := by unfold smallValid; decide +kernel

private theorem sp3605 : smallValid 3605 47 := by unfold smallValid; decide +kernel

private theorem sp3652 : smallValid 3652 47 := by unfold smallValid; decide +kernel

private theorem sp3699 : smallValid 3699 47 := by unfold smallValid; decide +kernel

private theorem sp3746 : smallValid 3746 46 := by unfold smallValid; decide +kernel

private theorem sp3792 : smallValid 3792 47 := by unfold smallValid; decide +kernel

private theorem sp3839 : smallValid 3839 47 := by unfold smallValid; decide +kernel

private theorem sp3886 : smallValid 3886 47 := by unfold smallValid; decide +kernel

private theorem sp3933 : smallValid 3933 47 := by unfold smallValid; decide +kernel

private theorem sp3980 : smallValid 3980 47 := by unfold smallValid; decide +kernel

private theorem sp4027 : smallValid 4027 47 := by unfold smallValid; decide +kernel

private theorem sp4074 : smallValid 4074 47 := by unfold smallValid; decide +kernel

private theorem sp4121 : smallValid 4121 46 := by unfold smallValid; decide +kernel

private theorem sp4167 : smallValid 4167 47 := by unfold smallValid; decide +kernel

private theorem sp4214 : smallValid 4214 47 := by unfold smallValid; decide +kernel

private theorem sp4261 : smallValid 4261 47 := by unfold smallValid; decide +kernel

private theorem sp4308 : smallValid 4308 47 := by unfold smallValid; decide +kernel

private theorem sp4355 : smallValid 4355 47 := by unfold smallValid; decide +kernel

private theorem sp4402 : smallValid 4402 47 := by unfold smallValid; decide +kernel

private theorem sp4449 : smallValid 4449 47 := by unfold smallValid; decide +kernel

private theorem sp4496 : smallValid 4496 46 := by unfold smallValid; decide +kernel

private theorem sp4542 : smallValid 4542 47 := by unfold smallValid; decide +kernel

private theorem sp4589 : smallValid 4589 47 := by unfold smallValid; decide +kernel

private theorem sp4636 : smallValid 4636 47 := by unfold smallValid; decide +kernel

private theorem sp4683 : smallValid 4683 46 := by unfold smallValid; decide +kernel

private theorem sp4729 : smallValid 4729 47 := by unfold smallValid; decide +kernel

private theorem sp4776 : smallValid 4776 47 := by unfold smallValid; decide +kernel

private theorem sp4823 : smallValid 4823 47 := by unfold smallValid; decide +kernel

private theorem sp4870 : smallValid 4870 46 := by unfold smallValid; decide +kernel

private theorem sp4916 : smallValid 4916 47 := by unfold smallValid; decide +kernel

private theorem sp4963 : smallValid 4963 47 := by unfold smallValid; decide +kernel

private theorem sp5010 : smallValid 5010 47 := by unfold smallValid; decide +kernel

private theorem sp5057 : smallValid 5057 47 := by unfold smallValid; decide +kernel

private theorem sp5104 : smallValid 5104 47 := by unfold smallValid; decide +kernel

private theorem sp5151 : smallValid 5151 47 := by unfold smallValid; decide +kernel

private theorem sp5198 : smallValid 5198 47 := by unfold smallValid; decide +kernel

private theorem sp5245 : smallValid 5245 46 := by unfold smallValid; decide +kernel

private theorem sp5291 : smallValid 5291 47 := by unfold smallValid; decide +kernel

private theorem sp5338 : smallValid 5338 47 := by unfold smallValid; decide +kernel

private theorem sp5385 : smallValid 5385 47 := by unfold smallValid; decide +kernel

private theorem sp5432 : smallValid 5432 47 := by unfold smallValid; decide +kernel

private theorem sp5479 : smallValid 5479 47 := by unfold smallValid; decide +kernel

private theorem sp5526 : smallValid 5526 47 := by unfold smallValid; decide +kernel

private theorem sp5573 : smallValid 5573 47 := by unfold smallValid; decide +kernel

private theorem sp5620 : smallValid 5620 46 := by unfold smallValid; decide +kernel

private theorem sp5666 : smallValid 5666 47 := by unfold smallValid; decide +kernel

private theorem sp5713 : smallValid 5713 47 := by unfold smallValid; decide +kernel

private theorem sp5760 : smallValid 5760 47 := by unfold smallValid; decide +kernel

private theorem sp5807 : smallValid 5807 47 := by unfold smallValid; decide +kernel

private theorem sp5854 : smallValid 5854 47 := by unfold smallValid; decide +kernel

private theorem sp5901 : smallValid 5901 47 := by unfold smallValid; decide +kernel

private theorem sp5948 : smallValid 5948 47 := by unfold smallValid; decide +kernel

private theorem sp5995 : smallValid 5995 46 := by unfold smallValid; decide +kernel

private theorem sp6041 : smallValid 6041 47 := by unfold smallValid; decide +kernel

private theorem sp6088 : smallValid 6088 47 := by unfold smallValid; decide +kernel

private theorem sp6135 : smallValid 6135 47 := by unfold smallValid; decide +kernel

private theorem sp6182 : smallValid 6182 46 := by unfold smallValid; decide +kernel

private theorem sp6228 : smallValid 6228 47 := by unfold smallValid; decide +kernel

private theorem sp6275 : smallValid 6275 47 := by unfold smallValid; decide +kernel

private theorem sp6322 : smallValid 6322 47 := by unfold smallValid; decide +kernel

private theorem sp6369 : smallValid 6369 46 := by unfold smallValid; decide +kernel

private theorem sp6415 : smallValid 6415 47 := by unfold smallValid; decide +kernel

private theorem sp6462 : smallValid 6462 47 := by unfold smallValid; decide +kernel

private theorem sp6509 : smallValid 6509 47 := by unfold smallValid; decide +kernel

private theorem sp6556 : smallValid 6556 47 := by unfold smallValid; decide +kernel

private theorem sp6603 : smallValid 6603 47 := by unfold smallValid; decide +kernel

private theorem sp6650 : smallValid 6650 47 := by unfold smallValid; decide +kernel

private theorem sp6697 : smallValid 6697 47 := by unfold smallValid; decide +kernel

private theorem sp6744 : smallValid 6744 46 := by unfold smallValid; decide +kernel

private theorem sp6790 : smallValid 6790 47 := by unfold smallValid; decide +kernel

private theorem sp6837 : smallValid 6837 47 := by unfold smallValid; decide +kernel

private theorem sp6884 : smallValid 6884 47 := by unfold smallValid; decide +kernel

private theorem sp6931 : smallValid 6931 46 := by unfold smallValid; decide +kernel

private theorem sp6977 : smallValid 6977 47 := by unfold smallValid; decide +kernel

private theorem sp7024 : smallValid 7024 47 := by unfold smallValid; decide +kernel

private theorem sp7071 : smallValid 7071 47 := by unfold smallValid; decide +kernel

private theorem sp7118 : smallValid 7118 46 := by unfold smallValid; decide +kernel

private theorem sp7164 : smallValid 7164 47 := by unfold smallValid; decide +kernel

private theorem sp7211 : smallValid 7211 47 := by unfold smallValid; decide +kernel

private theorem sp7258 : smallValid 7258 47 := by unfold smallValid; decide +kernel

private theorem sp7305 : smallValid 7305 47 := by unfold smallValid; decide +kernel

private theorem sp7352 : smallValid 7352 47 := by unfold smallValid; decide +kernel

private theorem sp7399 : smallValid 7399 47 := by unfold smallValid; decide +kernel

private theorem sp7446 : smallValid 7446 47 := by unfold smallValid; decide +kernel

private theorem sp7493 : smallValid 7493 46 := by unfold smallValid; decide +kernel

private theorem sp7539 : smallValid 7539 47 := by unfold smallValid; decide +kernel

private theorem sp7586 : smallValid 7586 47 := by unfold smallValid; decide +kernel

private theorem sp7633 : smallValid 7633 47 := by unfold smallValid; decide +kernel

private theorem sp7680 : smallValid 7680 46 := by unfold smallValid; decide +kernel

private theorem sp7726 : smallValid 7726 47 := by unfold smallValid; decide +kernel

private theorem sp7773 : smallValid 7773 47 := by unfold smallValid; decide +kernel

private theorem sp7820 : smallValid 7820 47 := by unfold smallValid; decide +kernel

private theorem sp7867 : smallValid 7867 46 := by unfold smallValid; decide +kernel

private theorem sp7913 : smallValid 7913 47 := by unfold smallValid; decide +kernel

private theorem sp7960 : smallValid 7960 47 := by unfold smallValid; decide +kernel

private theorem sp8007 : smallValid 8007 47 := by unfold smallValid; decide +kernel

private theorem sp8054 : smallValid 8054 47 := by unfold smallValid; decide +kernel

private theorem sp8101 : smallValid 8101 47 := by unfold smallValid; decide +kernel

private theorem sp8148 : smallValid 8148 47 := by unfold smallValid; decide +kernel

private theorem sp8195 : smallValid 8195 47 := by unfold smallValid; decide +kernel

private theorem sp8242 : smallValid 8242 46 := by unfold smallValid; decide +kernel

private theorem sp8288 : smallValid 8288 47 := by unfold smallValid; decide +kernel

private theorem sp8335 : smallValid 8335 47 := by unfold smallValid; decide +kernel

private theorem sp8382 : smallValid 8382 47 := by unfold smallValid; decide +kernel

private theorem sp8429 : smallValid 8429 47 := by unfold smallValid; decide +kernel

private theorem sp8476 : smallValid 8476 47 := by unfold smallValid; decide +kernel

private theorem sp8523 : smallValid 8523 47 := by unfold smallValid; decide +kernel

private theorem sp8570 : smallValid 8570 47 := by unfold smallValid; decide +kernel

private theorem sp8617 : smallValid 8617 46 := by unfold smallValid; decide +kernel

private theorem sp8663 : smallValid 8663 47 := by unfold smallValid; decide +kernel

private theorem sp8710 : smallValid 8710 47 := by unfold smallValid; decide +kernel

private theorem sp8757 : smallValid 8757 47 := by unfold smallValid; decide +kernel

private theorem sp8804 : smallValid 8804 47 := by unfold smallValid; decide +kernel

private theorem sp8851 : smallValid 8851 47 := by unfold smallValid; decide +kernel

private theorem sp8898 : smallValid 8898 47 := by unfold smallValid; decide +kernel

private theorem sp8945 : smallValid 8945 47 := by unfold smallValid; decide +kernel

private theorem sp8992 : smallValid 8992 46 := by unfold smallValid; decide +kernel

private theorem sp9038 : smallValid 9038 47 := by unfold smallValid; decide +kernel

private theorem sp9085 : smallValid 9085 47 := by unfold smallValid; decide +kernel

private theorem sp9132 : smallValid 9132 47 := by unfold smallValid; decide +kernel

private theorem sp9179 : smallValid 9179 46 := by unfold smallValid; decide +kernel

private theorem sp9225 : smallValid 9225 47 := by unfold smallValid; decide +kernel

private theorem sp9272 : smallValid 9272 47 := by unfold smallValid; decide +kernel

private theorem sp9319 : smallValid 9319 47 := by unfold smallValid; decide +kernel

private theorem sp9366 : smallValid 9366 46 := by unfold smallValid; decide +kernel

private theorem sp9412 : smallValid 9412 47 := by unfold smallValid; decide +kernel

private theorem sp9459 : smallValid 9459 47 := by unfold smallValid; decide +kernel

private theorem sp9506 : smallValid 9506 47 := by unfold smallValid; decide +kernel

private theorem sp9553 : smallValid 9553 47 := by unfold smallValid; decide +kernel

private theorem sp9600 : smallValid 9600 47 := by unfold smallValid; decide +kernel

private theorem sp9647 : smallValid 9647 47 := by unfold smallValid; decide +kernel

private theorem sp9694 : smallValid 9694 47 := by unfold smallValid; decide +kernel

private theorem sp9741 : smallValid 9741 46 := by unfold smallValid; decide +kernel

private theorem sp9787 : smallValid 9787 47 := by unfold smallValid; decide +kernel

private theorem sp9834 : smallValid 9834 47 := by unfold smallValid; decide +kernel

private theorem sp9881 : smallValid 9881 47 := by unfold smallValid; decide +kernel

private theorem sp9928 : smallValid 9928 47 := by unfold smallValid; decide +kernel

private theorem sp9975 : smallValid 9975 47 := by unfold smallValid; decide +kernel

private theorem sp10022 : smallValid 10022 47 := by unfold smallValid; decide +kernel

private theorem sp10069 : smallValid 10069 47 := by unfold smallValid; decide +kernel

private theorem sp10116 : smallValid 10116 46 := by unfold smallValid; decide +kernel

private theorem sp10162 : smallValid 10162 47 := by unfold smallValid; decide +kernel

private theorem sp10209 : smallValid 10209 47 := by unfold smallValid; decide +kernel

private theorem sp10256 : smallValid 10256 47 := by unfold smallValid; decide +kernel

private theorem sp10303 : smallValid 10303 47 := by unfold smallValid; decide +kernel

private theorem sp10350 : smallValid 10350 47 := by unfold smallValid; decide +kernel

private theorem sp10397 : smallValid 10397 47 := by unfold smallValid; decide +kernel

private theorem sp10444 : smallValid 10444 47 := by unfold smallValid; decide +kernel

private theorem sp10491 : smallValid 10491 46 := by unfold smallValid; decide +kernel

private theorem sp10537 : smallValid 10537 47 := by unfold smallValid; decide +kernel

private theorem sp10584 : smallValid 10584 47 := by unfold smallValid; decide +kernel

private theorem sp10631 : smallValid 10631 47 := by unfold smallValid; decide +kernel

private theorem sp10678 : smallValid 10678 46 := by unfold smallValid; decide +kernel

private theorem sp10724 : smallValid 10724 47 := by unfold smallValid; decide +kernel

private theorem sp10771 : smallValid 10771 47 := by unfold smallValid; decide +kernel

private theorem sp10818 : smallValid 10818 47 := by unfold smallValid; decide +kernel

private theorem sp10865 : smallValid 10865 46 := by unfold smallValid; decide +kernel

private theorem sp10911 : smallValid 10911 47 := by unfold smallValid; decide +kernel

private theorem sp10958 : smallValid 10958 47 := by unfold smallValid; decide +kernel

private theorem sp11005 : smallValid 11005 47 := by unfold smallValid; decide +kernel

private theorem sp11052 : smallValid 11052 47 := by unfold smallValid; decide +kernel

private theorem sp11099 : smallValid 11099 47 := by unfold smallValid; decide +kernel

private theorem sp11146 : smallValid 11146 47 := by unfold smallValid; decide +kernel

private theorem sp11193 : smallValid 11193 47 := by unfold smallValid; decide +kernel

private theorem sp11240 : smallValid 11240 46 := by unfold smallValid; decide +kernel

private theorem sp11286 : smallValid 11286 47 := by unfold smallValid; decide +kernel

private theorem sp11333 : smallValid 11333 47 := by unfold smallValid; decide +kernel

private theorem sp11380 : smallValid 11380 47 := by unfold smallValid; decide +kernel

private theorem sp11427 : smallValid 11427 47 := by unfold smallValid; decide +kernel

private theorem sp11474 : smallValid 11474 47 := by unfold smallValid; decide +kernel

private theorem sp11521 : smallValid 11521 47 := by unfold smallValid; decide +kernel

private theorem sp11568 : smallValid 11568 47 := by unfold smallValid; decide +kernel

private theorem sp11615 : smallValid 11615 46 := by unfold smallValid; decide +kernel

private theorem sp11661 : smallValid 11661 47 := by unfold smallValid; decide +kernel

private theorem sp11708 : smallValid 11708 47 := by unfold smallValid; decide +kernel

private theorem sp11755 : smallValid 11755 47 := by unfold smallValid; decide +kernel

private theorem sp11802 : smallValid 11802 47 := by unfold smallValid; decide +kernel

private theorem sp11849 : smallValid 11849 47 := by unfold smallValid; decide +kernel

private theorem sp11896 : smallValid 11896 47 := by unfold smallValid; decide +kernel

private theorem sp11943 : smallValid 11943 47 := by unfold smallValid; decide +kernel

private theorem sp11990 : smallValid 11990 46 := by unfold smallValid; decide +kernel

private theorem sp12036 : smallValid 12036 47 := by unfold smallValid; decide +kernel

private theorem sp12083 : smallValid 12083 47 := by unfold smallValid; decide +kernel

private theorem sp12130 : smallValid 12130 47 := by unfold smallValid; decide +kernel

private theorem sp12177 : smallValid 12177 46 := by unfold smallValid; decide +kernel

private theorem sp12223 : smallValid 12223 47 := by unfold smallValid; decide +kernel

private theorem sp12270 : smallValid 12270 47 := by unfold smallValid; decide +kernel

private theorem sp12317 : smallValid 12317 47 := by unfold smallValid; decide +kernel

private theorem sp12364 : smallValid 12364 46 := by unfold smallValid; decide +kernel

private theorem sp12410 : smallValid 12410 47 := by unfold smallValid; decide +kernel

private theorem sp12457 : smallValid 12457 47 := by unfold smallValid; decide +kernel

private theorem sp12504 : smallValid 12504 47 := by unfold smallValid; decide +kernel

private theorem sp12551 : smallValid 12551 47 := by unfold smallValid; decide +kernel

private theorem sp12598 : smallValid 12598 47 := by unfold smallValid; decide +kernel

private theorem sp12645 : smallValid 12645 47 := by unfold smallValid; decide +kernel

private theorem sp12692 : smallValid 12692 47 := by unfold smallValid; decide +kernel

private theorem sp12739 : smallValid 12739 46 := by unfold smallValid; decide +kernel

private theorem sp12785 : smallValid 12785 47 := by unfold smallValid; decide +kernel

private theorem sp12832 : smallValid 12832 47 := by unfold smallValid; decide +kernel

private theorem sp12879 : smallValid 12879 47 := by unfold smallValid; decide +kernel

private theorem sp12926 : smallValid 12926 46 := by unfold smallValid; decide +kernel

private theorem sp12972 : smallValid 12972 47 := by unfold smallValid; decide +kernel

private theorem sp13019 : smallValid 13019 47 := by unfold smallValid; decide +kernel

private theorem sp13066 : smallValid 13066 47 := by unfold smallValid; decide +kernel

private theorem sp13113 : smallValid 13113 46 := by unfold smallValid; decide +kernel

private theorem sp13159 : smallValid 13159 47 := by unfold smallValid; decide +kernel

private theorem sp13206 : smallValid 13206 47 := by unfold smallValid; decide +kernel

private theorem sp13253 : smallValid 13253 47 := by unfold smallValid; decide +kernel

private theorem sp13300 : smallValid 13300 47 := by unfold smallValid; decide +kernel

private theorem sp13347 : smallValid 13347 47 := by unfold smallValid; decide +kernel

private theorem sp13394 : smallValid 13394 47 := by unfold smallValid; decide +kernel

private theorem sp13441 : smallValid 13441 47 := by unfold smallValid; decide +kernel

private theorem sp13488 : smallValid 13488 46 := by unfold smallValid; decide +kernel

private theorem sp13534 : smallValid 13534 47 := by unfold smallValid; decide +kernel

private theorem sp13581 : smallValid 13581 47 := by unfold smallValid; decide +kernel

private theorem sp13628 : smallValid 13628 47 := by unfold smallValid; decide +kernel

private theorem sp13675 : smallValid 13675 46 := by unfold smallValid; decide +kernel

private theorem sp13721 : smallValid 13721 47 := by unfold smallValid; decide +kernel

private theorem sp13768 : smallValid 13768 47 := by unfold smallValid; decide +kernel

private theorem sp13815 : smallValid 13815 47 := by unfold smallValid; decide +kernel

private theorem sp13862 : smallValid 13862 46 := by unfold smallValid; decide +kernel

private theorem sp13908 : smallValid 13908 47 := by unfold smallValid; decide +kernel

private theorem sp13955 : smallValid 13955 47 := by unfold smallValid; decide +kernel

private theorem sp14002 : smallValid 14002 47 := by unfold smallValid; decide +kernel

private theorem sp14049 : smallValid 14049 47 := by unfold smallValid; decide +kernel

private theorem sp14096 : smallValid 14096 47 := by unfold smallValid; decide +kernel

private theorem sp14143 : smallValid 14143 47 := by unfold smallValid; decide +kernel

private theorem sp14190 : smallValid 14190 47 := by unfold smallValid; decide +kernel

private theorem sp14237 : smallValid 14237 46 := by unfold smallValid; decide +kernel

private theorem sp14283 : smallValid 14283 47 := by unfold smallValid; decide +kernel

private theorem sp14330 : smallValid 14330 47 := by unfold smallValid; decide +kernel

private theorem sp14377 : smallValid 14377 47 := by unfold smallValid; decide +kernel

private theorem sp14424 : smallValid 14424 47 := by unfold smallValid; decide +kernel

private theorem sp14471 : smallValid 14471 47 := by unfold smallValid; decide +kernel

private theorem sp14518 : smallValid 14518 47 := by unfold smallValid; decide +kernel

private theorem sp14565 : smallValid 14565 47 := by unfold smallValid; decide +kernel

private theorem sp14612 : smallValid 14612 46 := by unfold smallValid; decide +kernel

private theorem sp14658 : smallValid 14658 47 := by unfold smallValid; decide +kernel

private theorem sp14705 : smallValid 14705 47 := by unfold smallValid; decide +kernel

private theorem sp14752 : smallValid 14752 47 := by unfold smallValid; decide +kernel

private theorem sp14799 : smallValid 14799 47 := by unfold smallValid; decide +kernel

private theorem sp14846 : smallValid 14846 47 := by unfold smallValid; decide +kernel

private theorem sp14893 : smallValid 14893 47 := by unfold smallValid; decide +kernel

private theorem sp14940 : smallValid 14940 47 := by unfold smallValid; decide +kernel

private theorem sp14987 : smallValid 14987 46 := by unfold smallValid; decide +kernel

private theorem sp15033 : smallValid 15033 47 := by unfold smallValid; decide +kernel

private theorem sp15080 : smallValid 15080 47 := by unfold smallValid; decide +kernel

private theorem sp15127 : smallValid 15127 47 := by unfold smallValid; decide +kernel

private theorem sp15174 : smallValid 15174 46 := by unfold smallValid; decide +kernel

private theorem sp15220 : smallValid 15220 47 := by unfold smallValid; decide +kernel

private theorem sp15267 : smallValid 15267 47 := by unfold smallValid; decide +kernel

private theorem sp15314 : smallValid 15314 47 := by unfold smallValid; decide +kernel

private theorem sp15361 : smallValid 15361 46 := by unfold smallValid; decide +kernel

private theorem sp15407 : smallValid 15407 47 := by unfold smallValid; decide +kernel

private theorem sp15454 : smallValid 15454 47 := by unfold smallValid; decide +kernel

private theorem sp15501 : smallValid 15501 47 := by unfold smallValid; decide +kernel

private theorem sp15548 : smallValid 15548 47 := by unfold smallValid; decide +kernel

private theorem sp15595 : smallValid 15595 47 := by unfold smallValid; decide +kernel

private theorem sp15642 : smallValid 15642 47 := by unfold smallValid; decide +kernel

private theorem sp15689 : smallValid 15689 47 := by unfold smallValid; decide +kernel

private theorem sp15736 : smallValid 15736 46 := by unfold smallValid; decide +kernel

private theorem sp15782 : smallValid 15782 47 := by unfold smallValid; decide +kernel

private theorem sp15829 : smallValid 15829 47 := by unfold smallValid; decide +kernel

private theorem sp15876 : smallValid 15876 47 := by unfold smallValid; decide +kernel

private theorem sp15923 : smallValid 15923 47 := by unfold smallValid; decide +kernel

private theorem sp15970 : smallValid 15970 47 := by unfold smallValid; decide +kernel

private theorem sp16017 : smallValid 16017 47 := by unfold smallValid; decide +kernel

private theorem sp16064 : smallValid 16064 47 := by unfold smallValid; decide +kernel

private theorem sp16111 : smallValid 16111 46 := by unfold smallValid; decide +kernel

private theorem sp16157 : smallValid 16157 47 := by unfold smallValid; decide +kernel

private theorem sp16204 : smallValid 16204 47 := by unfold smallValid; decide +kernel

private theorem sp16251 : smallValid 16251 47 := by unfold smallValid; decide +kernel

private theorem sp16298 : smallValid 16298 47 := by unfold smallValid; decide +kernel

private theorem sp16345 : smallValid 16345 47 := by unfold smallValid; decide +kernel

private theorem sp16392 : smallValid 16392 47 := by unfold smallValid; decide +kernel

private theorem sp16439 : smallValid 16439 47 := by unfold smallValid; decide +kernel

private theorem sp16486 : smallValid 16486 46 := by unfold smallValid; decide +kernel

private theorem sp16532 : smallValid 16532 47 := by unfold smallValid; decide +kernel

private theorem sp16579 : smallValid 16579 47 := by unfold smallValid; decide +kernel

private theorem sp16626 : smallValid 16626 47 := by unfold smallValid; decide +kernel

private theorem sp16673 : smallValid 16673 46 := by unfold smallValid; decide +kernel

private theorem sp16719 : smallValid 16719 47 := by unfold smallValid; decide +kernel

private theorem sp16766 : smallValid 16766 47 := by unfold smallValid; decide +kernel

private theorem sp16813 : smallValid 16813 47 := by unfold smallValid; decide +kernel

private theorem sp16860 : smallValid 16860 46 := by unfold smallValid; decide +kernel

private theorem sp16906 : smallValid 16906 47 := by unfold smallValid; decide +kernel

private theorem sp16953 : smallValid 16953 47 := by unfold smallValid; decide +kernel

private theorem sp17000 : smallValid 17000 47 := by unfold smallValid; decide +kernel

private theorem sp17047 : smallValid 17047 47 := by unfold smallValid; decide +kernel

private theorem sp17094 : smallValid 17094 47 := by unfold smallValid; decide +kernel

private theorem sp17141 : smallValid 17141 47 := by unfold smallValid; decide +kernel

private theorem sp17188 : smallValid 17188 47 := by unfold smallValid; decide +kernel

private theorem sp17235 : smallValid 17235 46 := by unfold smallValid; decide +kernel

private theorem sp17281 : smallValid 17281 47 := by unfold smallValid; decide +kernel

private theorem sp17328 : smallValid 17328 47 := by unfold smallValid; decide +kernel

private theorem sp17375 : smallValid 17375 47 := by unfold smallValid; decide +kernel

private theorem sp17422 : smallValid 17422 47 := by unfold smallValid; decide +kernel

private theorem sp17469 : smallValid 17469 47 := by unfold smallValid; decide +kernel

private theorem sp17516 : smallValid 17516 47 := by unfold smallValid; decide +kernel

private theorem sp17563 : smallValid 17563 47 := by unfold smallValid; decide +kernel

private theorem sp17610 : smallValid 17610 46 := by unfold smallValid; decide +kernel

private theorem sp17656 : smallValid 17656 47 := by unfold smallValid; decide +kernel

private theorem sp17703 : smallValid 17703 47 := by unfold smallValid; decide +kernel

private theorem sp17750 : smallValid 17750 47 := by unfold smallValid; decide +kernel

private theorem sp17797 : smallValid 17797 47 := by unfold smallValid; decide +kernel

private theorem sp17844 : smallValid 17844 47 := by unfold smallValid; decide +kernel

private theorem sp17891 : smallValid 17891 47 := by unfold smallValid; decide +kernel

private theorem sp17938 : smallValid 17938 47 := by unfold smallValid; decide +kernel

private theorem sp17985 : smallValid 17985 46 := by unfold smallValid; decide +kernel

private theorem sp18031 : smallValid 18031 47 := by unfold smallValid; decide +kernel

private theorem sp18078 : smallValid 18078 47 := by unfold smallValid; decide +kernel

private theorem sp18125 : smallValid 18125 47 := by unfold smallValid; decide +kernel

private theorem sp18172 : smallValid 18172 46 := by unfold smallValid; decide +kernel

private theorem sp18218 : smallValid 18218 47 := by unfold smallValid; decide +kernel

private theorem sp18265 : smallValid 18265 47 := by unfold smallValid; decide +kernel

private theorem sp18312 : smallValid 18312 47 := by unfold smallValid; decide +kernel

private theorem sp18359 : smallValid 18359 46 := by unfold smallValid; decide +kernel

private theorem sp18405 : smallValid 18405 47 := by unfold smallValid; decide +kernel

private theorem sp18452 : smallValid 18452 47 := by unfold smallValid; decide +kernel

private theorem sp18499 : smallValid 18499 47 := by unfold smallValid; decide +kernel

private theorem sp18546 : smallValid 18546 47 := by unfold smallValid; decide +kernel

private theorem sp18593 : smallValid 18593 47 := by unfold smallValid; decide +kernel

private theorem sp18640 : smallValid 18640 47 := by unfold smallValid; decide +kernel

private theorem sp18687 : smallValid 18687 47 := by unfold smallValid; decide +kernel

private theorem sp18734 : smallValid 18734 46 := by unfold smallValid; decide +kernel

private theorem sp18780 : smallValid 18780 47 := by unfold smallValid; decide +kernel

private theorem sp18827 : smallValid 18827 47 := by unfold smallValid; decide +kernel

private theorem sp18874 : smallValid 18874 47 := by unfold smallValid; decide +kernel

private theorem sp18921 : smallValid 18921 46 := by unfold smallValid; decide +kernel

private theorem sp18967 : smallValid 18967 47 := by unfold smallValid; decide +kernel

private theorem sp19014 : smallValid 19014 47 := by unfold smallValid; decide +kernel

private theorem sp19061 : smallValid 19061 47 := by unfold smallValid; decide +kernel

private theorem sp19108 : smallValid 19108 46 := by unfold smallValid; decide +kernel

private theorem sp19154 : smallValid 19154 47 := by unfold smallValid; decide +kernel

private theorem sp19201 : smallValid 19201 47 := by unfold smallValid; decide +kernel

private theorem sp19248 : smallValid 19248 47 := by unfold smallValid; decide +kernel

private theorem sp19295 : smallValid 19295 47 := by unfold smallValid; decide +kernel

private theorem sp19342 : smallValid 19342 47 := by unfold smallValid; decide +kernel

private theorem sp19389 : smallValid 19389 47 := by unfold smallValid; decide +kernel

private theorem sp19436 : smallValid 19436 47 := by unfold smallValid; decide +kernel

private theorem sp19483 : smallValid 19483 46 := by unfold smallValid; decide +kernel

private theorem sp19529 : smallValid 19529 47 := by unfold smallValid; decide +kernel

private theorem sp19576 : smallValid 19576 47 := by unfold smallValid; decide +kernel

private theorem sp19623 : smallValid 19623 47 := by unfold smallValid; decide +kernel

private theorem sp19670 : smallValid 19670 46 := by unfold smallValid; decide +kernel

private theorem sp19716 : smallValid 19716 47 := by unfold smallValid; decide +kernel

private theorem sp19763 : smallValid 19763 47 := by unfold smallValid; decide +kernel

private theorem sp19810 : smallValid 19810 47 := by unfold smallValid; decide +kernel

private theorem sp19857 : smallValid 19857 46 := by unfold smallValid; decide +kernel

private theorem sp19903 : smallValid 19903 47 := by unfold smallValid; decide +kernel

private theorem sp19950 : smallValid 19950 47 := by unfold smallValid; decide +kernel

private theorem sp19997 : smallValid 19997 47 := by unfold smallValid; decide +kernel

private theorem sp20044 : smallValid 20044 47 := by unfold smallValid; decide +kernel

private theorem sp20091 : smallValid 20091 47 := by unfold smallValid; decide +kernel

private theorem sp20138 : smallValid 20138 47 := by unfold smallValid; decide +kernel

private theorem sp20185 : smallValid 20185 47 := by unfold smallValid; decide +kernel

private theorem sp20232 : smallValid 20232 46 := by unfold smallValid; decide +kernel

private theorem sp20278 : smallValid 20278 47 := by unfold smallValid; decide +kernel

private theorem sp20325 : smallValid 20325 47 := by unfold smallValid; decide +kernel

private theorem sp20372 : smallValid 20372 47 := by unfold smallValid; decide +kernel

private theorem sp20419 : smallValid 20419 47 := by unfold smallValid; decide +kernel

private theorem sp20466 : smallValid 20466 47 := by unfold smallValid; decide +kernel

private theorem sp20513 : smallValid 20513 47 := by unfold smallValid; decide +kernel

private theorem sp20560 : smallValid 20560 47 := by unfold smallValid; decide +kernel

private theorem sp20607 : smallValid 20607 46 := by unfold smallValid; decide +kernel

private theorem sp20653 : smallValid 20653 47 := by unfold smallValid; decide +kernel

private theorem sp20700 : smallValid 20700 47 := by unfold smallValid; decide +kernel

private theorem sp20747 : smallValid 20747 47 := by unfold smallValid; decide +kernel

private theorem sp20794 : smallValid 20794 47 := by unfold smallValid; decide +kernel

private theorem sp20841 : smallValid 20841 47 := by unfold smallValid; decide +kernel

private theorem sp20888 : smallValid 20888 47 := by unfold smallValid; decide +kernel

private theorem sp20935 : smallValid 20935 47 := by unfold smallValid; decide +kernel

private theorem sp20982 : smallValid 20982 46 := by unfold smallValid; decide +kernel

private theorem sp21028 : smallValid 21028 47 := by unfold smallValid; decide +kernel

private theorem sp21075 : smallValid 21075 47 := by unfold smallValid; decide +kernel

private theorem sp21122 : smallValid 21122 47 := by unfold smallValid; decide +kernel

private theorem sp21169 : smallValid 21169 46 := by unfold smallValid; decide +kernel

private theorem sp21215 : smallValid 21215 47 := by unfold smallValid; decide +kernel

private theorem sp21262 : smallValid 21262 47 := by unfold smallValid; decide +kernel

private theorem sp21309 : smallValid 21309 47 := by unfold smallValid; decide +kernel

private theorem sp21356 : smallValid 21356 46 := by unfold smallValid; decide +kernel

private theorem sp21402 : smallValid 21402 47 := by unfold smallValid; decide +kernel

private theorem sp21449 : smallValid 21449 47 := by unfold smallValid; decide +kernel

private theorem sp21496 : smallValid 21496 47 := by unfold smallValid; decide +kernel

private theorem sp21543 : smallValid 21543 47 := by unfold smallValid; decide +kernel

private theorem sp21590 : smallValid 21590 47 := by unfold smallValid; decide +kernel

private theorem sp21637 : smallValid 21637 47 := by unfold smallValid; decide +kernel

private theorem sp21684 : smallValid 21684 47 := by unfold smallValid; decide +kernel

private theorem sp21731 : smallValid 21731 46 := by unfold smallValid; decide +kernel

private theorem sp21777 : smallValid 21777 47 := by unfold smallValid; decide +kernel

private theorem sp21824 : smallValid 21824 47 := by unfold smallValid; decide +kernel

private theorem sp21871 : smallValid 21871 47 := by unfold smallValid; decide +kernel

private theorem sp21918 : smallValid 21918 47 := by unfold smallValid; decide +kernel

private theorem sp21965 : smallValid 21965 47 := by unfold smallValid; decide +kernel

private theorem sp22012 : smallValid 22012 47 := by unfold smallValid; decide +kernel

private theorem sp22059 : smallValid 22059 47 := by unfold smallValid; decide +kernel

private theorem sp22106 : smallValid 22106 46 := by unfold smallValid; decide +kernel

private theorem sp22152 : smallValid 22152 47 := by unfold smallValid; decide +kernel

private theorem sp22199 : smallValid 22199 47 := by unfold smallValid; decide +kernel

private theorem sp22246 : smallValid 22246 47 := by unfold smallValid; decide +kernel

private theorem sp22293 : smallValid 22293 47 := by unfold smallValid; decide +kernel

private theorem sp22340 : smallValid 22340 47 := by unfold smallValid; decide +kernel

private theorem sp22387 : smallValid 22387 47 := by unfold smallValid; decide +kernel

private theorem sp22434 : smallValid 22434 47 := by unfold smallValid; decide +kernel

private theorem sp22481 : smallValid 22481 46 := by unfold smallValid; decide +kernel

private theorem sp22527 : smallValid 22527 47 := by unfold smallValid; decide +kernel

private theorem sp22574 : smallValid 22574 47 := by unfold smallValid; decide +kernel

private theorem sp22621 : smallValid 22621 47 := by unfold smallValid; decide +kernel

private theorem sp22668 : smallValid 22668 46 := by unfold smallValid; decide +kernel

private theorem sp22714 : smallValid 22714 47 := by unfold smallValid; decide +kernel

private theorem sp22761 : smallValid 22761 47 := by unfold smallValid; decide +kernel

private theorem sp22808 : smallValid 22808 47 := by unfold smallValid; decide +kernel

private theorem sp22855 : smallValid 22855 46 := by unfold smallValid; decide +kernel

private theorem sp22901 : smallValid 22901 47 := by unfold smallValid; decide +kernel

private theorem sp22948 : smallValid 22948 47 := by unfold smallValid; decide +kernel

private theorem sp22995 : smallValid 22995 47 := by unfold smallValid; decide +kernel

private theorem sp23042 : smallValid 23042 47 := by unfold smallValid; decide +kernel

private theorem sp23089 : smallValid 23089 47 := by unfold smallValid; decide +kernel

private theorem sp23136 : smallValid 23136 47 := by unfold smallValid; decide +kernel

private theorem sp23183 : smallValid 23183 47 := by unfold smallValid; decide +kernel

private theorem sp23230 : smallValid 23230 46 := by unfold smallValid; decide +kernel

private theorem sp23276 : smallValid 23276 47 := by unfold smallValid; decide +kernel

private theorem sp23323 : smallValid 23323 47 := by unfold smallValid; decide +kernel

private theorem sp23370 : smallValid 23370 47 := by unfold smallValid; decide +kernel

private theorem sp23417 : smallValid 23417 47 := by unfold smallValid; decide +kernel

private theorem sp23464 : smallValid 23464 47 := by unfold smallValid; decide +kernel

private theorem sp23511 : smallValid 23511 47 := by unfold smallValid; decide +kernel

private theorem sp23558 : smallValid 23558 47 := by unfold smallValid; decide +kernel

private theorem sp23605 : smallValid 23605 46 := by unfold smallValid; decide +kernel

private theorem sp23651 : smallValid 23651 47 := by unfold smallValid; decide +kernel

private theorem sp23698 : smallValid 23698 47 := by unfold smallValid; decide +kernel

private theorem sp23745 : smallValid 23745 47 := by unfold smallValid; decide +kernel

private theorem sp23792 : smallValid 23792 47 := by unfold smallValid; decide +kernel

private theorem sp23839 : smallValid 23839 47 := by unfold smallValid; decide +kernel

private theorem sp23886 : smallValid 23886 47 := by unfold smallValid; decide +kernel

private theorem sp23933 : smallValid 23933 47 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤23979) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 23980 := (joinSmall (lo:=0) (a:=11990) (b:=11990) (joinSmall (lo:=0) (a:=5995) (b:=5995) (joinSmall (lo:=0) (a:=2997) (b:=2998) (joinSmall (lo:=0) (a:=1498) (b:=1499) (joinSmall (lo:=0) (a:=749) (b:=749) (joinSmall (lo:=0) (a:=374) (b:=375) (joinSmall (lo:=0) (a:=187) (b:=187) (joinSmall (lo:=0) (a:=93) (b:=94) (joinSmall (lo:=0) (a:=46) (b:=47) sp0 sp46) (joinSmall (lo:=93) (a:=47) (b:=47) sp93 sp140)) (joinSmall (lo:=187) (a:=93) (b:=94) (joinSmall (lo:=187) (a:=46) (b:=47) sp187 sp233) (joinSmall (lo:=280) (a:=47) (b:=47) sp280 sp327))) (joinSmall (lo:=374) (a:=187) (b:=188) (joinSmall (lo:=374) (a:=93) (b:=94) (joinSmall (lo:=374) (a:=46) (b:=47) sp374 sp420) (joinSmall (lo:=467) (a:=47) (b:=47) sp467 sp514)) (joinSmall (lo:=561) (a:=94) (b:=94) (joinSmall (lo:=561) (a:=47) (b:=47) sp561 sp608) (joinSmall (lo:=655) (a:=47) (b:=47) sp655 sp702)))) (joinSmall (lo:=749) (a:=374) (b:=375) (joinSmall (lo:=749) (a:=187) (b:=187) (joinSmall (lo:=749) (a:=93) (b:=94) (joinSmall (lo:=749) (a:=46) (b:=47) sp749 sp795) (joinSmall (lo:=842) (a:=47) (b:=47) sp842 sp889)) (joinSmall (lo:=936) (a:=93) (b:=94) (joinSmall (lo:=936) (a:=46) (b:=47) sp936 sp982) (joinSmall (lo:=1029) (a:=47) (b:=47) sp1029 sp1076))) (joinSmall (lo:=1123) (a:=187) (b:=188) (joinSmall (lo:=1123) (a:=93) (b:=94) (joinSmall (lo:=1123) (a:=46) (b:=47) sp1123 sp1169) (joinSmall (lo:=1216) (a:=47) (b:=47) sp1216 sp1263)) (joinSmall (lo:=1310) (a:=94) (b:=94) (joinSmall (lo:=1310) (a:=47) (b:=47) sp1310 sp1357) (joinSmall (lo:=1404) (a:=47) (b:=47) sp1404 sp1451))))) (joinSmall (lo:=1498) (a:=749) (b:=750) (joinSmall (lo:=1498) (a:=374) (b:=375) (joinSmall (lo:=1498) (a:=187) (b:=187) (joinSmall (lo:=1498) (a:=93) (b:=94) (joinSmall (lo:=1498) (a:=46) (b:=47) sp1498 sp1544) (joinSmall (lo:=1591) (a:=47) (b:=47) sp1591 sp1638)) (joinSmall (lo:=1685) (a:=93) (b:=94) (joinSmall (lo:=1685) (a:=46) (b:=47) sp1685 sp1731) (joinSmall (lo:=1778) (a:=47) (b:=47) sp1778 sp1825))) (joinSmall (lo:=1872) (a:=187) (b:=188) (joinSmall (lo:=1872) (a:=93) (b:=94) (joinSmall (lo:=1872) (a:=46) (b:=47) sp1872 sp1918) (joinSmall (lo:=1965) (a:=47) (b:=47) sp1965 sp2012)) (joinSmall (lo:=2059) (a:=94) (b:=94) (joinSmall (lo:=2059) (a:=47) (b:=47) sp2059 sp2106) (joinSmall (lo:=2153) (a:=47) (b:=47) sp2153 sp2200)))) (joinSmall (lo:=2247) (a:=375) (b:=375) (joinSmall (lo:=2247) (a:=187) (b:=188) (joinSmall (lo:=2247) (a:=93) (b:=94) (joinSmall (lo:=2247) (a:=46) (b:=47) sp2247 sp2293) (joinSmall (lo:=2340) (a:=47) (b:=47) sp2340 sp2387)) (joinSmall (lo:=2434) (a:=94) (b:=94) (joinSmall (lo:=2434) (a:=47) (b:=47) sp2434 sp2481) (joinSmall (lo:=2528) (a:=47) (b:=47) sp2528 sp2575))) (joinSmall (lo:=2622) (a:=187) (b:=188) (joinSmall (lo:=2622) (a:=93) (b:=94) (joinSmall (lo:=2622) (a:=46) (b:=47) sp2622 sp2668) (joinSmall (lo:=2715) (a:=47) (b:=47) sp2715 sp2762)) (joinSmall (lo:=2809) (a:=94) (b:=94) (joinSmall (lo:=2809) (a:=47) (b:=47) sp2809 sp2856) (joinSmall (lo:=2903) (a:=47) (b:=47) sp2903 sp2950)))))) (joinSmall (lo:=2997) (a:=1499) (b:=1499) (joinSmall (lo:=2997) (a:=749) (b:=750) (joinSmall (lo:=2997) (a:=374) (b:=375) (joinSmall (lo:=2997) (a:=187) (b:=187) (joinSmall (lo:=2997) (a:=93) (b:=94) (joinSmall (lo:=2997) (a:=46) (b:=47) sp2997 sp3043) (joinSmall (lo:=3090) (a:=47) (b:=47) sp3090 sp3137)) (joinSmall (lo:=3184) (a:=93) (b:=94) (joinSmall (lo:=3184) (a:=46) (b:=47) sp3184 sp3230) (joinSmall (lo:=3277) (a:=47) (b:=47) sp3277 sp3324))) (joinSmall (lo:=3371) (a:=187) (b:=188) (joinSmall (lo:=3371) (a:=93) (b:=94) (joinSmall (lo:=3371) (a:=46) (b:=47) sp3371 sp3417) (joinSmall (lo:=3464) (a:=47) (b:=47) sp3464 sp3511)) (joinSmall (lo:=3558) (a:=94) (b:=94) (joinSmall (lo:=3558) (a:=47) (b:=47) sp3558 sp3605) (joinSmall (lo:=3652) (a:=47) (b:=47) sp3652 sp3699)))) (joinSmall (lo:=3746) (a:=375) (b:=375) (joinSmall (lo:=3746) (a:=187) (b:=188) (joinSmall (lo:=3746) (a:=93) (b:=94) (joinSmall (lo:=3746) (a:=46) (b:=47) sp3746 sp3792) (joinSmall (lo:=3839) (a:=47) (b:=47) sp3839 sp3886)) (joinSmall (lo:=3933) (a:=94) (b:=94) (joinSmall (lo:=3933) (a:=47) (b:=47) sp3933 sp3980) (joinSmall (lo:=4027) (a:=47) (b:=47) sp4027 sp4074))) (joinSmall (lo:=4121) (a:=187) (b:=188) (joinSmall (lo:=4121) (a:=93) (b:=94) (joinSmall (lo:=4121) (a:=46) (b:=47) sp4121 sp4167) (joinSmall (lo:=4214) (a:=47) (b:=47) sp4214 sp4261)) (joinSmall (lo:=4308) (a:=94) (b:=94) (joinSmall (lo:=4308) (a:=47) (b:=47) sp4308 sp4355) (joinSmall (lo:=4402) (a:=47) (b:=47) sp4402 sp4449))))) (joinSmall (lo:=4496) (a:=749) (b:=750) (joinSmall (lo:=4496) (a:=374) (b:=375) (joinSmall (lo:=4496) (a:=187) (b:=187) (joinSmall (lo:=4496) (a:=93) (b:=94) (joinSmall (lo:=4496) (a:=46) (b:=47) sp4496 sp4542) (joinSmall (lo:=4589) (a:=47) (b:=47) sp4589 sp4636)) (joinSmall (lo:=4683) (a:=93) (b:=94) (joinSmall (lo:=4683) (a:=46) (b:=47) sp4683 sp4729) (joinSmall (lo:=4776) (a:=47) (b:=47) sp4776 sp4823))) (joinSmall (lo:=4870) (a:=187) (b:=188) (joinSmall (lo:=4870) (a:=93) (b:=94) (joinSmall (lo:=4870) (a:=46) (b:=47) sp4870 sp4916) (joinSmall (lo:=4963) (a:=47) (b:=47) sp4963 sp5010)) (joinSmall (lo:=5057) (a:=94) (b:=94) (joinSmall (lo:=5057) (a:=47) (b:=47) sp5057 sp5104) (joinSmall (lo:=5151) (a:=47) (b:=47) sp5151 sp5198)))) (joinSmall (lo:=5245) (a:=375) (b:=375) (joinSmall (lo:=5245) (a:=187) (b:=188) (joinSmall (lo:=5245) (a:=93) (b:=94) (joinSmall (lo:=5245) (a:=46) (b:=47) sp5245 sp5291) (joinSmall (lo:=5338) (a:=47) (b:=47) sp5338 sp5385)) (joinSmall (lo:=5432) (a:=94) (b:=94) (joinSmall (lo:=5432) (a:=47) (b:=47) sp5432 sp5479) (joinSmall (lo:=5526) (a:=47) (b:=47) sp5526 sp5573))) (joinSmall (lo:=5620) (a:=187) (b:=188) (joinSmall (lo:=5620) (a:=93) (b:=94) (joinSmall (lo:=5620) (a:=46) (b:=47) sp5620 sp5666) (joinSmall (lo:=5713) (a:=47) (b:=47) sp5713 sp5760)) (joinSmall (lo:=5807) (a:=94) (b:=94) (joinSmall (lo:=5807) (a:=47) (b:=47) sp5807 sp5854) (joinSmall (lo:=5901) (a:=47) (b:=47) sp5901 sp5948))))))) (joinSmall (lo:=5995) (a:=2997) (b:=2998) (joinSmall (lo:=5995) (a:=1498) (b:=1499) (joinSmall (lo:=5995) (a:=749) (b:=749) (joinSmall (lo:=5995) (a:=374) (b:=375) (joinSmall (lo:=5995) (a:=187) (b:=187) (joinSmall (lo:=5995) (a:=93) (b:=94) (joinSmall (lo:=5995) (a:=46) (b:=47) sp5995 sp6041) (joinSmall (lo:=6088) (a:=47) (b:=47) sp6088 sp6135)) (joinSmall (lo:=6182) (a:=93) (b:=94) (joinSmall (lo:=6182) (a:=46) (b:=47) sp6182 sp6228) (joinSmall (lo:=6275) (a:=47) (b:=47) sp6275 sp6322))) (joinSmall (lo:=6369) (a:=187) (b:=188) (joinSmall (lo:=6369) (a:=93) (b:=94) (joinSmall (lo:=6369) (a:=46) (b:=47) sp6369 sp6415) (joinSmall (lo:=6462) (a:=47) (b:=47) sp6462 sp6509)) (joinSmall (lo:=6556) (a:=94) (b:=94) (joinSmall (lo:=6556) (a:=47) (b:=47) sp6556 sp6603) (joinSmall (lo:=6650) (a:=47) (b:=47) sp6650 sp6697)))) (joinSmall (lo:=6744) (a:=374) (b:=375) (joinSmall (lo:=6744) (a:=187) (b:=187) (joinSmall (lo:=6744) (a:=93) (b:=94) (joinSmall (lo:=6744) (a:=46) (b:=47) sp6744 sp6790) (joinSmall (lo:=6837) (a:=47) (b:=47) sp6837 sp6884)) (joinSmall (lo:=6931) (a:=93) (b:=94) (joinSmall (lo:=6931) (a:=46) (b:=47) sp6931 sp6977) (joinSmall (lo:=7024) (a:=47) (b:=47) sp7024 sp7071))) (joinSmall (lo:=7118) (a:=187) (b:=188) (joinSmall (lo:=7118) (a:=93) (b:=94) (joinSmall (lo:=7118) (a:=46) (b:=47) sp7118 sp7164) (joinSmall (lo:=7211) (a:=47) (b:=47) sp7211 sp7258)) (joinSmall (lo:=7305) (a:=94) (b:=94) (joinSmall (lo:=7305) (a:=47) (b:=47) sp7305 sp7352) (joinSmall (lo:=7399) (a:=47) (b:=47) sp7399 sp7446))))) (joinSmall (lo:=7493) (a:=749) (b:=750) (joinSmall (lo:=7493) (a:=374) (b:=375) (joinSmall (lo:=7493) (a:=187) (b:=187) (joinSmall (lo:=7493) (a:=93) (b:=94) (joinSmall (lo:=7493) (a:=46) (b:=47) sp7493 sp7539) (joinSmall (lo:=7586) (a:=47) (b:=47) sp7586 sp7633)) (joinSmall (lo:=7680) (a:=93) (b:=94) (joinSmall (lo:=7680) (a:=46) (b:=47) sp7680 sp7726) (joinSmall (lo:=7773) (a:=47) (b:=47) sp7773 sp7820))) (joinSmall (lo:=7867) (a:=187) (b:=188) (joinSmall (lo:=7867) (a:=93) (b:=94) (joinSmall (lo:=7867) (a:=46) (b:=47) sp7867 sp7913) (joinSmall (lo:=7960) (a:=47) (b:=47) sp7960 sp8007)) (joinSmall (lo:=8054) (a:=94) (b:=94) (joinSmall (lo:=8054) (a:=47) (b:=47) sp8054 sp8101) (joinSmall (lo:=8148) (a:=47) (b:=47) sp8148 sp8195)))) (joinSmall (lo:=8242) (a:=375) (b:=375) (joinSmall (lo:=8242) (a:=187) (b:=188) (joinSmall (lo:=8242) (a:=93) (b:=94) (joinSmall (lo:=8242) (a:=46) (b:=47) sp8242 sp8288) (joinSmall (lo:=8335) (a:=47) (b:=47) sp8335 sp8382)) (joinSmall (lo:=8429) (a:=94) (b:=94) (joinSmall (lo:=8429) (a:=47) (b:=47) sp8429 sp8476) (joinSmall (lo:=8523) (a:=47) (b:=47) sp8523 sp8570))) (joinSmall (lo:=8617) (a:=187) (b:=188) (joinSmall (lo:=8617) (a:=93) (b:=94) (joinSmall (lo:=8617) (a:=46) (b:=47) sp8617 sp8663) (joinSmall (lo:=8710) (a:=47) (b:=47) sp8710 sp8757)) (joinSmall (lo:=8804) (a:=94) (b:=94) (joinSmall (lo:=8804) (a:=47) (b:=47) sp8804 sp8851) (joinSmall (lo:=8898) (a:=47) (b:=47) sp8898 sp8945)))))) (joinSmall (lo:=8992) (a:=1499) (b:=1499) (joinSmall (lo:=8992) (a:=749) (b:=750) (joinSmall (lo:=8992) (a:=374) (b:=375) (joinSmall (lo:=8992) (a:=187) (b:=187) (joinSmall (lo:=8992) (a:=93) (b:=94) (joinSmall (lo:=8992) (a:=46) (b:=47) sp8992 sp9038) (joinSmall (lo:=9085) (a:=47) (b:=47) sp9085 sp9132)) (joinSmall (lo:=9179) (a:=93) (b:=94) (joinSmall (lo:=9179) (a:=46) (b:=47) sp9179 sp9225) (joinSmall (lo:=9272) (a:=47) (b:=47) sp9272 sp9319))) (joinSmall (lo:=9366) (a:=187) (b:=188) (joinSmall (lo:=9366) (a:=93) (b:=94) (joinSmall (lo:=9366) (a:=46) (b:=47) sp9366 sp9412) (joinSmall (lo:=9459) (a:=47) (b:=47) sp9459 sp9506)) (joinSmall (lo:=9553) (a:=94) (b:=94) (joinSmall (lo:=9553) (a:=47) (b:=47) sp9553 sp9600) (joinSmall (lo:=9647) (a:=47) (b:=47) sp9647 sp9694)))) (joinSmall (lo:=9741) (a:=375) (b:=375) (joinSmall (lo:=9741) (a:=187) (b:=188) (joinSmall (lo:=9741) (a:=93) (b:=94) (joinSmall (lo:=9741) (a:=46) (b:=47) sp9741 sp9787) (joinSmall (lo:=9834) (a:=47) (b:=47) sp9834 sp9881)) (joinSmall (lo:=9928) (a:=94) (b:=94) (joinSmall (lo:=9928) (a:=47) (b:=47) sp9928 sp9975) (joinSmall (lo:=10022) (a:=47) (b:=47) sp10022 sp10069))) (joinSmall (lo:=10116) (a:=187) (b:=188) (joinSmall (lo:=10116) (a:=93) (b:=94) (joinSmall (lo:=10116) (a:=46) (b:=47) sp10116 sp10162) (joinSmall (lo:=10209) (a:=47) (b:=47) sp10209 sp10256)) (joinSmall (lo:=10303) (a:=94) (b:=94) (joinSmall (lo:=10303) (a:=47) (b:=47) sp10303 sp10350) (joinSmall (lo:=10397) (a:=47) (b:=47) sp10397 sp10444))))) (joinSmall (lo:=10491) (a:=749) (b:=750) (joinSmall (lo:=10491) (a:=374) (b:=375) (joinSmall (lo:=10491) (a:=187) (b:=187) (joinSmall (lo:=10491) (a:=93) (b:=94) (joinSmall (lo:=10491) (a:=46) (b:=47) sp10491 sp10537) (joinSmall (lo:=10584) (a:=47) (b:=47) sp10584 sp10631)) (joinSmall (lo:=10678) (a:=93) (b:=94) (joinSmall (lo:=10678) (a:=46) (b:=47) sp10678 sp10724) (joinSmall (lo:=10771) (a:=47) (b:=47) sp10771 sp10818))) (joinSmall (lo:=10865) (a:=187) (b:=188) (joinSmall (lo:=10865) (a:=93) (b:=94) (joinSmall (lo:=10865) (a:=46) (b:=47) sp10865 sp10911) (joinSmall (lo:=10958) (a:=47) (b:=47) sp10958 sp11005)) (joinSmall (lo:=11052) (a:=94) (b:=94) (joinSmall (lo:=11052) (a:=47) (b:=47) sp11052 sp11099) (joinSmall (lo:=11146) (a:=47) (b:=47) sp11146 sp11193)))) (joinSmall (lo:=11240) (a:=375) (b:=375) (joinSmall (lo:=11240) (a:=187) (b:=188) (joinSmall (lo:=11240) (a:=93) (b:=94) (joinSmall (lo:=11240) (a:=46) (b:=47) sp11240 sp11286) (joinSmall (lo:=11333) (a:=47) (b:=47) sp11333 sp11380)) (joinSmall (lo:=11427) (a:=94) (b:=94) (joinSmall (lo:=11427) (a:=47) (b:=47) sp11427 sp11474) (joinSmall (lo:=11521) (a:=47) (b:=47) sp11521 sp11568))) (joinSmall (lo:=11615) (a:=187) (b:=188) (joinSmall (lo:=11615) (a:=93) (b:=94) (joinSmall (lo:=11615) (a:=46) (b:=47) sp11615 sp11661) (joinSmall (lo:=11708) (a:=47) (b:=47) sp11708 sp11755)) (joinSmall (lo:=11802) (a:=94) (b:=94) (joinSmall (lo:=11802) (a:=47) (b:=47) sp11802 sp11849) (joinSmall (lo:=11896) (a:=47) (b:=47) sp11896 sp11943)))))))) (joinSmall (lo:=11990) (a:=5995) (b:=5995) (joinSmall (lo:=11990) (a:=2997) (b:=2998) (joinSmall (lo:=11990) (a:=1498) (b:=1499) (joinSmall (lo:=11990) (a:=749) (b:=749) (joinSmall (lo:=11990) (a:=374) (b:=375) (joinSmall (lo:=11990) (a:=187) (b:=187) (joinSmall (lo:=11990) (a:=93) (b:=94) (joinSmall (lo:=11990) (a:=46) (b:=47) sp11990 sp12036) (joinSmall (lo:=12083) (a:=47) (b:=47) sp12083 sp12130)) (joinSmall (lo:=12177) (a:=93) (b:=94) (joinSmall (lo:=12177) (a:=46) (b:=47) sp12177 sp12223) (joinSmall (lo:=12270) (a:=47) (b:=47) sp12270 sp12317))) (joinSmall (lo:=12364) (a:=187) (b:=188) (joinSmall (lo:=12364) (a:=93) (b:=94) (joinSmall (lo:=12364) (a:=46) (b:=47) sp12364 sp12410) (joinSmall (lo:=12457) (a:=47) (b:=47) sp12457 sp12504)) (joinSmall (lo:=12551) (a:=94) (b:=94) (joinSmall (lo:=12551) (a:=47) (b:=47) sp12551 sp12598) (joinSmall (lo:=12645) (a:=47) (b:=47) sp12645 sp12692)))) (joinSmall (lo:=12739) (a:=374) (b:=375) (joinSmall (lo:=12739) (a:=187) (b:=187) (joinSmall (lo:=12739) (a:=93) (b:=94) (joinSmall (lo:=12739) (a:=46) (b:=47) sp12739 sp12785) (joinSmall (lo:=12832) (a:=47) (b:=47) sp12832 sp12879)) (joinSmall (lo:=12926) (a:=93) (b:=94) (joinSmall (lo:=12926) (a:=46) (b:=47) sp12926 sp12972) (joinSmall (lo:=13019) (a:=47) (b:=47) sp13019 sp13066))) (joinSmall (lo:=13113) (a:=187) (b:=188) (joinSmall (lo:=13113) (a:=93) (b:=94) (joinSmall (lo:=13113) (a:=46) (b:=47) sp13113 sp13159) (joinSmall (lo:=13206) (a:=47) (b:=47) sp13206 sp13253)) (joinSmall (lo:=13300) (a:=94) (b:=94) (joinSmall (lo:=13300) (a:=47) (b:=47) sp13300 sp13347) (joinSmall (lo:=13394) (a:=47) (b:=47) sp13394 sp13441))))) (joinSmall (lo:=13488) (a:=749) (b:=750) (joinSmall (lo:=13488) (a:=374) (b:=375) (joinSmall (lo:=13488) (a:=187) (b:=187) (joinSmall (lo:=13488) (a:=93) (b:=94) (joinSmall (lo:=13488) (a:=46) (b:=47) sp13488 sp13534) (joinSmall (lo:=13581) (a:=47) (b:=47) sp13581 sp13628)) (joinSmall (lo:=13675) (a:=93) (b:=94) (joinSmall (lo:=13675) (a:=46) (b:=47) sp13675 sp13721) (joinSmall (lo:=13768) (a:=47) (b:=47) sp13768 sp13815))) (joinSmall (lo:=13862) (a:=187) (b:=188) (joinSmall (lo:=13862) (a:=93) (b:=94) (joinSmall (lo:=13862) (a:=46) (b:=47) sp13862 sp13908) (joinSmall (lo:=13955) (a:=47) (b:=47) sp13955 sp14002)) (joinSmall (lo:=14049) (a:=94) (b:=94) (joinSmall (lo:=14049) (a:=47) (b:=47) sp14049 sp14096) (joinSmall (lo:=14143) (a:=47) (b:=47) sp14143 sp14190)))) (joinSmall (lo:=14237) (a:=375) (b:=375) (joinSmall (lo:=14237) (a:=187) (b:=188) (joinSmall (lo:=14237) (a:=93) (b:=94) (joinSmall (lo:=14237) (a:=46) (b:=47) sp14237 sp14283) (joinSmall (lo:=14330) (a:=47) (b:=47) sp14330 sp14377)) (joinSmall (lo:=14424) (a:=94) (b:=94) (joinSmall (lo:=14424) (a:=47) (b:=47) sp14424 sp14471) (joinSmall (lo:=14518) (a:=47) (b:=47) sp14518 sp14565))) (joinSmall (lo:=14612) (a:=187) (b:=188) (joinSmall (lo:=14612) (a:=93) (b:=94) (joinSmall (lo:=14612) (a:=46) (b:=47) sp14612 sp14658) (joinSmall (lo:=14705) (a:=47) (b:=47) sp14705 sp14752)) (joinSmall (lo:=14799) (a:=94) (b:=94) (joinSmall (lo:=14799) (a:=47) (b:=47) sp14799 sp14846) (joinSmall (lo:=14893) (a:=47) (b:=47) sp14893 sp14940)))))) (joinSmall (lo:=14987) (a:=1499) (b:=1499) (joinSmall (lo:=14987) (a:=749) (b:=750) (joinSmall (lo:=14987) (a:=374) (b:=375) (joinSmall (lo:=14987) (a:=187) (b:=187) (joinSmall (lo:=14987) (a:=93) (b:=94) (joinSmall (lo:=14987) (a:=46) (b:=47) sp14987 sp15033) (joinSmall (lo:=15080) (a:=47) (b:=47) sp15080 sp15127)) (joinSmall (lo:=15174) (a:=93) (b:=94) (joinSmall (lo:=15174) (a:=46) (b:=47) sp15174 sp15220) (joinSmall (lo:=15267) (a:=47) (b:=47) sp15267 sp15314))) (joinSmall (lo:=15361) (a:=187) (b:=188) (joinSmall (lo:=15361) (a:=93) (b:=94) (joinSmall (lo:=15361) (a:=46) (b:=47) sp15361 sp15407) (joinSmall (lo:=15454) (a:=47) (b:=47) sp15454 sp15501)) (joinSmall (lo:=15548) (a:=94) (b:=94) (joinSmall (lo:=15548) (a:=47) (b:=47) sp15548 sp15595) (joinSmall (lo:=15642) (a:=47) (b:=47) sp15642 sp15689)))) (joinSmall (lo:=15736) (a:=375) (b:=375) (joinSmall (lo:=15736) (a:=187) (b:=188) (joinSmall (lo:=15736) (a:=93) (b:=94) (joinSmall (lo:=15736) (a:=46) (b:=47) sp15736 sp15782) (joinSmall (lo:=15829) (a:=47) (b:=47) sp15829 sp15876)) (joinSmall (lo:=15923) (a:=94) (b:=94) (joinSmall (lo:=15923) (a:=47) (b:=47) sp15923 sp15970) (joinSmall (lo:=16017) (a:=47) (b:=47) sp16017 sp16064))) (joinSmall (lo:=16111) (a:=187) (b:=188) (joinSmall (lo:=16111) (a:=93) (b:=94) (joinSmall (lo:=16111) (a:=46) (b:=47) sp16111 sp16157) (joinSmall (lo:=16204) (a:=47) (b:=47) sp16204 sp16251)) (joinSmall (lo:=16298) (a:=94) (b:=94) (joinSmall (lo:=16298) (a:=47) (b:=47) sp16298 sp16345) (joinSmall (lo:=16392) (a:=47) (b:=47) sp16392 sp16439))))) (joinSmall (lo:=16486) (a:=749) (b:=750) (joinSmall (lo:=16486) (a:=374) (b:=375) (joinSmall (lo:=16486) (a:=187) (b:=187) (joinSmall (lo:=16486) (a:=93) (b:=94) (joinSmall (lo:=16486) (a:=46) (b:=47) sp16486 sp16532) (joinSmall (lo:=16579) (a:=47) (b:=47) sp16579 sp16626)) (joinSmall (lo:=16673) (a:=93) (b:=94) (joinSmall (lo:=16673) (a:=46) (b:=47) sp16673 sp16719) (joinSmall (lo:=16766) (a:=47) (b:=47) sp16766 sp16813))) (joinSmall (lo:=16860) (a:=187) (b:=188) (joinSmall (lo:=16860) (a:=93) (b:=94) (joinSmall (lo:=16860) (a:=46) (b:=47) sp16860 sp16906) (joinSmall (lo:=16953) (a:=47) (b:=47) sp16953 sp17000)) (joinSmall (lo:=17047) (a:=94) (b:=94) (joinSmall (lo:=17047) (a:=47) (b:=47) sp17047 sp17094) (joinSmall (lo:=17141) (a:=47) (b:=47) sp17141 sp17188)))) (joinSmall (lo:=17235) (a:=375) (b:=375) (joinSmall (lo:=17235) (a:=187) (b:=188) (joinSmall (lo:=17235) (a:=93) (b:=94) (joinSmall (lo:=17235) (a:=46) (b:=47) sp17235 sp17281) (joinSmall (lo:=17328) (a:=47) (b:=47) sp17328 sp17375)) (joinSmall (lo:=17422) (a:=94) (b:=94) (joinSmall (lo:=17422) (a:=47) (b:=47) sp17422 sp17469) (joinSmall (lo:=17516) (a:=47) (b:=47) sp17516 sp17563))) (joinSmall (lo:=17610) (a:=187) (b:=188) (joinSmall (lo:=17610) (a:=93) (b:=94) (joinSmall (lo:=17610) (a:=46) (b:=47) sp17610 sp17656) (joinSmall (lo:=17703) (a:=47) (b:=47) sp17703 sp17750)) (joinSmall (lo:=17797) (a:=94) (b:=94) (joinSmall (lo:=17797) (a:=47) (b:=47) sp17797 sp17844) (joinSmall (lo:=17891) (a:=47) (b:=47) sp17891 sp17938))))))) (joinSmall (lo:=17985) (a:=2997) (b:=2998) (joinSmall (lo:=17985) (a:=1498) (b:=1499) (joinSmall (lo:=17985) (a:=749) (b:=749) (joinSmall (lo:=17985) (a:=374) (b:=375) (joinSmall (lo:=17985) (a:=187) (b:=187) (joinSmall (lo:=17985) (a:=93) (b:=94) (joinSmall (lo:=17985) (a:=46) (b:=47) sp17985 sp18031) (joinSmall (lo:=18078) (a:=47) (b:=47) sp18078 sp18125)) (joinSmall (lo:=18172) (a:=93) (b:=94) (joinSmall (lo:=18172) (a:=46) (b:=47) sp18172 sp18218) (joinSmall (lo:=18265) (a:=47) (b:=47) sp18265 sp18312))) (joinSmall (lo:=18359) (a:=187) (b:=188) (joinSmall (lo:=18359) (a:=93) (b:=94) (joinSmall (lo:=18359) (a:=46) (b:=47) sp18359 sp18405) (joinSmall (lo:=18452) (a:=47) (b:=47) sp18452 sp18499)) (joinSmall (lo:=18546) (a:=94) (b:=94) (joinSmall (lo:=18546) (a:=47) (b:=47) sp18546 sp18593) (joinSmall (lo:=18640) (a:=47) (b:=47) sp18640 sp18687)))) (joinSmall (lo:=18734) (a:=374) (b:=375) (joinSmall (lo:=18734) (a:=187) (b:=187) (joinSmall (lo:=18734) (a:=93) (b:=94) (joinSmall (lo:=18734) (a:=46) (b:=47) sp18734 sp18780) (joinSmall (lo:=18827) (a:=47) (b:=47) sp18827 sp18874)) (joinSmall (lo:=18921) (a:=93) (b:=94) (joinSmall (lo:=18921) (a:=46) (b:=47) sp18921 sp18967) (joinSmall (lo:=19014) (a:=47) (b:=47) sp19014 sp19061))) (joinSmall (lo:=19108) (a:=187) (b:=188) (joinSmall (lo:=19108) (a:=93) (b:=94) (joinSmall (lo:=19108) (a:=46) (b:=47) sp19108 sp19154) (joinSmall (lo:=19201) (a:=47) (b:=47) sp19201 sp19248)) (joinSmall (lo:=19295) (a:=94) (b:=94) (joinSmall (lo:=19295) (a:=47) (b:=47) sp19295 sp19342) (joinSmall (lo:=19389) (a:=47) (b:=47) sp19389 sp19436))))) (joinSmall (lo:=19483) (a:=749) (b:=750) (joinSmall (lo:=19483) (a:=374) (b:=375) (joinSmall (lo:=19483) (a:=187) (b:=187) (joinSmall (lo:=19483) (a:=93) (b:=94) (joinSmall (lo:=19483) (a:=46) (b:=47) sp19483 sp19529) (joinSmall (lo:=19576) (a:=47) (b:=47) sp19576 sp19623)) (joinSmall (lo:=19670) (a:=93) (b:=94) (joinSmall (lo:=19670) (a:=46) (b:=47) sp19670 sp19716) (joinSmall (lo:=19763) (a:=47) (b:=47) sp19763 sp19810))) (joinSmall (lo:=19857) (a:=187) (b:=188) (joinSmall (lo:=19857) (a:=93) (b:=94) (joinSmall (lo:=19857) (a:=46) (b:=47) sp19857 sp19903) (joinSmall (lo:=19950) (a:=47) (b:=47) sp19950 sp19997)) (joinSmall (lo:=20044) (a:=94) (b:=94) (joinSmall (lo:=20044) (a:=47) (b:=47) sp20044 sp20091) (joinSmall (lo:=20138) (a:=47) (b:=47) sp20138 sp20185)))) (joinSmall (lo:=20232) (a:=375) (b:=375) (joinSmall (lo:=20232) (a:=187) (b:=188) (joinSmall (lo:=20232) (a:=93) (b:=94) (joinSmall (lo:=20232) (a:=46) (b:=47) sp20232 sp20278) (joinSmall (lo:=20325) (a:=47) (b:=47) sp20325 sp20372)) (joinSmall (lo:=20419) (a:=94) (b:=94) (joinSmall (lo:=20419) (a:=47) (b:=47) sp20419 sp20466) (joinSmall (lo:=20513) (a:=47) (b:=47) sp20513 sp20560))) (joinSmall (lo:=20607) (a:=187) (b:=188) (joinSmall (lo:=20607) (a:=93) (b:=94) (joinSmall (lo:=20607) (a:=46) (b:=47) sp20607 sp20653) (joinSmall (lo:=20700) (a:=47) (b:=47) sp20700 sp20747)) (joinSmall (lo:=20794) (a:=94) (b:=94) (joinSmall (lo:=20794) (a:=47) (b:=47) sp20794 sp20841) (joinSmall (lo:=20888) (a:=47) (b:=47) sp20888 sp20935)))))) (joinSmall (lo:=20982) (a:=1499) (b:=1499) (joinSmall (lo:=20982) (a:=749) (b:=750) (joinSmall (lo:=20982) (a:=374) (b:=375) (joinSmall (lo:=20982) (a:=187) (b:=187) (joinSmall (lo:=20982) (a:=93) (b:=94) (joinSmall (lo:=20982) (a:=46) (b:=47) sp20982 sp21028) (joinSmall (lo:=21075) (a:=47) (b:=47) sp21075 sp21122)) (joinSmall (lo:=21169) (a:=93) (b:=94) (joinSmall (lo:=21169) (a:=46) (b:=47) sp21169 sp21215) (joinSmall (lo:=21262) (a:=47) (b:=47) sp21262 sp21309))) (joinSmall (lo:=21356) (a:=187) (b:=188) (joinSmall (lo:=21356) (a:=93) (b:=94) (joinSmall (lo:=21356) (a:=46) (b:=47) sp21356 sp21402) (joinSmall (lo:=21449) (a:=47) (b:=47) sp21449 sp21496)) (joinSmall (lo:=21543) (a:=94) (b:=94) (joinSmall (lo:=21543) (a:=47) (b:=47) sp21543 sp21590) (joinSmall (lo:=21637) (a:=47) (b:=47) sp21637 sp21684)))) (joinSmall (lo:=21731) (a:=375) (b:=375) (joinSmall (lo:=21731) (a:=187) (b:=188) (joinSmall (lo:=21731) (a:=93) (b:=94) (joinSmall (lo:=21731) (a:=46) (b:=47) sp21731 sp21777) (joinSmall (lo:=21824) (a:=47) (b:=47) sp21824 sp21871)) (joinSmall (lo:=21918) (a:=94) (b:=94) (joinSmall (lo:=21918) (a:=47) (b:=47) sp21918 sp21965) (joinSmall (lo:=22012) (a:=47) (b:=47) sp22012 sp22059))) (joinSmall (lo:=22106) (a:=187) (b:=188) (joinSmall (lo:=22106) (a:=93) (b:=94) (joinSmall (lo:=22106) (a:=46) (b:=47) sp22106 sp22152) (joinSmall (lo:=22199) (a:=47) (b:=47) sp22199 sp22246)) (joinSmall (lo:=22293) (a:=94) (b:=94) (joinSmall (lo:=22293) (a:=47) (b:=47) sp22293 sp22340) (joinSmall (lo:=22387) (a:=47) (b:=47) sp22387 sp22434))))) (joinSmall (lo:=22481) (a:=749) (b:=750) (joinSmall (lo:=22481) (a:=374) (b:=375) (joinSmall (lo:=22481) (a:=187) (b:=187) (joinSmall (lo:=22481) (a:=93) (b:=94) (joinSmall (lo:=22481) (a:=46) (b:=47) sp22481 sp22527) (joinSmall (lo:=22574) (a:=47) (b:=47) sp22574 sp22621)) (joinSmall (lo:=22668) (a:=93) (b:=94) (joinSmall (lo:=22668) (a:=46) (b:=47) sp22668 sp22714) (joinSmall (lo:=22761) (a:=47) (b:=47) sp22761 sp22808))) (joinSmall (lo:=22855) (a:=187) (b:=188) (joinSmall (lo:=22855) (a:=93) (b:=94) (joinSmall (lo:=22855) (a:=46) (b:=47) sp22855 sp22901) (joinSmall (lo:=22948) (a:=47) (b:=47) sp22948 sp22995)) (joinSmall (lo:=23042) (a:=94) (b:=94) (joinSmall (lo:=23042) (a:=47) (b:=47) sp23042 sp23089) (joinSmall (lo:=23136) (a:=47) (b:=47) sp23136 sp23183)))) (joinSmall (lo:=23230) (a:=375) (b:=375) (joinSmall (lo:=23230) (a:=187) (b:=188) (joinSmall (lo:=23230) (a:=93) (b:=94) (joinSmall (lo:=23230) (a:=46) (b:=47) sp23230 sp23276) (joinSmall (lo:=23323) (a:=47) (b:=47) sp23323 sp23370)) (joinSmall (lo:=23417) (a:=94) (b:=94) (joinSmall (lo:=23417) (a:=47) (b:=47) sp23417 sp23464) (joinSmall (lo:=23511) (a:=47) (b:=47) sp23511 sp23558))) (joinSmall (lo:=23605) (a:=187) (b:=188) (joinSmall (lo:=23605) (a:=93) (b:=94) (joinSmall (lo:=23605) (a:=46) (b:=47) sp23605 sp23651) (joinSmall (lo:=23698) (a:=47) (b:=47) sp23698 sp23745)) (joinSmall (lo:=23792) (a:=94) (b:=94) (joinSmall (lo:=23792) (a:=47) (b:=47) sp23792 sp23839) (joinSmall (lo:=23886) (a:=47) (b:=47) sp23886 sp23933)))))))))
  have good : (List.range 23980).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 575000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 23979 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 23979 := by
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


private def packet (i : ℕ) : ℕ := (if i < 146 then (if i < 73 then (if i < 36 then (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else (if i < 8 then 0 else 0)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else 0)) else (if i < 15 then (if i < 14 then 0 else 0) else (if i < 16 then 0 else (if i < 17 then 0 else 0))))) else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then 0 else 0) else (if i < 21 then 0 else 0)) else (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else (if i < 26 then 0 else 0)))) else (if i < 31 then (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else 0)) else (if i < 33 then (if i < 32 then 0 else 0) else (if i < 34 then 0 else (if i < 35 then 0 else 0)))))) else (if i < 54 then (if i < 45 then (if i < 40 then (if i < 38 then (if i < 37 then 0 else 0) else (if i < 39 then 0 else 0)) else (if i < 42 then (if i < 41 then 0 else 0) else (if i < 43 then 0 else (if i < 44 then 0 else 0)))) else (if i < 49 then (if i < 47 then (if i < 46 then 0 else 0) else (if i < 48 then 0 else 0)) else (if i < 51 then (if i < 50 then 0 else 0) else (if i < 52 then 0 else (if i < 53 then 0 else 0))))) else (if i < 63 then (if i < 58 then (if i < 56 then (if i < 55 then 0 else 0) else (if i < 57 then 0 else 0)) else (if i < 60 then (if i < 59 then 0 else 0) else (if i < 61 then 0 else (if i < 62 then 0 else 0)))) else (if i < 68 then (if i < 65 then (if i < 64 then 0 else 0) else (if i < 66 then 0 else (if i < 67 then 0 else 0))) else (if i < 70 then (if i < 69 then 0 else 0) else (if i < 71 then 0 else (if i < 72 then 0 else 0))))))) else (if i < 109 then (if i < 91 then (if i < 82 then (if i < 77 then (if i < 75 then (if i < 74 then 0 else 0) else (if i < 76 then 0 else 0)) else (if i < 79 then (if i < 78 then 0 else 0) else (if i < 80 then 0 else (if i < 81 then 0 else 0)))) else (if i < 86 then (if i < 84 then (if i < 83 then 0 else 0) else (if i < 85 then 0 else 0)) else (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else (if i < 90 then 0 else 0))))) else (if i < 100 then (if i < 95 then (if i < 93 then (if i < 92 then 0 else 0) else (if i < 94 then 0 else 0)) else (if i < 97 then (if i < 96 then 0 else 0) else (if i < 98 then 0 else (if i < 99 then 0 else 0)))) else (if i < 104 then (if i < 102 then (if i < 101 then 0 else 0) else (if i < 103 then 0 else 0)) else (if i < 106 then (if i < 105 then 0 else 0) else (if i < 107 then 0 else (if i < 108 then 0 else 0)))))) else (if i < 127 then (if i < 118 then (if i < 113 then (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else 0)) else (if i < 115 then (if i < 114 then 0 else 0) else (if i < 116 then 0 else (if i < 117 then 0 else 0)))) else (if i < 122 then (if i < 120 then (if i < 119 then 0 else 0) else (if i < 121 then 0 else 0)) else (if i < 124 then (if i < 123 then 0 else 0) else (if i < 125 then 0 else (if i < 126 then 0 else 0))))) else (if i < 136 then (if i < 131 then (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else 0)) else (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else (if i < 135 then 0 else 0)))) else (if i < 141 then (if i < 138 then (if i < 137 then 0 else 0) else (if i < 139 then 0 else (if i < 140 then 0 else 0))) else (if i < 143 then (if i < 142 then 0 else 0) else (if i < 144 then 0 else (if i < 145 then 0 else 0)))))))) else (if i < 219 then (if i < 182 then (if i < 164 then (if i < 155 then (if i < 150 then (if i < 148 then (if i < 147 then 0 else 0) else (if i < 149 then 0 else 0)) else (if i < 152 then (if i < 151 then 0 else 0) else (if i < 153 then 0 else (if i < 154 then 0 else 0)))) else (if i < 159 then (if i < 157 then (if i < 156 then 0 else 0) else (if i < 158 then 0 else 0)) else (if i < 161 then (if i < 160 then 0 else 0) else (if i < 162 then 0 else (if i < 163 then 0 else 0))))) else (if i < 173 then (if i < 168 then (if i < 166 then (if i < 165 then 0 else 0) else (if i < 167 then 0 else 0)) else (if i < 170 then (if i < 169 then 0 else 0) else (if i < 171 then 0 else (if i < 172 then 0 else 0)))) else (if i < 177 then (if i < 175 then (if i < 174 then 0 else 0) else (if i < 176 then 0 else 0)) else (if i < 179 then (if i < 178 then 0 else 0) else (if i < 180 then 0 else (if i < 181 then 0 else 0)))))) else (if i < 200 then (if i < 191 then (if i < 186 then (if i < 184 then (if i < 183 then 0 else 0) else (if i < 185 then 0 else 0)) else (if i < 188 then (if i < 187 then 0 else 0) else (if i < 189 then 0 else (if i < 190 then 0 else 0)))) else (if i < 195 then (if i < 193 then (if i < 192 then 0 else 0) else (if i < 194 then 0 else 0)) else (if i < 197 then (if i < 196 then 0 else 0) else (if i < 198 then 0 else (if i < 199 then 0 else 0))))) else (if i < 209 then (if i < 204 then (if i < 202 then (if i < 201 then 0 else 0) else (if i < 203 then 0 else 0)) else (if i < 206 then (if i < 205 then 0 else 0) else (if i < 207 then 0 else (if i < 208 then 0 else 0)))) else (if i < 214 then (if i < 211 then (if i < 210 then 0 else 0) else (if i < 212 then 0 else (if i < 213 then 0 else 0))) else (if i < 216 then (if i < 215 then 0 else 0) else (if i < 217 then 0 else (if i < 218 then 0 else 0))))))) else (if i < 256 then (if i < 237 then (if i < 228 then (if i < 223 then (if i < 221 then (if i < 220 then 0 else 0) else (if i < 222 then 0 else 0)) else (if i < 225 then (if i < 224 then 0 else 0) else (if i < 226 then 0 else (if i < 227 then 0 else 0)))) else (if i < 232 then (if i < 230 then (if i < 229 then 0 else 0) else (if i < 231 then 0 else 0)) else (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else (if i < 236 then 0 else 0))))) else (if i < 246 then (if i < 241 then (if i < 239 then (if i < 238 then 0 else 0) else (if i < 240 then 0 else 0)) else (if i < 243 then (if i < 242 then 0 else 0) else (if i < 244 then 0 else (if i < 245 then 0 else 0)))) else (if i < 251 then (if i < 248 then (if i < 247 then 0 else 0) else (if i < 249 then 0 else (if i < 250 then 0 else 0))) else (if i < 253 then (if i < 252 then 0 else 0) else (if i < 254 then 0 else (if i < 255 then 0 else 0)))))) else (if i < 274 then (if i < 265 then (if i < 260 then (if i < 258 then (if i < 257 then 0 else 0) else (if i < 259 then 0 else 0)) else (if i < 262 then (if i < 261 then 0 else 0) else (if i < 263 then 0 else (if i < 264 then 0 else 0)))) else (if i < 269 then (if i < 267 then (if i < 266 then 0 else 0) else (if i < 268 then 0 else 0)) else (if i < 271 then (if i < 270 then 0 else 0) else (if i < 272 then 0 else (if i < 273 then 0 else 0))))) else (if i < 283 then (if i < 278 then (if i < 276 then (if i < 275 then 0 else 0) else (if i < 277 then 0 else 0)) else (if i < 280 then (if i < 279 then 0 else 0x1b8810c2cd94b49ac47f20d8ee46b630d15188ec3c417c09303180d000001b87b362bb948c99a46d2010e7867e2ee14308a03a217208c02dc0ae00001b875202da15549de48f21a0f5c6ec312158095c3d418109083080d800001b86f3c2c014949884662060ea46922e814a88b83a217e09103040bc00001b869712ba14449604521fe0ea06982e8141889c39a17108a82f00b000001b8637d2cb14e89ae46f20b0ef869e2ff14e88d43b417a09102fc0b800001b85d442ef1600a404be2290fe4718328162899c3fe19c09a03100c600001b857442cb94f49c048920f8f146b02f614c09003c218509203100c400001b851342da155c9e649a21e0f846f631c15a893c3ce18309182fc0d200001b84b592b9145c97645e2018ea069c2e6149087c3a017d08d02d80b000001b8454e2d615409da48a2110f286dc30415109083c418109103280c400001b83f672be14549664632028e906982e814b08f83c218c09003040b200001b839502d9151c9be4812100eb86aa2fb14d08cc3c417d091030c0c600001b8331c2e715a0a104a82200f506ec31015009003c418409003040bc00001b82d262c514b499246b2048ea86922e214a08b039c17f09383180d800001b8273e2c914b499e46b2028eac6a42f114b08dc3b217e08e82d40a200001b821502c714dc9bc47c20a8f006d430a15389043ac17c08e82fc0c400001b81b582cd94c499c46d2058ee46be30215409003c218609002ec0ca00001b815742c614b09a447820e8ef46a62f314788cc39c16e08b03100be00001b80f5f2e015509ee49c21b0f446d231015489243c617e08e82fc0c000001b8094c2da95449d24892168f406d030714b08c03aa18a09203040bc00001b803652c114ac9ae4822110f246bc30515689183d019409703100cc00001b7fd9e2b6945495a45a2008e6c6902e514788d83b417608c02e00a800001b7f7a72ca94d09b648d2168f1c6d630a15909003b417a08c82c40ac00001b7f1ba2cb94c899e47c2128f186c02fb14a88e83b016f08982bc0a600001b7eba12dc95789ea49421a8f206ee30c15509343c817e09183080ae00001b7e58b2d495149c447a20d0ef46aa2f414988fc3be184090031c0ca00001b7df852d495089b647a20b0ee86c630f15809703f819709683440ce00001b7d99f2c314d09ca48320d0edc6a030014e88fc3b017d08e82e40c400001b7d3ab2c915009c04842140f246d42fd15309183b818108c02e00ba00001b7cdaa2d295149c047f2118f306de31215489003c417808902e40ac00001b7c7a22d595009c447e2118f2c6d031515c895c3ea18d09683240d200001b7c1a62ce14c499c4682080eb069c2f814a08c43ae17a09203040c000001b7bbb72c8148899046c20b0e9c6aa2ed14a88c03a417308c82f00bc00001b7b5b62ce14f49b247820e8f186de30715008e83ae17e093032c0c000001b7afc12ce94cc9b447720f0f2c6da308153892c3dc19309783280ce00001b7a9be2d295249d248c2168f386de30715509103c217e08e02f00be00001b7a3c72c714a89a647320b0eec6a02ec14a08c03a217508e83080a800001b79dc72cb94ec99e47b20d0ed46c030915308f83c018208e031c0d200001b797ac2dd95689e64902170f046be2f815288fc3cc18308f02e40bc00001b791b02ce951c9be48c2108f2c6b830314e08ec3b617d08d82dc0b200001b78bc52c414ac98c4602040ec069a2fb14988e83bc18208f82ec0cc00001b785de2c3947c98e4652070e8c6922ec14388d03a418108f82fc0b200001b780042bc94c09964652028ee06be30315288fc3a017908902d00ac00001b77a1e2c514b09804692050ee06ba2f314c89043b218309303140b800001b7742a2ce94cc99647320b0eec6ba2fa14d09083c818a09603400c200001b76e352c514b49a44752098ec069c2ef14b88d43c218008f832c0ca00001b768532c2949c97a4622050ea86982f614888b439e17608882e40c000001b762402d495389ea49921f8f386dc31015489203c417c08b82b80aa00001b75c4b2cd94c49a84692080eb46aa2fc15109043b217f09603040c000001b7563e2d295089b247e2150f246ce30615609383e018b091831c0d400001b750662bf14989864642038eac6a42f614f08e43b017708702b40ac00001b74a852c294a49a047720c8ee46b62fe15289143c017808702d40ae00001b744912c614a49a64732090ecc6a62f214508d83be17408d83040aa00001b73e8c2d515249c448b20d0efc6ce2f714a88d43ba17b08a830c0c800001b738a62c514c499e4732090ee06a42ef14988e43b417308a02e40b800001b732ad2d4152c9c447720f8ec46ae2eb14508bc3b218509283080d000001b72caf2d595189c247e2120efc6b42ff14b88c43bc180094832c0ce00001b726bc2c514c09a24792078ec86ba2f214c08c43ae17c09082e80ba00001b720cc2c794d09ac4872160f386de2fc14d08d039c17e08d83080cc00001b71aa42e115609e449421b8f4c6e030f15709003c217708e03040b400001b714cf2bd94709804682038ec86a42e514408c83aa18409482c00a600001b70ebc2d995649ee4902168f206d830315009083d218008d82e40ac00001b708d62c614d09ac47520b0f0c6c02fe14e88cc3c617e08c82f00b6000) else (if i < 281 then 0x1b9ff2e2cb94e09a647b2090ed86a630615189143c617e091831c0ca00001b9f9452c914bc97a4582008e686782d813f087038a16308682d40b800001b9f34d2c914b49ac46f20a0ec06b230114e09183ca17a08e02f00ce00001b9ed742b894389744622028e9c6922f114608e43b017908f03200d600001b9e77e2cf94f89ac47d20d0f006aa2ee143889039c16e08982bc0a400001b9e1752d895589f648c2140edc6c42f8145089839417008882d80b600001b9dba12bb948897e46720a8f246d031215989383dc184091030c0be00001b9d5ac2ce14b899046c2038ea46942e514a08e83b617509102d00ca00001b9cf8e2e195a0a184a42248fa870432215d096c3ea18d096831c0ca00001b9c9942d014f49c24852110f146d2309158094c3d218d09503280c200001b9c3a82ca94d89ac47520f8ef06b22f514608a839416f08d02cc0b000001b9bd992d895009d048a2168f3c6f031c159896c3e4190096831c0cc00001b9b7b02c194809784632020ebc6b22f9146889438e17208602c00b200001b9b1a42d415349ec4872160f346e030c15b89343d818709102f80b000001b9abc22c114889804641f98e746622cf13b88b839617908a02f40d400001b9a5b62d215249d848720c0ee46bc2fe14e88f03b218209403540e000001b99fc42ce14b09b247120c8ed86aa2f314888c83a618108f82f00ba00001b999cb2ce94f499c4702088ed46ba2fa14c88b03a017e08e02dc0aa00001b993962ee95dca224a821d0f5c6d831115409043be17c08902ec0ac00001b98d902d295249da4882120f0c6cc30015509143c417c08f02fc0c400001b987982c814a096c45c2038e7067e2e414208a839016508a83140b400001b981b52c594a498847720d8ed46b42f714a08d03a417f08c02f40b800001b97bca2c414c89c04842148f0c6b22f914d88fc3ce18d09303140c600001b975d52d114e49be48520d8ee86c030514a88a839c17908a82dc0a800001b96fb02e495589de4892190f406e8312153091c3c818008f830c0c400001b969c42c714c89a446e2080eb06b02fd15209603e2193099831c0d000001b963ba2d515609f24992138f406e030d15a89503f41a209a03640ca00001b95df12b8141495e4592018e706602d913d886c38216a08302840a000001b957f92c614b899e47220a0ec86b030515608f03a617e08e032c0d800001b952072c614e09ac4732070ed86b22f914b88d43a016d08a02d80b800001b94c082d094e89b047420a8ec869c2ec14588b83a217608782d00be00001b9462b2bf948899445b1fc8e8067c2e914308a03b617308d03000be00001b940412c494889904712090ec068e2e914488d03a417308b82dc0ba00001b93a392d395409d04882168f346dc31015b09343cc17f08d02e80bc00001b9343c2c614a899246f20e0ef46c430315709543e619009103200b000001b92e292d715489ea48d2188f506e431515d09603f619309903240d200001b928332c4146c97a45d2038ea06942f114708b03a617b08c83180ca00001b922302d1153c9e84812168f046ba2f514d09203c417d08c83240d000001b91c492c194d09a64812110ef46c830215289383e618d09383040c200001b9167d2b694509824632040e8c69e2f414a88f83cc18509083240d200001b910a92bb149c98e4682010eac6922f114b08e83aa17809003240c800001b90ab02cf94c89ae47e20f8f486dc31a15c89643e618b09003100c800001b904ac2d3952c9e44882180f146ca30115288f83cc18909082f80b800001b8fead2cd94b499847320a0ea86b22ff14d88cc3a017608482b40ac00001b8f8b42cc95049b447b20f0ef86b22eb14d08d83a217208882b80a400001b8f2af2d295489e649821f0f646d430b15209043c018e09382fc0b200001b8ecbe2cd15009ce4832138ee86ba30315689283c418109403200c600001b8e6be2cb14c499c46c2048e9c6822e814988f43c0185092030c0ce00001b8e0cd2c2148c9824622018e806822e114188903a017908b82cc0ac00001b8dac22d215249cc4832118efc6a02ee14408d43a616f08a82c00c400001b8d4ed2c0947898446b20a8ee46922e714708b83aa17908e030c0c600001b8cee82d495249e84912148f386e8309154891c3c218209303100b600001b8c8d12e59594a1649f21e0f8c71433216009743ee18909503380c800001b8c2e82cb14e89b64732080ebc6aa2fd14e08f43a416f08a02c40aa00001b8bced2ce14f09b84772060ecc6962ef14a88f03b617d09002bc0b600001b8b6d82d795489d84842118f206d630815c09583ee18d09682fc0a200001b8b0ba2de157c9f84a82248ff473833e16e89a041219c0a503680de00001b8aab92d114ec9c247b20f0f046b42f914d88d43bc18108902f40ba00001b8a4d72bf94909924732078ed86aa2f214988f03b217d09083080c800001b89eea2c7149098846b1fc0e906a62f6142089438816f08d03080b600001b898dd2d495289e649721d0f646fa313155892c3e419509682f80ba00001b8931c2ae93fc9304481fb0e806942e914908dc3ae17008782e00c200001b88d0b2d815449d248f21a0f206dc30d15d89583f218e09a03200d000001b887102cf15009be4792120ebc69a2eb14688a439616e08902fc0ba000 else (if i < 282 then 0x1bb7d162c194a099446f2048eac68e2e213c886438416008602e40be00001bb77122d014f89b64852138f006ca2fe150890c3c417b08e03000bc00001bb71412bb147098046c20d0efc6ba30015109003cc18808f03040c200001bb6b552cb94d89a847b20e0f1c6c430414d08c03a417608982dc0b200001bb65682c114c098a4672060ebc6a22f8154892c3d218c09803280dc00001bb5f4e2df95589e24922188f686d831815c09583d818c09b03680e000001bb59632cb14c49b648120c0ecc6a82f114988d43ba18109103140bc00001bb53882b994789704501fa8e786862e014488ac39417608e02fc0b000001bb4d8b2ce14fc9c84832140f186ce30615489343e419009082fc0b800001bb47ad2c194949904642080ed86a82f414988d43ac17909083200ca00001bb41c32c294b099646d2020eac69e2ef14688a039216008202b00ac00001bb3bac2d415309cc4872130f346d030015109343e819009883380d200001bb35bf2cc94d09bc47720a8edc6bc2f514d08e83b818308f02f00c600001bb2fc52c914d09b447e2098eec69e2e614408d03ae18208b82e80c200001bb29db2c994f89b046e2090ee46c630715208f03c617e08c831c0c800001bb23c12dd957c9ee4952148f306d02fc15009043ce188092830c0cc00001bb1dde2c3146c9764602008e9c67e2dd139885838816808202a80ac00001bb17d52d695209ea49521c0f4c6dc31415609203dc18609283140c200001bb11ef2c7149898e46d2050ed46ae2f915008f83c017d08c83000c600001bb0bf22ce94d89a446f20d0efc6a22f015008ec3b217c08902ec0b800001bb05e52d715349e649421c0f246da31915d89503f419b09903140c400001baffec2cf15009d648c2170f1c6d831715b09603d418509103000b800001baf9fb2c814d09ac47c20d8eec6bc2fd14e88e839616808783000b000001baf4302b814289544551ff8e5c66e2dc14008c43b017108b82dc0be00001baee3c2cc94d89aa47720a8ef46cc30715408f83a217f09303200c800001bae8642be14809804662020e9468a2ee1430888384163085829c0a200001bae2892c694b09a44682028e886a02ed148887437e16a08702a40a200001badc9f2c714b499a47420a8ec46842e7144089839216b08682b00a400001bad6a22d294f09bc47e2150f186b22eb14808c039016d08902bc0b000001bad0b82c494a49a047a2140f286de30f15589383d218d09203000be00001bacab42d595349de48420d8efc6c42fc14e08e43a816e08882dc0bc00001bac4942dc1570a024a421f8f786e831215809443ea19b09903280bc00001babe932d315149ee49e21f0f8c70231b15a09403e219509b833c0c200001bab8c32ba146098046b2050ed86b02fc15188f43be17608903180ca00001bab2ce2c6949c99c46a2070ea06a22f214908f83bc17308e83000d200001baace72c314809704541f98e7c6942f114888bc3b217708c02d00b400001baa6ec2c914bc9a846f2078eb469a2f514788c439617808d02f00bc00001baa0c32e915d0a2c4b722a8fbc70631e15e89403e818a09803300da00001ba9aae2da15309dc4862148f4c6e831115009303e619009903140cc00001ba94a52d515249dc47d2110f1c6d62ff15008e83b218508902d80b600001ba8ec72c794d89a04732070ed86b62fe14f88ec3c218209182f40ba00001ba88d72c9949096e45a1ff8eac6aa2f414c08c43aa17709102e00c000001ba82f42c6149498c4682048ed46aa2f414a88b43a617708f83240ca00001ba7cde2da152c9da4852100f246da2fd14e08e43ba189092831c0d400001ba76fc2c0148897e4581fd0e686802dd143088836615c08402c40b200001ba710f2c414a899e46e2050eb86a02f014f89043b417d09303200de00001ba6aee2de15409e448d2160f3c6cc30815909543ea19209803140c400001ba649d2f61630a524bd2280fb871632f15f89803fe19509703140c200001ba5eb82bf948897e4612060ec46ae2ee14788bc3a817808a02d00c800001ba58d62c214bc9a64742098ec06942ee14508ac3a817308c82d00b600001ba52cd2d5953c9d44812138ef46ca2ff157095c3de18909603100c200001ba4cf02c914c098e4632050e846922ed14a08f03b217e08e02fc0ae00001ba46f32d2954c9e848b2128ee86b42fd14e08fc3bc17e08f83080cc00001ba40ec2d695549e24882138f246e031315508fc3c018209403040be00001ba3abe2e5958c9fc4a42230f7c6fa32115b094c3da18c08e82e40ba00001ba34e22c014549664561fe8e9068e2dc139085437c16208202a40a400001ba2ee92c994d49ac4752050e9c6802e314688c83aa18308e831c0c400001ba28cc2df95809f248f2148f386e030515609303d218d09182fc0c200001ba22f32c0947c9704602010eac6a82f414b08d03ac17308c02cc0b000001ba1d172be14709784591f88e6467e2e814b891c3d218308a02c40a600001ba17252ca94cc9964682090eb46982e914c88cc3b418009302d80ac00001ba112b2ca14a89744631fe8e7066a2da140089839817009103080c800001ba0b292ce14f49b647920b8ef86c630214d89043cc18f093030c0c400001ba051e2d515209d048d21b8f4c6c631215289443ca18308982bc0b8000 else 0x1bcfa1c2d094e49a646d20b8ef46b230315108e43c618b09483080d000001bcf4212d595389d248a2160f586e431115789843fe19d099830c0c400001bcee1b2cf14dc9b84712060ec46a62f814c08e83ac17808e82dc0c400001bce8322c2148c9864682038e946a62f615189003ae17908b82e80c200001bce2452ca14d09a047620c0ee06c230214e88e83ac17e08d02d80b800001bcdc592cc94dc9c448320b8ef46b831215689483dc18d093031c0b600001bcd6402db1568a004a92210f806f032015d099441019609b83540d400001bcd0222de15549ec4892130f346de308156891c3d818c09402dc0bc00001bcca4f2b594389584511f60e486742d913b086438816608002cc0a800001bcc46c2be14849804571fd8e9c6762e914808d03a418209182ec0c200001bcbe692cf15209c647920e0ee86b42f915088f83b817e08a02cc0b600001bcb8642d995349c647f2108f006c62f814a88ec39c17208582b80a200001bcb2822c2949c9904662048ed469e2f014908d03a417808e82f00c400001bcac7a2cf15049c447a2120efc6cc30d15309383d0191093832c0d400001bca6a82c314c49ae46e2078ed46b42f814808ac3ac18509503380d600001bca09e2d715189ca47d20f8f086e230c157890c3b817f08e03180be00001bc9ab22c994cc9a047020c8ee86b430815809203ba18008d82e40b800001bc94ba2ca94dc9b247c2060eb46942de14208983b018409102f80bc00001bc8eed2b6943c9704561ff8e906842e714908dc3ba17e08f02c80ac00001bc89022c3949c9a24792048ed06b62fc14988e43be17f09402dc0ba00001bc82e82dc95549da4952188f146e8312155093c3d8182091830c0b600001bc7d252b094309464441fb0e986882e514508d43b217e08d82ec0b200001bc77242cd94e09d048220d8efc6a82f615089283ca17c08a83080ca00001bc71092d814f89c247e2110f0c6c82fb14f88e03bc18209482fc0be00001bc6b1d2c594b09b247720b8ed46b02f314888a039a17708b02f40be00001bc652f2c794c09a447e20b8ea468c2e914308b03aa17708a02e40a600001bc5f292d514f89ca4842148f146ca30b15309403cc18609703540c600001bc593b2cd14e09b447a2038ea06aa2f714a08bc39816808b02e80b400001bc534c2c994c099c47c20e8ee06be2ed14488ac3a216e08882c80ae00001bc4d3c2da952c9cc47a2108ed86ca2ff15189343ee196097833c0cc00001bc47602c1946095044e1fb0e486722ec14488d43b0182094033c0d200001bc415a2cf15109ce48721b0f7070231f15f09443de19609603100c400001bc3b702c914e49b447c20f0f146c230614f08dc3c418b09382f80c000001bc356b2d195049b447520a8ecc6b22fc14e88ec3b617608e03000c000001bc2f962bc146497e45b2030e9068c2e314388bc39417208983100d000001bc29cb2b6145c9864612080eb468c2e914588bc3ac17508a02e40be00001bc24082b4944497445e2010e8869e2ee14f88f03c818809983180d200001bc1e062d114c498e47420b8edc6842e714108803a017b08702f40c200001bc17f52da954ca004a22238f506dc30415389183d0185093830c0ca00001bc12042c514b099e46b2078edc6bc2fa14d88c43a416a08582d80ac00001bc0c0a2c794a899a4692038e886882df13f086838e16e08582c80bc00001bc05fb2d815549fa4952198f446e631115a895c3fc19909202fc0c800001bbfff22d415389f649e21f0f746d830a15589283c418208982f40a600001bbf9fc2cc14e89b64852140efc6bc2f714c08d439e17308b02e80c000001bbf3ec2d7952c9d848b2180f306d630115088f03ba17c08f82e80c000001bbedf72c894d89a24692070ea86982f614f08fc3c418609383140c200001bbe7f72cb94cc9aa4692028e786782e6144087c38c15907d02b409e00001bbe2172c194a499247820b0ef06be30915209003c217c08c83200d800001bbdc0f2d215389dc4852180f086c430115389243d018208e830c0c200001bbd6102cd95109d248820c8eec6be30b15109003b818009583140c000001bbd0372bd14709904752060ee46ba303153891c3dc18909202f80ca00001bbca3d2d295249de4892110f006d831115809583f219009683580e000001bbc4432cd94d09a447d20b0ee46b82f314d89083c017b08982cc0ac00001bbbe442cc14d49ac47020d8ed46ae2ff15689143c417f09082fc0c200001bbb82d2de9598a0649421b0f1c6e630e15889303e419e09703000d200001bbb23c2d1150c9d04882118efc6c22fa14c08e43a617908a03080ca00001bbac432d615289c047e2138f286d2308156092c3da182092830c0c000001bba6532c594b499e4652010ec06ac30014d88c43bc18609083080c200001bba0662c814ac9a647820e0edc6ba2fe14b88e03d218909283100cc00001bb9a8e2bc94689644592038ecc6a42ee14888e83b817d09502f80d800001bb94ba2b9946497645c1fb8e6c6842e9140087437e15808282c80b400001bb8ef12b8145c97445c1f60e1c65c2d3137085837e16d08c02d00ba00001bb89062be14ac9824602020e9c6922f014288ac3a418608e831c0bc00001bb83032d495189c04842110ef46a62ec14a08dc3ce18b09303200ce000)))) else (if i < 288 then (if i < 285 then (if i < 284 then 0x1be77a32bc14549684662048eb86a22f114b88dc39817708983000ba00001be71952d295149d248620e8ef86bc2fa14f88fc3b217a09283000ae00001be6b8d2ce95049b848020e8ecc6b430415509043be18709183000bc00001be65a62c3148c99a47d20b8ef46ae2fb15609083b617608b02bc0a600001be5fb32ca94d89ba47d20d0f186bc2ff15b09583de190099830c0cc00001be59da2bd94889904612010e8067c2ef14888d039216608702f80be00001be53d32cf94f09ae47720d0efc6d230a158092c3e418609683240e400001be4dcf2d7153c9de49621c8f546f631815909103b617a08c02c00b200001be47e62c994909844672018e986642d3142086c3a016808682b40b600001be41e92cf15009cc48f2130efc6cc31815a09343c417f08f02f40be00001be3bf02ca94949744531fb0e7468c2ea14408ac3a617708c83040c600001be36052c3948c9944682020eb069a2f014708b839e17808a82cc0ba00001be2fef2dc95409f049221a0f2c6d031015609383e218909983340ca00001be29fe2c714b89a047a2098eec6c630e15409203d418c09603100e400001be24072cf14e89b647f20b0eb86a830415189043ca18c09383100b400001be1df82d495449e24922130ef86bc30414d08d83b017308002a809e00001be17e12d895189cc47c2110f246d030f154890c3c017c08e02e80b800001be11ba2e295609ec4902168f606d830515389083c817f08b830c0c200001be0bc82cc14fc9c24842120f086ba2fc14d89043d0184096832c0da00001be05ed2ba14609784622000e8867e2e8143888c38c17408982c80b600001bdfffc2cb14cc9984762078ef86bc2f514c89103b217708f82f00a000001bdfa0c2cb94e49b447320b8f006aa2f414f88f43a617708983180ce00001bdf41b2d195189ca48420b8ebc6a62f114808c439a16c08682e80c400001bdee322c814e49a046f2068eb06982f214b08bc39c17b09082f00b800001bde82c2cc14d49b247920d8ef46ce30715989483f419609c03300e600001bde2492c294d499e4642028e806962f114388bc39817708a82f00ba00001bddc682c0949c98c46b2070ebc6b22fe14e88ec3a017308c82f00be00001bdd6712d515449dc4842108f306d230614f89143c418609383140c200001bdd0792c714b09904742028ec86a02ee14508a43a017108a82e40be00001bdca7b2cb14ec9c048c2168f2c6de31315689303fc19209b83340c200001bdc4942ca14d49aa4782090eb46aa2f615088f83c017809483340cc00001bdbec12bd94a899c46e20b8ec06ae2f414908dc3ae17a08b02e00b400001bdb8d92c414ac98c4622068e946a62f714808d43be18209903600d600001bdb2ed2c914c89c047f2150f2c6ce30614b88fc3c817e08d82ec0b000001bdace22d515389d64892160f046c430f15a09383d618c096033c0d400001bda6dc2d415389bc47f2160f346d630f15c09403f819909983200ca00001bda0b62e19560a0249c21f0f8070231d15d097c3f019f09b832c0d800001bd9ab52d495209d64802100eec6ae2ea14508f03b616f08482c40b600001bd94d32c014a099046e2020eac69e2e3141089438817608e02d40bc00001bd8ec42d195249d64912150f0c6c430715209203c017508f02d80b200001bd88a52dc152c9d248c2170f0c6c430214e09003c618008f02f80c800001bd82e62ae13f49584531f88e286662cd13c888038e17008b02d80ba00001bd7cce2d9155c9e048f2160f346e430d15189183e6193093032c0d400001bd77022b9946c97e46b2070e9c6a62ea14988e43c417c08f031c0be00001bd711d2c194b09a046f2090eb86a22fa15188ec3be18308f82e40ba00001bd6b252cf15009ba4882118f2c6ca30e15f09583f019309a03380ca00001bd655c2b9946897244c1fb0e4065e2d013a086437e16d08282bc0b000001bd5f5c2cd95209d04872120ee468e2ea14a08cc3be17c08b82f80c800001bd59442d895509da48a2170f406fe32515b09503f219109203000b400001bd536a2c2149899e4602068ea06982e414408b83ac17308802d40b400001bd4d752cb14c099a47320a8ed46a02f114888dc3ac17908d02dc0c400001bd47762d5154c9ec48d2128f146bc30515188f83c817808b02ec0cc00001bd41a82b794409604511fd8e8467c2e8142089c3a017708e03040ba00001bd3bad2cf95109c84852108f146cc30214c88c439a17108902a80b000001bd35db2b414449844652030ea86a42f514608cc3b417c09103140be00001bd2fca2d915649f84a321e0f4c6d830d15209143be17d09003040c200001bd29ed2bf94a89844621fd0e7c6762d713f88b83b018008a82ec0be00001bd241a2c014c09a648620b0f046c230115509183d418509183080c200001bd1df72e215a4a1a4ac2260fc073632c160098c3ea19309a836c0d800001bd18102c514cc9a847b2150f146ca30a14f08f83d217a09082fc0c000001bd120d2d715489e848e2150f306c42ff14e09103d618709383340c400001bd0c112cb95009c447e20c0eec6ac2fb14988cc3bc18508e83000b800001bd060b2d115349ce4882110f106c230015188f83c418d08e03140be00001bd00162cd94d89aa47520c0ed86aa2f914e08e03be17609083400da000 else 0x1bff47b2c614a498445d1fc0e646842e3141089038216508682c00a600001bfee8c2c314a898a4622008eb86942f514a88f43c618709483340d200001bfe8832d594d099846c2060eac6a22ef14c89183c017b09203100ca00001bfe28f2cb14e89ac4762108ed46ac2ff14b88e43b618609883540cc00001bfdc5c2ea95b4a124a92240fa06f232015909283c818309183440d400001bfd6592d314d89a047d20e0ee86b62f214988d439617609583400d000001bfd0772c594e49b847720d0edc6ae2fc14688d83c417808a02f40c000001bfca7d2cc14fc9b84732030ebc68c2e014388b439417408d03040cc00001bfc4922c194b49b24782120f246c030214c08b83a616808882e80ba00001bfbec62b4142896445a2000e7868a2e414588cc3a217d08a02d00b400001bfb8b62da155c9ea49e21a0f406ee31c15c095c3f018609503300ca00001bfb2ee2b194149504471f70e3c66c2e914508ac3a417508c82c40ae00001bfacff2c214a898846d2088ec46b62fb14f08e03b817508c02c40b000001bfa7112c714e49c64812128f2c6e830d15689283d418b09583300c800001bfa1252c614a09a647a20c0e9c6a02f114a08dc3ac16a08882e80ca00001bf9b1c2d2153c9e44952168f306d630a154890c3de18d094830c0c000001bf95322cd14dc9b047920c8f046c22fd15688ec3b217408a82dc0c400001bf8f692b3944096645b1fc8e7c69a2f114a88fc3c218509103040ca00001bf899b2be144097e4652000eb06962ea14e08b439217608d03040bc00001bf839d2cb14c49a646b2088ef46b02f314708ac39217308a02c40b400001bf7d842d695209d647a20b8ebc69e2f614a09083b817b08a82cc0bc00001bf776b2da955c9e248e2168f106c030315309003b018308f02c40a400001bf71802ca14cc9b448220d8ec06ac30415109083c017908e82b40b800001bf6b832cc14e09ae47d2110f186ba2ff14b09083ce18408e82e00b200001bf658d2cd14c49ac4732090eec6cc309157091c3ce191097833c0d600001bf5f8d2d2152c9b047b20c0f0c6ba30714f08f43be17a08c82d80b000001bf59832d214fc9c64852118edc6c42fd14e88ec3ba18208c830c0c600001bf53a62be14b49a247f20a0ed86b82fc14f09043ca18a09283280ca00001bf4dab2c894d499447220b0edc6ba2f414b88dc3b617d08d82ec0c200001bf47ca2c1949c99c4682040ebc6942e8144087c38e16008602c40b800001bf41cb2ce15149cc48120b8eb869e2ee14988b83a817408482d00c200001bf3b9d2dc15689f24962148f386c630715189343de19309a032c0cc00001bf35be2b994809664591fc0ea06962f4146087838e16f08983080c800001bf2ffc2b794489824672020e846ae2e814688e43bc18109102ec0b400001bf29f22d895389ea48f2150f206c430315289183b017308602b00ac00001bf24002cd14f49a64712028e8868a2eb14488b039a17008a82f40d200001bf1e072c894cc9c44882180ef46c22f314608bc3b417e08a02c40b200001bf183b2ba146c9644591fc8e646862e714408c43a216f08e02f80bc00001bf124d2c894ac9924632030eb86982ea146889c3ac17c09283100c200001bf0c702c094949824622060ea46942df14588c43a017708602ac0c800001bf06962bb946497e45c1f48e306502d714088a83a417609002f40b000001bf00b12c2949899645c2040ea469a2f114a08d43a217e08b82dc0a800001befac92c794b897c45a2000eac69e2ef14588c438c16808482d80aa00001bef4cd2cc14e89b647220e0ef46c830b15589143d418508e82e00b800001beeec22d2952c9e848b2138efc6b6309150890c3b617f09303100cc00001bee8ce2c894ac9aa4762130ec86ae2f314988bc3aa17a09182e40b800001bee2d32cd14e89c647b20c0ef86aa2fd14a08f83ce18309503240c000001bedcb02dd954c9dc49420e0ef86de30715589343d218509303040da00001bed6d72bb14749884652018e9468e2ed14b88ec3aa17909003000cc00001bed0c72d495109d849721e0f6c70031b160095c3e419409402fc0b600001becab62d315089cc4872150f486f631715909403d618509683480d000001bec4b22d214ec9b84722098ecc69c2f914a09003ca18b09503140d600001bebece2c714a099a4631ff0e886922ef14808a838e16f08e82f80b000001beb8c82d115409f048a2140f306e030c15288fc3b017a08e03080bc00001beb2f32be948099645a1fe0ec06aa30615108f43aa17208602d00a000001bead042c894b09a04782080ebc6a42f714f092c3d218b098831c0d800001bea70f2c815189b648a2130f286c8305152893c3e8194096032c0cc00001bea1372c1147097c45f2028e8c6842e414508cc3a017008c82e80b800001be9b552c0947499446c2068e9c6862dd142088439016908b02cc09e00001be956c2cf14f09b847420c8edc6b02f6148089c3aa17709082f40ca00001be8fa22bb943897845f2000ea068a2f514d89083ba18009383140c200001be89b82ca15049b64872108f006b62f114708e43c217d09203340ca00001be83a82d495489da4882130f006ac2f314908d83b817d08d82e40c800001be7d7b2e815a8a1c4a12238f846fc31615389003c818109103040ba000) else (if i < 286 then 0x1c171ee2c294c899446b2068ed46a62f514888c03b017808982e40c800001c16c0a2c3148c9a046d20b8ee46ac2f314c08d439e17609102f40c800001c166012d395009c44802100ed06ac2fc15009083cc18409282f80ce00001c160242c5948c98e46e2018ea06842e1141888438216708a82d40bc00001c15a1e2d495109c64822110f446d230915789303d817b08d83000d600001c1543a2c1948098e46a2070ec46b22f5143889c3a017508a02d00bc00001c14e1d2dd95609f248c2168f1c6d430515609443e219209183100bc00001c147ef2e915c8a1a4a42220f646fe32916889b441e1a909d83400d600001c142222b514589664621fb0e846802e714488ac3a216808982e40b000001c13c312cb14e89b847f2130ee86b42f214908e03d418009383080c800001c1360c2e2957c9fa49d2188f306d6309152890c3c419109683040d000001c12fd82e595749ee49d21b8f246d630514d08f83b017d08c82f00b400001c129f02cc15049aa46f2140ef06aa2f814708dc3ba18009203100b600001c124002c694889584541fc0e386602d4142889839e17008402bc0b000001c11e382b013fc9304361ee8de864e2d0139085c37815e08382ac0b600001c118262dc95509e448d2118f006cc30c156893c3e619b09903100c400001c112032e795a0a004a321b8f686f630315009183c218309283140ce00001c10c212bc146c98e47320a8ebc6a02e614508b038e16908582e00b200001c106502b8946497a4551f90e3465a2d513b885436e16508602d80ac00001c100372d815549d64852150ef46c630e15789203da19409703280b400001c0fa412cb94dc9ae47020a8ee86b82fd15108e43b618008f02e40c000001c0f42a2d9954c9ce47d20b0ebc6962f514e09083c618409603100ca00001c0ee462c0949c9804672058e9c6a02f414808e43aa17f09002e40bc00001c0e8222e41594a0e4a32230f846e631415a09803fe19709a03480c800001c0e2372cb14bc9984672050ebc6862df14588bc3ae18109102f80b800001c0dc312d695489e248c2140f1c6cc2fe14f09243c418509203200c400001c0d6382cc15009a246c2070eb86962ed14c08fc3be17f08d82e00bc00001c0d02b2d595349cc4892110f306d230715288f03bc18608c02d80c200001c0ca4c2c2948098a4692000e9466c2e1145089c39e17108982ac0a200001c0c4832b1941095244c1f70e386682e214488c439c16a08b02d00bc00001c0bea22c0948498246720a8f046b82f914f08f03c018b09102f40d200001c0b8c62b7143894e4511f80e3c6742e614408b039e17408802f00ac00001c0b2aa2db95589f249b21e0f8c70231b15709283ca17b09002f00be00001c0acac2d095089b447c20f0ee86b62f314988f43aa17c08d02f80c000001c0a6cb2c514d89a047620d0efc6ca30e15789343cc18108f03240d000001c0a0e02cc150c9c447720f8f3c6d430715609103c617f08d82c80c200001c09b012bd94909824692058ebc69a2eb14a08d83ae17f08e02e40ba00001c095122c0948499046c2068ed06aa2eb14a08e03c017908f83180ce00001c08f042d294f49ca48b2190f346fa31215c09543dc18e09983340ca00001c089162c714d49aa47320a8ecc6b630315309343d018409382f80bc00001c0832e2c414b49c24832118f246d230915409383e419009583240d400001c07d522c094689924652020e8c6822e714b09043c217e08a02e00b000001c077672c094a499047320b8edc6ac2fa15209203d418f094031c0d400001c071b52af13e49544551f48e486742e114408a03a017308c82d00b400001c06bb52ce94ec9ca4852168f346b630a15309243c419109503280ba00001c065c42c614b89b24712060ec86a830715309183b617c09082ec0c600001c05fc32d515309de4982140ef46aa2ee14c08f03be17e08e83100c000001c059e92ba946497245d2040eb86a42f914b88e03a017409183180d000001c054122bd948098a4682070ef86b82fd14b88d43a017508b83040b600001c04df92d995349e648d2150f206c030715288f03b417808c82cc0ac00001c047f12d595109da4902168f186e22ff14e88e83a416908582c00b000001c041eb2d194f89bc48b2180f146bc2f414a888039617708b83100ac00001c03bd82d595189ea4942188f586de30f15a09403d618208e02cc0b400001c035d02d915509d448a2138f406e230b15209043c818308f82f00bc00001c02ff32b794589624531f70e606802ef14888c83b218109203080b600001c02a2e2b2144095c4571fc0e5c6722e013f089839217308782d40b200001c024482bf148c9924652098f006b82fd14e08e43c418308c83040ca00001c01e3a2d3152c9d64952188f5c6ec30f15309103c818c09483280d000001c018462cb94cc9a647120d0ed86b42fc14688a439e17308602f40c800001c012432d715109dc48f2130ef86c630415589143ce18108e02d40be00001c00c4e2c794b899e46d2038ebc6782e4142888839417409103040cc00001c006562cd14d89b447620e0ef06b42f215009103c4186092831c0ba00001c000892be945896a4561ff0e8467a2e414208bc3ae17d091030c0d400001bffa692df95949fa49c21e8f7c70431715c09383ca18709102e40b8000 else (if i < 287 then 0x1c2eed62d395189ca48e2160f386c02fe14d08e03b016e08a83240ca00001c2e9162af940093e4461f48e606702df14408cc3a417308a82d80ba00001c2e32e2c714c499847520a8ef86b6304152091c3dc196096032c0c000001c2dd2d2c914c09ac46d20c8eec6b62fc14d88e83a817408d82f40c000001c2d73f2cb14f49c247d20b0ed06a22f514a08dc3a817208602c40aa00001c2d14f2c794e89b447720b8ee86b22f5150090c3b817d08d82d00b800001c2cb622c594b09964702068ee86a22ea14488d83ae17f09183100ba00001c2c5562d114d49ac47f20f8f106d830c15509283d018408c02fc0ba00001c2bf722c6148098446b2008e946a02f314d893c3d618408f83140c800001c2b98b2c694dc9c247920b0ec86b62fc14c08f03bc18109202e80c600001c2b3a12c894ac98645d1ff0e5866a2db141089c39e16e08c02f80ca00001c2ad802df156c9e249121a8f706e830f15889543dc184095831c0bc00001c2a7a22c014909a647320a0ed86b42f714c88e43a617408982f40b200001c2a1ae2c894e09a847f2090ed06c830414e09003ae17d08a82d40be00001c29b982d695349c447b20e8ee06ba2f314988c83b618109103140c400001c295ae2c8149c99846f2058ec06902e7141088838217709002d40b800001c28fda2bb14a898245f2020e6866e2e314208a03be18508882d40b800001c289e42cc94a09884622050eb86be2fe15289103c417e09102f40bc00001c283ba2e31594a064aa2278fa46fc32016389b43f21a0099032c0d200001c27dcb2cf94f49c247c20a0ed46a82fb14c08e83ac17908a02e80c200001c277b82d594f89c04872128f186d631315389203bc17308802b40a800001c271b62d2952c9b647b2138f046c0307155890c3c618109203100b800001c26bff2b2942496244a1fc8e7c68a2e314588ac3aa177091832c0d200001c2661a2c5148097e4692088ebc68a2e514c08fc3c218c08c82c80bc00001c260312c414bc9a84762070eb469c2ea142089039c17108702d809800001c25a3b2cf14f09c24812120f306e831815b89303ce18c09583000be00001c2542c2d415189dc48d20e8ecc6ac2ff14c89243c418509402f80bc00001c24e1f2d695109a64732068edc6c42fe15189183d018609103140c800001c2485b2b1942c94c44b1f70e786862e914888dc3aa18109082e40ac00001c2426a2c714bc97e4612000e6466a2dd13f889038216b08282c40aa00001c23c5e2dc9570a0449d2198f4c6f431c15789483da18909583300dc00001c236642cb14e49b64792078ecc6a02f114b08f43be17609102e40b600001c2304e2dc15789e648b2190f406ce30915289203de18909103100d600001c22a5d2ce950c9b847e20d0ecc6962e014608d43b418309382f40a800001c2247c2c2148497a4571ff0e9c6902f714808c03b217709082fc0c800001c21e812ce14f09be4812110f286c62fe15109303d818809083040b000001c2189c2c814a899a46f20a8f006b22fa14d09103aa17b09082e00bc00001c212ae2c614a09b64812118f006ca2f914c08c839e17808e02e80b600001c20cca2c1949099846f2050eb86aa30c15609083c017e08b82ec0ba00001c206d72cc94fc9c247320c0ec869a2eb14688e03be17e08e82dc0c400001c200bd2de956c9e448e2188f686e631215a09403c218208e02e00bc00001c1fad02ca14d09a647b2160f246ca31215889243c818209683140c600001c1f4d62ca94d49a247b2118f086ae2fa14d08d03c818509003000cc00001c1eeb92de15689f048821d0f7c6ec31b15c09403ba18109503240ce00001c1e8a22df156c9f649d2200f786e831415789403e8192094030c0b800001c1e2af2c914d49c047f2090eb86822db14208b838417408a82e80b200001c1dce42b4945097a4561f68e5865e2d813e889039016c08682f80b400001c1d7032c6149899446f2080ed46ac2fe14e09103c817b09183040ac00001c1d13f2af141c95e4491f30e4c65e2d214308a83b217808902f80c800001c1cb442c894bc9b647f2090eb86ae2f314888e83ba17b08802d00b600001c1c56c2bb947095c4542080edc69a2e814488c839817608a02c80b000001c1bf6c2d1950c9c44812110ef06ba2ff14e09203ce18409002d80b000001c1b97b2ce14dc9c447d2120f0c6b030014e89103ce18609303200c600001c1b3772d995309cc48220f8f106d630e15c89343ce19309783300c400001c1ad8d2c1949099246d2058eb46b42eb140088c3a217308d031c0bc00001c1a7aa2c294749864632028eb46b230215309083c618208f03140c200001c1a1a12cd14dc9a64832108f006c22fa15388fc3b817008e830c0b200001c19bc32c494b099c47120b0ee869c2eb14c88d03a816f08d82ec0c000001c195af2d4152c9dc4892148f1c6ca2f214e89183d418509083000d200001c18fb22cd14d49a847b2098ebc69a2f414708cc38c16f08c82f00b800001c189842e795c4a0449e2168f446e831215589383c218009403080be00001c183ac2bf14b89a846b1ff8e7868c2e1139884037c15708082b00b600001c17dba2cd14e49a446c20b8efc6ba304150090c3dc18408d82e40b800001c177cf2c994dc9c247a20b8edc6a42f114288c43a417b08c82e40ba000 else 0x1c46baf2d195149c648a2120f286e030d157893c3e218408f02d40ba00001c465cf2bf14909964692050e8c6822e914608d83ae17c08f03080c400001c45fe72c394cc9944682038e646742e214588c83a217908d02e40ba00001c459f32ca14dc9a247a2098ed46b82f314a88f43b017508882f40ca00001c454112c094b099e4782070ea86a22ec148089c38e16c08c82e00c000001c44e2f2c994d49ae4782050eb46962f014608cc3a816f08a82c40b400001c448102da954c9d64882188f206c830f15689143ce17c09102ec0b400001c442262c494a499c4712048eb46942ef14b08f83b617808e03040ce00001c43c292d015249c647f2120f206c430815689043c418709082f40c200001c436342c594dc9ae4792058ea46962ed14388ac3aa17508902d80b800001c4302c2cf15349d24822150f4c6e030d15809443cc18e08f83040b800001c42a672b3941495c44e1f50e7067a2e214688c43a817408f82f80b600001c4246b2cd95189dc4842150f0c6c2307152092c3e618309783200be00001c41e632d495209d84972168f1c6be30014d08ec3d218d09a03140d800001c418562dc15549e248721d0f5c6fc31b15c89483e418508b02dc0a800001c4124a2d495389d44882168f246de30814f08ec3a417c09103240dc00001c40c612c414a89aa4702088ea869c2ef14b08c439e16408903080c400001c4066a2ce95009be48120f0ef86b030415409243d419209f83500d200001c400802c914fc9c648220e0efc6e631b15d09543e018e095031c0ce00001c3faa52c3148c98a46920d0ed069c2f915089383d618409103100b400001c3f4c92bb14709744501f70e2065c2cc139084c38416908582cc0aa00001c3eed02c494a89784602050eb46ae2f814908dc3c217908a02d40b200001c3e8d92d014f49bc47720e8ef86b42ef14a08d83b018409003000ba00001c3e2e12d094e49d448420c8ef06b62f214688b83a017808c02c80ae00001c3dcfa2c214a49b04752090edc6a02fe14f89183b417908d83000bc00001c3d70f2c314b09a246c2088ec46ba2fb14b88f03b618108e82f40a800001c3d11a2cc94e09aa4762118efc6ac2f914908d039c17208d02dc0be00001c3cb322c1947898e47320c8ed468a2f614d88f43c018109303040be00001c3c5612b8941095244f1f98e906a62e414308b839016a08b82dc0ac00001c3bf722ce94f89b04782138ef86d230715509083da18b095032c0c600001c3b9842ca14e499a46b2060f006ce308151091c3ca18108e02d80c600001c3b3772d094ec9c246a2080ec069c2f7147887c37e17108d83000ca00001c3ad642db95589e64982180f286e231015809443ce186091030c0c200001c3a78e2ba94509544441f50e4c6742e013b086437815d08782d40bc00001c3a19c2c5949897e45e2018e906962f214808c43a416f08a82b40a800001c39b932d3152c9c44862110ee06b62f715088f03b416908a82e80b800001c395872da95589ec48e2190f8070432215c89583e218e097832c0c400001c38f702d795449e049721e0f406d830315208f03d819009803140ce00001c389ac2b4943c94c4451ef0e1c6602db140886c37416708602dc0b200001c383c72be946498645b2010e6867e2d814288d83ae16e08a02dc0b800001c37db62d415409e249821a8f2c6d02f914a89083cc18209002ec0ca00001c377bc2d194b09ac47a2050eb46962ed14388b83a817008c03040c200001c371b92d515489f84942200f986fc32116309783ee19b09c83680e600001c36bc32cc94f89cc49021c8f506d430515209043a017308e02fc0b200001c365d32c494ac98e47820d0ed46b82f114a88d83a617d09182fc0ba00001c35fe12d095289b447b20e8ef46be30215289183c217e08f03080c000001c359c12de9578a0449d2210f586e6311156093c3da18008d031c0c800001c353ee2ba945c96a45d2030ea06a02ea14388b83a816708702dc0b400001c34de82ce14d89b047720a0ed06982f314989003b417b08b83040bc00001c347fe2c514b09a246e2098ed46a82f914a890c3b618509203180d200001c342142c894ec9b447920d0f406de31915c09143c618809402f80ba00001c33be72e895c0a0849b2240f906f4315158895c3ec18b09202f40ae00001c335ed2ce14f89be47620e0ecc6922ec14708c039817408d030c0b000001c3300e2c414a89b446f20a0edc6942eb14708d83ae17708902e80b400001c329fd2d515149da48e2148f006ce30315189083d418709382f80d200001c324202c114589604611fc8eac6b02fd14b08c039e17408c83000b600001c31e252ce15009c448120f8ef86c030a15609103b217308e83280a600001c3184a2ba947496e45e2038eb869e2f214a08d43aa17909182f40b400001c3126d2c294a898846e2090f146f030615a09683f61a70a103500da00001c30c852c714a099446e2090ee869e2e614688cc3a818208b02e00bc00001c3069c2c694c09a646d2070ea46a42fc14988fc3ac17708902e00bc00001c300b52c4949899846d2090eb86ac2ff155094c3dc18608d82e80b200001c2fab02d295249d249a21a8f686dc30a15909383dc18409002f40c400001c2f4d22c194bc9aa47820b8f0c6c0302151890c3d218609102dc0b2000))) else (if i < 290 then (if i < 289 then 0x1c5e8ca2e5159ca0049f21a0f546e431815989583de18e09583340cc00001c5e2e82c194a49a44802118ef46d4308154090c3b418009403280c000001c5dcea2d295009b647c2108f086c0309157891c3ce17f08c02e40a600001c5d6f12cc14d49a24702048e906942f014b08e43c218409482ec0c400001c5d0f42d0950c9be4872138f0c6bc2f614888d83b4181090030c0c000001c5cae92da15549d649021d8f7c6ec307155892c3d418909303140d200001c5c4e72d695409f449a21f8f786fc31515b89383c818108f02ec0be00001c5bef22cf14fc9be47220a8ec86b430914888a83a617608802d80c000001c5b9002c514ac99245f2030ea86902e414688a43a017708b83040d400001c5b30d2cd94cc99c4692038e8c67c2dc13e88a039016e08b02dc0ba00001c5ad152cb94d89ae47a20c0ec86902e4142889839217308882d80ac00001c5a7462bd148498a46f20b8ee06a22f7149889438817308782d00a000001c5a16f2c014609684501fb8e586802f114b88c439c17308b02c00a200001c59b772cb14d09b647c20c8ef86c430114e89003c418709402f00b400001c5957c2cd14e09bc47720b0ef46c02fb14c88c839c17008a82f80b200001c58f6e2d295209ca48520f8f206ca30b14f890c3c218009083080b000001c589582dc95209d848820f0eb86b62f814708d43b816c08b82cc0a600001c583562d2953c9d84842140ef86ae2ff15409103de18f09283240ca00001c57d8b2b5941895e4582018e946902ec14688a039e17808c82d40ae00001c577722e215a8a204ae2290fc8724333160098c3fc193096031c0c200001c571982bd943c9644521fd0e946842ea14608c83a217f08f02e40be00001c56ba22cb14e09a246b2048e8c6902db13e08ac39817508b02d009600001c565aa2cd95149bc4772120f306c630815309403f219309603100d400001c55fa12d415189a848020f8f106d030114e090c3de19409883340ce00001c559b52c714b899e47a2098ee46a02e814708d83a017708782e80bc00001c553a42dc154c9fe4a02208f786ec31015509383e018f09602fc0c400001c54dae2c894dc9c84752090ed46b42f914e88f83aa17b08c03040b200001c547e32b7946097445c1fe0ea46a42e914708c83b617f08d02e80bc00001c541ff2c594cc9b848320f0ef06ca2ff14988a439416908782d40ba00001c53c002cc94e49a247b2088ea06962f714888f03be18508e82f00c200001c536202bd944497645d1f98e586782e8142888c3a617b09202ec0b400001c5302a2cd15089c848320a0eac69a2f614b88b839817308802c40a600001c52a642b4941c96c4551ff8e6c6802e314a88dc3a217608b02ec0bc00001c5245c2d5152c9cc48a2190f386d430d15389383bc18208c82f80c600001c51e842c4149c97e4642050e986922ed14988b839817608a82c80ba00001c518a42c314dc9a648020f8ee46be2f214988dc39c17808782bc0a400001c512982d6953c9e048e2168f106ce30615489343d8191093031c0c800001c50c892d215289d04852130f2c6e030715489343e018909503040b200001c506542e995f8a284b42290f8870231315d09483dc18d09c83340e000001c500942b8142c95a4411f20e346622d714208a838216008082a00ba00001c4fa872d215009c847720b0ef86b630014f08f03c018609303280d000001c4f46d2dc15509f24992198f546d031715809503da18409283300ca00001c4ee562da15409e44872148f206d030b15b09503da18708c82f80ae00001c4e85c2cc94d89c048a2168f386d22fe14f08fc3a617108d02f00b200001c4e2902b7143896845b1ff8ebc6842ec14408b039617308a82fc0ae00001c4dcc12bc147897e46920b0ed86b430014f88f83c618309082fc0c000001c4d70a2a613d094e4531fe8e5c6802e714408a0392179092030c0cc00001c4d11d2c794b89904702078edc6b8303155090c3d6181094031c0d200001c4cb342ca94d49a84762070ec06922ec142889439017108f02fc0c000001c4c5452c5949097c4642010ea46aa30215489103b618908e83000c200001c4bf232e215b0a164a62220f886fc31e15e89443e018c08f82e40b600001c4b91a2d5152c9d44902190f306da2fd14b88e03ba17c08e82ec0b600001c4b3372c514a89a447720a0f046c62fe14e88f83cc17e09182ec0c800001c4ad4f2c815149c44872150f006bc30314e88c43a217e08e83100b800001c4a7302db95509e44912198f146c02f614b88b83a616c08a82f00a600001c4a1602b7143096c4591fc8e646a22fd15108f83c418409003040ca00001c49b6d2cc94c09aa4822110f346da30714f08ec3ae17d08d83000ba00001c495512db15449c048a2170efc6a42f014c09083c017e09403140d000001c48f862b3140494a4491f78e406782dc13c884836215608282b40b200001c489a52bf14809844581fc8e7467c2e7144889c39217008982e00c600001c4839d2d895489f049921b8f586d430915108f03bc17808d83080b000001c47da32ce14d09ae47f2120f386cc30415289543f219c09a83500be00001c477b12ce94d89ac47420c0f0c6da30815389143d017f08d82c00b800001c471be2c494a499246a20b8ef06d030b15709083e018c09603440da000 else 0x1c765832d215489fc4a321f8f686fc31d15c09743e419709d83640d200001c75f952cd14ec9aa47a20f0ef06d630415589183ce18809002ec0ba00001c759b62c3148497e46f20c8f0c6b230715088ec3d0187093031c0b800001c753ab2d915789f048f2188f3c6da30b15209103c418609483280d400001c74da02d515449dc48120b0eb069c2fa14a88f43be18309483040b600001c7479b2d195249c648e2180f3c6c430415709243c617a08d82d40b600001c741b72c414b899a4692000eb06ac2fd14d88a439817008e82fc0c000001c73bba2cc15009c24882108f086d230d153894c3ee19509603100d400001c735f22ae94089564582018e846802db144089839417608d82dc0c000001c7301c2be145c9664551fb8e486782e1140889c39416608702d40bc00001c72a2b2cc14f89b047920a0f006c030b14d88c839c17a09002f80cc00001c724122dc15649f84962150f446d631415c09343bc17608b82e40b800001c71e462ba143c9624652058e9c69c30015088f03c818108f82e40c200001c718792b6946095444e1f48e3c6562cc138885837216308082b40b600001c712a52bc947097846c2068edc6aa2f414d08d439617b08f02f80ae00001c70ca52cf94e89c447d20d8ec86a62ee14888f83b818008f82ec0c000001c706c02c0147097a45b2040ed06b02f714688cc3aa17b08f030c0b800001c700dc2c0146497e4631fe0e686762e314408a43ae17f08e03100b800001c6fad82db956c9e848b20f0f006c62f815109503d217f090831c0ce00001c6f4c42df95b0a064a521d8f5c6ce30014d08f43a417708c82dc0b200001c6eeda2c814e49b447b2120eec6aa2ef14788b839216408702c00b400001c6e8cd2d715349ce48b2130f186a62f314b88c83ba17c08c83140ba00001c6e2e42c594b09b847920f0ef06ae30015089143c818608f83100bc00001c6dcf22cb94cc99646f2048ec46b230215188f03da18508e03040c400001c6d6f72c694b09a24792128ee86c0304152891c3d8186095032c0d800001c6d0ee2d195089da4842118f046be2fd15589283c817f09083180c000001c6cb0f2c494a89864661ff0eb06942f114708ac37c16a08802e00c200001c6c53a2be946098a46b2098ed46a62f114888ec3aa17a08f03000c600001c6bf512c714a09a646e20a0eac69a2f614888e83ac17308d02d80b600001c6b95f2c714a499646a2058eb46b02fc14308a838c17108882d40bc00001c6b3602cc14e89c647c20b8efc6b42fb15008dc3b417108c02f80b800001c6ad822bf949c98646c2098ee86aa2f514708a039217708c83040d600001c6a7912c894b49b648d2118efc6c830315009003bc17c09002f00ac00001c6a1962ce14dc9ae4802138f186c62fe14f88fc3be17a08f02f40ba00001c69b952da151c9c648220f8ef46c030314f09203d417c08e83040be00001c695bb2be948098c46d2058eb46a02ef14788fc3ba17808e03000b800001c68fbb2d514e49be4812130ef06aa2f914808e43b217f09103100b200001c689d52c594ac9a647720d8ee06b82fa14b08e03b617a08f03140c600001c683af2df15449dc48e2138f2c6c430714f090c3ce17d08b82d40ac00001c67db92ca94cc9a247220d0ee06aa2f414808b838815d08102ac0ae00001c677b52d094fc9c84842138f006b230815309003c418509303080b600001c671c52c714d49a24682038ec86a62ee14588a43ac17b08f03100c000001c66bb12d295149d248520f8ed06b22fe14e08e03bc17a08c82fc0b400001c665b32ce14f89a847720d8ef06c230614f89043be17f08f82ec0b600001c65ffb2ac13e494a4451f10dfc6482c5137882835815707c02c40a600001c65a0d2c614d89c447b20e0edc6bc2fd15188e83bc17909202ec0aa00001c6540c2d415289d247a2108ef46ac2fa14b08e03b817a08e82e80b200001c64e152c314ac99e47720b0ed46bc2f514c88c43a418709302f80bc00001c648302c0149899047320a0edc6962e814888ec3c218d09303040d000001c642412c914e49aa47220d0ef06962e914808dc3ae17b08b03000ce00001c63c512d2950c9ca4822158f406c230b15108e43ba17308902e80be00001c636572d114e49ae4752110f306e031615a89643de19009783240cc00001c630422df954c9e84912120f246dc30615009043d818309102dc0b800001c62a5e2c2146c98245d1fe8e586942e914988c039c16e08882ec0bc00001c624612d495109ca4902170f386ce31315e09803f819409482f00ae00001c61e632ce150c9bc47420f0efc6ba30915189283de18909383280cc00001c6186a2cc94e89be47c2130f1c6be300152092c3e218209003080c000001c6129d2b594349644532008e906822df14408b83ac17608d82fc0ac00001c60cb52bf948c9a04672068ecc6cc303157893c3c818409002f80ca00001c606c82c514c099246b20d0ef86c22f714f09143ca18d09403300c800001c600bf2d8954c9f24912188f406cc31015608f43be18f09583440d800001c5fad32bd947498646a2020e9c6b230215509203ca18209283100d000001c5f4d52cc950c9d04882100f1c6ba2f614e08dc3a216d08b82e00b200001c5eee82cc94c49a246e2040eac6822e3142889438a16b08a02fc0b6000) else (if i < 291 then 0x1c8e20e2cb14e09c047c2100f0c6be2f914988dc3a216f08682e80c200001c8dc122ca94e09b24772090ee86ae306154891c3d619109483280ba00001c8d62c2bf949497645e1ff8e7468c2ea143888438616f08b82c40aa00001c8d03c2c814dc99a47820f8f146c430414d08f43b018309182fc0cc00001c8ca692bd145897044b1fa8e3865a2d314088a039217408982dc0a600001c8c4502d9956c9f24922190f486f630f15a89283d018108d82f00d600001c8be802b2942c95e4592010e846862e614288c83a817d08e82f40c400001c8b8812cc95049ce4782098ef06b02fb15108d03be17208782b40b200001c8b28a2d0150899c4712078e9868e2f214b89043c017108b82e40ba00001c8ac922ca94f89c44872140f386dc30b15488f43c417008a02dc0b800001c8a6892ce94e89c648d2128ef86a22f014688a83a8187094032c0d200001c8a0d82aa13bc92e43d1f48e3466e2e214208ac39417508a02b80a800001c89aea2cd14dc9bc48c2148f4c6de30d157894c3ea196098833c0d200001c894ee2cd15009c448b2140f506da30b15789403d8189091832c0be00001c88eee2d495349d84822130f4c6d830e15709483ce17708b02f40b200001c888f02ce95289be4872140f0c6ca30315609683da18d09303080be00001c883032c694b898c4642060eb86a22f514888c83c018109503400d000001c87d122c614a499e46d2050ea06922ec14708c43ba17b08e82e40ac00001c877162d014e099646e2068e9c66c2d813a887c37a15b08882bc0ac00001c871132cf15089a84692078ea468e2eb14108c03c017f08b82e40be00001c86b182ce94e89ba4792118f086c02fb14d88fc3c418109082f80d600001c865302c494849724561fd8e8468a2e514b88dc3b018509003240c000001c85f562be948497c4631fa8e506742d713f08a03a816f08782bc0b200001c859592ce94f49aa4842110f446c62fa14b88d83ac17208702dc0ac00001c853652d095409d44852138f406d630b15589003ac17908e831c0ca00001c84d4a2df15789e24942160f286c830015189043c417908802e80b000001c8474f2d415249cc48f2158f406da31015a09643e019909a03500d800001c841542ce950c9ce49521c0f706fc31a15a89583ea19209603200d000001c83b902b914649724561fe8e986902e814108c43a016f08b02c80b000001c835b02c414c49ac47020e8ee06da309151090c3c418309203240ca00001c82fa72ce14f49d44882168f006be30514f08cc39c17d08e82e40c400001c829dc2bc144c96645d1fe8e706842e814d89083de19309203240ce00001c823ff2c1949498a4662090ed06a82fc15489483e219009483140b800001c81dd42e315a0a044a92210f586dc30c15689383d618908e02ec0ba00001c817c92d9155c9da49421b8f446ce30214e091c3d218609103080c200001c812112a613dc93443c1f48e5c6802de144088839016f08f02ec0b800001c80c0b2cf95189c44832138ee86a02ee14008a838e17308903040d400001c806152c594d89b247f20f8edc6a62f014488ac3b417708a03040be00001c8002a2bf94609844571fd8e886742dc13f88c83b217808f83340d400001c7fa3a2c894b899a47020f8f086a62e914488d83a817508a82e80be00001c7f4122e1159c9ec48a2190f406ce30a15509503d418908d02ec0be00001c7ee3a2bd947c98446c2040ea46a22f014788c03aa17c09102ec0be00001c7e86d2b8143c95c44a1f58e3c6702d613b087436615e08282cc0ae00001c7e2662cb94c49a84772078edc69c2ec14d89003a617108a82ec0b400001c7dc872c6149c9a44712098ebc6b22fa14e08fc3d018f09a03200b800001c7d6932d215149c847a20f8eec6c030514e89083d6183091030c0ce00001c7d0922d495089bc4862130f206e630d15509103e219809b83340cc00001c7caad2c4148899647c20b0edc6b42f114d88f03b217c09083280c000001c7c4a12da15689f249c21f8f506f231415b095c3d2191094832c0d600001c7be9a2d495089bc4842148f186c62fa15089143d818409683180c600001c7b8c52c0148897c46f2070e9469c2ef14c08ec3be17c08f82f80ca00001c7b2d82cd14e89b648420b0ee86b82fc14e09043cc19609903280c200001c7acbb2e415d4a2a4ac21e0f5c6e830f15989103ce17f09483380d800001c7a6b62cd14bc99a4742098ee06c02ff14889143e819309502e80be00001c7a0e92b514589704592010eac6b02f4152090c3ca17808f82f00d400001c79b0f2be14c09a247f2130f086c630715489043da19309202d40ae00001c795242c0149898a4642058eb86b02f014b08a037816708602d40be00001c78f3f2c194a498645a1f98e7067c2e514b09003c218809883200c800001c7893a2d415049d44832128f346c430f15289043c818208f03180bc00001c783672bc949899246a2040eb86ba2fe151890c3c618008f02fc0b800001c77d7d2c594c899e46e2070e8468c2e514608b83a816d08582b40b000001c777882c994d499247520a8ed86b02f114588983a017308d02d80b400001c7719f2c2948099047120a8ec46ac2fd15209143c218809483180c000001c76b912cf95109c447f2120ef46b22f515089043c818809303100ba000 else (if i < 292 then 0x1ca5f842bf944097645e1fa8e786702e014808e03c218408e03140b800001ca59902ca94cc9a846c2058ea46962e914788c039a17908b82f40b800001ca53942d315289e04912168f1c6c630715208e83bc18509103180d800001ca4da92cc14b09984632070ea86782f214f88f43ba18609103400de00001ca47c82c1149898a46e2060efc6c230714b88d43c218909203200c600001ca41de2c514b099c4652040eb46862d913e88ac3b417e09083080c400001ca3bcf2d915209ca49321a8f7870231415889383dc18a09383180ba00001ca35ed2c1948098c4652050eb86ba30415389343e418909703180ca00001ca301b2c0147498846c20b8ebc6ae2f514788dc3a617608f02e80c600001ca2a0f2d715149d248620d8ef06b830115189103c217f09303240d200001ca23ff2d895589f449921a0f386c230a15509003c617808d02e40a600001ca1e112c614a49ac47720c8efc6c42fd14e08d83b017708d030c0cc00001ca18222cf14b89a446f2048ecc6b22f714b08dc3b618009083140c200001ca12492bf149098c45f2020e9468e2ef14408bc39c17308b02dc0b800001ca0c492ca94dc9ae47e2120f0c6d230914f88f03ac16d08b82d40bc00001ca06602c3949097e4662038ed86b030215188fc3d218308f02d40b800001ca00692cd14d499a47720f8ef06aa2f914c08d039816d08f83280ca00001c9fa5e2d615289ca4842120ef06c6306151092c3e018408e02fc0c200001c9f49c2b8146095e4541fb8e5c67c2d513f888437a16d08602d00b800001c9eea12cf94e89bc47620c8ec46982dd14608a039817308c83040b600001c9e8812dc95349d448120f0f206d230015089083bc17f08c82f80c000001c9e2942c714f89d44892158ee86b02f414808dc3ba17508e02f40b000001c9dc7c2d8154c9ca4802120f106be2fe14e08e03a817d08982d80b200001c9d69a2be949099846c2070ea06982f414808cc3aa17108c02f00b800001c9d0a22c814ac9924651ff0e4c6682cc138085839016408802c00b600001c9cab22c614b499a4722070ec86b02f914f89103ae17308e02f40c000001c9c4bc2d014f09b247b2098ed86ba2fe14708bc38e16d08602e00bc00001c9bec62cd94e49bc47c20c8ec86aa2e414788cc3a818309002f00c600001c9b8cd2c694d49b04842158f346ce2f614d89043cc184092030c0ca00001c9b2cc2d114e49a447120a0ef06be2fd14788d03b016708902e40b600001c9accf2cd94ec9b247220d8f186c630114d08cc39a16e08682c00b800001c9a6e32c614c89a64742100f206e230915209203c2182095831c0c200001c9a1022be94b09984712078ed86cc30114b08e43cc17f08982f00bc00001c99aff2d015289d648821a0f486c630c14e89083d017108a02f80d600001c994f12d895409e24942150f1c6c6313158897840419409703100b200001c98eef2ca94b09a04642078edc6a42ea14708c83b018308d82e40c400001c989042cd94c09ae4872130f2c6da30915509083d418f095031c0c800001c983352bc146896244f1fb8e6c6782d613f089039816f08b02dc0b000001c97d392cb14e89b447e20b8ee06c22fa14e89043ba17408a02f00ae00001c9774c2c594d09a84762100f086d430615809243ec19709c033c0d600001c9713f2d6951c9d048921c8f446d830715789643e018809282fc0be00001c96b4a2ca14a498245d1fe0e8c6942e714808a438a17308502cc0b200001c965312e11598a104a02228f8c70032316009503d418a096030c0ca00001c95f462cd94bc99c47320e8ef06b62ec14d89003ca17b08b03000b200001c9597b2b5943c96045c2010e9c6922f614a88c43b017708b82ec0b800001c953862c914bc99446e2060ed46b62ff15109203e019609803200be00001c94d902cf151c9b44752118f086d431515a09543e419409303280c600001c947b52c294a899446f2048ea46ac2f814b88dc3ca18208f02e00b000001c941db2c1148c9a247a20d8f0c6ac2f714b08f03ae17309102f80b200001c93bd92cf14d09a247020b0ef46b6301154092c3c6188092031c0ce00001c935d42d6954c9d64902150eec6cc30514f09043c619309883540e200001c92fe12c4148c97e45c2018e906862ea14b08d83ae18a08f03080c600001c929f52ca15009a847d20e8ee46ae30515309103c217608c82e80cc00001c9240c2c514a49784571fa0e586702e614388a839817008e02d80b200001c91e242c094949924632080eb06982ef15109103c617e09203000bc00001c917f02e415bca084a52210f8470c31915a096c3e218209283180c200001c911bb2e995a49fe48c2158f0c6cc30414f890c3b217d094830c0be00001c90bc82cb15049d64862160f186d631015689443d018609703380d200001c905ae2db159ca1e4a42210f746ee31315309143ce17f08e03000b600001c8ffe12b014149524471f38e1866e2c913e889839616608782fc0b600001c8f9f52c894d099a46d2010e7c6842df14388a439817708e82e40ba00001c8f41f2be147496e4551fa0e9868a2de140086837215f08082b00a600001c8ee192d195109c84922128f286cc30114b88dc3a416e08202a00b400001c8e7fe2dc156c9f84982190f406de30e14e88d43a417408d02e40ba000 else 0x1cb11e90000000000000000000000030214f88d83c017d08b83100d200001cb0bf52c694bc9a846e2098eb86b82fa14d08f43cc18208e83040c000001cb05fb2cb14cc9b247f20b0ef06aa2f014a08a439c17108602ac0ae00001caffff2d215009d048c2148f146a42fc14c09143dc18608b03040b200001caf9f52d215149bc48220d0ec06aa2f914e09203d218109403100c200001caf4052c7947c97e45b2060ea06aa2f714e08f03ac17908e02ec0ca00001caee0f2cb94e89b248320e8efc6b62ff14d88fc3bc17208782d40b000001cae7f12e295a4a104aa2230f786f831f16009883f219809b83440ce00001cae21c2c314a897a45c2010e5c66a2de14108b038816808b03000ce00001cadbd82f59610a424bb22e0ff472e32e16489843f219f09e03600de00001cad5d72d415189de49521a0f746e0313156893c3ce18008f02f80d200001cacff12c714ec9b64742098ed86b02f714988cc3a817608c82d00ae00001caca0b2c894a099a4752080ef86b62f615088d43a017408d82ec0c000001cac4342bb948096e4531fe8e7066c2e214588a03c418b09383180be00001cabe462c394b89984652068ea86962e214688c03ac17f08b83100d200001cab86f2bf946c97e4652010e906962f414c08d43ae18409603280d600001cab27c2c814e89a44852130f346d82fd14e89083ae17808b02e40a800001caac902c794e09b046e2098ed469e2f014708c83a817f08a02c00bc00001caa6852d8955c9ee4952188f346d430614f09183d618509403440e200001caa0ca2b1940094644c1f98e686882e814908b838e17208b02dc0b800001ca9abd2d595149d048420f0ed06a42ec14888b038c17308c02f80c200001ca94d92c4149098e45f2018eb46a42f114a08f83b417d08d02e80b600001ca8ee82c7949098c4692040ec86aa2f914e08ec3c818609283180be00001ca88f92c694a89804632018e8c6922f114c88ec3ac17808b82f80b400001ca830f2c594889a047720d0ef86b42fd14c88d039a17808c82e80ce00001ca7d282bf949c99446820b8ed46b830c15209183c417d08e82fc0ae00001ca77562b994489684571fa0e5c6642d314408b43a417509083140c600001ca715d2c994d09b047b2118ef46c2302152891c3c818208c02f00cc00001ca6b542d5952c9e249d2220f806ea31715989683f019209983480cc00001ca655f2ce14fc9bc47c20e0efc6ac2fe14688dc3b817e09583180bc000)))))))))

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



private theorem b286391 : covered 286391 286464 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286464 : covered 286464 286537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286537 : covered 286537 286611 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286611 : covered 286611 286684 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286684 : covered 286684 286757 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286757 : covered 286757 286830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286830 : covered 286830 286903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286903 : covered 286903 286976 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286976 : covered 286976 287049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287049 : covered 287049 287122 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287122 : covered 287122 287196 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287196 : covered 287196 287269 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287269 : covered 287269 287342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287342 : covered 287342 287415 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287415 : covered 287415 287488 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287488 : covered 287488 287561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287561 : covered 287561 287634 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287634 : covered 287634 287707 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287707 : covered 287707 287781 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287781 : covered 287781 287854 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287854 : covered 287854 287927 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b287927 : covered 287927 288000 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288000 : covered 288000 288073 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288073 : covered 288073 288146 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288146 : covered 288146 288219 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288219 : covered 288219 288292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288292 : covered 288292 288366 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288366 : covered 288366 288439 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288439 : covered 288439 288512 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288512 : covered 288512 288585 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288585 : covered 288585 288658 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288658 : covered 288658 288731 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288731 : covered 288731 288804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288804 : covered 288804 288877 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288877 : covered 288877 288951 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b288951 : covered 288951 289024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289024 : covered 289024 289097 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289097 : covered 289097 289170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289170 : covered 289170 289243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289243 : covered 289243 289316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289316 : covered 289316 289389 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289389 : covered 289389 289462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289462 : covered 289462 289536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289536 : covered 289536 289609 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289609 : covered 289609 289682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289682 : covered 289682 289755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289755 : covered 289755 289828 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289828 : covered 289828 289901 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289901 : covered 289901 289974 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b289974 : covered 289974 290047 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290047 : covered 290047 290121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290121 : covered 290121 290194 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290194 : covered 290194 290267 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290267 : covered 290267 290340 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290340 : covered 290340 290413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290413 : covered 290413 290486 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290486 : covered 290486 290559 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290559 : covered 290559 290632 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290632 : covered 290632 290705 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290705 : covered 290705 290778 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290778 : covered 290778 290851 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290851 : covered 290851 290924 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290924 : covered 290924 290997 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b290997 : covered 290997 291070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291070 : covered 291070 291143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291143 : covered 291143 291216 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291216 : covered 291216 291290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291290 : covered 291290 291363 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291363 : covered 291363 291436 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291436 : covered 291436 291509 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291509 : covered 291509 291582 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291582 : covered 291582 291655 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291655 : covered 291655 291728 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291728 : covered 291728 291801 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291801 : covered 291801 291875 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291875 : covered 291875 291948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b291948 : covered 291948 292021 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292021 : covered 292021 292094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292094 : covered 292094 292167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292167 : covered 292167 292240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292240 : covered 292240 292313 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292313 : covered 292313 292386 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292386 : covered 292386 292460 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292460 : covered 292460 292533 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292533 : covered 292533 292606 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292606 : covered 292606 292679 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292679 : covered 292679 292752 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292752 : covered 292752 292825 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292825 : covered 292825 292898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292898 : covered 292898 292971 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b292971 : covered 292971 293045 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293045 : covered 293045 293118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293118 : covered 293118 293191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293191 : covered 293191 293264 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293264 : covered 293264 293337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293337 : covered 293337 293410 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293410 : covered 293410 293483 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293483 : covered 293483 293556 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293556 : covered 293556 293630 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293630 : covered 293630 293703 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293703 : covered 293703 293776 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293776 : covered 293776 293849 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293849 : covered 293849 293922 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293922 : covered 293922 293995 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b293995 : covered 293995 294068 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294068 : covered 294068 294141 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294141 : covered 294141 294215 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294215 : covered 294215 294288 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294288 : covered 294288 294361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294361 : covered 294361 294434 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294434 : covered 294434 294507 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294507 : covered 294507 294580 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294580 : covered 294580 294653 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294653 : covered 294653 294726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294726 : covered 294726 294800 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294800 : covered 294800 294873 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294873 : covered 294873 294946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b294946 : covered 294946 295019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295019 : covered 295019 295092 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295092 : covered 295092 295165 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295165 : covered 295165 295238 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295238 : covered 295238 295311 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295311 : covered 295311 295385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295385 : covered 295385 295458 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295458 : covered 295458 295531 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295531 : covered 295531 295604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295604 : covered 295604 295677 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295677 : covered 295677 295750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295750 : covered 295750 295823 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295823 : covered 295823 295896 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295896 : covered 295896 295970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b295970 : covered 295970 296043 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296043 : covered 296043 296116 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296116 : covered 296116 296189 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296189 : covered 296189 296262 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296262 : covered 296262 296335 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296335 : covered 296335 296408 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296408 : covered 296408 296481 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296481 : covered 296481 296555 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296555 : covered 296555 296628 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296628 : covered 296628 296701 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296701 : covered 296701 296774 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296774 : covered 296774 296847 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296847 : covered 296847 296920 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296920 : covered 296920 296993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b296993 : covered 296993 297066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297066 : covered 297066 297140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297140 : covered 297140 297213 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297213 : covered 297213 297286 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297286 : covered 297286 297359 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297359 : covered 297359 297432 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297432 : covered 297432 297505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297505 : covered 297505 297578 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297578 : covered 297578 297651 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297651 : covered 297651 297725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297725 : covered 297725 297798 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297798 : covered 297798 297871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297871 : covered 297871 297944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b297944 : covered 297944 298017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298017 : covered 298017 298090 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298090 : covered 298090 298163 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298163 : covered 298163 298236 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298236 : covered 298236 298310 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298310 : covered 298310 298383 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298383 : covered 298383 298456 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298456 : covered 298456 298529 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298529 : covered 298529 298602 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298602 : covered 298602 298675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298675 : covered 298675 298748 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298748 : covered 298748 298821 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298821 : covered 298821 298895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298895 : covered 298895 298968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b298968 : covered 298968 299041 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299041 : covered 299041 299114 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299114 : covered 299114 299187 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299187 : covered 299187 299260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299260 : covered 299260 299333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299333 : covered 299333 299406 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299406 : covered 299406 299480 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 286391 299480 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b286391 b286464) (joinCoverage b286537 (joinCoverage b286611 b286684))) (joinCoverage (joinCoverage b286757 (joinCoverage b286830 b286903)) (joinCoverage b286976 (joinCoverage b287049 b287122)))) (joinCoverage (joinCoverage (joinCoverage b287196 b287269) (joinCoverage b287342 (joinCoverage b287415 b287488))) (joinCoverage (joinCoverage b287561 (joinCoverage b287634 b287707)) (joinCoverage b287781 (joinCoverage b287854 b287927))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b288000 b288073) (joinCoverage b288146 (joinCoverage b288219 b288292))) (joinCoverage (joinCoverage b288366 (joinCoverage b288439 b288512)) (joinCoverage b288585 (joinCoverage b288658 b288731)))) (joinCoverage (joinCoverage (joinCoverage b288804 b288877) (joinCoverage b288951 (joinCoverage b289024 b289097))) (joinCoverage (joinCoverage b289170 (joinCoverage b289243 b289316)) (joinCoverage b289389 (joinCoverage b289462 b289536)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b289609 b289682) (joinCoverage b289755 (joinCoverage b289828 b289901))) (joinCoverage (joinCoverage b289974 (joinCoverage b290047 b290121)) (joinCoverage b290194 (joinCoverage b290267 b290340)))) (joinCoverage (joinCoverage (joinCoverage b290413 b290486) (joinCoverage b290559 (joinCoverage b290632 b290705))) (joinCoverage (joinCoverage b290778 (joinCoverage b290851 b290924)) (joinCoverage b290997 (joinCoverage b291070 b291143))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b291216 b291290) (joinCoverage b291363 (joinCoverage b291436 b291509))) (joinCoverage (joinCoverage b291582 (joinCoverage b291655 b291728)) (joinCoverage b291801 (joinCoverage b291875 b291948)))) (joinCoverage (joinCoverage (joinCoverage b292021 (joinCoverage b292094 b292167)) (joinCoverage b292240 (joinCoverage b292313 b292386))) (joinCoverage (joinCoverage b292460 (joinCoverage b292533 b292606)) (joinCoverage b292679 (joinCoverage b292752 b292825))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b292898 b292971) (joinCoverage b293045 (joinCoverage b293118 b293191))) (joinCoverage (joinCoverage b293264 (joinCoverage b293337 b293410)) (joinCoverage b293483 (joinCoverage b293556 b293630)))) (joinCoverage (joinCoverage (joinCoverage b293703 b293776) (joinCoverage b293849 (joinCoverage b293922 b293995))) (joinCoverage (joinCoverage b294068 (joinCoverage b294141 b294215)) (joinCoverage b294288 (joinCoverage b294361 b294434))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b294507 b294580) (joinCoverage b294653 (joinCoverage b294726 b294800))) (joinCoverage (joinCoverage b294873 (joinCoverage b294946 b295019)) (joinCoverage b295092 (joinCoverage b295165 b295238)))) (joinCoverage (joinCoverage (joinCoverage b295311 (joinCoverage b295385 b295458)) (joinCoverage b295531 (joinCoverage b295604 b295677))) (joinCoverage (joinCoverage b295750 (joinCoverage b295823 b295896)) (joinCoverage b295970 (joinCoverage b296043 b296116)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b296189 b296262) (joinCoverage b296335 (joinCoverage b296408 b296481))) (joinCoverage (joinCoverage b296555 (joinCoverage b296628 b296701)) (joinCoverage b296774 (joinCoverage b296847 b296920)))) (joinCoverage (joinCoverage (joinCoverage b296993 b297066) (joinCoverage b297140 (joinCoverage b297213 b297286))) (joinCoverage (joinCoverage b297359 (joinCoverage b297432 b297505)) (joinCoverage b297578 (joinCoverage b297651 b297725))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b297798 b297871) (joinCoverage b297944 (joinCoverage b298017 b298090))) (joinCoverage (joinCoverage b298163 (joinCoverage b298236 b298310)) (joinCoverage b298383 (joinCoverage b298456 b298529)))) (joinCoverage (joinCoverage (joinCoverage b298602 (joinCoverage b298675 b298748)) (joinCoverage b298821 (joinCoverage b298895 b298968))) (joinCoverage (joinCoverage b299041 (joinCoverage b299114 b299187)) (joinCoverage b299260 (joinCoverage b299333 b299406))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 286391 ≤ index 550000000/512 := by decide +kernel
private theorem starting_value : fast 550000000=28845356 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 550000000=28845356) (n : ℕ) (low : 550000000≤n) (bound : n≤575000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=550000000
    · rw [first,anchor]
      exact starting_value
    · have past : 550000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤575000000 by omega)
        have within : index n / 512 < 299480 := by omega
        have lower : index 550000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤575000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ550000000To575000000
