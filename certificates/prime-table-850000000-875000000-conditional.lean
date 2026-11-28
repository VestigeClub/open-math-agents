import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ850000000To875000000

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




private def radical : ℕ := 0x1690fa8fb4275e898839d0f6707f63bd9ee63ba1dadafe4233b2e0f98617aab55e707982e3401e7f615243f9dfdb4df2bce7ab9237f47afd3f6aaf88cd2cf83d907144fd1928df7029206fd0eb3b1a391463b31396d83a6bcbaf14c9eacf9f0ebe882e4aa5fa4585bcc0cf9e052e9f9904150526f67ba4dbd82e21ac57f7b16a1420b2e993e3777beef8de443dac03f819b2ee589493cad869c3c6c4f29b64c9fd003b89f661a4b7e6f0aaea51abcb8c0d33fd63db2ef0039a67879b56bbcedc37d9dba93d34ea2fd0010e99911ae46d44b189aa3b7c2f24b265711df8b9faa53d6f3d0e3fc2fc57d488f35f68ca5d413ad669e7df2a53724bd570e58c0cc49b1951204beb7451def26a75ae67e2d33b879b623cfed0947c28141abbbb52051a166e48fbf4a8ca9b65c101478b0f9de7db1851996b68e463f7ef3eeb97e73becf17f4bc25bd15758e1fc36ab10931a7e3e6399452324f8dcaf863263191883abe49e3b1f98605bbcd2f4aa7914729ddb2ee126152967f9bdf809a217e52480adb241fa4147e5aedfb6e75076d2f2d6d8132ee917b6aa84c218b9fcfa98a5f2cdc9f1647d676149da6c4f19b90d1e688a6325fe0da80036938fa335dd29ff27825a6a3b292b97b3c5dd1120807371d86b7c86e8e020cd470a386e5ca74950a19901de744d1f6ed33aa6916ae07176f5f9cb08af8679ceb36b7f025f27d78aae9d405457949897717cbdc999877d5ec6c2cbec23f46160f30e62f0e3adcef606d5198436dcc237a9de048e22e346bc0435cbb3f4a5ec001a0e3ed3a048ebba16dbc3a5203eb1443488a94836d38afe86ee120a66fc414aedcbfccf9588c35314c2d5545bc6111c05bacc1b873b5ed16d8e9b7135747409e639c08071b7297087f1ee482cb62eb3318dc707e9067842f793b6706907eb33bd574f9769ebab22bcdd8fc3ba1eba00b2cfb89bd5c9ef32a8fabf8a1fff1629bbb0e31a3f349fe170c5649d074dbd2b56f7c7d8a5d91763ba6b5beb6ae55df7caff391dfa4059916f02c74abe9b5f56345c910226f7ca945d3ad38372aa066ed573ae7b43e310121247e12ef0936e96badd8254a35926d35a74d047f0d2f4a4df675252783f91764324fcd1994340719c1ac6198abbace080a5bf4e036eaa67f8e6f43a6f0f864d18a550791f8a1877e65d9bdaa620c2aec695dfcd510bd38f75beaa98a531720ce8be2657f937529c11b6f3736f9fa4ce92cb43c9ca2070a68208193da467d2a441564a4f2b792b1fc02ca64545f26d756574f4c6ca13be1096bfd53897c2f7cf5aafcaca6e271e249742ed860e70cc80523dd400768ab40ec06bc5f29fd5ba0be1ebbe9ed36c6aa74028de19656e8004260f1640880c3b45590dae42a5aac19ef08c0892879c5e734a2aa351a3e2585de550098d53783e6d534c451471a68e9d3549849fc76d6f148fc46f5a1a0e10fbc3015b9267f2690a65275ca8d9b45d1a7204da712c2a179a4c0cdabeb5c723f36366c038e2840453ed16b27fe5de39ad087a6e752ebe882097403061d2e99b9cfa9240bce47f73cd91bc52ee534cff7ed54ecbacf39b7254b20563a26d9d8448e6c683c985a5444f8d1aa2dd559d64dc36d16a545367cbf428e0d0e7f32d1140cb78bbac6356662c2e4fa1a0d2637842d151eef67690a17cef66910c74642cd387615a960af4993c145e2f7e28a415950a01b62662bec34dfe8c87475979f68d4baad6275d0a5fabcb0d5f43138d0cf9af41122b27715a857b418feed2cf25826db2c178a106e2400ad1892cef8bbd6aaf1c6ba073f22282e66015679ed8d99b776b6b79784f46f70ffcb929e5be28e253f356068737f16443a75c531f6774248f220d4dce657fce8393c5b73796275ee48679a53cf3c915da5bd87f1a994ee166c106a2daeae9007ffb66f7774d18a5f6255a65c6aa991c9626441c5c08fbb6a181a8dccb2fa1c96144fd28f6cdb3b04a4a542846f001141341b6d73f476193c7035ba37dd5b750d48b5b332fe52c235f5344c9322f5a569d1fd0a4331952d2fd9f6de676d67ddce75e81547169b3b1c9919e7ea993001cfd58c44e4411d7a0e8b3bd3cf9d3bf7d295b394eb9d46f020078d1551e8cf1c5a730ae26b3a2f9d0441dd9c85e8c2042e8b3db8ed34854ef2f9e740e6ee57f8ef9186b929a1a92928ff2a63b4b017674d1a2534756f05c9e2b63ca4ff6defeda2388a4ea5bb3e2420e6077577328f03670152ec349552fa22c7fdd30472cb4d02a358a3f6aec2c26b04a5359e43d19afeff5c88db2d8553264633a27e3771e4940e022b2d912d1fdb131f2853c6616447ab0eda7c93db4690184cd68da097f200564cdb5aed4d3d0099abffca01d5d27d07291f8ff1a3724920ce0821ef1cb64fc9b79f4b9244dc86a18d9db0396af2b857cfaae3987481cbe47e76da5890010436d142ef230ad56925d5dd5a76f46120740abd2b481a6aa50f0c37d3d6cd6bd31544a0109f75a9da3233310d9d1d5837e1aff75f1887aece840d153c3932fe44fb8cc8303ffb0e6ae91a1e0e77882d549e4e16caf295cd05d10a393b626f314080956d71a0fef77db80355f24a8109b71c4e8d1f3f8096d8d20a0f94ff7ef429b68fd32cdcf0968593e7fc8668e42ad48ea46c3a98c992785f848fe6e68e26b8015bece06de1b6764068988ba33d1d230667b987ce07626736ab17cbaf0e942bc3d339720c37d6f85ac697137204e95719d168d67e71f4500fda655764a408f2437eee392280d7dd9e882cde5bdc6506854117826ab7f21f2b8e54d183f42624a03917154d8b58dc1ca81ce1b1209e721a9605d0bb51464cecfad0d330816021ef25ff4b1fd686b94aa83ee7057cc2222ede6a55ccb8f40b2d1ec9b5e608a3db768427335475f180eeb5e0baa7a507cc3d6b71e2015073c33ed574c56abc4256649f385b5fb1739da2025fdd63e3ce798d3cd64503d7f2cbb3cbc75fa9b455e31336bcf05dc195884ef10fd8c1b7326ccbd6a65964f16e42173988d8a99fac66c8dde7927f9efc7e1816339d3838c183a52f40eaff54a927bda4eb646fbe7ce9c115a5a8ffe00d11c34ba2f0e1a08253a8b022d0d5f151835f0ade50c7396444f3b583225f72d256e6755609e04cdc3b720e04e18ceae18a8633cba4ac03b8ba7755b81743dbb5bd95b3ffd4d9e579e9a05bf03f064279f73b068df9009291c4ecd7eae493253e5dc8a8d17bec9620a4c9c54d10def3c3c4ee693727bd2240366c1162ecfd1b3d19a666b81ae8c20916bc480bc8aa0f3ab40346d3cf08b96fb34a5e632653cdc56bc78f1178f9be4124aac6b8add292f30e922bf7bf4617e12d43c2224ed2008a8a28b127d1800e8132f543276cce271b8a7af3245e596ef6e1d76cc6b66e2e4a75acc47988dd82e09e5de8e36d7798a3eae43e05aaeb645c0a72a56ba1e6d7deaf8adf2ccd8e7026fad858196b142c02cbae66d00509af4a35ca05c5a4a3e35efedc832c86ec928087a6aedcfa7c88d6baa89c5824d253aa6d4d80bbfa213104ef882b2e425dc0f4695b3267e4f29b7c1fae1d3cd3ed6a01b0bfe0e5defc2edc8ea6292fdb5f7ae793cf908fda74124fe028b29c3fd1fa7bb5f4464d114dacfa7b6399f699d3da2304cc3532b034835797ab2a8ef1b4d7087fbe1920bcafe4a2daa280943558e5ccbfb2b86edf8b80d6f2b50119810eff14c7a11def6373300ac11eef5552e0c79f6ee50c3fafc6417c5090b5e98f1d885502d8096ec34fea1f9ecd0010ffdb428887ac597b94e572c13657f7802d65f57b946732b5bd614f0d0bbc8292435673a94025b18b37da63a175f16b42ba353bbb11b05d14c12bbc063e6c16a79973b1a6213769a9a525dbd798d9deddeb586987fba3810e882df145dd2288d73ef147a3f83bfa2e3f5c32119e02272e1a109ab796ca932b242826aa1461d018374aceac0b231e831edb10f70eabc7183413727a8126cc5f59e4b25d425d6fe5088b49e15db13db567f2b5ddc77cbe3aad7b4aa421792d41ae42af921de33d7088f2b32a0c1501e4e283d4734fb8fe78682e0cdd950239c1928aba5036d6fa347e6f83e93cc8ac5efdebacd53040f52f2332dddca9d690f07949d6b69c399901d34473fabc945a73b5813e632ef8a5ad677eee43d02ed471113f35d905f4bab41d1815120058b5aa8073df50d304bb295321026e3bad12be103b1931ddfd770fb7808a4dd84b95fdb25358acfc6cd99f9402b758978090c13a467a1e702e0c804ed0c43021845622f5b305287f82f09a6fee2f79a451826b7ad01b778f247929c8431c2c622c45b87da5637af2d68a673e91fbe7afcc15b0be797892bf6d2a0a37b394a5a218d9f985c170b27ad6ddb1139073af14e567f519538adef0e42e3cb67bb77cdeabaa979db1616dcf14121148a83c3f3f1730f678050a44cf4dee59ed8a9cf9c7d3608fa634dd84c46d95ae8651188b718f50879c193fa83806ffae43216327e2a2f3b31861eb882a23b6b9289ffadc60467044527c791b5613ec91d7433013a61bd1babee475b3833c09baccdb9d4a3769c9c5a32dcdedfff867e5687748db5c9d0dea8b8c4318a1287fbbbf39997186c37ff5974726a21d1f8dfd694122b7945369a925e1bc9b59ff77f71709b473ab5914380c67ee2367461b9e76a5ce191171686551dbcca51be4254e66d0b3aa75731b204896b93f345d62437bc4ba73a6d30137df5037715ea538c43a818d58b3cffe233c14b0f38ce8b4f3a42fcf06f55fc986f6abbc54355017c9793334387c419f6ae84f2d230c1deb3829751b14f190a9c402601947de885381155c6f0349132125e770b5aaa30b9503b043ce1f88491f564aeb7fbf4f80dedadc483410b4301dcb7825d9f49e0fd8b55057cc98b1a13f4ba69976e4bef0f21e0dd36b9d2ba7565ca4138cf56a48dd2cbef940866a26d69698d477517833c29440393ab4aa52ed1b87695b3e117cd8ed8b6cb230c7fd09915004979d8476765c1b0bf3694a4d0389b91e6037a04e77cf437eb5116c9f82dff598ed7abfcd236e9220605370999ca35b9446bb6c7ded06a0c83669569aa03ba3a27ee8de9f5d68c8a49bc3842f9fc29cc1883e41625e9be9440fc88c70e90d28467e62cdd578f275ee6f10c2d1d1b8eb9079b64c64c693d3033753bee62b14e91dd339cf02d4ddb884d4863db1dc4123930f28850d29156a4c1e8ebe83b6e3fb9371f5d8a759e4bd97bcc961438a74cdd8901578ebb468f6663f417569de183c1e3516d6f170316bdcec42cb518781fae99bd6f9626a8ce5be83c692c5c7d66ac5f6a3e63c70750d9a836b9998abc4e100f83dae6575a9f4fe9e9a053faf4c9d1f8af80fa0278ddd95cb36f9dfcc303b784d2848bb1b819d2ff0ce11618a5f712e84f64a80a094ce7fd8eb11afa52805254c3a0ab33f1390609d0e6b0efc014b4b173f8e5e4d5a3272728e1559e81eb35a500b53546988eb97f01fc46e108f8fe60ef74c7fb245b87299349eb60733c81ae60b1840874b8ab5755b32ea208d8a6a59bf395198916a9ebceb0d82f44be30d470d45104c2e5a7fa4a8868f8da0425f6924fc308434b3c574294cae6a753f3f99becca2da36ca60d2d68fff6b08b92f05e546d1aeb3f489d15c54679e4ca8988df25a2d01cad27f1d555aa91ad5c97c842d57d646f8f2bcb222fd2e372d2dba5638a243d915cbb49c1fb324e262c05c80dd1f7656aa56eec76ff8b75d1c909b9f4a65fa31f6113795172cacdf2eb9ecedd35238594a19b43c4d4ab28ac0d8bfa07659a040cf07dab83c947ce3c3e0247df127c126105bf9afff4561a7cb2d4d0b09d2ad4a3aec42c2512101518c563af32723003e4c4e81aa43257752d5a5dfc443dacef4cab99b4bd9f6d9a93be7bc45917e3ddb5db902819cccf1195538734a6df6e35413bcf889faa50b110b26ca8c27f25b33d8afaf359856f84b3cce8be4cb41defee9c30bc4db062c3808bd4739dc43560c2a5b7e0621ddb2f4f37e1c5da86f88d79501fe3904d6855240422e4e7bd0cd85476b4eef9059e231d518e23475f6e01980869100f7aa744b8774a28e2848dd2c21170d612f97b5ef72e4a614eb0721a19f181eb673951b03b3cff18bfc66ed62757b72bd58b6ea3635a59732f321e6d6441fa2bf562eb7f15d5562e8e197f77c069af28eb9d56c33941515b24aff9da27a0706f00a54629b62dccfb5d472cbbc0b39b361a1ad4be6e7392447ce034dac5c0d9842d90e7d2731f6ae5eb69b1d4532231125a20ce6bebae9dfa4508afdfc067e8f719fdb5df4ee6f5a053ae421b3c4de4db10eeb7dcc9b1e4f79acaa4a79fba2d548cac3732375260fcc16705c562239472df0ff864e29acbaa1e4b57d7b5e9a6311c47dc3ba09561c81159f7bb4e9a781bd6e88912df14db31727aefce429d437f700e14e5b4df36f02c64cdcaad8bd5d9c5339a3bff9ed428ee5005c024fb9aada3c775c00e012e2e0ab9bea80628b234a1b8cd1665a70427324fa9d58aa65e91528046c0d656cb7e7e10dd336db289afff35fb6b2cab9d1f75983a6be25b93a0d25af015569c80b4085370919367f06a73b0cbc29bd39727730aa80bd35b5c6dfeb798904b3df4e3d97a514328aff46458174019e1562ab983c0639d0db92912d30896e5df5332663cef812c8e6bb5aabd77176e1b8b498ad7b065b353a15a7efe7ad08f4f3d1d12ac120eee7726a7bea864b8b88048898b345b80a8156a11ef7530f96ffffe477bc3d36d27cddbdbf8bb0e0cb6776376950548c1f9948841b852d9b6a87ffd2099681aa15e06da38ef4ba9ef4043492f75f6499296f88397b443788699719e68d1a38ac4f9a133cbb1f0aa55d42dbf4700ca966745453eb51e23744d363ea8557ab9c50cc597342ce4d323cab9bafce0caf607cb76a2a59c094b08ef5e691111182a6336106add5c35012bef81d5610fbe603d35e24d18933412614447a9939640fad7283aef3eb8784869b6d6724147a9bf18441b521fd500bba25ac6a1018c7ff358ef002eed70dae91a867d9bc9ac8834bfd4a4d0561aa71603d941165cf3e4ff1457ae1b620c34385282cd182e50dcc237faf5b7034a2abb7f251c6e3f1ab5e5171ae9c21829952039f6ae1e10e0c53f29726af8411e72fdd58629886d796f94b7079270b1b76b8cb990687885c6eb4debc59c51130651ba3c29ee620f577ae1df9e039fc7a715b162f8314c911807b327cdc8b428626b0bd0c4af3e03d2c60b4e46d6bf5c54e3266e9875b9c832f6e72b57b1ec740028d3ecb9c46497b7021aede0472ccf0e1bfc1ea345dc2029251ece39f363c6dcf281b5d6329b7799e8c6c952f7bfacdcc8cf89f49d76407733fe9808b1598cab02a10e35218fb6fdeb906c0947276e38b529429402f5555b72126d373184e9c56471ff199a4e9ba7cdca1f95548ce7f71520d8aa2303ffdcfda24211b365d551566

private def light (n : ℕ) : Bool :=
  if n≤171 then decide n.Prime else n.gcd 1241018070217667823424840524103103992616605577501693185388951803611996075221691752992751978120487585576464959501670387052809889858690710767331242032218484364310473577889968548278290754541561964852153468318044293239598173696899657235903947616152278558180061176365108428800000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤29580) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 171 = 1241018070217667823424840524103103992616605577501693185388951803611996075221691752992751978120487585576464959501670387052809889858690710767331242032218484364310473577889968548278290754541561964852153468318044293239598173696899657235903947616152278558180061176365108428800000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 171 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤29580 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 57 := by unfold smallValid; decide +kernel

private theorem sp57 : smallValid 57 58 := by unfold smallValid; decide +kernel

private theorem sp115 : smallValid 115 58 := by unfold smallValid; decide +kernel

private theorem sp173 : smallValid 173 58 := by unfold smallValid; decide +kernel

private theorem sp231 : smallValid 231 57 := by unfold smallValid; decide +kernel

private theorem sp288 : smallValid 288 58 := by unfold smallValid; decide +kernel

private theorem sp346 : smallValid 346 58 := by unfold smallValid; decide +kernel

private theorem sp404 : smallValid 404 58 := by unfold smallValid; decide +kernel

private theorem sp462 : smallValid 462 57 := by unfold smallValid; decide +kernel

private theorem sp519 : smallValid 519 58 := by unfold smallValid; decide +kernel

private theorem sp577 : smallValid 577 58 := by unfold smallValid; decide +kernel

private theorem sp635 : smallValid 635 58 := by unfold smallValid; decide +kernel

private theorem sp693 : smallValid 693 57 := by unfold smallValid; decide +kernel

private theorem sp750 : smallValid 750 58 := by unfold smallValid; decide +kernel

private theorem sp808 : smallValid 808 58 := by unfold smallValid; decide +kernel

private theorem sp866 : smallValid 866 58 := by unfold smallValid; decide +kernel

private theorem sp924 : smallValid 924 57 := by unfold smallValid; decide +kernel

private theorem sp981 : smallValid 981 58 := by unfold smallValid; decide +kernel

private theorem sp1039 : smallValid 1039 58 := by unfold smallValid; decide +kernel

private theorem sp1097 : smallValid 1097 58 := by unfold smallValid; decide +kernel

private theorem sp1155 : smallValid 1155 57 := by unfold smallValid; decide +kernel

private theorem sp1212 : smallValid 1212 58 := by unfold smallValid; decide +kernel

private theorem sp1270 : smallValid 1270 58 := by unfold smallValid; decide +kernel

private theorem sp1328 : smallValid 1328 58 := by unfold smallValid; decide +kernel

private theorem sp1386 : smallValid 1386 57 := by unfold smallValid; decide +kernel

private theorem sp1443 : smallValid 1443 58 := by unfold smallValid; decide +kernel

private theorem sp1501 : smallValid 1501 58 := by unfold smallValid; decide +kernel

private theorem sp1559 : smallValid 1559 58 := by unfold smallValid; decide +kernel

private theorem sp1617 : smallValid 1617 57 := by unfold smallValid; decide +kernel

private theorem sp1674 : smallValid 1674 58 := by unfold smallValid; decide +kernel

private theorem sp1732 : smallValid 1732 58 := by unfold smallValid; decide +kernel

private theorem sp1790 : smallValid 1790 58 := by unfold smallValid; decide +kernel

private theorem sp1848 : smallValid 1848 57 := by unfold smallValid; decide +kernel

private theorem sp1905 : smallValid 1905 58 := by unfold smallValid; decide +kernel

private theorem sp1963 : smallValid 1963 58 := by unfold smallValid; decide +kernel

private theorem sp2021 : smallValid 2021 58 := by unfold smallValid; decide +kernel

private theorem sp2079 : smallValid 2079 57 := by unfold smallValid; decide +kernel

private theorem sp2136 : smallValid 2136 58 := by unfold smallValid; decide +kernel

private theorem sp2194 : smallValid 2194 58 := by unfold smallValid; decide +kernel

private theorem sp2252 : smallValid 2252 58 := by unfold smallValid; decide +kernel

private theorem sp2310 : smallValid 2310 57 := by unfold smallValid; decide +kernel

private theorem sp2367 : smallValid 2367 58 := by unfold smallValid; decide +kernel

private theorem sp2425 : smallValid 2425 58 := by unfold smallValid; decide +kernel

private theorem sp2483 : smallValid 2483 58 := by unfold smallValid; decide +kernel

private theorem sp2541 : smallValid 2541 57 := by unfold smallValid; decide +kernel

private theorem sp2598 : smallValid 2598 58 := by unfold smallValid; decide +kernel

private theorem sp2656 : smallValid 2656 58 := by unfold smallValid; decide +kernel

private theorem sp2714 : smallValid 2714 58 := by unfold smallValid; decide +kernel

private theorem sp2772 : smallValid 2772 57 := by unfold smallValid; decide +kernel

private theorem sp2829 : smallValid 2829 58 := by unfold smallValid; decide +kernel

private theorem sp2887 : smallValid 2887 58 := by unfold smallValid; decide +kernel

private theorem sp2945 : smallValid 2945 58 := by unfold smallValid; decide +kernel

private theorem sp3003 : smallValid 3003 57 := by unfold smallValid; decide +kernel

private theorem sp3060 : smallValid 3060 58 := by unfold smallValid; decide +kernel

private theorem sp3118 : smallValid 3118 58 := by unfold smallValid; decide +kernel

private theorem sp3176 : smallValid 3176 58 := by unfold smallValid; decide +kernel

private theorem sp3234 : smallValid 3234 57 := by unfold smallValid; decide +kernel

private theorem sp3291 : smallValid 3291 58 := by unfold smallValid; decide +kernel

private theorem sp3349 : smallValid 3349 58 := by unfold smallValid; decide +kernel

private theorem sp3407 : smallValid 3407 58 := by unfold smallValid; decide +kernel

private theorem sp3465 : smallValid 3465 58 := by unfold smallValid; decide +kernel

private theorem sp3523 : smallValid 3523 58 := by unfold smallValid; decide +kernel

private theorem sp3581 : smallValid 3581 58 := by unfold smallValid; decide +kernel

private theorem sp3639 : smallValid 3639 58 := by unfold smallValid; decide +kernel

private theorem sp3697 : smallValid 3697 57 := by unfold smallValid; decide +kernel

private theorem sp3754 : smallValid 3754 58 := by unfold smallValid; decide +kernel

private theorem sp3812 : smallValid 3812 58 := by unfold smallValid; decide +kernel

private theorem sp3870 : smallValid 3870 58 := by unfold smallValid; decide +kernel

private theorem sp3928 : smallValid 3928 57 := by unfold smallValid; decide +kernel

private theorem sp3985 : smallValid 3985 58 := by unfold smallValid; decide +kernel

private theorem sp4043 : smallValid 4043 58 := by unfold smallValid; decide +kernel

private theorem sp4101 : smallValid 4101 58 := by unfold smallValid; decide +kernel

private theorem sp4159 : smallValid 4159 57 := by unfold smallValid; decide +kernel

private theorem sp4216 : smallValid 4216 58 := by unfold smallValid; decide +kernel

private theorem sp4274 : smallValid 4274 58 := by unfold smallValid; decide +kernel

private theorem sp4332 : smallValid 4332 58 := by unfold smallValid; decide +kernel

private theorem sp4390 : smallValid 4390 57 := by unfold smallValid; decide +kernel

private theorem sp4447 : smallValid 4447 58 := by unfold smallValid; decide +kernel

private theorem sp4505 : smallValid 4505 58 := by unfold smallValid; decide +kernel

private theorem sp4563 : smallValid 4563 58 := by unfold smallValid; decide +kernel

private theorem sp4621 : smallValid 4621 57 := by unfold smallValid; decide +kernel

private theorem sp4678 : smallValid 4678 58 := by unfold smallValid; decide +kernel

private theorem sp4736 : smallValid 4736 58 := by unfold smallValid; decide +kernel

private theorem sp4794 : smallValid 4794 58 := by unfold smallValid; decide +kernel

private theorem sp4852 : smallValid 4852 57 := by unfold smallValid; decide +kernel

private theorem sp4909 : smallValid 4909 58 := by unfold smallValid; decide +kernel

private theorem sp4967 : smallValid 4967 58 := by unfold smallValid; decide +kernel

private theorem sp5025 : smallValid 5025 58 := by unfold smallValid; decide +kernel

private theorem sp5083 : smallValid 5083 57 := by unfold smallValid; decide +kernel

private theorem sp5140 : smallValid 5140 58 := by unfold smallValid; decide +kernel

private theorem sp5198 : smallValid 5198 58 := by unfold smallValid; decide +kernel

private theorem sp5256 : smallValid 5256 58 := by unfold smallValid; decide +kernel

private theorem sp5314 : smallValid 5314 58 := by unfold smallValid; decide +kernel

private theorem sp5372 : smallValid 5372 58 := by unfold smallValid; decide +kernel

private theorem sp5430 : smallValid 5430 58 := by unfold smallValid; decide +kernel

private theorem sp5488 : smallValid 5488 58 := by unfold smallValid; decide +kernel

private theorem sp5546 : smallValid 5546 57 := by unfold smallValid; decide +kernel

private theorem sp5603 : smallValid 5603 58 := by unfold smallValid; decide +kernel

private theorem sp5661 : smallValid 5661 58 := by unfold smallValid; decide +kernel

private theorem sp5719 : smallValid 5719 58 := by unfold smallValid; decide +kernel

private theorem sp5777 : smallValid 5777 57 := by unfold smallValid; decide +kernel

private theorem sp5834 : smallValid 5834 58 := by unfold smallValid; decide +kernel

private theorem sp5892 : smallValid 5892 58 := by unfold smallValid; decide +kernel

private theorem sp5950 : smallValid 5950 58 := by unfold smallValid; decide +kernel

private theorem sp6008 : smallValid 6008 57 := by unfold smallValid; decide +kernel

private theorem sp6065 : smallValid 6065 58 := by unfold smallValid; decide +kernel

private theorem sp6123 : smallValid 6123 58 := by unfold smallValid; decide +kernel

private theorem sp6181 : smallValid 6181 58 := by unfold smallValid; decide +kernel

private theorem sp6239 : smallValid 6239 57 := by unfold smallValid; decide +kernel

private theorem sp6296 : smallValid 6296 58 := by unfold smallValid; decide +kernel

private theorem sp6354 : smallValid 6354 58 := by unfold smallValid; decide +kernel

private theorem sp6412 : smallValid 6412 58 := by unfold smallValid; decide +kernel

private theorem sp6470 : smallValid 6470 57 := by unfold smallValid; decide +kernel

private theorem sp6527 : smallValid 6527 58 := by unfold smallValid; decide +kernel

private theorem sp6585 : smallValid 6585 58 := by unfold smallValid; decide +kernel

private theorem sp6643 : smallValid 6643 58 := by unfold smallValid; decide +kernel

private theorem sp6701 : smallValid 6701 57 := by unfold smallValid; decide +kernel

private theorem sp6758 : smallValid 6758 58 := by unfold smallValid; decide +kernel

private theorem sp6816 : smallValid 6816 58 := by unfold smallValid; decide +kernel

private theorem sp6874 : smallValid 6874 58 := by unfold smallValid; decide +kernel

private theorem sp6932 : smallValid 6932 57 := by unfold smallValid; decide +kernel

private theorem sp6989 : smallValid 6989 58 := by unfold smallValid; decide +kernel

private theorem sp7047 : smallValid 7047 58 := by unfold smallValid; decide +kernel

private theorem sp7105 : smallValid 7105 58 := by unfold smallValid; decide +kernel

private theorem sp7163 : smallValid 7163 58 := by unfold smallValid; decide +kernel

private theorem sp7221 : smallValid 7221 58 := by unfold smallValid; decide +kernel

private theorem sp7279 : smallValid 7279 58 := by unfold smallValid; decide +kernel

private theorem sp7337 : smallValid 7337 58 := by unfold smallValid; decide +kernel

private theorem sp7395 : smallValid 7395 57 := by unfold smallValid; decide +kernel

private theorem sp7452 : smallValid 7452 58 := by unfold smallValid; decide +kernel

private theorem sp7510 : smallValid 7510 58 := by unfold smallValid; decide +kernel

private theorem sp7568 : smallValid 7568 58 := by unfold smallValid; decide +kernel

private theorem sp7626 : smallValid 7626 57 := by unfold smallValid; decide +kernel

private theorem sp7683 : smallValid 7683 58 := by unfold smallValid; decide +kernel

private theorem sp7741 : smallValid 7741 58 := by unfold smallValid; decide +kernel

private theorem sp7799 : smallValid 7799 58 := by unfold smallValid; decide +kernel

private theorem sp7857 : smallValid 7857 57 := by unfold smallValid; decide +kernel

private theorem sp7914 : smallValid 7914 58 := by unfold smallValid; decide +kernel

private theorem sp7972 : smallValid 7972 58 := by unfold smallValid; decide +kernel

private theorem sp8030 : smallValid 8030 58 := by unfold smallValid; decide +kernel

private theorem sp8088 : smallValid 8088 57 := by unfold smallValid; decide +kernel

private theorem sp8145 : smallValid 8145 58 := by unfold smallValid; decide +kernel

private theorem sp8203 : smallValid 8203 58 := by unfold smallValid; decide +kernel

private theorem sp8261 : smallValid 8261 58 := by unfold smallValid; decide +kernel

private theorem sp8319 : smallValid 8319 57 := by unfold smallValid; decide +kernel

private theorem sp8376 : smallValid 8376 58 := by unfold smallValid; decide +kernel

private theorem sp8434 : smallValid 8434 58 := by unfold smallValid; decide +kernel

private theorem sp8492 : smallValid 8492 58 := by unfold smallValid; decide +kernel

private theorem sp8550 : smallValid 8550 57 := by unfold smallValid; decide +kernel

private theorem sp8607 : smallValid 8607 58 := by unfold smallValid; decide +kernel

private theorem sp8665 : smallValid 8665 58 := by unfold smallValid; decide +kernel

private theorem sp8723 : smallValid 8723 58 := by unfold smallValid; decide +kernel

private theorem sp8781 : smallValid 8781 57 := by unfold smallValid; decide +kernel

private theorem sp8838 : smallValid 8838 58 := by unfold smallValid; decide +kernel

private theorem sp8896 : smallValid 8896 58 := by unfold smallValid; decide +kernel

private theorem sp8954 : smallValid 8954 58 := by unfold smallValid; decide +kernel

private theorem sp9012 : smallValid 9012 57 := by unfold smallValid; decide +kernel

private theorem sp9069 : smallValid 9069 58 := by unfold smallValid; decide +kernel

private theorem sp9127 : smallValid 9127 58 := by unfold smallValid; decide +kernel

private theorem sp9185 : smallValid 9185 58 := by unfold smallValid; decide +kernel

private theorem sp9243 : smallValid 9243 57 := by unfold smallValid; decide +kernel

private theorem sp9300 : smallValid 9300 58 := by unfold smallValid; decide +kernel

private theorem sp9358 : smallValid 9358 58 := by unfold smallValid; decide +kernel

private theorem sp9416 : smallValid 9416 58 := by unfold smallValid; decide +kernel

private theorem sp9474 : smallValid 9474 57 := by unfold smallValid; decide +kernel

private theorem sp9531 : smallValid 9531 58 := by unfold smallValid; decide +kernel

private theorem sp9589 : smallValid 9589 58 := by unfold smallValid; decide +kernel

private theorem sp9647 : smallValid 9647 58 := by unfold smallValid; decide +kernel

private theorem sp9705 : smallValid 9705 57 := by unfold smallValid; decide +kernel

private theorem sp9762 : smallValid 9762 58 := by unfold smallValid; decide +kernel

private theorem sp9820 : smallValid 9820 58 := by unfold smallValid; decide +kernel

private theorem sp9878 : smallValid 9878 58 := by unfold smallValid; decide +kernel

private theorem sp9936 : smallValid 9936 57 := by unfold smallValid; decide +kernel

private theorem sp9993 : smallValid 9993 58 := by unfold smallValid; decide +kernel

private theorem sp10051 : smallValid 10051 58 := by unfold smallValid; decide +kernel

private theorem sp10109 : smallValid 10109 58 := by unfold smallValid; decide +kernel

private theorem sp10167 : smallValid 10167 57 := by unfold smallValid; decide +kernel

private theorem sp10224 : smallValid 10224 58 := by unfold smallValid; decide +kernel

private theorem sp10282 : smallValid 10282 58 := by unfold smallValid; decide +kernel

private theorem sp10340 : smallValid 10340 58 := by unfold smallValid; decide +kernel

private theorem sp10398 : smallValid 10398 57 := by unfold smallValid; decide +kernel

private theorem sp10455 : smallValid 10455 58 := by unfold smallValid; decide +kernel

private theorem sp10513 : smallValid 10513 58 := by unfold smallValid; decide +kernel

private theorem sp10571 : smallValid 10571 58 := by unfold smallValid; decide +kernel

private theorem sp10629 : smallValid 10629 57 := by unfold smallValid; decide +kernel

private theorem sp10686 : smallValid 10686 58 := by unfold smallValid; decide +kernel

private theorem sp10744 : smallValid 10744 58 := by unfold smallValid; decide +kernel

private theorem sp10802 : smallValid 10802 58 := by unfold smallValid; decide +kernel

private theorem sp10860 : smallValid 10860 58 := by unfold smallValid; decide +kernel

private theorem sp10918 : smallValid 10918 58 := by unfold smallValid; decide +kernel

private theorem sp10976 : smallValid 10976 58 := by unfold smallValid; decide +kernel

private theorem sp11034 : smallValid 11034 58 := by unfold smallValid; decide +kernel

private theorem sp11092 : smallValid 11092 57 := by unfold smallValid; decide +kernel

private theorem sp11149 : smallValid 11149 58 := by unfold smallValid; decide +kernel

private theorem sp11207 : smallValid 11207 58 := by unfold smallValid; decide +kernel

private theorem sp11265 : smallValid 11265 58 := by unfold smallValid; decide +kernel

private theorem sp11323 : smallValid 11323 57 := by unfold smallValid; decide +kernel

private theorem sp11380 : smallValid 11380 58 := by unfold smallValid; decide +kernel

private theorem sp11438 : smallValid 11438 58 := by unfold smallValid; decide +kernel

private theorem sp11496 : smallValid 11496 58 := by unfold smallValid; decide +kernel

private theorem sp11554 : smallValid 11554 57 := by unfold smallValid; decide +kernel

private theorem sp11611 : smallValid 11611 58 := by unfold smallValid; decide +kernel

private theorem sp11669 : smallValid 11669 58 := by unfold smallValid; decide +kernel

private theorem sp11727 : smallValid 11727 58 := by unfold smallValid; decide +kernel

private theorem sp11785 : smallValid 11785 57 := by unfold smallValid; decide +kernel

private theorem sp11842 : smallValid 11842 58 := by unfold smallValid; decide +kernel

private theorem sp11900 : smallValid 11900 58 := by unfold smallValid; decide +kernel

private theorem sp11958 : smallValid 11958 58 := by unfold smallValid; decide +kernel

private theorem sp12016 : smallValid 12016 57 := by unfold smallValid; decide +kernel

private theorem sp12073 : smallValid 12073 58 := by unfold smallValid; decide +kernel

private theorem sp12131 : smallValid 12131 58 := by unfold smallValid; decide +kernel

private theorem sp12189 : smallValid 12189 58 := by unfold smallValid; decide +kernel

private theorem sp12247 : smallValid 12247 57 := by unfold smallValid; decide +kernel

private theorem sp12304 : smallValid 12304 58 := by unfold smallValid; decide +kernel

private theorem sp12362 : smallValid 12362 58 := by unfold smallValid; decide +kernel

private theorem sp12420 : smallValid 12420 58 := by unfold smallValid; decide +kernel

private theorem sp12478 : smallValid 12478 57 := by unfold smallValid; decide +kernel

private theorem sp12535 : smallValid 12535 58 := by unfold smallValid; decide +kernel

private theorem sp12593 : smallValid 12593 58 := by unfold smallValid; decide +kernel

private theorem sp12651 : smallValid 12651 58 := by unfold smallValid; decide +kernel

private theorem sp12709 : smallValid 12709 58 := by unfold smallValid; decide +kernel

private theorem sp12767 : smallValid 12767 58 := by unfold smallValid; decide +kernel

private theorem sp12825 : smallValid 12825 58 := by unfold smallValid; decide +kernel

private theorem sp12883 : smallValid 12883 58 := by unfold smallValid; decide +kernel

private theorem sp12941 : smallValid 12941 57 := by unfold smallValid; decide +kernel

private theorem sp12998 : smallValid 12998 58 := by unfold smallValid; decide +kernel

private theorem sp13056 : smallValid 13056 58 := by unfold smallValid; decide +kernel

private theorem sp13114 : smallValid 13114 58 := by unfold smallValid; decide +kernel

private theorem sp13172 : smallValid 13172 57 := by unfold smallValid; decide +kernel

private theorem sp13229 : smallValid 13229 58 := by unfold smallValid; decide +kernel

private theorem sp13287 : smallValid 13287 58 := by unfold smallValid; decide +kernel

private theorem sp13345 : smallValid 13345 58 := by unfold smallValid; decide +kernel

private theorem sp13403 : smallValid 13403 57 := by unfold smallValid; decide +kernel

private theorem sp13460 : smallValid 13460 58 := by unfold smallValid; decide +kernel

private theorem sp13518 : smallValid 13518 58 := by unfold smallValid; decide +kernel

private theorem sp13576 : smallValid 13576 58 := by unfold smallValid; decide +kernel

private theorem sp13634 : smallValid 13634 57 := by unfold smallValid; decide +kernel

private theorem sp13691 : smallValid 13691 58 := by unfold smallValid; decide +kernel

private theorem sp13749 : smallValid 13749 58 := by unfold smallValid; decide +kernel

private theorem sp13807 : smallValid 13807 58 := by unfold smallValid; decide +kernel

private theorem sp13865 : smallValid 13865 57 := by unfold smallValid; decide +kernel

private theorem sp13922 : smallValid 13922 58 := by unfold smallValid; decide +kernel

private theorem sp13980 : smallValid 13980 58 := by unfold smallValid; decide +kernel

private theorem sp14038 : smallValid 14038 58 := by unfold smallValid; decide +kernel

private theorem sp14096 : smallValid 14096 57 := by unfold smallValid; decide +kernel

private theorem sp14153 : smallValid 14153 58 := by unfold smallValid; decide +kernel

private theorem sp14211 : smallValid 14211 58 := by unfold smallValid; decide +kernel

private theorem sp14269 : smallValid 14269 58 := by unfold smallValid; decide +kernel

private theorem sp14327 : smallValid 14327 57 := by unfold smallValid; decide +kernel

private theorem sp14384 : smallValid 14384 58 := by unfold smallValid; decide +kernel

private theorem sp14442 : smallValid 14442 58 := by unfold smallValid; decide +kernel

private theorem sp14500 : smallValid 14500 58 := by unfold smallValid; decide +kernel

private theorem sp14558 : smallValid 14558 58 := by unfold smallValid; decide +kernel

private theorem sp14616 : smallValid 14616 58 := by unfold smallValid; decide +kernel

private theorem sp14674 : smallValid 14674 58 := by unfold smallValid; decide +kernel

private theorem sp14732 : smallValid 14732 58 := by unfold smallValid; decide +kernel

private theorem sp14790 : smallValid 14790 57 := by unfold smallValid; decide +kernel

private theorem sp14847 : smallValid 14847 58 := by unfold smallValid; decide +kernel

private theorem sp14905 : smallValid 14905 58 := by unfold smallValid; decide +kernel

private theorem sp14963 : smallValid 14963 58 := by unfold smallValid; decide +kernel

private theorem sp15021 : smallValid 15021 57 := by unfold smallValid; decide +kernel

private theorem sp15078 : smallValid 15078 58 := by unfold smallValid; decide +kernel

private theorem sp15136 : smallValid 15136 58 := by unfold smallValid; decide +kernel

private theorem sp15194 : smallValid 15194 58 := by unfold smallValid; decide +kernel

private theorem sp15252 : smallValid 15252 57 := by unfold smallValid; decide +kernel

private theorem sp15309 : smallValid 15309 58 := by unfold smallValid; decide +kernel

private theorem sp15367 : smallValid 15367 58 := by unfold smallValid; decide +kernel

private theorem sp15425 : smallValid 15425 58 := by unfold smallValid; decide +kernel

private theorem sp15483 : smallValid 15483 57 := by unfold smallValid; decide +kernel

private theorem sp15540 : smallValid 15540 58 := by unfold smallValid; decide +kernel

private theorem sp15598 : smallValid 15598 58 := by unfold smallValid; decide +kernel

private theorem sp15656 : smallValid 15656 58 := by unfold smallValid; decide +kernel

private theorem sp15714 : smallValid 15714 57 := by unfold smallValid; decide +kernel

private theorem sp15771 : smallValid 15771 58 := by unfold smallValid; decide +kernel

private theorem sp15829 : smallValid 15829 58 := by unfold smallValid; decide +kernel

private theorem sp15887 : smallValid 15887 58 := by unfold smallValid; decide +kernel

private theorem sp15945 : smallValid 15945 57 := by unfold smallValid; decide +kernel

private theorem sp16002 : smallValid 16002 58 := by unfold smallValid; decide +kernel

private theorem sp16060 : smallValid 16060 58 := by unfold smallValid; decide +kernel

private theorem sp16118 : smallValid 16118 58 := by unfold smallValid; decide +kernel

private theorem sp16176 : smallValid 16176 57 := by unfold smallValid; decide +kernel

private theorem sp16233 : smallValid 16233 58 := by unfold smallValid; decide +kernel

private theorem sp16291 : smallValid 16291 58 := by unfold smallValid; decide +kernel

private theorem sp16349 : smallValid 16349 58 := by unfold smallValid; decide +kernel

private theorem sp16407 : smallValid 16407 57 := by unfold smallValid; decide +kernel

private theorem sp16464 : smallValid 16464 58 := by unfold smallValid; decide +kernel

private theorem sp16522 : smallValid 16522 58 := by unfold smallValid; decide +kernel

private theorem sp16580 : smallValid 16580 58 := by unfold smallValid; decide +kernel

private theorem sp16638 : smallValid 16638 57 := by unfold smallValid; decide +kernel

private theorem sp16695 : smallValid 16695 58 := by unfold smallValid; decide +kernel

private theorem sp16753 : smallValid 16753 58 := by unfold smallValid; decide +kernel

private theorem sp16811 : smallValid 16811 58 := by unfold smallValid; decide +kernel

private theorem sp16869 : smallValid 16869 57 := by unfold smallValid; decide +kernel

private theorem sp16926 : smallValid 16926 58 := by unfold smallValid; decide +kernel

private theorem sp16984 : smallValid 16984 58 := by unfold smallValid; decide +kernel

private theorem sp17042 : smallValid 17042 58 := by unfold smallValid; decide +kernel

private theorem sp17100 : smallValid 17100 57 := by unfold smallValid; decide +kernel

private theorem sp17157 : smallValid 17157 58 := by unfold smallValid; decide +kernel

private theorem sp17215 : smallValid 17215 58 := by unfold smallValid; decide +kernel

private theorem sp17273 : smallValid 17273 58 := by unfold smallValid; decide +kernel

private theorem sp17331 : smallValid 17331 57 := by unfold smallValid; decide +kernel

private theorem sp17388 : smallValid 17388 58 := by unfold smallValid; decide +kernel

private theorem sp17446 : smallValid 17446 58 := by unfold smallValid; decide +kernel

private theorem sp17504 : smallValid 17504 58 := by unfold smallValid; decide +kernel

private theorem sp17562 : smallValid 17562 57 := by unfold smallValid; decide +kernel

private theorem sp17619 : smallValid 17619 58 := by unfold smallValid; decide +kernel

private theorem sp17677 : smallValid 17677 58 := by unfold smallValid; decide +kernel

private theorem sp17735 : smallValid 17735 58 := by unfold smallValid; decide +kernel

private theorem sp17793 : smallValid 17793 57 := by unfold smallValid; decide +kernel

private theorem sp17850 : smallValid 17850 58 := by unfold smallValid; decide +kernel

private theorem sp17908 : smallValid 17908 58 := by unfold smallValid; decide +kernel

private theorem sp17966 : smallValid 17966 58 := by unfold smallValid; decide +kernel

private theorem sp18024 : smallValid 18024 57 := by unfold smallValid; decide +kernel

private theorem sp18081 : smallValid 18081 58 := by unfold smallValid; decide +kernel

private theorem sp18139 : smallValid 18139 58 := by unfold smallValid; decide +kernel

private theorem sp18197 : smallValid 18197 58 := by unfold smallValid; decide +kernel

private theorem sp18255 : smallValid 18255 58 := by unfold smallValid; decide +kernel

private theorem sp18313 : smallValid 18313 58 := by unfold smallValid; decide +kernel

private theorem sp18371 : smallValid 18371 58 := by unfold smallValid; decide +kernel

private theorem sp18429 : smallValid 18429 58 := by unfold smallValid; decide +kernel

private theorem sp18487 : smallValid 18487 57 := by unfold smallValid; decide +kernel

private theorem sp18544 : smallValid 18544 58 := by unfold smallValid; decide +kernel

private theorem sp18602 : smallValid 18602 58 := by unfold smallValid; decide +kernel

private theorem sp18660 : smallValid 18660 58 := by unfold smallValid; decide +kernel

private theorem sp18718 : smallValid 18718 57 := by unfold smallValid; decide +kernel

private theorem sp18775 : smallValid 18775 58 := by unfold smallValid; decide +kernel

private theorem sp18833 : smallValid 18833 58 := by unfold smallValid; decide +kernel

private theorem sp18891 : smallValid 18891 58 := by unfold smallValid; decide +kernel

private theorem sp18949 : smallValid 18949 57 := by unfold smallValid; decide +kernel

private theorem sp19006 : smallValid 19006 58 := by unfold smallValid; decide +kernel

private theorem sp19064 : smallValid 19064 58 := by unfold smallValid; decide +kernel

private theorem sp19122 : smallValid 19122 58 := by unfold smallValid; decide +kernel

private theorem sp19180 : smallValid 19180 57 := by unfold smallValid; decide +kernel

private theorem sp19237 : smallValid 19237 58 := by unfold smallValid; decide +kernel

private theorem sp19295 : smallValid 19295 58 := by unfold smallValid; decide +kernel

private theorem sp19353 : smallValid 19353 58 := by unfold smallValid; decide +kernel

private theorem sp19411 : smallValid 19411 57 := by unfold smallValid; decide +kernel

private theorem sp19468 : smallValid 19468 58 := by unfold smallValid; decide +kernel

private theorem sp19526 : smallValid 19526 58 := by unfold smallValid; decide +kernel

private theorem sp19584 : smallValid 19584 58 := by unfold smallValid; decide +kernel

private theorem sp19642 : smallValid 19642 57 := by unfold smallValid; decide +kernel

private theorem sp19699 : smallValid 19699 58 := by unfold smallValid; decide +kernel

private theorem sp19757 : smallValid 19757 58 := by unfold smallValid; decide +kernel

private theorem sp19815 : smallValid 19815 58 := by unfold smallValid; decide +kernel

private theorem sp19873 : smallValid 19873 57 := by unfold smallValid; decide +kernel

private theorem sp19930 : smallValid 19930 58 := by unfold smallValid; decide +kernel

private theorem sp19988 : smallValid 19988 58 := by unfold smallValid; decide +kernel

private theorem sp20046 : smallValid 20046 58 := by unfold smallValid; decide +kernel

private theorem sp20104 : smallValid 20104 58 := by unfold smallValid; decide +kernel

private theorem sp20162 : smallValid 20162 58 := by unfold smallValid; decide +kernel

private theorem sp20220 : smallValid 20220 58 := by unfold smallValid; decide +kernel

private theorem sp20278 : smallValid 20278 58 := by unfold smallValid; decide +kernel

private theorem sp20336 : smallValid 20336 57 := by unfold smallValid; decide +kernel

private theorem sp20393 : smallValid 20393 58 := by unfold smallValid; decide +kernel

private theorem sp20451 : smallValid 20451 58 := by unfold smallValid; decide +kernel

private theorem sp20509 : smallValid 20509 58 := by unfold smallValid; decide +kernel

private theorem sp20567 : smallValid 20567 57 := by unfold smallValid; decide +kernel

private theorem sp20624 : smallValid 20624 58 := by unfold smallValid; decide +kernel

private theorem sp20682 : smallValid 20682 58 := by unfold smallValid; decide +kernel

private theorem sp20740 : smallValid 20740 58 := by unfold smallValid; decide +kernel

private theorem sp20798 : smallValid 20798 57 := by unfold smallValid; decide +kernel

private theorem sp20855 : smallValid 20855 58 := by unfold smallValid; decide +kernel

private theorem sp20913 : smallValid 20913 58 := by unfold smallValid; decide +kernel

private theorem sp20971 : smallValid 20971 58 := by unfold smallValid; decide +kernel

private theorem sp21029 : smallValid 21029 57 := by unfold smallValid; decide +kernel

private theorem sp21086 : smallValid 21086 58 := by unfold smallValid; decide +kernel

private theorem sp21144 : smallValid 21144 58 := by unfold smallValid; decide +kernel

private theorem sp21202 : smallValid 21202 58 := by unfold smallValid; decide +kernel

private theorem sp21260 : smallValid 21260 57 := by unfold smallValid; decide +kernel

private theorem sp21317 : smallValid 21317 58 := by unfold smallValid; decide +kernel

private theorem sp21375 : smallValid 21375 58 := by unfold smallValid; decide +kernel

private theorem sp21433 : smallValid 21433 58 := by unfold smallValid; decide +kernel

private theorem sp21491 : smallValid 21491 57 := by unfold smallValid; decide +kernel

private theorem sp21548 : smallValid 21548 58 := by unfold smallValid; decide +kernel

private theorem sp21606 : smallValid 21606 58 := by unfold smallValid; decide +kernel

private theorem sp21664 : smallValid 21664 58 := by unfold smallValid; decide +kernel

private theorem sp21722 : smallValid 21722 57 := by unfold smallValid; decide +kernel

private theorem sp21779 : smallValid 21779 58 := by unfold smallValid; decide +kernel

private theorem sp21837 : smallValid 21837 58 := by unfold smallValid; decide +kernel

private theorem sp21895 : smallValid 21895 58 := by unfold smallValid; decide +kernel

private theorem sp21953 : smallValid 21953 58 := by unfold smallValid; decide +kernel

private theorem sp22011 : smallValid 22011 58 := by unfold smallValid; decide +kernel

private theorem sp22069 : smallValid 22069 58 := by unfold smallValid; decide +kernel

private theorem sp22127 : smallValid 22127 58 := by unfold smallValid; decide +kernel

private theorem sp22185 : smallValid 22185 57 := by unfold smallValid; decide +kernel

private theorem sp22242 : smallValid 22242 58 := by unfold smallValid; decide +kernel

private theorem sp22300 : smallValid 22300 58 := by unfold smallValid; decide +kernel

private theorem sp22358 : smallValid 22358 58 := by unfold smallValid; decide +kernel

private theorem sp22416 : smallValid 22416 57 := by unfold smallValid; decide +kernel

private theorem sp22473 : smallValid 22473 58 := by unfold smallValid; decide +kernel

private theorem sp22531 : smallValid 22531 58 := by unfold smallValid; decide +kernel

private theorem sp22589 : smallValid 22589 58 := by unfold smallValid; decide +kernel

private theorem sp22647 : smallValid 22647 57 := by unfold smallValid; decide +kernel

private theorem sp22704 : smallValid 22704 58 := by unfold smallValid; decide +kernel

private theorem sp22762 : smallValid 22762 58 := by unfold smallValid; decide +kernel

private theorem sp22820 : smallValid 22820 58 := by unfold smallValid; decide +kernel

private theorem sp22878 : smallValid 22878 57 := by unfold smallValid; decide +kernel

private theorem sp22935 : smallValid 22935 58 := by unfold smallValid; decide +kernel

private theorem sp22993 : smallValid 22993 58 := by unfold smallValid; decide +kernel

private theorem sp23051 : smallValid 23051 58 := by unfold smallValid; decide +kernel

private theorem sp23109 : smallValid 23109 57 := by unfold smallValid; decide +kernel

private theorem sp23166 : smallValid 23166 58 := by unfold smallValid; decide +kernel

private theorem sp23224 : smallValid 23224 58 := by unfold smallValid; decide +kernel

private theorem sp23282 : smallValid 23282 58 := by unfold smallValid; decide +kernel

private theorem sp23340 : smallValid 23340 57 := by unfold smallValid; decide +kernel

private theorem sp23397 : smallValid 23397 58 := by unfold smallValid; decide +kernel

private theorem sp23455 : smallValid 23455 58 := by unfold smallValid; decide +kernel

private theorem sp23513 : smallValid 23513 58 := by unfold smallValid; decide +kernel

private theorem sp23571 : smallValid 23571 57 := by unfold smallValid; decide +kernel

private theorem sp23628 : smallValid 23628 58 := by unfold smallValid; decide +kernel

private theorem sp23686 : smallValid 23686 58 := by unfold smallValid; decide +kernel

private theorem sp23744 : smallValid 23744 58 := by unfold smallValid; decide +kernel

private theorem sp23802 : smallValid 23802 58 := by unfold smallValid; decide +kernel

private theorem sp23860 : smallValid 23860 58 := by unfold smallValid; decide +kernel

private theorem sp23918 : smallValid 23918 58 := by unfold smallValid; decide +kernel

private theorem sp23976 : smallValid 23976 58 := by unfold smallValid; decide +kernel

private theorem sp24034 : smallValid 24034 57 := by unfold smallValid; decide +kernel

private theorem sp24091 : smallValid 24091 58 := by unfold smallValid; decide +kernel

private theorem sp24149 : smallValid 24149 58 := by unfold smallValid; decide +kernel

private theorem sp24207 : smallValid 24207 58 := by unfold smallValid; decide +kernel

private theorem sp24265 : smallValid 24265 57 := by unfold smallValid; decide +kernel

private theorem sp24322 : smallValid 24322 58 := by unfold smallValid; decide +kernel

private theorem sp24380 : smallValid 24380 58 := by unfold smallValid; decide +kernel

private theorem sp24438 : smallValid 24438 58 := by unfold smallValid; decide +kernel

private theorem sp24496 : smallValid 24496 57 := by unfold smallValid; decide +kernel

private theorem sp24553 : smallValid 24553 58 := by unfold smallValid; decide +kernel

private theorem sp24611 : smallValid 24611 58 := by unfold smallValid; decide +kernel

private theorem sp24669 : smallValid 24669 58 := by unfold smallValid; decide +kernel

private theorem sp24727 : smallValid 24727 57 := by unfold smallValid; decide +kernel

private theorem sp24784 : smallValid 24784 58 := by unfold smallValid; decide +kernel

private theorem sp24842 : smallValid 24842 58 := by unfold smallValid; decide +kernel

private theorem sp24900 : smallValid 24900 58 := by unfold smallValid; decide +kernel

private theorem sp24958 : smallValid 24958 57 := by unfold smallValid; decide +kernel

private theorem sp25015 : smallValid 25015 58 := by unfold smallValid; decide +kernel

private theorem sp25073 : smallValid 25073 58 := by unfold smallValid; decide +kernel

private theorem sp25131 : smallValid 25131 58 := by unfold smallValid; decide +kernel

private theorem sp25189 : smallValid 25189 57 := by unfold smallValid; decide +kernel

private theorem sp25246 : smallValid 25246 58 := by unfold smallValid; decide +kernel

private theorem sp25304 : smallValid 25304 58 := by unfold smallValid; decide +kernel

private theorem sp25362 : smallValid 25362 58 := by unfold smallValid; decide +kernel

private theorem sp25420 : smallValid 25420 57 := by unfold smallValid; decide +kernel

private theorem sp25477 : smallValid 25477 58 := by unfold smallValid; decide +kernel

private theorem sp25535 : smallValid 25535 58 := by unfold smallValid; decide +kernel

private theorem sp25593 : smallValid 25593 58 := by unfold smallValid; decide +kernel

private theorem sp25651 : smallValid 25651 58 := by unfold smallValid; decide +kernel

private theorem sp25709 : smallValid 25709 58 := by unfold smallValid; decide +kernel

private theorem sp25767 : smallValid 25767 58 := by unfold smallValid; decide +kernel

private theorem sp25825 : smallValid 25825 58 := by unfold smallValid; decide +kernel

private theorem sp25883 : smallValid 25883 57 := by unfold smallValid; decide +kernel

private theorem sp25940 : smallValid 25940 58 := by unfold smallValid; decide +kernel

private theorem sp25998 : smallValid 25998 58 := by unfold smallValid; decide +kernel

private theorem sp26056 : smallValid 26056 58 := by unfold smallValid; decide +kernel

private theorem sp26114 : smallValid 26114 57 := by unfold smallValid; decide +kernel

private theorem sp26171 : smallValid 26171 58 := by unfold smallValid; decide +kernel

private theorem sp26229 : smallValid 26229 58 := by unfold smallValid; decide +kernel

private theorem sp26287 : smallValid 26287 58 := by unfold smallValid; decide +kernel

private theorem sp26345 : smallValid 26345 57 := by unfold smallValid; decide +kernel

private theorem sp26402 : smallValid 26402 58 := by unfold smallValid; decide +kernel

private theorem sp26460 : smallValid 26460 58 := by unfold smallValid; decide +kernel

private theorem sp26518 : smallValid 26518 58 := by unfold smallValid; decide +kernel

private theorem sp26576 : smallValid 26576 57 := by unfold smallValid; decide +kernel

private theorem sp26633 : smallValid 26633 58 := by unfold smallValid; decide +kernel

private theorem sp26691 : smallValid 26691 58 := by unfold smallValid; decide +kernel

private theorem sp26749 : smallValid 26749 58 := by unfold smallValid; decide +kernel

private theorem sp26807 : smallValid 26807 57 := by unfold smallValid; decide +kernel

private theorem sp26864 : smallValid 26864 58 := by unfold smallValid; decide +kernel

private theorem sp26922 : smallValid 26922 58 := by unfold smallValid; decide +kernel

private theorem sp26980 : smallValid 26980 58 := by unfold smallValid; decide +kernel

private theorem sp27038 : smallValid 27038 57 := by unfold smallValid; decide +kernel

private theorem sp27095 : smallValid 27095 58 := by unfold smallValid; decide +kernel

private theorem sp27153 : smallValid 27153 58 := by unfold smallValid; decide +kernel

private theorem sp27211 : smallValid 27211 58 := by unfold smallValid; decide +kernel

private theorem sp27269 : smallValid 27269 57 := by unfold smallValid; decide +kernel

private theorem sp27326 : smallValid 27326 58 := by unfold smallValid; decide +kernel

private theorem sp27384 : smallValid 27384 58 := by unfold smallValid; decide +kernel

private theorem sp27442 : smallValid 27442 58 := by unfold smallValid; decide +kernel

private theorem sp27500 : smallValid 27500 58 := by unfold smallValid; decide +kernel

private theorem sp27558 : smallValid 27558 58 := by unfold smallValid; decide +kernel

private theorem sp27616 : smallValid 27616 58 := by unfold smallValid; decide +kernel

private theorem sp27674 : smallValid 27674 58 := by unfold smallValid; decide +kernel

private theorem sp27732 : smallValid 27732 57 := by unfold smallValid; decide +kernel

private theorem sp27789 : smallValid 27789 58 := by unfold smallValid; decide +kernel

private theorem sp27847 : smallValid 27847 58 := by unfold smallValid; decide +kernel

private theorem sp27905 : smallValid 27905 58 := by unfold smallValid; decide +kernel

private theorem sp27963 : smallValid 27963 57 := by unfold smallValid; decide +kernel

private theorem sp28020 : smallValid 28020 58 := by unfold smallValid; decide +kernel

private theorem sp28078 : smallValid 28078 58 := by unfold smallValid; decide +kernel

private theorem sp28136 : smallValid 28136 58 := by unfold smallValid; decide +kernel

private theorem sp28194 : smallValid 28194 57 := by unfold smallValid; decide +kernel

private theorem sp28251 : smallValid 28251 58 := by unfold smallValid; decide +kernel

private theorem sp28309 : smallValid 28309 58 := by unfold smallValid; decide +kernel

private theorem sp28367 : smallValid 28367 58 := by unfold smallValid; decide +kernel

private theorem sp28425 : smallValid 28425 57 := by unfold smallValid; decide +kernel

private theorem sp28482 : smallValid 28482 58 := by unfold smallValid; decide +kernel

private theorem sp28540 : smallValid 28540 58 := by unfold smallValid; decide +kernel

private theorem sp28598 : smallValid 28598 58 := by unfold smallValid; decide +kernel

private theorem sp28656 : smallValid 28656 57 := by unfold smallValid; decide +kernel

private theorem sp28713 : smallValid 28713 58 := by unfold smallValid; decide +kernel

private theorem sp28771 : smallValid 28771 58 := by unfold smallValid; decide +kernel

private theorem sp28829 : smallValid 28829 58 := by unfold smallValid; decide +kernel

private theorem sp28887 : smallValid 28887 57 := by unfold smallValid; decide +kernel

private theorem sp28944 : smallValid 28944 58 := by unfold smallValid; decide +kernel

private theorem sp29002 : smallValid 29002 58 := by unfold smallValid; decide +kernel

private theorem sp29060 : smallValid 29060 58 := by unfold smallValid; decide +kernel

private theorem sp29118 : smallValid 29118 57 := by unfold smallValid; decide +kernel

private theorem sp29175 : smallValid 29175 58 := by unfold smallValid; decide +kernel

private theorem sp29233 : smallValid 29233 58 := by unfold smallValid; decide +kernel

private theorem sp29291 : smallValid 29291 58 := by unfold smallValid; decide +kernel

private theorem sp29349 : smallValid 29349 58 := by unfold smallValid; decide +kernel

private theorem sp29407 : smallValid 29407 58 := by unfold smallValid; decide +kernel

private theorem sp29465 : smallValid 29465 58 := by unfold smallValid; decide +kernel

private theorem sp29523 : smallValid 29523 58 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤29580) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 29581 := (joinSmall (lo:=0) (a:=14790) (b:=14791) (joinSmall (lo:=0) (a:=7395) (b:=7395) (joinSmall (lo:=0) (a:=3697) (b:=3698) (joinSmall (lo:=0) (a:=1848) (b:=1849) (joinSmall (lo:=0) (a:=924) (b:=924) (joinSmall (lo:=0) (a:=462) (b:=462) (joinSmall (lo:=0) (a:=231) (b:=231) (joinSmall (lo:=0) (a:=115) (b:=116) (joinSmall (lo:=0) (a:=57) (b:=58) sp0 sp57) (joinSmall (lo:=115) (a:=58) (b:=58) sp115 sp173)) (joinSmall (lo:=231) (a:=115) (b:=116) (joinSmall (lo:=231) (a:=57) (b:=58) sp231 sp288) (joinSmall (lo:=346) (a:=58) (b:=58) sp346 sp404))) (joinSmall (lo:=462) (a:=231) (b:=231) (joinSmall (lo:=462) (a:=115) (b:=116) (joinSmall (lo:=462) (a:=57) (b:=58) sp462 sp519) (joinSmall (lo:=577) (a:=58) (b:=58) sp577 sp635)) (joinSmall (lo:=693) (a:=115) (b:=116) (joinSmall (lo:=693) (a:=57) (b:=58) sp693 sp750) (joinSmall (lo:=808) (a:=58) (b:=58) sp808 sp866)))) (joinSmall (lo:=924) (a:=462) (b:=462) (joinSmall (lo:=924) (a:=231) (b:=231) (joinSmall (lo:=924) (a:=115) (b:=116) (joinSmall (lo:=924) (a:=57) (b:=58) sp924 sp981) (joinSmall (lo:=1039) (a:=58) (b:=58) sp1039 sp1097)) (joinSmall (lo:=1155) (a:=115) (b:=116) (joinSmall (lo:=1155) (a:=57) (b:=58) sp1155 sp1212) (joinSmall (lo:=1270) (a:=58) (b:=58) sp1270 sp1328))) (joinSmall (lo:=1386) (a:=231) (b:=231) (joinSmall (lo:=1386) (a:=115) (b:=116) (joinSmall (lo:=1386) (a:=57) (b:=58) sp1386 sp1443) (joinSmall (lo:=1501) (a:=58) (b:=58) sp1501 sp1559)) (joinSmall (lo:=1617) (a:=115) (b:=116) (joinSmall (lo:=1617) (a:=57) (b:=58) sp1617 sp1674) (joinSmall (lo:=1732) (a:=58) (b:=58) sp1732 sp1790))))) (joinSmall (lo:=1848) (a:=924) (b:=925) (joinSmall (lo:=1848) (a:=462) (b:=462) (joinSmall (lo:=1848) (a:=231) (b:=231) (joinSmall (lo:=1848) (a:=115) (b:=116) (joinSmall (lo:=1848) (a:=57) (b:=58) sp1848 sp1905) (joinSmall (lo:=1963) (a:=58) (b:=58) sp1963 sp2021)) (joinSmall (lo:=2079) (a:=115) (b:=116) (joinSmall (lo:=2079) (a:=57) (b:=58) sp2079 sp2136) (joinSmall (lo:=2194) (a:=58) (b:=58) sp2194 sp2252))) (joinSmall (lo:=2310) (a:=231) (b:=231) (joinSmall (lo:=2310) (a:=115) (b:=116) (joinSmall (lo:=2310) (a:=57) (b:=58) sp2310 sp2367) (joinSmall (lo:=2425) (a:=58) (b:=58) sp2425 sp2483)) (joinSmall (lo:=2541) (a:=115) (b:=116) (joinSmall (lo:=2541) (a:=57) (b:=58) sp2541 sp2598) (joinSmall (lo:=2656) (a:=58) (b:=58) sp2656 sp2714)))) (joinSmall (lo:=2772) (a:=462) (b:=463) (joinSmall (lo:=2772) (a:=231) (b:=231) (joinSmall (lo:=2772) (a:=115) (b:=116) (joinSmall (lo:=2772) (a:=57) (b:=58) sp2772 sp2829) (joinSmall (lo:=2887) (a:=58) (b:=58) sp2887 sp2945)) (joinSmall (lo:=3003) (a:=115) (b:=116) (joinSmall (lo:=3003) (a:=57) (b:=58) sp3003 sp3060) (joinSmall (lo:=3118) (a:=58) (b:=58) sp3118 sp3176))) (joinSmall (lo:=3234) (a:=231) (b:=232) (joinSmall (lo:=3234) (a:=115) (b:=116) (joinSmall (lo:=3234) (a:=57) (b:=58) sp3234 sp3291) (joinSmall (lo:=3349) (a:=58) (b:=58) sp3349 sp3407)) (joinSmall (lo:=3465) (a:=116) (b:=116) (joinSmall (lo:=3465) (a:=58) (b:=58) sp3465 sp3523) (joinSmall (lo:=3581) (a:=58) (b:=58) sp3581 sp3639)))))) (joinSmall (lo:=3697) (a:=1849) (b:=1849) (joinSmall (lo:=3697) (a:=924) (b:=925) (joinSmall (lo:=3697) (a:=462) (b:=462) (joinSmall (lo:=3697) (a:=231) (b:=231) (joinSmall (lo:=3697) (a:=115) (b:=116) (joinSmall (lo:=3697) (a:=57) (b:=58) sp3697 sp3754) (joinSmall (lo:=3812) (a:=58) (b:=58) sp3812 sp3870)) (joinSmall (lo:=3928) (a:=115) (b:=116) (joinSmall (lo:=3928) (a:=57) (b:=58) sp3928 sp3985) (joinSmall (lo:=4043) (a:=58) (b:=58) sp4043 sp4101))) (joinSmall (lo:=4159) (a:=231) (b:=231) (joinSmall (lo:=4159) (a:=115) (b:=116) (joinSmall (lo:=4159) (a:=57) (b:=58) sp4159 sp4216) (joinSmall (lo:=4274) (a:=58) (b:=58) sp4274 sp4332)) (joinSmall (lo:=4390) (a:=115) (b:=116) (joinSmall (lo:=4390) (a:=57) (b:=58) sp4390 sp4447) (joinSmall (lo:=4505) (a:=58) (b:=58) sp4505 sp4563)))) (joinSmall (lo:=4621) (a:=462) (b:=463) (joinSmall (lo:=4621) (a:=231) (b:=231) (joinSmall (lo:=4621) (a:=115) (b:=116) (joinSmall (lo:=4621) (a:=57) (b:=58) sp4621 sp4678) (joinSmall (lo:=4736) (a:=58) (b:=58) sp4736 sp4794)) (joinSmall (lo:=4852) (a:=115) (b:=116) (joinSmall (lo:=4852) (a:=57) (b:=58) sp4852 sp4909) (joinSmall (lo:=4967) (a:=58) (b:=58) sp4967 sp5025))) (joinSmall (lo:=5083) (a:=231) (b:=232) (joinSmall (lo:=5083) (a:=115) (b:=116) (joinSmall (lo:=5083) (a:=57) (b:=58) sp5083 sp5140) (joinSmall (lo:=5198) (a:=58) (b:=58) sp5198 sp5256)) (joinSmall (lo:=5314) (a:=116) (b:=116) (joinSmall (lo:=5314) (a:=58) (b:=58) sp5314 sp5372) (joinSmall (lo:=5430) (a:=58) (b:=58) sp5430 sp5488))))) (joinSmall (lo:=5546) (a:=924) (b:=925) (joinSmall (lo:=5546) (a:=462) (b:=462) (joinSmall (lo:=5546) (a:=231) (b:=231) (joinSmall (lo:=5546) (a:=115) (b:=116) (joinSmall (lo:=5546) (a:=57) (b:=58) sp5546 sp5603) (joinSmall (lo:=5661) (a:=58) (b:=58) sp5661 sp5719)) (joinSmall (lo:=5777) (a:=115) (b:=116) (joinSmall (lo:=5777) (a:=57) (b:=58) sp5777 sp5834) (joinSmall (lo:=5892) (a:=58) (b:=58) sp5892 sp5950))) (joinSmall (lo:=6008) (a:=231) (b:=231) (joinSmall (lo:=6008) (a:=115) (b:=116) (joinSmall (lo:=6008) (a:=57) (b:=58) sp6008 sp6065) (joinSmall (lo:=6123) (a:=58) (b:=58) sp6123 sp6181)) (joinSmall (lo:=6239) (a:=115) (b:=116) (joinSmall (lo:=6239) (a:=57) (b:=58) sp6239 sp6296) (joinSmall (lo:=6354) (a:=58) (b:=58) sp6354 sp6412)))) (joinSmall (lo:=6470) (a:=462) (b:=463) (joinSmall (lo:=6470) (a:=231) (b:=231) (joinSmall (lo:=6470) (a:=115) (b:=116) (joinSmall (lo:=6470) (a:=57) (b:=58) sp6470 sp6527) (joinSmall (lo:=6585) (a:=58) (b:=58) sp6585 sp6643)) (joinSmall (lo:=6701) (a:=115) (b:=116) (joinSmall (lo:=6701) (a:=57) (b:=58) sp6701 sp6758) (joinSmall (lo:=6816) (a:=58) (b:=58) sp6816 sp6874))) (joinSmall (lo:=6932) (a:=231) (b:=232) (joinSmall (lo:=6932) (a:=115) (b:=116) (joinSmall (lo:=6932) (a:=57) (b:=58) sp6932 sp6989) (joinSmall (lo:=7047) (a:=58) (b:=58) sp7047 sp7105)) (joinSmall (lo:=7163) (a:=116) (b:=116) (joinSmall (lo:=7163) (a:=58) (b:=58) sp7163 sp7221) (joinSmall (lo:=7279) (a:=58) (b:=58) sp7279 sp7337))))))) (joinSmall (lo:=7395) (a:=3697) (b:=3698) (joinSmall (lo:=7395) (a:=1848) (b:=1849) (joinSmall (lo:=7395) (a:=924) (b:=924) (joinSmall (lo:=7395) (a:=462) (b:=462) (joinSmall (lo:=7395) (a:=231) (b:=231) (joinSmall (lo:=7395) (a:=115) (b:=116) (joinSmall (lo:=7395) (a:=57) (b:=58) sp7395 sp7452) (joinSmall (lo:=7510) (a:=58) (b:=58) sp7510 sp7568)) (joinSmall (lo:=7626) (a:=115) (b:=116) (joinSmall (lo:=7626) (a:=57) (b:=58) sp7626 sp7683) (joinSmall (lo:=7741) (a:=58) (b:=58) sp7741 sp7799))) (joinSmall (lo:=7857) (a:=231) (b:=231) (joinSmall (lo:=7857) (a:=115) (b:=116) (joinSmall (lo:=7857) (a:=57) (b:=58) sp7857 sp7914) (joinSmall (lo:=7972) (a:=58) (b:=58) sp7972 sp8030)) (joinSmall (lo:=8088) (a:=115) (b:=116) (joinSmall (lo:=8088) (a:=57) (b:=58) sp8088 sp8145) (joinSmall (lo:=8203) (a:=58) (b:=58) sp8203 sp8261)))) (joinSmall (lo:=8319) (a:=462) (b:=462) (joinSmall (lo:=8319) (a:=231) (b:=231) (joinSmall (lo:=8319) (a:=115) (b:=116) (joinSmall (lo:=8319) (a:=57) (b:=58) sp8319 sp8376) (joinSmall (lo:=8434) (a:=58) (b:=58) sp8434 sp8492)) (joinSmall (lo:=8550) (a:=115) (b:=116) (joinSmall (lo:=8550) (a:=57) (b:=58) sp8550 sp8607) (joinSmall (lo:=8665) (a:=58) (b:=58) sp8665 sp8723))) (joinSmall (lo:=8781) (a:=231) (b:=231) (joinSmall (lo:=8781) (a:=115) (b:=116) (joinSmall (lo:=8781) (a:=57) (b:=58) sp8781 sp8838) (joinSmall (lo:=8896) (a:=58) (b:=58) sp8896 sp8954)) (joinSmall (lo:=9012) (a:=115) (b:=116) (joinSmall (lo:=9012) (a:=57) (b:=58) sp9012 sp9069) (joinSmall (lo:=9127) (a:=58) (b:=58) sp9127 sp9185))))) (joinSmall (lo:=9243) (a:=924) (b:=925) (joinSmall (lo:=9243) (a:=462) (b:=462) (joinSmall (lo:=9243) (a:=231) (b:=231) (joinSmall (lo:=9243) (a:=115) (b:=116) (joinSmall (lo:=9243) (a:=57) (b:=58) sp9243 sp9300) (joinSmall (lo:=9358) (a:=58) (b:=58) sp9358 sp9416)) (joinSmall (lo:=9474) (a:=115) (b:=116) (joinSmall (lo:=9474) (a:=57) (b:=58) sp9474 sp9531) (joinSmall (lo:=9589) (a:=58) (b:=58) sp9589 sp9647))) (joinSmall (lo:=9705) (a:=231) (b:=231) (joinSmall (lo:=9705) (a:=115) (b:=116) (joinSmall (lo:=9705) (a:=57) (b:=58) sp9705 sp9762) (joinSmall (lo:=9820) (a:=58) (b:=58) sp9820 sp9878)) (joinSmall (lo:=9936) (a:=115) (b:=116) (joinSmall (lo:=9936) (a:=57) (b:=58) sp9936 sp9993) (joinSmall (lo:=10051) (a:=58) (b:=58) sp10051 sp10109)))) (joinSmall (lo:=10167) (a:=462) (b:=463) (joinSmall (lo:=10167) (a:=231) (b:=231) (joinSmall (lo:=10167) (a:=115) (b:=116) (joinSmall (lo:=10167) (a:=57) (b:=58) sp10167 sp10224) (joinSmall (lo:=10282) (a:=58) (b:=58) sp10282 sp10340)) (joinSmall (lo:=10398) (a:=115) (b:=116) (joinSmall (lo:=10398) (a:=57) (b:=58) sp10398 sp10455) (joinSmall (lo:=10513) (a:=58) (b:=58) sp10513 sp10571))) (joinSmall (lo:=10629) (a:=231) (b:=232) (joinSmall (lo:=10629) (a:=115) (b:=116) (joinSmall (lo:=10629) (a:=57) (b:=58) sp10629 sp10686) (joinSmall (lo:=10744) (a:=58) (b:=58) sp10744 sp10802)) (joinSmall (lo:=10860) (a:=116) (b:=116) (joinSmall (lo:=10860) (a:=58) (b:=58) sp10860 sp10918) (joinSmall (lo:=10976) (a:=58) (b:=58) sp10976 sp11034)))))) (joinSmall (lo:=11092) (a:=1849) (b:=1849) (joinSmall (lo:=11092) (a:=924) (b:=925) (joinSmall (lo:=11092) (a:=462) (b:=462) (joinSmall (lo:=11092) (a:=231) (b:=231) (joinSmall (lo:=11092) (a:=115) (b:=116) (joinSmall (lo:=11092) (a:=57) (b:=58) sp11092 sp11149) (joinSmall (lo:=11207) (a:=58) (b:=58) sp11207 sp11265)) (joinSmall (lo:=11323) (a:=115) (b:=116) (joinSmall (lo:=11323) (a:=57) (b:=58) sp11323 sp11380) (joinSmall (lo:=11438) (a:=58) (b:=58) sp11438 sp11496))) (joinSmall (lo:=11554) (a:=231) (b:=231) (joinSmall (lo:=11554) (a:=115) (b:=116) (joinSmall (lo:=11554) (a:=57) (b:=58) sp11554 sp11611) (joinSmall (lo:=11669) (a:=58) (b:=58) sp11669 sp11727)) (joinSmall (lo:=11785) (a:=115) (b:=116) (joinSmall (lo:=11785) (a:=57) (b:=58) sp11785 sp11842) (joinSmall (lo:=11900) (a:=58) (b:=58) sp11900 sp11958)))) (joinSmall (lo:=12016) (a:=462) (b:=463) (joinSmall (lo:=12016) (a:=231) (b:=231) (joinSmall (lo:=12016) (a:=115) (b:=116) (joinSmall (lo:=12016) (a:=57) (b:=58) sp12016 sp12073) (joinSmall (lo:=12131) (a:=58) (b:=58) sp12131 sp12189)) (joinSmall (lo:=12247) (a:=115) (b:=116) (joinSmall (lo:=12247) (a:=57) (b:=58) sp12247 sp12304) (joinSmall (lo:=12362) (a:=58) (b:=58) sp12362 sp12420))) (joinSmall (lo:=12478) (a:=231) (b:=232) (joinSmall (lo:=12478) (a:=115) (b:=116) (joinSmall (lo:=12478) (a:=57) (b:=58) sp12478 sp12535) (joinSmall (lo:=12593) (a:=58) (b:=58) sp12593 sp12651)) (joinSmall (lo:=12709) (a:=116) (b:=116) (joinSmall (lo:=12709) (a:=58) (b:=58) sp12709 sp12767) (joinSmall (lo:=12825) (a:=58) (b:=58) sp12825 sp12883))))) (joinSmall (lo:=12941) (a:=924) (b:=925) (joinSmall (lo:=12941) (a:=462) (b:=462) (joinSmall (lo:=12941) (a:=231) (b:=231) (joinSmall (lo:=12941) (a:=115) (b:=116) (joinSmall (lo:=12941) (a:=57) (b:=58) sp12941 sp12998) (joinSmall (lo:=13056) (a:=58) (b:=58) sp13056 sp13114)) (joinSmall (lo:=13172) (a:=115) (b:=116) (joinSmall (lo:=13172) (a:=57) (b:=58) sp13172 sp13229) (joinSmall (lo:=13287) (a:=58) (b:=58) sp13287 sp13345))) (joinSmall (lo:=13403) (a:=231) (b:=231) (joinSmall (lo:=13403) (a:=115) (b:=116) (joinSmall (lo:=13403) (a:=57) (b:=58) sp13403 sp13460) (joinSmall (lo:=13518) (a:=58) (b:=58) sp13518 sp13576)) (joinSmall (lo:=13634) (a:=115) (b:=116) (joinSmall (lo:=13634) (a:=57) (b:=58) sp13634 sp13691) (joinSmall (lo:=13749) (a:=58) (b:=58) sp13749 sp13807)))) (joinSmall (lo:=13865) (a:=462) (b:=463) (joinSmall (lo:=13865) (a:=231) (b:=231) (joinSmall (lo:=13865) (a:=115) (b:=116) (joinSmall (lo:=13865) (a:=57) (b:=58) sp13865 sp13922) (joinSmall (lo:=13980) (a:=58) (b:=58) sp13980 sp14038)) (joinSmall (lo:=14096) (a:=115) (b:=116) (joinSmall (lo:=14096) (a:=57) (b:=58) sp14096 sp14153) (joinSmall (lo:=14211) (a:=58) (b:=58) sp14211 sp14269))) (joinSmall (lo:=14327) (a:=231) (b:=232) (joinSmall (lo:=14327) (a:=115) (b:=116) (joinSmall (lo:=14327) (a:=57) (b:=58) sp14327 sp14384) (joinSmall (lo:=14442) (a:=58) (b:=58) sp14442 sp14500)) (joinSmall (lo:=14558) (a:=116) (b:=116) (joinSmall (lo:=14558) (a:=58) (b:=58) sp14558 sp14616) (joinSmall (lo:=14674) (a:=58) (b:=58) sp14674 sp14732)))))))) (joinSmall (lo:=14790) (a:=7395) (b:=7396) (joinSmall (lo:=14790) (a:=3697) (b:=3698) (joinSmall (lo:=14790) (a:=1848) (b:=1849) (joinSmall (lo:=14790) (a:=924) (b:=924) (joinSmall (lo:=14790) (a:=462) (b:=462) (joinSmall (lo:=14790) (a:=231) (b:=231) (joinSmall (lo:=14790) (a:=115) (b:=116) (joinSmall (lo:=14790) (a:=57) (b:=58) sp14790 sp14847) (joinSmall (lo:=14905) (a:=58) (b:=58) sp14905 sp14963)) (joinSmall (lo:=15021) (a:=115) (b:=116) (joinSmall (lo:=15021) (a:=57) (b:=58) sp15021 sp15078) (joinSmall (lo:=15136) (a:=58) (b:=58) sp15136 sp15194))) (joinSmall (lo:=15252) (a:=231) (b:=231) (joinSmall (lo:=15252) (a:=115) (b:=116) (joinSmall (lo:=15252) (a:=57) (b:=58) sp15252 sp15309) (joinSmall (lo:=15367) (a:=58) (b:=58) sp15367 sp15425)) (joinSmall (lo:=15483) (a:=115) (b:=116) (joinSmall (lo:=15483) (a:=57) (b:=58) sp15483 sp15540) (joinSmall (lo:=15598) (a:=58) (b:=58) sp15598 sp15656)))) (joinSmall (lo:=15714) (a:=462) (b:=462) (joinSmall (lo:=15714) (a:=231) (b:=231) (joinSmall (lo:=15714) (a:=115) (b:=116) (joinSmall (lo:=15714) (a:=57) (b:=58) sp15714 sp15771) (joinSmall (lo:=15829) (a:=58) (b:=58) sp15829 sp15887)) (joinSmall (lo:=15945) (a:=115) (b:=116) (joinSmall (lo:=15945) (a:=57) (b:=58) sp15945 sp16002) (joinSmall (lo:=16060) (a:=58) (b:=58) sp16060 sp16118))) (joinSmall (lo:=16176) (a:=231) (b:=231) (joinSmall (lo:=16176) (a:=115) (b:=116) (joinSmall (lo:=16176) (a:=57) (b:=58) sp16176 sp16233) (joinSmall (lo:=16291) (a:=58) (b:=58) sp16291 sp16349)) (joinSmall (lo:=16407) (a:=115) (b:=116) (joinSmall (lo:=16407) (a:=57) (b:=58) sp16407 sp16464) (joinSmall (lo:=16522) (a:=58) (b:=58) sp16522 sp16580))))) (joinSmall (lo:=16638) (a:=924) (b:=925) (joinSmall (lo:=16638) (a:=462) (b:=462) (joinSmall (lo:=16638) (a:=231) (b:=231) (joinSmall (lo:=16638) (a:=115) (b:=116) (joinSmall (lo:=16638) (a:=57) (b:=58) sp16638 sp16695) (joinSmall (lo:=16753) (a:=58) (b:=58) sp16753 sp16811)) (joinSmall (lo:=16869) (a:=115) (b:=116) (joinSmall (lo:=16869) (a:=57) (b:=58) sp16869 sp16926) (joinSmall (lo:=16984) (a:=58) (b:=58) sp16984 sp17042))) (joinSmall (lo:=17100) (a:=231) (b:=231) (joinSmall (lo:=17100) (a:=115) (b:=116) (joinSmall (lo:=17100) (a:=57) (b:=58) sp17100 sp17157) (joinSmall (lo:=17215) (a:=58) (b:=58) sp17215 sp17273)) (joinSmall (lo:=17331) (a:=115) (b:=116) (joinSmall (lo:=17331) (a:=57) (b:=58) sp17331 sp17388) (joinSmall (lo:=17446) (a:=58) (b:=58) sp17446 sp17504)))) (joinSmall (lo:=17562) (a:=462) (b:=463) (joinSmall (lo:=17562) (a:=231) (b:=231) (joinSmall (lo:=17562) (a:=115) (b:=116) (joinSmall (lo:=17562) (a:=57) (b:=58) sp17562 sp17619) (joinSmall (lo:=17677) (a:=58) (b:=58) sp17677 sp17735)) (joinSmall (lo:=17793) (a:=115) (b:=116) (joinSmall (lo:=17793) (a:=57) (b:=58) sp17793 sp17850) (joinSmall (lo:=17908) (a:=58) (b:=58) sp17908 sp17966))) (joinSmall (lo:=18024) (a:=231) (b:=232) (joinSmall (lo:=18024) (a:=115) (b:=116) (joinSmall (lo:=18024) (a:=57) (b:=58) sp18024 sp18081) (joinSmall (lo:=18139) (a:=58) (b:=58) sp18139 sp18197)) (joinSmall (lo:=18255) (a:=116) (b:=116) (joinSmall (lo:=18255) (a:=58) (b:=58) sp18255 sp18313) (joinSmall (lo:=18371) (a:=58) (b:=58) sp18371 sp18429)))))) (joinSmall (lo:=18487) (a:=1849) (b:=1849) (joinSmall (lo:=18487) (a:=924) (b:=925) (joinSmall (lo:=18487) (a:=462) (b:=462) (joinSmall (lo:=18487) (a:=231) (b:=231) (joinSmall (lo:=18487) (a:=115) (b:=116) (joinSmall (lo:=18487) (a:=57) (b:=58) sp18487 sp18544) (joinSmall (lo:=18602) (a:=58) (b:=58) sp18602 sp18660)) (joinSmall (lo:=18718) (a:=115) (b:=116) (joinSmall (lo:=18718) (a:=57) (b:=58) sp18718 sp18775) (joinSmall (lo:=18833) (a:=58) (b:=58) sp18833 sp18891))) (joinSmall (lo:=18949) (a:=231) (b:=231) (joinSmall (lo:=18949) (a:=115) (b:=116) (joinSmall (lo:=18949) (a:=57) (b:=58) sp18949 sp19006) (joinSmall (lo:=19064) (a:=58) (b:=58) sp19064 sp19122)) (joinSmall (lo:=19180) (a:=115) (b:=116) (joinSmall (lo:=19180) (a:=57) (b:=58) sp19180 sp19237) (joinSmall (lo:=19295) (a:=58) (b:=58) sp19295 sp19353)))) (joinSmall (lo:=19411) (a:=462) (b:=463) (joinSmall (lo:=19411) (a:=231) (b:=231) (joinSmall (lo:=19411) (a:=115) (b:=116) (joinSmall (lo:=19411) (a:=57) (b:=58) sp19411 sp19468) (joinSmall (lo:=19526) (a:=58) (b:=58) sp19526 sp19584)) (joinSmall (lo:=19642) (a:=115) (b:=116) (joinSmall (lo:=19642) (a:=57) (b:=58) sp19642 sp19699) (joinSmall (lo:=19757) (a:=58) (b:=58) sp19757 sp19815))) (joinSmall (lo:=19873) (a:=231) (b:=232) (joinSmall (lo:=19873) (a:=115) (b:=116) (joinSmall (lo:=19873) (a:=57) (b:=58) sp19873 sp19930) (joinSmall (lo:=19988) (a:=58) (b:=58) sp19988 sp20046)) (joinSmall (lo:=20104) (a:=116) (b:=116) (joinSmall (lo:=20104) (a:=58) (b:=58) sp20104 sp20162) (joinSmall (lo:=20220) (a:=58) (b:=58) sp20220 sp20278))))) (joinSmall (lo:=20336) (a:=924) (b:=925) (joinSmall (lo:=20336) (a:=462) (b:=462) (joinSmall (lo:=20336) (a:=231) (b:=231) (joinSmall (lo:=20336) (a:=115) (b:=116) (joinSmall (lo:=20336) (a:=57) (b:=58) sp20336 sp20393) (joinSmall (lo:=20451) (a:=58) (b:=58) sp20451 sp20509)) (joinSmall (lo:=20567) (a:=115) (b:=116) (joinSmall (lo:=20567) (a:=57) (b:=58) sp20567 sp20624) (joinSmall (lo:=20682) (a:=58) (b:=58) sp20682 sp20740))) (joinSmall (lo:=20798) (a:=231) (b:=231) (joinSmall (lo:=20798) (a:=115) (b:=116) (joinSmall (lo:=20798) (a:=57) (b:=58) sp20798 sp20855) (joinSmall (lo:=20913) (a:=58) (b:=58) sp20913 sp20971)) (joinSmall (lo:=21029) (a:=115) (b:=116) (joinSmall (lo:=21029) (a:=57) (b:=58) sp21029 sp21086) (joinSmall (lo:=21144) (a:=58) (b:=58) sp21144 sp21202)))) (joinSmall (lo:=21260) (a:=462) (b:=463) (joinSmall (lo:=21260) (a:=231) (b:=231) (joinSmall (lo:=21260) (a:=115) (b:=116) (joinSmall (lo:=21260) (a:=57) (b:=58) sp21260 sp21317) (joinSmall (lo:=21375) (a:=58) (b:=58) sp21375 sp21433)) (joinSmall (lo:=21491) (a:=115) (b:=116) (joinSmall (lo:=21491) (a:=57) (b:=58) sp21491 sp21548) (joinSmall (lo:=21606) (a:=58) (b:=58) sp21606 sp21664))) (joinSmall (lo:=21722) (a:=231) (b:=232) (joinSmall (lo:=21722) (a:=115) (b:=116) (joinSmall (lo:=21722) (a:=57) (b:=58) sp21722 sp21779) (joinSmall (lo:=21837) (a:=58) (b:=58) sp21837 sp21895)) (joinSmall (lo:=21953) (a:=116) (b:=116) (joinSmall (lo:=21953) (a:=58) (b:=58) sp21953 sp22011) (joinSmall (lo:=22069) (a:=58) (b:=58) sp22069 sp22127))))))) (joinSmall (lo:=22185) (a:=3698) (b:=3698) (joinSmall (lo:=22185) (a:=1849) (b:=1849) (joinSmall (lo:=22185) (a:=924) (b:=925) (joinSmall (lo:=22185) (a:=462) (b:=462) (joinSmall (lo:=22185) (a:=231) (b:=231) (joinSmall (lo:=22185) (a:=115) (b:=116) (joinSmall (lo:=22185) (a:=57) (b:=58) sp22185 sp22242) (joinSmall (lo:=22300) (a:=58) (b:=58) sp22300 sp22358)) (joinSmall (lo:=22416) (a:=115) (b:=116) (joinSmall (lo:=22416) (a:=57) (b:=58) sp22416 sp22473) (joinSmall (lo:=22531) (a:=58) (b:=58) sp22531 sp22589))) (joinSmall (lo:=22647) (a:=231) (b:=231) (joinSmall (lo:=22647) (a:=115) (b:=116) (joinSmall (lo:=22647) (a:=57) (b:=58) sp22647 sp22704) (joinSmall (lo:=22762) (a:=58) (b:=58) sp22762 sp22820)) (joinSmall (lo:=22878) (a:=115) (b:=116) (joinSmall (lo:=22878) (a:=57) (b:=58) sp22878 sp22935) (joinSmall (lo:=22993) (a:=58) (b:=58) sp22993 sp23051)))) (joinSmall (lo:=23109) (a:=462) (b:=463) (joinSmall (lo:=23109) (a:=231) (b:=231) (joinSmall (lo:=23109) (a:=115) (b:=116) (joinSmall (lo:=23109) (a:=57) (b:=58) sp23109 sp23166) (joinSmall (lo:=23224) (a:=58) (b:=58) sp23224 sp23282)) (joinSmall (lo:=23340) (a:=115) (b:=116) (joinSmall (lo:=23340) (a:=57) (b:=58) sp23340 sp23397) (joinSmall (lo:=23455) (a:=58) (b:=58) sp23455 sp23513))) (joinSmall (lo:=23571) (a:=231) (b:=232) (joinSmall (lo:=23571) (a:=115) (b:=116) (joinSmall (lo:=23571) (a:=57) (b:=58) sp23571 sp23628) (joinSmall (lo:=23686) (a:=58) (b:=58) sp23686 sp23744)) (joinSmall (lo:=23802) (a:=116) (b:=116) (joinSmall (lo:=23802) (a:=58) (b:=58) sp23802 sp23860) (joinSmall (lo:=23918) (a:=58) (b:=58) sp23918 sp23976))))) (joinSmall (lo:=24034) (a:=924) (b:=925) (joinSmall (lo:=24034) (a:=462) (b:=462) (joinSmall (lo:=24034) (a:=231) (b:=231) (joinSmall (lo:=24034) (a:=115) (b:=116) (joinSmall (lo:=24034) (a:=57) (b:=58) sp24034 sp24091) (joinSmall (lo:=24149) (a:=58) (b:=58) sp24149 sp24207)) (joinSmall (lo:=24265) (a:=115) (b:=116) (joinSmall (lo:=24265) (a:=57) (b:=58) sp24265 sp24322) (joinSmall (lo:=24380) (a:=58) (b:=58) sp24380 sp24438))) (joinSmall (lo:=24496) (a:=231) (b:=231) (joinSmall (lo:=24496) (a:=115) (b:=116) (joinSmall (lo:=24496) (a:=57) (b:=58) sp24496 sp24553) (joinSmall (lo:=24611) (a:=58) (b:=58) sp24611 sp24669)) (joinSmall (lo:=24727) (a:=115) (b:=116) (joinSmall (lo:=24727) (a:=57) (b:=58) sp24727 sp24784) (joinSmall (lo:=24842) (a:=58) (b:=58) sp24842 sp24900)))) (joinSmall (lo:=24958) (a:=462) (b:=463) (joinSmall (lo:=24958) (a:=231) (b:=231) (joinSmall (lo:=24958) (a:=115) (b:=116) (joinSmall (lo:=24958) (a:=57) (b:=58) sp24958 sp25015) (joinSmall (lo:=25073) (a:=58) (b:=58) sp25073 sp25131)) (joinSmall (lo:=25189) (a:=115) (b:=116) (joinSmall (lo:=25189) (a:=57) (b:=58) sp25189 sp25246) (joinSmall (lo:=25304) (a:=58) (b:=58) sp25304 sp25362))) (joinSmall (lo:=25420) (a:=231) (b:=232) (joinSmall (lo:=25420) (a:=115) (b:=116) (joinSmall (lo:=25420) (a:=57) (b:=58) sp25420 sp25477) (joinSmall (lo:=25535) (a:=58) (b:=58) sp25535 sp25593)) (joinSmall (lo:=25651) (a:=116) (b:=116) (joinSmall (lo:=25651) (a:=58) (b:=58) sp25651 sp25709) (joinSmall (lo:=25767) (a:=58) (b:=58) sp25767 sp25825)))))) (joinSmall (lo:=25883) (a:=1849) (b:=1849) (joinSmall (lo:=25883) (a:=924) (b:=925) (joinSmall (lo:=25883) (a:=462) (b:=462) (joinSmall (lo:=25883) (a:=231) (b:=231) (joinSmall (lo:=25883) (a:=115) (b:=116) (joinSmall (lo:=25883) (a:=57) (b:=58) sp25883 sp25940) (joinSmall (lo:=25998) (a:=58) (b:=58) sp25998 sp26056)) (joinSmall (lo:=26114) (a:=115) (b:=116) (joinSmall (lo:=26114) (a:=57) (b:=58) sp26114 sp26171) (joinSmall (lo:=26229) (a:=58) (b:=58) sp26229 sp26287))) (joinSmall (lo:=26345) (a:=231) (b:=231) (joinSmall (lo:=26345) (a:=115) (b:=116) (joinSmall (lo:=26345) (a:=57) (b:=58) sp26345 sp26402) (joinSmall (lo:=26460) (a:=58) (b:=58) sp26460 sp26518)) (joinSmall (lo:=26576) (a:=115) (b:=116) (joinSmall (lo:=26576) (a:=57) (b:=58) sp26576 sp26633) (joinSmall (lo:=26691) (a:=58) (b:=58) sp26691 sp26749)))) (joinSmall (lo:=26807) (a:=462) (b:=463) (joinSmall (lo:=26807) (a:=231) (b:=231) (joinSmall (lo:=26807) (a:=115) (b:=116) (joinSmall (lo:=26807) (a:=57) (b:=58) sp26807 sp26864) (joinSmall (lo:=26922) (a:=58) (b:=58) sp26922 sp26980)) (joinSmall (lo:=27038) (a:=115) (b:=116) (joinSmall (lo:=27038) (a:=57) (b:=58) sp27038 sp27095) (joinSmall (lo:=27153) (a:=58) (b:=58) sp27153 sp27211))) (joinSmall (lo:=27269) (a:=231) (b:=232) (joinSmall (lo:=27269) (a:=115) (b:=116) (joinSmall (lo:=27269) (a:=57) (b:=58) sp27269 sp27326) (joinSmall (lo:=27384) (a:=58) (b:=58) sp27384 sp27442)) (joinSmall (lo:=27500) (a:=116) (b:=116) (joinSmall (lo:=27500) (a:=58) (b:=58) sp27500 sp27558) (joinSmall (lo:=27616) (a:=58) (b:=58) sp27616 sp27674))))) (joinSmall (lo:=27732) (a:=924) (b:=925) (joinSmall (lo:=27732) (a:=462) (b:=462) (joinSmall (lo:=27732) (a:=231) (b:=231) (joinSmall (lo:=27732) (a:=115) (b:=116) (joinSmall (lo:=27732) (a:=57) (b:=58) sp27732 sp27789) (joinSmall (lo:=27847) (a:=58) (b:=58) sp27847 sp27905)) (joinSmall (lo:=27963) (a:=115) (b:=116) (joinSmall (lo:=27963) (a:=57) (b:=58) sp27963 sp28020) (joinSmall (lo:=28078) (a:=58) (b:=58) sp28078 sp28136))) (joinSmall (lo:=28194) (a:=231) (b:=231) (joinSmall (lo:=28194) (a:=115) (b:=116) (joinSmall (lo:=28194) (a:=57) (b:=58) sp28194 sp28251) (joinSmall (lo:=28309) (a:=58) (b:=58) sp28309 sp28367)) (joinSmall (lo:=28425) (a:=115) (b:=116) (joinSmall (lo:=28425) (a:=57) (b:=58) sp28425 sp28482) (joinSmall (lo:=28540) (a:=58) (b:=58) sp28540 sp28598)))) (joinSmall (lo:=28656) (a:=462) (b:=463) (joinSmall (lo:=28656) (a:=231) (b:=231) (joinSmall (lo:=28656) (a:=115) (b:=116) (joinSmall (lo:=28656) (a:=57) (b:=58) sp28656 sp28713) (joinSmall (lo:=28771) (a:=58) (b:=58) sp28771 sp28829)) (joinSmall (lo:=28887) (a:=115) (b:=116) (joinSmall (lo:=28887) (a:=57) (b:=58) sp28887 sp28944) (joinSmall (lo:=29002) (a:=58) (b:=58) sp29002 sp29060))) (joinSmall (lo:=29118) (a:=231) (b:=232) (joinSmall (lo:=29118) (a:=115) (b:=116) (joinSmall (lo:=29118) (a:=57) (b:=58) sp29118 sp29175) (joinSmall (lo:=29233) (a:=58) (b:=58) sp29233 sp29291)) (joinSmall (lo:=29349) (a:=116) (b:=116) (joinSmall (lo:=29349) (a:=58) (b:=58) sp29349 sp29407) (joinSmall (lo:=29465) (a:=58) (b:=58) sp29465 sp29523)))))))))
  have good : (List.range 29581).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 875000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 29580 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 29580 := by
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


private def packet (i : ℕ) : ℕ := (if i < 223 then (if i < 111 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else 0)))) else (if i < 20 then (if i < 16 then (if i < 14 then 0 else (if i < 15 then 0 else 0)) else (if i < 18 then (if i < 17 then 0 else 0) else (if i < 19 then 0 else 0))) else (if i < 23 then (if i < 21 then 0 else (if i < 22 then 0 else 0)) else (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else 0))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then 0 else (if i < 29 then 0 else 0)) else (if i < 32 then (if i < 31 then 0 else 0) else (if i < 33 then 0 else 0))) else (if i < 37 then (if i < 35 then 0 else (if i < 36 then 0 else 0)) else (if i < 39 then (if i < 38 then 0 else 0) else (if i < 40 then 0 else 0)))) else (if i < 48 then (if i < 44 then (if i < 42 then 0 else (if i < 43 then 0 else 0)) else (if i < 46 then (if i < 45 then 0 else 0) else (if i < 47 then 0 else 0))) else (if i < 51 then (if i < 49 then 0 else (if i < 50 then 0 else 0)) else (if i < 53 then (if i < 52 then 0 else 0) else (if i < 54 then 0 else 0)))))) else (if i < 83 then (if i < 69 then (if i < 62 then (if i < 58 then (if i < 56 then 0 else (if i < 57 then 0 else 0)) else (if i < 60 then (if i < 59 then 0 else 0) else (if i < 61 then 0 else 0))) else (if i < 65 then (if i < 63 then 0 else (if i < 64 then 0 else 0)) else (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else 0)))) else (if i < 76 then (if i < 72 then (if i < 70 then 0 else (if i < 71 then 0 else 0)) else (if i < 74 then (if i < 73 then 0 else 0) else (if i < 75 then 0 else 0))) else (if i < 79 then (if i < 77 then 0 else (if i < 78 then 0 else 0)) else (if i < 81 then (if i < 80 then 0 else 0) else (if i < 82 then 0 else 0))))) else (if i < 97 then (if i < 90 then (if i < 86 then (if i < 84 then 0 else (if i < 85 then 0 else 0)) else (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else 0))) else (if i < 93 then (if i < 91 then 0 else (if i < 92 then 0 else 0)) else (if i < 95 then (if i < 94 then 0 else 0) else (if i < 96 then 0 else 0)))) else (if i < 104 then (if i < 100 then (if i < 98 then 0 else (if i < 99 then 0 else 0)) else (if i < 102 then (if i < 101 then 0 else 0) else (if i < 103 then 0 else 0))) else (if i < 107 then (if i < 105 then 0 else (if i < 106 then 0 else 0)) else (if i < 109 then (if i < 108 then 0 else 0) else (if i < 110 then 0 else 0))))))) else (if i < 167 then (if i < 139 then (if i < 125 then (if i < 118 then (if i < 114 then (if i < 112 then 0 else (if i < 113 then 0 else 0)) else (if i < 116 then (if i < 115 then 0 else 0) else (if i < 117 then 0 else 0))) else (if i < 121 then (if i < 119 then 0 else (if i < 120 then 0 else 0)) else (if i < 123 then (if i < 122 then 0 else 0) else (if i < 124 then 0 else 0)))) else (if i < 132 then (if i < 128 then (if i < 126 then 0 else (if i < 127 then 0 else 0)) else (if i < 130 then (if i < 129 then 0 else 0) else (if i < 131 then 0 else 0))) else (if i < 135 then (if i < 133 then 0 else (if i < 134 then 0 else 0)) else (if i < 137 then (if i < 136 then 0 else 0) else (if i < 138 then 0 else 0))))) else (if i < 153 then (if i < 146 then (if i < 142 then (if i < 140 then 0 else (if i < 141 then 0 else 0)) else (if i < 144 then (if i < 143 then 0 else 0) else (if i < 145 then 0 else 0))) else (if i < 149 then (if i < 147 then 0 else (if i < 148 then 0 else 0)) else (if i < 151 then (if i < 150 then 0 else 0) else (if i < 152 then 0 else 0)))) else (if i < 160 then (if i < 156 then (if i < 154 then 0 else (if i < 155 then 0 else 0)) else (if i < 158 then (if i < 157 then 0 else 0) else (if i < 159 then 0 else 0))) else (if i < 163 then (if i < 161 then 0 else (if i < 162 then 0 else 0)) else (if i < 165 then (if i < 164 then 0 else 0) else (if i < 166 then 0 else 0)))))) else (if i < 195 then (if i < 181 then (if i < 174 then (if i < 170 then (if i < 168 then 0 else (if i < 169 then 0 else 0)) else (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else 0))) else (if i < 177 then (if i < 175 then 0 else (if i < 176 then 0 else 0)) else (if i < 179 then (if i < 178 then 0 else 0) else (if i < 180 then 0 else 0)))) else (if i < 188 then (if i < 184 then (if i < 182 then 0 else (if i < 183 then 0 else 0)) else (if i < 186 then (if i < 185 then 0 else 0) else (if i < 187 then 0 else 0))) else (if i < 191 then (if i < 189 then 0 else (if i < 190 then 0 else 0)) else (if i < 193 then (if i < 192 then 0 else 0) else (if i < 194 then 0 else 0))))) else (if i < 209 then (if i < 202 then (if i < 198 then (if i < 196 then 0 else (if i < 197 then 0 else 0)) else (if i < 200 then (if i < 199 then 0 else 0) else (if i < 201 then 0 else 0))) else (if i < 205 then (if i < 203 then 0 else (if i < 204 then 0 else 0)) else (if i < 207 then (if i < 206 then 0 else 0) else (if i < 208 then 0 else 0)))) else (if i < 216 then (if i < 212 then (if i < 210 then 0 else (if i < 211 then 0 else 0)) else (if i < 214 then (if i < 213 then 0 else 0) else (if i < 215 then 0 else 0))) else (if i < 219 then (if i < 217 then 0 else (if i < 218 then 0 else 0)) else (if i < 221 then (if i < 220 then 0 else 0) else (if i < 222 then 0 else 0)))))))) else (if i < 334 then (if i < 278 then (if i < 250 then (if i < 236 then (if i < 229 then (if i < 226 then (if i < 224 then 0 else (if i < 225 then 0 else 0)) else (if i < 227 then 0 else (if i < 228 then 0 else 0))) else (if i < 232 then (if i < 230 then 0 else (if i < 231 then 0 else 0)) else (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else 0)))) else (if i < 243 then (if i < 239 then (if i < 237 then 0 else (if i < 238 then 0 else 0)) else (if i < 241 then (if i < 240 then 0 else 0) else (if i < 242 then 0 else 0))) else (if i < 246 then (if i < 244 then 0 else (if i < 245 then 0 else 0)) else (if i < 248 then (if i < 247 then 0 else 0) else (if i < 249 then 0 else 0))))) else (if i < 264 then (if i < 257 then (if i < 253 then (if i < 251 then 0 else (if i < 252 then 0 else 0)) else (if i < 255 then (if i < 254 then 0 else 0) else (if i < 256 then 0 else 0))) else (if i < 260 then (if i < 258 then 0 else (if i < 259 then 0 else 0)) else (if i < 262 then (if i < 261 then 0 else 0) else (if i < 263 then 0 else 0)))) else (if i < 271 then (if i < 267 then (if i < 265 then 0 else (if i < 266 then 0 else 0)) else (if i < 269 then (if i < 268 then 0 else 0) else (if i < 270 then 0 else 0))) else (if i < 274 then (if i < 272 then 0 else (if i < 273 then 0 else 0)) else (if i < 276 then (if i < 275 then 0 else 0) else (if i < 277 then 0 else 0)))))) else (if i < 306 then (if i < 292 then (if i < 285 then (if i < 281 then (if i < 279 then 0 else (if i < 280 then 0 else 0)) else (if i < 283 then (if i < 282 then 0 else 0) else (if i < 284 then 0 else 0))) else (if i < 288 then (if i < 286 then 0 else (if i < 287 then 0 else 0)) else (if i < 290 then (if i < 289 then 0 else 0) else (if i < 291 then 0 else 0)))) else (if i < 299 then (if i < 295 then (if i < 293 then 0 else (if i < 294 then 0 else 0)) else (if i < 297 then (if i < 296 then 0 else 0) else (if i < 298 then 0 else 0))) else (if i < 302 then (if i < 300 then 0 else (if i < 301 then 0 else 0)) else (if i < 304 then (if i < 303 then 0 else 0) else (if i < 305 then 0 else 0))))) else (if i < 320 then (if i < 313 then (if i < 309 then (if i < 307 then 0 else (if i < 308 then 0 else 0)) else (if i < 311 then (if i < 310 then 0 else 0) else (if i < 312 then 0 else 0))) else (if i < 316 then (if i < 314 then 0 else (if i < 315 then 0 else 0)) else (if i < 318 then (if i < 317 then 0 else 0) else (if i < 319 then 0 else 0)))) else (if i < 327 then (if i < 323 then (if i < 321 then 0 else (if i < 322 then 0 else 0)) else (if i < 325 then (if i < 324 then 0 else 0) else (if i < 326 then 0 else 0))) else (if i < 330 then (if i < 328 then 0 else (if i < 329 then 0 else 0)) else (if i < 332 then (if i < 331 then 0 else 0) else (if i < 333 then 0 else 0))))))) else (if i < 390 then (if i < 362 then (if i < 348 then (if i < 341 then (if i < 337 then (if i < 335 then 0 else (if i < 336 then 0 else 0)) else (if i < 339 then (if i < 338 then 0 else 0) else (if i < 340 then 0 else 0))) else (if i < 344 then (if i < 342 then 0 else (if i < 343 then 0 else 0)) else (if i < 346 then (if i < 345 then 0 else 0) else (if i < 347 then 0 else 0)))) else (if i < 355 then (if i < 351 then (if i < 349 then 0 else (if i < 350 then 0 else 0)) else (if i < 353 then (if i < 352 then 0 else 0) else (if i < 354 then 0 else 0))) else (if i < 358 then (if i < 356 then 0 else (if i < 357 then 0 else 0)) else (if i < 360 then (if i < 359 then 0 else 0) else (if i < 361 then 0 else 0))))) else (if i < 376 then (if i < 369 then (if i < 365 then (if i < 363 then 0 else (if i < 364 then 0 else 0)) else (if i < 367 then (if i < 366 then 0 else 0) else (if i < 368 then 0 else 0))) else (if i < 372 then (if i < 370 then 0 else (if i < 371 then 0 else 0)) else (if i < 374 then (if i < 373 then 0 else 0) else (if i < 375 then 0 else 0)))) else (if i < 383 then (if i < 379 then (if i < 377 then 0 else (if i < 378 then 0 else 0)) else (if i < 381 then (if i < 380 then 0 else 0) else (if i < 382 then 0 else 0))) else (if i < 386 then (if i < 384 then 0 else (if i < 385 then 0 else 0)) else (if i < 388 then (if i < 387 then 0 else 0) else (if i < 389 then 0 else 0)))))) else (if i < 418 then (if i < 404 then (if i < 397 then (if i < 393 then (if i < 391 then 0 else (if i < 392 then 0 else 0)) else (if i < 395 then (if i < 394 then 0 else 0) else (if i < 396 then 0 else 0))) else (if i < 400 then (if i < 398 then 0 else (if i < 399 then 0 else 0)) else (if i < 402 then (if i < 401 then 0 else 0) else (if i < 403 then 0 else 0)))) else (if i < 411 then (if i < 407 then (if i < 405 then 0 else (if i < 406 then 0 else 0)) else (if i < 409 then (if i < 408 then 0 else 0) else (if i < 410 then 0 else 0))) else (if i < 414 then (if i < 412 then 0 else (if i < 413 then 0 else 0)) else (if i < 416 then (if i < 415 then 0 else 0) else (if i < 417 then 0 else 0))))) else (if i < 432 then (if i < 425 then (if i < 421 then (if i < 419 then 0 else (if i < 420 then 0 else 0)) else (if i < 423 then (if i < 422 then 0 else 0) else (if i < 424 then 0 else 0))) else (if i < 428 then (if i < 426 then 0 else (if i < 427 then 0 else 0)) else (if i < 430 then (if i < 429 then 0 else 0) else (if i < 431 then 0 else 0)))) else (if i < 439 then (if i < 435 then (if i < 433 then 0x299f4f72d315089ca4872128f4c6e631415b89683e218e09583040a40000299ef302b2143497445f1fd0e886862e9141088c39617508c830c0d20000299e99429e93ac90e42c1ec8e0c6542d9141087c382162080828809c0000299e3b42c314b89a247720d8ee06ba2f914788c83ae18708f83140cc0000299ddc02cf95209d648c2158f4c6e631415909403e018b08e83200ca0000299d7ea2b6944c97a4631ff0e9869e2f614d08f43b817608f03100be0000299d1fd2cb94f49bc4842170f286d431a15a893c3d418709283080c00000299cc712a413b891a4351e88de862e2c4139083c36c15807c82a40ba0000299c66b2d094f89ba48b2140f306c630c150091c3d018708f03040ca0000299c08b2bd14989984702098ed86b02fe14808c43be18109803640d20000299bab02c1149898e4622000e9c68a2ea14508b03b4179096830c0c60000299b4d62c1147c9904672058e9467e2de14088a038817308582cc0ba0000299af062bb144495644f1f80e686762df14408b439e17008c82fc0cc0000299a96929d136c9044231e38db46442d013e888838016108182c40c20000299a3a22b6944896c45d2020ed06a02ef14388943a016b08582e00b000002999dca2c1947c97e4622028e8c67a2e2141889038016608c82e00c2000029997e52ba94789704562008e786962f214c88ec3ae17708b82c80bc000029991fb2c2144c9764511f70e686782e114608ac3a616708302ac0b200002998c112cc14bc9a846d20c8ea86ae30315309103c018909803200c60000299861e2ce94b898c4702050e946862f014988fc3b217b09102f80b8000029980402c294b898e46e2068ecc6a62fa14b08cc39217408a82d80a800002997a9f2a913e49364431f20e7c69e2e6142889038c16a08482dc0ae000029974ec2b0942496c4562010e546742d813d086c3a217609183140ba00002996f052c1148098a46a2078eb468e2f614f08f83b617908e83100ba0000299690a2d695289e849221a8f3c6e830815709503c418509283200be000029963592a893f49404451ef8e186502c813d089c39c17209003000cc00002995d6d2c614a49824542010e806802e614a88a039c17008d03100c0000029957902c394909904601fe8e746842e814488c039017908802e80be000029951c22b714489664571fc8ea46842f014808b43a017a08d82fc0ca00002994bdb2c694a097e4521fc0e5867a2f514a08c83aa17208582f00c00000299462f2a993c49284431f48e2866c2db140088439c171088031c0c00000299404e2c494e49b646c2050e7067c2e1141088c3a417308882c80a600002993acf295132c8d64191e20db06422c213a088838816c08a02fc0b6000029934ca2d195309d248d2178f5870031715b89743d818309403140d000002992f192ae941893a4411f10dec6362be134084836c16508502c00be0000299294f2ba145c96e4511fa0e4c6742e314208a038e15d07e82a80a8000029923882b5141495644d1fb0e5066c2dd13f888438e16e08882bc0ae00002991d962c7149899c4752148f146da30b15488fc3ba17f09083240c4000029917d42b094389764622008eac68a2e814888cc39216b08b02e40c0000029912062b8142c9484512018e846802e314308b439817208982d80b600002990c1c2c494989844621ff8ea868a2ea14488c43a817008e82ec0ba000029906582b614389524491f40e546662da13f088037416508602c40ae0000299007e2c1145896e4561fb8e5c6722d4140089c39617509102f80ba0000298faa12c1149c9904672008e6c6742e5141888438616108782a00b60000298f4d12bd949c98e45b2020e9468c2df14908a839416e08a82d40aa0000298ef132b214389704581fe0ea06a82ec14688c03a217508982d40ac0000298e9342c3949498e46920d8f0c6da30a156893c3e418e09483000ca0000298e3432c514cc99446d2088ecc6a42f614a08b03b417c08e82e40a20000298dd622be146c98a4611ff8e7867c2e414408cc3ba17f09483080c60000298d7832bd145897645f1ff0e846782d913b886035e15808082a80b00000298d1562e21588a084a321d8f986f631315a89483d418809803180c80000298cb572d515309d048c2128efc6ca30015309243ce18209282c80ae0000298c58d2ba14489664641fe0e6c66a2da141087c39a17608d82f00c20000298bfc92b094189564602010e9068c2e214388a43a417508d02f40ae0000298ba052b3944c9564522030e7c69a2f114988c43aa17d08c83080c20000298b4192c3949499047420d0ec468c2ef144089c39216d08782d40c40000298ae482bd14449984612030ee46ae2f914908d03a817809183180bc0000298a8792bb948498245f1fc8e8069a2f214b08e03c218309203280c20000298a2752d294fc9bc47620e8f086cc30615089203c018109103000c800002989ca12bb94b89944692088ee86c6308154892c3d618a09603140c80000298970e299135c8fe42f1ee0e286682dc140088c39a16908882c80b6000029891332be94889884622058eb46c830e157893c3e018909603240bc00002988b3a2cd14f89bc4862110ee46ae30315108e03b617c08c02ec0c40000298857f2aa93e49464471fb8e7c6882e514708dc3ac17c08b83140c4000 else (if i < 434 then 0x29b6a202be949098246e2078ee06a22e914a08b43b817b08e82f40ce000029b64522bc149497e45f2020e8067e2e214788a439016708a82e00b0000029b5e5b2cb94ac9a04672000ebc6aa2f114b88fc3d818609303080c6000029b58872ba94489504561fa8e5c6802de14688b039416e08783040c4000029b52ac2c2949097e4632040ea06a22f715009003cc19109b83280c0000029b4d002a813f494a44c1f38e1864e2dc14008a039c17709383100cc000029b47402af14209524541fd0e506562cf13f88b439416b08b82d00bc000029b414a2cd94f898a45b2040ea46922f314688e43b818009303280c0000029b3b932ac93e893a4431f58e3c6622d213d884837a16908b02f00b0000029b35ca2b714349484531f90e8468e2f114808fc3b417d09203000ce000029b2ff82b8146c97a4652060ed06b02f414688d43b018009103140ba000029b2a252bb946c97a4662000eb86922f014488b83b417908a82fc0ce000029b24382c614b899e47520e8ef46c230115008dc3a417b08c82e40c2000029b1e722b4943c98445c1fa8e546622d1138888039616908a02b40a2000029b18942be148c98c4672030eb46862e613c088438a16e08802f00c4000029b12a92c394949904642030e7c6782e514688ac39a17208a82f00b6000029b0ccc2ba947899246a2038ea46842e414508c43bc18408f02e80ae000029b06f52bc94809844692080ed46b22ff14c08e83c418b09983300d8000029b012f2b794749764641fe0e746822e013f08c839c17008e02fc0b8000029afb6c2b6143096e4511fc8e8867e2e9146888c3a017608b82e40c2000029af5b22ac140496244d1f30e286542d714908e83c618309502f00be000029aefee2b7142095444c1fa8e686762e914208ac39a17408982d80c4000029aea232b4940c94c4581f78e5c68e2e9145089438616d08802e80aa000029ae4342be94709804602050eb86b630814f88e03c417408702b40ae000029ade492ca14a89964702090f186ba2f914508a43a016d08683000be000029ad8802b994689624511fa8e5467c2df140889c39416e08982bc0aa000029ad2a72bb146c96444f1f88e3c6562d913b084437415b08382b80ac000029acccb2be14549704572008e906882e414308b038c16908902c40be000029ac6fd2b6144495444d1fd0e846962f614908cc3aa17d08d82e40b6000029ac11b2bd945096845c2010e9868a2e414288ac3a216b08b02d00bc000029abb412bc94889884672008e906882e713f08903a017508582c00aa000029ab5932a393ac92a43f1fd8e6c68e2e414388ac3b017a08a02c40b0000029aafc32b9949497c4692010ea46962f514808a03a816e08902ec0c0000029aaa092b494389584511fa0e706642e114088ac3ac17608b02cc0c4000029aa3fc2da153c9c44842158f206cc31415889043d218e096030c0b8000029a9e292b9948499246e2020e7867c2e7144889039e17008882f80c8000029a986a2ab942096844d1f78e4c66a2d413d087437c16a08602dc0b2000029a92762c9148498845e1fe8e8068e2ea14508dc3a216e08b02b80b0000029a8c7c2c914f49c04852120ee86c430e155890c3b017a08d83180ce000029a86902cb94d49b246c2060e986982eb14588b43b217808a82c40b8000029a80e82a993d892a4391f10e1062e2c0135886838816508902c00b4000029a7b222b293f895245c1fb0e446702da140089c38e17108e03040ce000029a754c2b894709764591f98e7c6722ea14788b839616608202b80b4000029a6f5b2cb14dc99e46f2078ef86a82f814508bc3ac17708a02d00bc000029a69822b8946497445e2018ea868c2ef14e88e83c018308c82e40b6000029a63df2a193c494643f1f48e3064e2ce13b887438e16d08b831c0d0000029a5e1f2af141895c45d2008e6066e2e114808a43a417008f83040bc000029a58472bd94609684581fc0e6c67e2e714708a43a417e09303180d6000029a52592c914e49b847e20d8ee86b42fe15109103ce19409803340d8000029a4ca22af140494644d1fa8e8868e2ec147890c3d018709303000aa000029a46f12b094049584541ff8e886982f114e08dc3a417208802bc0aa000029a41232b8144c9684571fa8e206702e2141889438816708482b40ae000029a3b4e2b7145096845a1fd8e5c68c2e614788f83ba18509482f40d0000029a35892af140c94e4461fb8e586782ec14608c83ac17e09303200b6000029a2fbe2b2140c93e4461fa0e746742d213b886837016007f82dc0be000029a29fb2b393ec94a4471f70e046662d4134886437c15c08602c00a4000029a24272b9146496444c1f90e8068a2ea14788b43be17608b82f00b8000029a1e4a2c314a498c4622098edc6c02fb15109083b017d09603080c4000029a183a2d495149e04922118f106ca30915789203e018709503280b2000029a12452c794ac99446d2020e9c6ae301151892c3ba18708f02e80ba000029a0c8d2ad93f494243e1f10dd863c2d113c088438e17d09503340cc000029a06b52b2141c95a4501f80e506662dd143089c39616308782d40ac000029a00cb2c214ac9824642010e9c6782e513f086037415a081827c0a00000299fb092af142896044e1f80e3c6742e414908f43c818008d02d40b8000 else 0x29ce0342bd145c9884601ff8e806702df14108a039c17a08f82d40be000029cda622bb148098c4652010e7867e2db140088c39617308c82dc0be000029cd48b2be949499e4702060e7c6902e2142889c39617809083040c2000029ccea12c794cc99e4682030ec46b62f414508b438c17208582e00b8000029cc8d72bc948097845f2008e7867e2e2142087c3a216f08902cc0ce000029cc30d2ba147498a4692060eb868c2e1145088838216d08982f40b8000029cbd382b994689504461fc0e446822e014688c43b017d08b02c00aa000029cb7802a8939c92a4351e68dc86342c0133082c35e15907d828c09a000029cb1ad2b9947c9844642090ecc6b82f915289103d619509683200dc000029cabd62bd14909844632088eb06822df14808e03b617b09082f80bc000029ca5e02cc94e09bc4852148f286d62fe15189143d018008f02e00bc000029ca01a2b3142895a44d1f50e2464e2cd1398868378165087828c096000029c9a0e2d394f49b04812100ef46b42f814b08fc3cc19109903380d0000029c93fd2de958c9f24992220fc471232a15d09683f41a009b03580d0000029c8e5829e937890c42e1e90dd863e2ca13c087838016008702d80b2000029c887d2bf944496245e1fc8e7c6902e914c88e43ae17b09102c40a8000029c82892c714c099e47020c8f006ba30914a88cc39017308c82e40ce000029c7ca82bd948098c4692070eac69a2e213f88a039e17008982c4098000029c76bc2c394809804651fb8e646642da13d08ac3aa17f08c82f00b8000029c70fa2ae14249404461fa8e6c66c2d8138085c36816308502e80b2000029c6b362bc145c9664521f88e886962f214608c03b017b09103080c4000029c65472c514a099847220d8ee06ac2f114908c838a16a08702d00b0000029c5fa32a5142095044a1fd0e906822d914088903a8182093031c0ca000029c59da2b294289544491f58e586822f414788bc3ac17108e83080ca000029c53f42c694c09ae47a2068e986982f614c08fc3ba17e09083200ca000029c4e2e2b294409624571f98e2c6582dc14188a839a17008a02c80ae000029c48412c3949898645f2030ed06be2f214a88c03a617408502c40ac000029c428a2ac93d493443e1f28e0c6442cf13c886c37c15f08702ac0b2000029c3cbb2bb94689884602010ec06a42f714988ac39817608c83140ce000029c36f22b8945c9584531f90e2066e2d3136082836e15e08082cc0be000029c31202b9944c97a4581fc8e306502d913e888838a16f08882dc0b8000029c2b762a993f09504561ff8ea46962e914e08d03b617c09703180bc000029c25902c514a099846c2080eb468c2ee14688ec39216d08a82ec0c4000029c1fb02c594a89a64682070ee06ae2f914d88f83ca18008f83180ac000029c19d52b2942895844f1fb0e8c69e2ef14b89003b817d09302f80a4000029c13f42c094b49ae4702040eac6822e614888a839c18009002fc0b8000029c0e182c0947c99246b2040eac6b22f814b88e03b817c09283180c8000029c08442bd94509664521f98e486642cf13b086c38216908b02f40b8000029c02832b6946496845f2010ec06ac2fb152090c3d218108a02c40a8000029bfc8e2d195149c24882138f486dc311159896c3ea18e094030c0ba000029bf6942d315389d847c2150f286d430f15809603f218d09182f80bc000029bf0c92b5143095644a1f90e5865a2da13d084037e16b08402b00b0000029beb102b0145896a4571fd8e646782e214088c03a017608a02f40ce000029be5382b7945c9584501f80e5c6762e7142089c38a16408802ec0b4000029bdf682ba144497045a2008e8c68c2f014888bc3aa17508a82d80b8000029bd99f2bc146897245a2088ec06aa2ea144887838817408c02cc0b4000029bd3ca2c014ac99e46c2098ea06922e914788b438815b08582bc0ba000029bcdfa2bf146c96045d1fb8e4868a2e7141087839817908782c80b6000029bc80d2c914c49904672008e8c6842e814388843a017709183100c0000029bc23e2b8146c96c45b1fc8e786782e414b88d03ac16d08602c00aa000029bbc692bc144c9704611fe0e706702dd14308a03a016a08c02e00ac000029bb68f2c2949499845f2010e986942ee14208a03a217a08d82e00a8000029bb0c02c114a49884671fc0e7c66e2e1140889837416b08a02c80b6000029baad12c994e49a846f2020ee46b02ff14c09043ac17b08a82f40b8000029ba4e52c194bc9b44832108f246d630b15609203d617f09103080be000029b9efe2c614d09b04692078e986a42f814f08fc3da17908c83180cc000029b99392b5945496a45a1ff0e6868a2e814288cc3b217208c82b40bc000029b934e2c494a89b046b2040ec46ac2f214808d83aa17008c03040ce000029b8da12aa13dc93c43f1ef8e1865c2cb13a888438416108082940ac000029b87922d815309d448c2130f446c82fb15409083be18309202f80c0000029b81b22c794b499045f2010e986822e614588d83be17508e83180c6000029b7bc32c914a899647220b8ec06b42f915009003c217708d02ec0c4000029b75a72df95a8a164a521a0f4c6e0313153890c3c0173092031c0cc000029b6ffb2a0938891042f1eb0de462c2bd130080035615608302840a6000)) else (if i < 437 then (if i < 436 then 0x29e55442a493b49384461f60e1c66a2d814388a43a217b09102f80d4000029e4f672c0947c9864662040eb86882e313d085c37e16d08782d00b4000029e49a42ae14209644521f98e786802df14488b83aa17a08e02fc0b0000029e43e92b013fc9504441f30e406542cf14108a43ac16908482bc0c2000029e3e0a2bb949898c45f2038e906982f514c89003d218509103180ce000029e38672a413b09324381e90de86482ca138887038c16508982d40c4000029e327d2c194789a24682070ea068a2e5143887038416c08a82d00b8000029e2cd62a393d493e4421f58e3867c2e1140889c38216908d02f80c4000029e26dd2ca14c09a44792088ea869a2e4142888c38816908782f00ba000029e210e2bc148098846720a8ee46942eb14e08f43ac16f08c83040b4000029e1b3f2bb14509604591fd8e9868c2e8142088837816d08a02fc0b2000029e156a2c4149498446c2088ef86c22fb15109003d818d09703380d4000029e0fa82b3946c98c4622028ea06922e3142888c39617008282b00ac000029e09c22be146098246e2078ec86ba2ff152090c3d818a09483380cc000029e03d32c914f49c64832108ed86ac2f614788c43a617908f83080c0000029dfe0b2bb94849644571ff8e786782e314388bc3bc17c08982c40b4000029df8412b4943096445e2048ebc69a2ef14908d03aa16e08882dc0a8000029df2672be945c96a4552000eb46a02e214088903b217508d02f40b0000029deca02bd14689864571fd8e886962e914388a039216d08a02f40c2000029de6972d695389e64962180f586f6311157091c3c218109103100be000029de0d32b413e894844e1f78e346622de13e087837216608902e00ba000029ddae42c994cc9b647320a8eec6ca305159093c3da19109883000c0000029dd5142ba947097445d2000e906802e7141088838416c08702e00be000029dcf662ab93cc9104301e70dcc63c2ba135885037e15e08002c00b2000029dc9a62b5145c9684602068eac6a4300153092c3e219009b835c0c4000029dc3d12bd94649844612030ed46962ed14a88e83bc17f08f03000ce000029dbe092b5940494e4561fc0e9068c2ea14608ac3b417f09003180bc000029db8312ba148c98c45e2078ea869e2ed14808b03ae18009502f00b8000029db2642b193f09404431ec8df86602d713e886c39816c08602d00c0000029dac8c2bd14749804692058ef06cc30415089003bc17f08b82d80b4000029da6c62b3144096c44e1fa0e406682e114588c03a017c09002e00b4000029da0d82c914d89a046d2058ec46b830015189103be17f09002fc0b8000029d9b082b9146c9744612038e8c6ae2f614f090c3c417809103340c8000029d95402af944c95e4591f80e4c6922e014508ac39217108982dc0a2000029d8f9c29e936c90e42b1ee8ddc6542db13f08a43a017e09083040b2000029d89e22b3142c9704642018e9c6942e6146888039a16308582b80c4000029d84042c3949c9a24662088ed06c22fc14b88e83b017f08c83180c4000029d7e152c3149498846b2058edc6be2ff15209303de193092830c0c2000029d78222cc15049ba4822170f146ca2fb15189043b818208d02e80b6000029d725a2b414149564411f48e4c6702e514588d43be18408f82ec0ba000029d6c7f2bc94809904632040ec46b02fc151091c3e019509803340d2000029d66ae2c1147898246d2030ea46822e614588b839416908b82d00b6000029d60d12c194909904631ff0ed06a42f614988c83a217408802dc0aa000029d5ae92c314a099c4732090ec46a62f8150890c3be18109283080c6000029d55042c094a89904602068ecc6b22fa15189083bc17f09003080be000029d4f2a2bd947c97e45c2028e906942e7145888c3ac17108e02f40ba000029d493c2c914d099e46f20a8ecc6b62f914a88c43a417409183200cc000029d435e2c0148c9864571fb0e906782e014008b43a416f08802d80c2000029d3d8a2b5946c9784682090ee06b22fc14f89143ba17108c02e80b2000029d37ab2c314a09a447a2108f0c6be2f915389083c417b08f03040d0000029d31f32ac941493843f1f30e3866a2dc14708c03ac17508b82f80bc000029d2c522a113b091a4311ea0e0864a2bf132081436615f08382c00b8000029d266e2c5148498c45e2050eac68e2e4144087838a16908482e40be000029d20882c3148099c46a2038e8868c2f114588c039c16e08582c40a6000029d1a8d2cd14cc9a046b2098ef06ca2fb14d08f43aa17608f82f80be000029d14a52c594c09c24872170f406da30a15188e83ce17408c83080ce000029d0ec72be94a098245b1fb8eac6742df14208a03a017608d82fc0c8000029d08f92ba14709684602030ea068a2ed14d88dc3b017408c02dc0bc000029d030b2cb14d09a04702088ecc6982f414c88dc39c17008a02c00ac000029cfd362c0147c9664581fa8e6868c2f514808b83a416a08502a8098000029cf7712b4941895c4431f40e6465a2d4137084836c15d08382c40b0000029cf19c2c1149c9ae47a20e0f086b82f914808fc3b617a09002ec0be000029cebe82ad94009464481f68e446562d713a884437216208902ac0a6000029ce60c2bf94cc99e46c2020ed46a42f114d89083ce18e09303240c6000 else 0x29fca752ae93e49484501f98e7c6802f014688c03ae17d08e82d40c0000029fc4ce2a613989144341ed0e2064c2d613d889c38617208802c40b2000029fbf382a013809224431f60e606942eb142889039e17708e02f00c8000029fb9732b4942094e44e1f80e706722d9142888436215a08382a40b0000029fb3a12b9944897645f2008e986882e513f88b03a417608d82ec0c4000029fadcc2be946c9784521fb8e486642d4142089838a16508502dc0bc000029fa8042b6942894c44d1f88e4466a2d6140086037416007e826c09e000029fa24f2aa13f894e44c1f28e1c66e2d714208ac3bc17c08f83100aa000029f9c7e2b9949498045b2028ec468e2e714308c43ae178092032c0c4000029f96832cf14f49b447320c8eb069c2ed14b08ec3a617c09203040ca000029f90ab2bb943897c4642028e786802d913e88a83a417c08f83300ba000029f8af82ad141c9524551fc0e446782d6142088437616808002a00a4000029f85252b694549744702098ed46b82f414b08d03bc18609382fc0b0000029f7f3e2cd953c9da48b2120f0c6ba2fd14e88e839416508a02f40ba000029f793f2c994bc9884732088eb46a02f414b08d839e17708b02c00a6000029f73522c694c89b44822130f086cc30615108f03b218309283240ca000029f6d732bf947097846b20c8eec6ce30314c88cc3ac18008a82e40c6000029f67992be949099a4692080ec869e2e8144089839816e08e02f40b8000029f61bd2bf948899047620d0ed469a2f214909003b818109683200c0000029f5bd42c2149899c4732058ec86a62fb15308f83c617e08e82f00ba000029f561c2af142895844c1f10e2466e2da14588b43b017a08b02d80c8000029f50422bc147498847220d0ef86a62f514b88d83a417308782c80b4000029f4a662c194b89a047f2120f046c030414e88ec3d418c094031c0ca000029f44ae2b2143496245c2000e986942ed14688ec3c617d09102f00c0000029f3ec52bb14549744591fc0e646782e714608cc3b017409083240ca000029f38c72ce94f49b447b20d0ee86b830515409543d819009603500c2000029f331e2a613c89304441f20e2c6682d7142887438817008b83200c6000029f2d602b5942896a45b1ff0e746862ef14b88c439e17a08702c40b8000029f27702c795049ca4882198f386ea30d15589383ce188097832c0d6000029f21842cb94b099846b2098ed86a430014e89243d618d09803080ba000029f1bc12b614289704572020e6067a2d9141089839c16b08982d80bc000029f16052b3142095e44f1f58e2c6602d713f089439c17a08c02f80ce000029f101d2c514a09844722100f046d230215789283dc18c096031c0ce000029f0a482be94b09944632010ea46a82fe15289043cc17d08f02d40aa000029f047c2b614149404371ec8e0463a2c3133885838616808502a80b0000029efea32bc146c97e45d2088ef46a62ec14988f83c817c08a02fc0c0000029ef8db2b7942497645e2000ea06942ea14508d83c417c090830c0ca000029ef2eb2c994e89c44892188f3c6d42fd15088f03be18108f03040b8000029eed282ad13f895044d1f48e406522d513c088038e17608e02c40ac000029ee75e2b9143c96c45c1fd0e886962ec14a08fc3ba18508e82d00b2000029ee17f2bf145097e4631ff8e9c6962fb14788e43ce17c09183200d6000029edbb72b714409564491fd8e746702e114408b439816308a82ac0ba000029ed5b12d815309d248f2168f486ec30815609383e018c09383240d6000029ecffa2af13fc93c4431f70e706a62e214188a039416308302a80ae000029ec9e62da153c9da4882158f106d02fd14c091c3b417c08f82e00b6000029ec4132bc946c98245c2058ec06ac2ed14908e43a216d08782e00b8000029ebe2f2bf946c97e45f2008eb068c2ee14f09103c018709403380ce000029eb8602b614389604561ff8ea46a42e814808cc3a417508c82f40a8000029eb27b2c8948498a4652020e9469a2dc14488c03bc17808982d80b6000029eac8a2c594cc9904672008e846902f314e08bc39417408982cc0aa000029ea69c2c914c09a847f2118f006b82fc14888c839e17c08b830c0bc000029ea0d82b6941895244b1f80e4c6822e914108c03a417e08b82e40bc000029e9afc2c214c89a64702048e906a42f114c08ec3ae17c09283400c4000029e956529d137491442f1f28e1464c2c813f08a439a16808982e00c8000029e8f902b6943496645b1fc0e3466e2db14188a439c17508982cc0c4000029e89b52bb147897845e2058e786702da13f089838015e08202bc0a8000029e83fa2ac941494a4441fa0e346522cf142088c3a017608882ec0ac000029e7e352b314289504551f98e546802dc14588b83a417108982ec0c0000029e78562c0948c99246a2058e7067a2e214588b439e17f09203200ca000029e726e2c494989984702058e7c6862e914808d83ac17508e83200c6000029e6c682d215289e049d21a0f986f231d15c89543fc19a09803280c4000029e66b32b193f892e4311ee0e2865a2d014008bc39c17308802f00b0000029e60cf2c3149c98a4652070eac68e2e7142887c39817508782d00ac000029e5aed2c514a49a447620b8ec06922f814a08c43ac16f08e83300c8000) else (if i < 438 then 0x2a13ee02be94b09a44792098ec069a2fa14a88fc3ce17f08c02e80c600002a138f12c814c89a047620f8ef86ba2fb15289043c017d08d82ec0be00002a133132c494c09a44882150f186ca2fa14d89143ca18109183080c400002a12d3d2b814209544592008ea46aa2f314988fc3c417e09182f80ae00002a1276a2bb145498a46d2088ee86b62fe15309043b216d08882d80b800002a1218b2c314c49a24712098eec6a62fb15509483f019109683180bc00002a11bb42bd947498a4612040ea869e2ec14488c43ae186098033c0ce00002a115db2ba14589564502000e906982f914f89243be17608c02b40b200002a10ffa2be146097a4602028ea469e2ec14608ac3a417508f82dc0ba00002a10a362b4141895a44c1f90e5c6702df13f888c39816908602e80ac00002a104842b114189464471f68e706642d813e08ac39216e08882cc0c200002a0feab2b794289804581fd0ea46a22f914a889c38e16608202b80ae00002a0f8c92bf94989704581fc8eb06882e914588a439616e087029c09e00002a0f2f32bd14509624541f18e5866e2de144089438a16f08e03000c400002a0ed382b0940895c45b1fb8e5c65e2da13c085439417408782b80b200002a0e7892ad941c95c4571f90e386722e214108a438416f08682c80aa00002a0e1c92b0141496844f1fb8e8067e2d713f086837416008682b00a800002a0dbed2be14809804642038ec469e2e0141088439816c08e02ec0bc00002a0d62e2b214389744642038e8068a2e014888b038416608502e00ac00002a0d04c2c394d89ac47520d8f286da2fe14e89243d217d09003080c200002a0ca812b914649624571fa8e446762df140887839c17c08e02c40b400002a0c4832ce14e89c04862118f246ce312155094c3e218809183140da00002a0bebc2b3946c96c4571ff8e706842dd14908c03be18f09503340d000002a0b8c72c914d09a24772100ef86ba2fa15008e83ce18a094830c0be00002a0b2e32c6948c9984601fe8e8c6902f2149089c39e17808d02ec0ac00002a0acef2c914ec9be47820d8ef46ba2fa15089243d818309102fc0c200002a0a7532a013b89184331f08e146622d3139885838216308802f00ac00002a0a1892b214149364411f78e5c6822e914508a03a817608f82e40ac00002a09bdb2aa93f094e44f1f90e686902e4143889c3b617808782f80ba00002a096202b1141896444f1f98e646722d713f886c37c16c08c82e80ba00002a0904e2b714689844631fe0e9468e2e314788a439216908e830c0c400002a08a812ba14609924661ff0e6c67e2e614388a43a417808502c40ae00002a0849b2c614a89844672048eb468a2e814689003be17e09283100b600002a07ed02b4143c97446420a8ea86942ef14708d039c17208802e00ae00002a078ec2c094b098c4622040e986862e814208cc3a0175091030c0cc00002a0732a2b594489724612038ea86962e8142089c3a416c08a82f00bc00002a06d3e2c694a499246b2038e9868a2e814988d83c018408f03040be00002a0676c2bb145095e4501f38e706762da140884435e16108482bc0c400002a061a92b3945c96e4642040eb86aa2f914a88fc3a217208982e00b000002a05bb62cd94e89b847820f0edc6b42f414888dc3ac17408882c80c200002a055dd2c294d49a047c20d8efc6b62ff15208f43b0185094030c0ce00002a0500e2b2143c9404421f30e186422c9133884036814e07c027409200002a04a512ad93f493c44a1f80e5c6762d813f889039c17908e02f80ce00002a044892b493fc9384511f50e406582d013c88ac3a817f08f82e40b400002a03e902ce95009c44812128f0c6c830115309203dc18e096832c0c200002a038d02ab13f093a4441f20e086582d013b08a439616408502b40aa00002a033022bb947496e4612068ecc6a62ef14708a83a017708f02ec0b600002a02d132cb94d89c847f2138f246dc31215709443d818909183240e000002a027482ba947c9804601fe0e686862df14288bc3a617008c83100b400002a021882b1142495a4511f58e2465a2d213d886037c16208282d00b800002a01be32a914189544501f80e8068c2f114688d43c017b09303080ce00002a016172b5145095e4521fd0ea46ac2f514e09083c617e091830c0be00002a0103e2c394bc9a447420e0f086b6306155892c3bc18408a02e40c000002a00a842b214249564501f50e4865c2ce138886438215d08082a00a200002a004a12c194a49a246b2080ee86b02f814708f43c417b08c030c0c2000029ffee02af94089564551ff0ea06822dd141889c39616e08502e40a8000029ff9172b194349704592008ebc6b230314988dc3be18a097830c0ae000029ff35f2ad93e893a4471f70e3c6782d9139884437015e08302a80a0000029fedaa2a993b89244351ec0dfc6542cd139886839016708602c00b2000029fe7cd2c0149c97a45c2000e746882e714508b43b217b08c02e80b2000029fe1d22d315289ec4912190f346d231015308fc3c817f09283080b2000029fdbf22c314cc9b847720c0ed46c02fb14888b839617008c02cc0c6000029fd5f32d715209ca47d20c0f086c631115709443d218c092830c0c6000029fd0312ad142c95044f1f48e346702e7140888838c16108202a40aa000 else 0x2a2b3f72c814a098e4682028ea46842e3142889c3a217108e82d80b200002a2ae142be948898a46a2058ed46a82f915008e43b617b08602a80ac00002a2a8512b0941c95445c2028e8c6842e714b08cc3aa17108a82e40b200002a2a2702c1148c9a047920e8f0c6ce30f15509283d2192098834c0f200002a29c932bf14a49904602080ef46c630215609403de191095034c0cc00002a296ba2be948096c4572000e9c68e2e9145089c39816508382c00be00002a290fa2b594489764611fa0e6068e2ea14288b839417608d02dc0c400002a28b642a613b893a4411f58e5466e2d813b089439216608502cc0c400002a285802c694c099a45a2030e9c69c2e113f088839416b08e83040ba00002a27f942c594b09a44702010eb46962ed14c08f03cc189097031c0c800002a279b62c3149899a46e20a0f186c630a14e88d43b017b08582f00be00002a273f82af940495c45c2018e9c6902e614a08ec3b817809083040c800002a26e022cd14cc9944622058ef06a82f514908d43aa16e08802d40b800002a268392b7144c9664561f38e446682dc140887c38a16508682940aa00002a262632b9944c96645c1fb0e486602da13d886838617008b02e40ba00002a25c732cf14bc99847320c8ec06a42ff14e89283d217c08882d40b400002a256972be148c9944661fe8e646922da13d889839217308902f80b800002a250c12bd147898e4702008e846a02e414308a839a16e08682d80ba00002a24af92b414209524501f40e706862ee143888c39a16a08802e80a800002a245342b094209504461ee8df064e2c913c088038617408d82f00b600002a23f6d2b5144098845b2010eac69e2ea14508d43ba18108f82d40ba00002a239a12b5944094c44a1ff0eac69a2e714988a439e16708482b40aa00002a233e42b494349684551ff8ebc6aa2fb15208ec3ca18009182fc0cc00002a22e202b4144496a4591fa0e486842e514208a039617708f02f40ac00002a2283f2c094949764591ff0e7c6982f314c08ec3ac16f08a83100cc00002a222222df95789e248b2138f306d830915689383d219309803300ce00002a21c302ca14cc9bc47c2070ed069c2ef14c08bc3aa17808e82e00b400002a216882aa13c89124391ed8e106702df13f087439c16e08783080be00002a210802d6954c9ec4a22200f6c70632315c89483d0183092834c0ce00002a20ab02b8144c9644511f58e4066a2d613d88a43a217108b02a40b400002a204ee2b0145899246f2088e886882e214508b03aa17108782c00b600002a1ff2c2ae13fc93643a1f08e3465a2d613d086837c15808482b80c600002a1f9892a593ac9144391ed8de863a2c2134080c348151081829c0c000002a1f3b22b714249484522008e6c66c2dc13d887438216707f026c0a000002a1edb92d014e89a84782078ec868e2ee14f88c43a417e08e02d80ba00002a1e7cf2ca94dc9aa4722068ed46b02fb14a88f03c018008d03080da00002a1e1dd2c714b098e4732090ed86b230114e89083c018108782d40b200002a1dc092b794509864602020e7c6882fc15189243dc18a09203100c400002a1d6552a713d492042e1e60de461e2bb133082c37015208182a808400002a1d0702c0947c97e4612000e846942ed14a08f03ba17f08e03080be00002a1cab42b5143c96a4511fa8e546762e114688e43d018409703200ca00002a1c4dc2bb14809704591fe8ea46942f214f88f039c17c08d83300c800002a1bf322aa13e89384401f48e386722d613c88d039017108802b80a000002a1b97a2af140094a44c1fc8e5c6862d414008b439a16c08e82f80ca00002a1b3a22c1149098845e1fd8e7c69c2f515009083cc184096834c0d600002a1adbd2c194b49a446c2008e906962f014c88dc39c17008f82fc0b800002a1a7fd2b3942894c4481f28e4464c2cf13c885c37816408c83000c600002a1a21a2c4948898c46f20d0f0c6b62fe15188f83a416d08782b409800002a19c102d915289e448c2140ee06a82fa15109043a417008682c40a000002a196302bf945c9724642018e8c67a2e714808d03ac16c08583180c800002a190642b714409664612008e806862e914988d439616508682a80ae00002a18a802c0948c98446e2080ec46a42fd15109283e618a09903140b800002a184982c014809a04712090ea86902ef14788d83c218809283200da00002a17eb22c314a899446b2068ea46902ec14288d03ae17909383000b400002a178ca2c494b89a847a20a0ebc6a42f314e89243c617c093830c0ae00002a173012bd14889924682060e9067e2de13f88b83aa17208502e00b400002a16d2f2bd947497c45e1fe8e5c6742da141089c39016908a02f80d000002a167422c594d09964702050ec46b02f914988cc3b6189097832c0be00002a161702ba147c98c4622020ea46982ed14708b03b017408b82fc0c000002a15be02a0136890e42e1e70dc862c2ca134882035816508182b40a000002a1561c2b494389584521fe8ea86aa2fe14e88f83c6181093031c0de00002a150382c3148897e45f1ff0e9c68a2e814688d43a817008d82ec0be00002a14a802ad13f494c4461fc8e8867e2d913b884c37615c07f82b40be00002a144b22b7945c9844632040e906762e314488c43a817408c82e00be000))) else (if i < 442 then (if i < 440 then 0x2a429992bc948097a4682048ea06902f814d88f43c817b09002e00be00002a423bf2be946896c4551f60e4067a2e5143889c39017609082fc0c000002a41e0f2a893e094644c1f80e306542cb138886838816708402c80a200002a4183c2ba143c95e44c1f10e0863a2cb136086837a17008b82d40a200002a412712b614609784561fe0e706702d913f887c39016e08702f80c000002a40c942bc14889924632028e606822e8142089c3a016508482c00b000002a406c42bc946c9824662030ed86ae2eb14808c43ae17f09303240bc00002a400f32b9948c9804582040e9c6882e214508b839e17008c83040b400002a3fb2b2bb949098046a2080ec06ae30114e08d43a017a08982c40be00002a3f5632b3145c97e4692048eb069e2f114788b03aa17309002e40b000002a3efb02ad13d493044c1f80e5c6662dd14088c43a416d08882e80ac00002a3e9ea2b5945097045b2020e9c6ae2fa15088f43bc18009283040dc00002a3e4272b1942895845a1fb0e4467c2d6140888c39217708c02b00ac00002a3de222d4952c9de4922168f386c62fb15188e43ac17a08d83280ca00002a3d82d2cb94c09a24732078ee06c230715489243de17f08f830c0d200002a3d2492c394989884662078e9c6882e014788b03a017108e033c0b800002a3cc832b1942095c45e1fe0e5c67a2d4138085837e16008502f40ac00002a3c6aa2bf948897e4602000ea069c2f613d087038616c08882f40b600002a3c0c22bf149899c47620d0f006b030415509243d818509003080c600002a3bac32d415389e249a2208f746d231215b09243da18508e02d00bc00002a3b4d22c914bc9ac47120d8ed86b22f714988c03c217d09082d40b600002a3aef82c0946897045c2040eb46902e414588a438e16408682dc0be00002a3a9002ca14cc9ae48520e0ecc6b42fa15008e03a017708a82d00a800002a3a3302bd947097a4581f88e3c6802e614588b83b017b08b03000ce00002a39d672b314489544471f90e7468e2ed14788c83b417908b02e80be00002a397bc2a413dc9204341ed8e2864a2d313c089438a16b08902ec0ae00002a391b52cd94f09d048020e8f186d230b156094c3c218709583180c200002a38be62bb147c97c45f2020eb86882e214588b438816c07f02ac0b600002a386092c394b099245d1ff0e8468e2e814808a039816d08a82cc0c400002a380252c094a898a4622000e946882e914688b439816e08382b00ae00002a37a362ca94c899a4672020e9869c2f314388e83c418e09703100c400002a374422cd95149de4892158f186ce30515188e03aa17908c02b80b000002a36e892b0942095244c1f38e286662e213d087038216c08802a00b800002a368d32ae93dc93a4431f88e846722e114288a039017008882cc0ae00002a3630d2b4141c95045a1ff0e8069c2e814308dc3b817b09103340be00002a35d482b414149444401ef8dfc6582cf138087c38816508582e40ae00002a357492d114f89c04832118f186b430715088f83d418a08e02e80ba00002a3516f2c214749844632038ea46962f514988e03a817808a02dc0a800002a34ba02bb14549684591ff8e6467a2e314709043d018f09403180bc00002a345b52cd14e89ba47e20b8ed46a42f314608c03b017b09103040c000002a33fd52c094909a24712080eb46b22f614d08fc3ca18209203180d000002a339fa2bc144097e4682000e8468a2e214308cc3b617b08902f00c000002a334162c1148499a4632048e7c6942e814208ac3a017e09182f40b600002a32e562af93f09364371f28e1064c2c313b085c37c16e084029c0aa00002a328832bc145c9764602028eb86ba2fb14c08dc3c418309203080b600002a322c62b5940c95c4592010e9869a2e614688d83a217f09102f40c600002a31cf72b994489664541fd8e9867e2d413c884836c15f07e02980ba00002a317252bc949497c4662020e586882d913a887438016c09083100b800002a311402c0147c98a4581ff8e5c6882dd14708c43a617208882fc0c200002a30b6d2bf945c97646620a8ee06ae2fc14e08e83ba189096033c0cc00002a305742cf94e89ac46e2060eb469e2f714809143d619309703200cc00002a2ffaa2bc946497c4662020e9c69c2e7146089439c17208702c80c200002a2f9b32c914c09b847920f0ef469a2fa152091c3c418009403040c000002a2f3e22bc949498a4692090ebc6bc30e15b89243dc18609283280d600002a2edfd2bf945497645c1fd8e7c69a2f114508c03a017a08e83140b200002a2e8252ba147497045f2008e706662e014708c83a216c08882fc0ae00002a2e29c29913448e04181d80d846242b7132881035a152078828c0aa00002a2dcc92bb947897a4642038e9c6ae2f715409043c218409382ec0b800002a2d72e2a093a09144301eb0e0c6462d013b087839217009002f00ca00002a2d1442cd95149dc4922110ef86be30114e89143d418c09b83340de00002a2cb6d2b8945c9764612000e8c6742de13c885037416b08882bc0be00002a2c5a32b894949964632000e746a42ee145887037c16508402c80b800002a2bfb22c614a899e4722040ec86b02f014b88c83a417208a03100d600002a2b9e02ba94589624531fc0e8467a2d613a087038c16608482c40ac000 else (if i < 441 then 0x2a59e8a2c0147498c4682018e9468c2db13b08a038617408982d40a600002a598b62bb94609824631fe8e9c69e2f514888dc3b418d09603280be00002a592dc2c3949898c4622088ea068a2e114788ac39017b09102fc0b000002a58d182b193ec9264331ed8dec6582cd13a087438816a08603040b800002a587572b7144095443f1f48e3066e2dc13f88a43a617a08b82f80be00002a5816d2c694ac9964682068eac6a62fc14d08e83b8177094032c0be00002a57b872c214c89a64792080ef06a02f214b88e43b617c08e030c0bc00002a575992c694a89a647b2108f086ac2f814788e43a617208c02e00c200002a56fcd2bc14509724511fe8ea869c2e613f088438616c08582d40b400002a569f12c014a49a04702110ed86942f414b08c839616508582c40a600002a5640f2c4949098246e2068eb46a82fc14f091c3da18c09383140b800002a55e462b7143895c45a1fe0ea06a82f815108ec3b417e09303000c200002a558502cc94d09b447c2130f106be302154891c3d018b09383040b200002a5528b2b213fc9624501fb0e946722cf137887438817409003040b400002a54cbb2b3943094a4491fb0e4866c2db14388d03b217e09183200b800002a546e92b6142494e4521f80e5c67c2dc14488b439417908c82f00a800002a5411e2b193f49464451ef8de864a2cd13a086438c17308902cc0a200002a53b542b193f095a4511f38e3466a2db140886438416a08b02fc0c400002a535852b9145497c4612040eb06a82f614988d43b016808b02ec0b800002a52fbc2ba144896444a1f68e1064e2c6134886835615407b82c40b200002a529c62cb94fc9c647f20e0ea06902e614308b43a416a08602b00ac00002a523f42ba145896645d2020e806882ee145889839017908f82f00b400002a51e182be14ac9a247420d0ee46be30015089183c217f08902c80b600002a518562ae940c94e4501f90e7066a2d213e089839e16f08e83280b000002a5126d2c294b09a247320e0ee86d831315c094c3ee18b09403000ce00002a50cc02ab14149544481f60e046462c8133885038416a08e03000c400002a5071c2a893b491c4351ef0e446562cf138885c37c16408602b80b600002a5013a2b714089484451ef0e2065c2d213a887437c15f08702ac0a200002a4fb802a713f49444471fc0e606742db13d888439016f08e02ec0b200002a4f5942cc94c09ae46a2060e786862e113e885438a16a08302e40b200002a4efd82b5144094a44c1f78e546682dd14208a839216908782e80bc00002a4e9d72cf95209d24832110ef46b22f514c89283ca18a09703200c600002a4e4172b2943496a4541fd8e886882f214988d039216b08482c00b600002a4de582b0940894444d1f80e5c67c2e514c08b038216c08382d00c200002a4d88c2b914889884692038e9469c2f514a88d83a417308e83040ce00002a4d2c72b7143c96645a2070ea46a62f714d89203d618b09b83280c400002a4ccd42c594a09a64702098ef86be2fa15489103c417c08982e00a800002a4c747297136c8fc4241e30da061e2bf138085436e16008282c00a600002a4c1772ba947497445a1fe0e746782e014708c03ac17008a82fc0cc00002a4bbba2b294389764672080ea06a02f914988d039c17508a02e40ba00002a4b5f42af941896244a1f60e4c65a2db13e08b039c16a08b02c80c600002a4aff72ce15209c64842120ee46c22fe15009043b817608602c40b600002a4aa392b8945097a4571fb8e7468c2e714488c439816e08082dc0c000002a4a48c2a913f495844f1f98e8c6662d913e086036a15107e02980a200002a49ed02a813dc93e4431f18de86502cf139888038c16708602c40ce00002a498e62ce14b898e47620d0ef86b02eb14a08ac38a17508802bc0b600002a4931b2b6944898646920c8f046cc308154091c3bc17908b02e80b600002a48d3e2be147c9824662048ea068a2ed143089c39a17608b03000b000002a487702bb146c97c4602018e9468a2e514788d83b417108902d40ba00002a481892c714d89c047d2108f106c631215789483c618009182f00c800002a47baf2b594649744642038e8c6962f414788a43a416f08c03040c600002a475f42af141496044a1f40e106582d713f889039216c08882fc0c200002a470102c214b49a047220e0ee46c230415209103c818c09383000ba00002a46a2b2c614ac9a647c2128f106dc30e15909243ce181090032c0ba00002a464402ca94e499c47620c8eec6b02f414f89343d818e091831c0c400002a45e6c2bc946c9704521f70e646582ce13c886c39016b08282c00b600002a4587f2c3148499246f20d0edc6b02f214d88f83c017e08a82f00c400002a452922c7148c98c4652060ea869a2ee14788b83a817a08e83040cc00002a44cc62bc945097e45b2028eb46802ea14488b439017108502b80a800002a446db2c514d89c247f2118eec69e2fc152891c3e819109983280d600002a4410e2b4143c98046e2048ed86b22f814908c03be17908c82ec0b600002a43b4a2b6943095644f1fc0e646682d313f089c38816b08702dc0c400002a435612c314a09a447420c8ef86c830414f89003ca18409083100c600002a42f722cb94d89b848321c0f546dc30915589543da18a08e02ec0b6000 else 0x2a714812b293f495a44d1f90e7466e2df14288b83b617d09083040b400002a70eac2ba147896a4621ff8eb86a22ef14908c83a417408c02cc0b000002a708cf2c494e49ac4762088eb06962fb14b08f43bc17408f82f00d600002a702c32d8952c9ce48a2198f086c02f614708f03ba18008d82ec0c000002a6fccf2ca14b89b847520a8e986882f014808e83b218909083000b200002a6f6ec2c494b89924772100ee86c0300154092c3d017508b82ec0a800002a6f13d2ab13f89464461f00e346682c6137085037817108b02d00bc00002a6eb582c614a09904692090e946782e414788bc3ae17e08b82c409a00002a6e58c2b994609604511f30e346642d613c885836a15708502d80aa00002a6dfa62c4149498c4612000eb467e2e114608d03bc18309182f00ca00002a6d9d12be94849864661fe8e5c67e2db13d086039016608982ec0b000002a6d3f42bb94c099e4662028eb46a42f814b88d03a417309002f00ba00002a6ce0b2c594a49ae4862178f646d830114d88ec3b017108802cc0b800002a6c8522ad14009704561fe8e5c6982ef14608c43b818809382e40ca00002a6c2a32a413a093243f1ef0de86462c5139083c37c16908f82f80b400002a6bcc22c1949c9a047320d0ed86b02fb14f09083de18b09402f40c000002a6b6d12c614f89c447b20d8f046c030114f09003d418e09a03240c400002a6b1042b8142896c4582008e586802e213c886c39017208602980a200002a6ab242c2147097a45d2000e886902f314c88d43aa17508782d00c000002a6a53d2c6149c9824662028e9c69a2e214788f43c217f08f82e80d000002a69f792af13e491c4311f30e3c6682dc140087c39e17908e82f80b600002a6998c2cd94c099446f20a0ef06ca30014f89203d618c09303380c800002a693db2a813e495a4592008e806922e114688ac3a416f08402bc0ba00002a68e122b594349584501fa8e846982f714f09083c018309683240d600002a6884e2ae141895044c1fb0e746862ea14c08e43c617509003180d000002a6828b2b1943c9624511fb0e646862e6140888038c17708e83380c600002a67ce22aa93e493a43e1f38e0c6542d113c889039016808902dc0c200002a677182b714309604521f68e5066c2de14388b438616708982dc0c400002a671572b0940495a4501f70e586882ed14608a438416d08882c80be00002a66b612c814f89b647b20e8f006a02f614d88e03b217708b02c40ac00002a6658e2bd949499e4682058e846902e614488c439417508e82dc0b800002a65fa42cb14f09b848020b8ed86b830114f09043d218a09083340dc00002a659db2b914609684652020e9c6902ef14a08c43a417f092830c0c400002a6540f2b8144896c4501f98e446822f414d890c3c217d08e83140c200002a64e1a2ce94dc99e47520a8ee86b62ef14588ac39217309002e80b600002a6484d2b6145498645c1ff0e9c6ae2fa14d88d43b817108902d80b200002a642662c094c49b04832158f106bc2ff14b08dc3c618009183200c000002a63c8d2ba948c98246b20a8eb468e2f815008f83c018809103000c200002a636af2ba146496845d1fb8e546702de13b085c38017008b82cc0a800002a6311d2a0139c9144321e68de46402bd1348824364160083028009200002a62b612b114109464511f60e0c6462c3133885c36416107f827c0a800002a625712c394a498c4672080ebc69a2ec14188c03a217208682e80ba00002a61f602d795349ce4872170f606e8313157093c3de19709783440de00002a619b22a613d893444b1f20e146662d113a885839216508682ec0b800002a6140f2a513b48f24241e20dbc6282bc132084036415608482b00ac00002a60e5e2aa93e895244c1f80e6465a2e213f088838817508d02f40c000002a608592d6150c9d249a21d8f646fc31815e89603f619709503180d000002a6024b2d5152c9ce4932198f0c6da30b15609343de18908c82e40b800002a5fc832b7145497e45e1fd0e7c6742e0144889039816b08a83100be00002a5f69a2c514cc9a247c2098ee06c430014d88f43b217108a82e40b200002a5f0ab2cb94b499846d2078ec86ba2f914d88d43b617709103140b600002a5eac82c814a49a647c20e8f186ce30e15409203ca18509103180d600002a5e4f72bc94ac9904642030e986a62f214908b03a617608a82bc0bc00002a5defd2cc14f89a24672098ebc6a62f514d091c3ce17f091830c0d000002a5d9292c094949a84702080eb068e2f414b08ec3a417c09403180ce00002a5d32b2cb94c89a847120b0ee86c630215189203d218f09883300ca00002a5cd6c2b0944895e4541fd8e986982f614208a83a817f09203180cc00002a5c7a12b2146497645d2000e4c6702da14488a839c17508982c80cc00002a5c1c12bd148098445f1fd0ea06a02f514908cc39617908582b40a200002a5bc0a2b1141496a4612008e686922ef14508a439a16f08482d00a600002a5b6062ce95149d44872148f486dc306154893c3e018f09482ec0a800002a5b03a2b314049524421f58e2864e2d313a08a038016608082cc0a200002a5aa3f2c894b499c46f2078ed46ae2fb14f89143d218f09383240bc00002a5a4662ba942c9664622020ea869e2fa14b09103c617a08d83100ba000)) else (if i < 444 then (if i < 443 then 0x2a889cc2b614609704591fe8e806822df13c087038816908582d80b400002a883de2c414a098446e2080e846942f314b88cc3b017c08f82e80ac00002a87e232ab93d492a42f1e90de46342c4136884038416308382bc0b200002a878462c014989a047a20c8f286da2f414d08d03b017c08f831c0c800002a8727c2b5943096044d1fa8e886862e2143889838e16308882dc0c600002a86c832c894b09a647520e8efc6b62fc14c88ec3b818008982f40ba00002a866c72b193ec94e4531f70e7867c2db14608983a216808102c80b600002a860f82b9945895043f1ec8e046502c8137883836615d08102980a600002a85afc2ca94d09b047f20a8ecc6a22f714888dc3b618108d82d40ca00002a8552e2b8144c9744571fa8e9067c2e514508b039e17c08e02f80c200002a84f722b514209564591fe0e7467a2e4141088039816d08882cc0b600002a8499e2bf949097844b1f68e8066a2dd141888838416808682c40aa00002a843c42bf149c99a46a20c0f1c6c42fd150092c3d818808e030c0ca00002a83dfe2ae13f89364331ec8e186442ca139083c37815f08202c40a600002a838222be14549664561ff0eac6902e4143889439e17308b82cc0ba00002a832382c0948c99845e1fb0e8c69e2f014808dc3c818809383140cc00002a82c572c214b899046f2088ec46b02fb15288fc3ba18409182f40ae00002a826ad2ab94409544501fb8e846902ed14c88c03a216708482bc0a800002a820e32ba944c94e44b1fa8e786922f014d88f43c018008e82c80a600002a81aef2c994a898a4622050ec069a2f014508d03ae17c08c82ec0ca00002a815012c814c09924602038eac6842ea14788d83ba17a092830c0d400002a80f252c2149899446a2020e4c69a2ea14b88e039017808e02fc0aa00002a8094a2be146496a4581fd8e7c6862e6141089c39616908582cc0c400002a803992aa13c893a4451f50e7c6782d413d886838216608402b00aa00002a7fdbe2c014909804642070ed46b42f314c08e83bc17f08e82d40c000002a7f7e02c314cc9ac4682038e946962e814788b83a217208d02d80aa00002a7f2252a813e49304401f68e5c6722de14388b43a617909303180ba00002a7ec152d615249da48c2138f146ac2fc14f090c3b017a08c02fc0be00002a7e64c2af93f895c45d2020e846942ef14408a03a217308a83040c200002a7e07c2b8142094e44f1f88e5867e2e714988c03a817008903000ba00002a7da9c2c994e49c848d2108ee06bc302157893c3c817c08f82dc0b200002a7d4cd2b8145c97645b1ff0e806842eb14108c43a017308b82f00b200002a7cee32c394a097a4652078ebc6b030114f88e83ac17b08d03140d800002a7c9422a293b49224301f30e2c6462d913d888c39016508602980b000002a7c3432ca94f09d448e21d0f486de30615309183f218b094833c0ce00002a7bd652c1948899e46f2098ef06d030515008ec3c618e09603380de00002a7b7992b6941c9624531fc8eb46a02f214888c83b018109082f00ba00002a7b1bd2bf94a89a44762100f246d630515209503e018f096834c0e400002a7ac072b013dc92e4371ed0e006462bc131882836616208702b80ac00002a7a6252c294989844642030e8469a2f114988c43b216f08a82e80c400002a7a01c2d395409ee49a21a0f4c6da30415409083c417908902e00b600002a79a3c2c414b098845a2030ea86a42e714308a839816708202cc0b200002a7945f2bb14809864652028e986a82f414a09043c218b095833c0dc00002a78e5d2d495249d248d2130f286c82fb14c88dc3b417a08c82fc0bc00002a788562cc94e49cc48a2190f246d430c15409303d819409103280c800002a782ad2aa13e494a43b1ee8e2865c2dd13d889839c17408c02b40ae00002a77cfb2a813c89364451ee8e4065a2d4139885835e16308502c40b000002a777362b794209484541fc0e6c68a2ed14608cc3ba17008702e00aa00002a771752ae940c9504561f68e846742d513a087837616508c82dc0c200002a76ba42c0945c97845d1fe0e586842e314308a83a217108c03180ca00002a765d52be946498046820a0ef46d430314f09003be17808f030c0cc00002a75fff2bf946896645c1fe0ea868a2e614808e03b017f08f82e00ae00002a75a062cd14bc99a4671ff0e846862ec14908c03a417108c82fc0be00002a7544e2af140495044b1ef0e3866a2d813c887437c17008f03140ae00002a74e782b7945895845b1f80e5466a2e214108d43b417e09003180b800002a748a82be146c9744511fe8e986842e614488d43ba18509302fc0cc00002a742b12cf15309d64872118f206ce308159892c3c218609583200d400002a73cf32b1942494a44a1f88e586842e814488a436c16508502ac09400002a737182b7942c9764632028e846962f814988d43a017e09603280c800002a731532b5145096a4572008e646722df14708ac39616e08c02e00ae00002a72b822b8144096a44b1f70dfc64e2d513b086c38415f08382f00b800002a725d22a993b891243c1f00e3466c2cb137886039217708d82f80ca00002a71ffd2c2948c97c4632010ea46942f614908f03ce18a09583080d000002a71a3b2b314449884682088eec6bc2f614b08c43a817c08a03040c0000 else 0x2a9fe3a2d1153c9de48e2120f206c42ff14b88e43c217a08d02d80ae00002a9f8662bc145c9704641fe0e8468e2eb14788bc3ac17808c02e00d000002a9f2712ca94e89cc4872110ed869c2ee14888d83b217008c03180c200002a9ec932bf14949b047a20a8ed06b02ea14e09143c817c08e830c0be00002a9e6bd2bd147096a4531fc8eb06aa2f014708bc39617b08e82ec0be00002a9e0e52b714749804642068edc6aa2fa14c08e839e17b08b830c0ca00002a9db192ba145898245b2038ed46b430a14f891c3c618809203280d400002a9d50b2d815389ea48e2130f346d230615609183ce17808f03040c600002a9cf3c2b7141096245f1fe0e5867c2de14689003c418509082fc0dc00002a9c9652c214749664592010e706802e314488c839416c08602dc0b800002a9c3a02b6943895644d1fc8e886902f014988c838e16808902cc0b800002a9bdef2ab13c092a43a1f28e0c63a2c7137084837416108682c00a600002a9b7f82cf15449d84832140f286d430e15a89543f019509d83500e400002a9b23a2b3942095e4561fc0e6468c2eb13f887c37416708603040c400002a9ac7c2b1942095643f1f08dfc6522da13e087c38c16708482c40c200002a9a69f2c3149898446e2078ebc6902ec14688a438e16c09182e009e00002a9a10d29b938c90e4291e08dd46342c513a085437c16a08782ec0be00002a99b272c714cc9bc47e2120efc6c430815008e43c218309202fc0d400002a995682b6947897c46920c8ea46ae2fe14d08fc3b217d08f031c0c600002a98fa72b3142c95a4481fb8e586742db13f889839c16f08882c80b400002a989fc2a693f09444491f38e006462c6132081036415408402a40a200002a9842f2b914589864602028e846902f014988d439817408b82dc0c400002a97e302cb14b09b647d20e0f086d430a15589203ca17c08e82f40ba00002a9783b2cd15109d84892118f346f031615389343f418b09183100b000002a972822ab93d493c4491fa8e6066c2d913a884c37015a08282b40ae00002a96c8f2c914a498847420a8ecc6ac2f114b08f43b417e09002ec0c400002a966c72b2943895444f1f90e406642d113f88bc3a218609083140be00002a960ef2c014a099046e2078ec46a62e914388b43a617c08d82ec0e200002a95b012c614b098846820b8ed86902f314d08d039c17708d830c0c200002a955512ab941495444b1f90e586722e3141888c39617408d02f00be00002a94f722be949498c4792098ed06a82e514808c03ac17808c02f40b200002a9497a2ca14e89c247e2160f486e831515509303dc18809203140b800002a943c02ad13d49484491f60e606722dd14108bc39616c08702b40a600002a93dd02c614ec9a846f2098ed46942eb142889838016c08802e40cc00002a9380b2b1945096845c1fd8e806882e714708d03ce17a09082f80c200002a931e92d915a0a064ab2248fb070a31f15d09203ca18708e82e40b200002a92c142bc945096c44e1fa8e906922e514408b03a617608482b00a000002a9264f2b814509704531f80e486822ea14788e83d418208e82e40ac00002a920812b8145c9684532000e746982e714408c8398178091830c0c000002a91abc2b8144c9524511fc0e906802e713b087c38217108c82f80b800002a914eb2b514049524521f80e4c6622db13f88903a618a09803340ba00002a90f132c094bc9984772080ecc6a82fc15409183b817d08a02f40b200002a9093d2c414b499446e2068ed06ba2f814b88b438816508782e80c200002a9036d2bc14709944652018ea86a62f1149888839c16a08982f40b200002a8fd9d2b714309564511f88e7c68e2f014c88e43ba17a08c82f00b400002a8f79d2d195249e049821c8f5c6cc307159894c3e018e08c02f40b800002a8f1ec2b1942c93443e1f40e306742e514208ac39a17208e82dc0ac00002a8ec1a2bd148498c4682068e906a02f214d88dc3c617a08e82f80b600002a8e63f2be14709884661fb8e586902e514c89043cc17d09203280d200002a8e07c2b9140896045a2010e906822dd14388b039c17108b02d40b000002a8dab92b013d093444d1f20e5c67a2dc139887839017208702e00b000002a8d4f02bc94689804602000e806842e414788e43a016e08b83180c400002a8cf2d2b4142894e4421f58e5867a2e013f089c38e16d08902bc0a800002a8c9742af14109524461f60e4866c2e814908d83c018409283040b600002a8c3ae2ba945c97445d2040e986a22e8143888c39416c08802ec0b200002a8bdb52ce150c9c44862108f186c82ff14d88b03a217008e02dc0aa00002a8b7ed2ae940494043f1f40e2c6522ce13d089838416c08602c00ae00002a8b22d2b8944c96c44d1f88e586662e014388a439c17b08f82fc0c600002a8ac802a813dc9464401f50e306642e313c88a03a817308602d40b600002a8a6ce2b0145096445f1fd0e7868a2e0140089438816908282c80a400002a8a0ed2bc146c9a04772088eb067a2e113f888038c16b08c82e00bc00002a89b162bc946c97a4622020e9c6882ec14888b03a417308682dc0ae00002a895502aa13d092e43c1f08e146522da14288d439e179088029c0b600002a88f992ac93ec9424341ef8e0463c2bb133883036816407e02c00b0000) else (if i < 445 then 0x2ab741c2a3137891a42c1ea0de06562c5135084038016708c03100c600002ab6e132d215389d04932128f486d830c15a09283c618808f02f40b800002ab680c2d115089a84752078ea469c2e8141888039617a09103080c200002ab621d2cb14c49b248020f8f406de30815589243d617a08a82e40a600002ab5c262ce95089e448d2168f1c6c8301157095c3fe1a209983440d200002ab564f2c0946496e45f2018e6c67c2de14088a838c17108882bc0ac00002ab50b129d13588f242a1e90df464a2c4132083836e16108982bc0ac00002ab4abb2ca14ac9a447820a0ebc6b430715108f83ba17b09203000c200002ab44e02c414a498c47320c0ef06b82fd15009103ce18b09503540d600002ab3f032c2148898846b20d0ef06ca30815409043b016e08682d00b800002ab39122c814d09b447a2108f286bc30315089143ce18b09983600dc00002ab335d2ad941c94c4451f78e686722dc144089c39616808902d80b200002ab2d962b8945c9864531fc8e706822e5143889838a17008302d40c600002ab27bc2ba946497c4591fd8e406682d7144889839016d08682ec0b600002ab21bf2d014e09b44862160f146c630814c88d83cc18609283180c000002ab1c002ad940494c4571fb0e8c6882e114708ec3b417608982e00c200002ab16252bd945c97845f2020eb46a22fb14e08fc3ca18309182fc0cc00002ab10762b0140093a43a1f18e3467c2e4141888039816a08a02c40a600002ab0a8c2c514a499c4772090ec46bc2f714488c039e17108882cc0c400002ab04702dc15649ee49821d0f686ee31b16189403d018809303340ca00002aafeed29913909144301ed0de06482ca137085037816b08782cc0ba00002aaf90e2b394189504551f78e646702eb147889838817208c03000be00002aaf34e2af940c94c4521fb8e9869c2e5146089438e16d08a03040c600002aaed432d995689f049221a0f3c6d630a15f09143d019309282f80c000002aae78a2b113ec94a44c1fd8e6c6782e0144889038a16b08982d00ac00002aae1be2ba946498a46d2090ea46902e814588cc39217208b030c0be00002aadbeb2bc145896e4541fd0e986982f714f08fc3a617a08b02d00be00002aad60f2c0949099246c2090ed06b02f314b88c83a816e08902f00d200002aad0532b1140893e44c1f68e546782d414188c03ae17808f83080c600002aacaa62aa140093844f1f60e486582c8138084c37216308502c80aa00002aac4c62c594a09804692060ea069a2fd151090c3ba17709102f80ac00002aabef62b8947097845a1fa0e7469a2f014e08b83ac18208f82f80c000002aab8fe2cf15049be47220a0ec46a22ea14808e03b417808e02ec0ae00002aab3422ac141895244b1f60e286682d813a084437016408982c40ca00002aaad7b2b6145c96a45d2070ea86a430315089283d418b09603200ca00002aaa7952c4147097845e1fe8e846802e9140886437e15e08282c00aa00002aaa1b72c0949898646f2038ea868a2e4142087838a17608d03080b800002aa9c002b2943897c4611fc8e686842ea14788cc3b417408d02d40be00002aa960a2c494a498c4672078ea46882e5140088039616b08302a809600002aa908c29513709184401f30e5466e2d814008a83a817a09383100be00002aa8abf2bd14449544592010e4c6782ce13a887c37616d09003180be00002aa84e22bc14449524541f88e5c66e2da14188a438e16b08902f40c600002aa7f202b113f09444471fa0e6466a2d214508a43a417008882d009c00002aa794a2c0147495a4561fa0e4465e2d413e888439817a09203040b000002aa73502cd94b899e4782088eb86862ea14a08a03b218209683140ba00002aa6d6b2c2949899646c20a0ea06962f114988dc3b216e08d82e00bc00002aa67982bc94749664652078ec06922e514808ec3ae18009283180c000002aa61d32b994a49964682090ec86b42f9152891c3a817d08e02e80c600002aa5c092b5944496e45d1f90e586862eb14388b03be17c08d83000c400002aa56312bd948c97c46e2038e906962fa14b88c83a816d08902f00c400002aa50642b6945c9744652008e986862dd141888438e17208d82e00bc00002aa4a692cc14d498c4642000e7868e2ee14908c43b217d08b82cc0ba00002aa44642d795549de4952170f606e631615b89503ea19909603140ce00002aa3e9d2b7144c98045b2068ee86a42f214b88f43ac17908d02ec0ca00002aa38d42bb14489724662028ea46842ea14688a438a16c08c03040b400002aa33052ba947098c47120b0ee06a82f414d88f83b818608b82e00bc00002aa2d232c614cc9ac4772098ef06b22f6153892c3c818409282fc0be00002aa27652b1140c9584521ff0e7c6982f914c88dc3aa17008b02f40cc00002aa21952bb14689764431f70e0c6582cf13b889c38a16508a02e40b600002aa1ba72c914c499c4662010e8069e2ee14909103de18a09603200cc00002aa15cb2bd947c98445b1ff0e7c6722e714588bc3aa17c08f02e80c000002aa0fda2c594a49884581ff8e986a22ea14588bc3b617908c02f00b600002aa09fd2bf145098245f2018e7467e2e714688a039217008402d80b200002aa04372b6145497e4662088ec068e2f114408b43b017408a03040d0000 else 0x2ab8b4400000000000000000000000000000000000000000003080de00002ab85782b294509564552000e9c6922eb146088838415c08802c00c000002ab7f962c0146897a4602020e9468a2f814888c039a17109102f00b400002ab79c52b6143c9784612050ecc6aa2f014788d038e17108382d40b2000)))))))))

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



private theorem b442600 : covered 442600 442711 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442711 : covered 442711 442823 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442823 : covered 442823 442934 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442934 : covered 442934 443045 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443045 : covered 443045 443156 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443156 : covered 443156 443268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443268 : covered 443268 443379 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443379 : covered 443379 443490 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443490 : covered 443490 443601 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443601 : covered 443601 443713 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443713 : covered 443713 443824 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443824 : covered 443824 443935 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b443935 : covered 443935 444046 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444046 : covered 444046 444158 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444158 : covered 444158 444269 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444269 : covered 444269 444380 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444380 : covered 444380 444491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444491 : covered 444491 444603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444603 : covered 444603 444714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444714 : covered 444714 444825 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444825 : covered 444825 444936 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b444936 : covered 444936 445048 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445048 : covered 445048 445159 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445159 : covered 445159 445270 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445270 : covered 445270 445381 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445381 : covered 445381 445493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445493 : covered 445493 445604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445604 : covered 445604 445715 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445715 : covered 445715 445826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445826 : covered 445826 445938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b445938 : covered 445938 446049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446049 : covered 446049 446160 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446160 : covered 446160 446271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446271 : covered 446271 446383 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446383 : covered 446383 446494 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446494 : covered 446494 446605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446605 : covered 446605 446716 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446716 : covered 446716 446828 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446828 : covered 446828 446939 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b446939 : covered 446939 447050 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447050 : covered 447050 447161 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447161 : covered 447161 447273 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447273 : covered 447273 447384 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447384 : covered 447384 447495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447495 : covered 447495 447606 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447606 : covered 447606 447718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447718 : covered 447718 447829 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447829 : covered 447829 447940 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b447940 : covered 447940 448051 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448051 : covered 448051 448163 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448163 : covered 448163 448274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448274 : covered 448274 448386 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448386 : covered 448386 448497 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448497 : covered 448497 448609 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448609 : covered 448609 448720 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448720 : covered 448720 448831 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448831 : covered 448831 448942 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b448942 : covered 448942 449054 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449054 : covered 449054 449165 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449165 : covered 449165 449276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449276 : covered 449276 449387 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449387 : covered 449387 449499 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449499 : covered 449499 449610 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449610 : covered 449610 449721 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449721 : covered 449721 449832 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449832 : covered 449832 449944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b449944 : covered 449944 450055 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450055 : covered 450055 450166 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450166 : covered 450166 450277 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450277 : covered 450277 450389 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450389 : covered 450389 450500 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450500 : covered 450500 450611 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450611 : covered 450611 450722 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450722 : covered 450722 450834 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450834 : covered 450834 450945 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b450945 : covered 450945 451056 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451056 : covered 451056 451167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451167 : covered 451167 451279 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451279 : covered 451279 451390 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451390 : covered 451390 451501 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451501 : covered 451501 451612 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451612 : covered 451612 451724 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451724 : covered 451724 451835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451835 : covered 451835 451946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b451946 : covered 451946 452057 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452057 : covered 452057 452169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452169 : covered 452169 452280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452280 : covered 452280 452391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452391 : covered 452391 452502 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452502 : covered 452502 452614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452614 : covered 452614 452725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452725 : covered 452725 452836 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452836 : covered 452836 452947 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b452947 : covered 452947 453059 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453059 : covered 453059 453170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453170 : covered 453170 453281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453281 : covered 453281 453392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453392 : covered 453392 453504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453504 : covered 453504 453615 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453615 : covered 453615 453726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453726 : covered 453726 453837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453837 : covered 453837 453949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b453949 : covered 453949 454060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454060 : covered 454060 454171 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454171 : covered 454171 454282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454282 : covered 454282 454394 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454394 : covered 454394 454505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454505 : covered 454505 454616 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454616 : covered 454616 454727 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454727 : covered 454727 454839 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454839 : covered 454839 454950 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b454950 : covered 454950 455061 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b455061 : covered 455061 455172 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b455172 : covered 455172 455284 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b455284 : covered 455284 455395 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b455395 : covered 455395 455507 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b455507 : covered 455507 455618 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b455618 : covered 455618 455730 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 442600 455730 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b442600 (joinCoverage b442711 b442823)) (joinCoverage (joinCoverage b442934 b443045) (joinCoverage b443156 b443268))) (joinCoverage (joinCoverage b443379 (joinCoverage b443490 b443601)) (joinCoverage (joinCoverage b443713 b443824) (joinCoverage b443935 b444046)))) (joinCoverage (joinCoverage (joinCoverage b444158 (joinCoverage b444269 b444380)) (joinCoverage (joinCoverage b444491 b444603) (joinCoverage b444714 b444825))) (joinCoverage (joinCoverage (joinCoverage b444936 b445048) (joinCoverage b445159 b445270)) (joinCoverage (joinCoverage b445381 b445493) (joinCoverage b445604 b445715))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b445826 (joinCoverage b445938 b446049)) (joinCoverage (joinCoverage b446160 b446271) (joinCoverage b446383 b446494))) (joinCoverage (joinCoverage (joinCoverage b446605 b446716) (joinCoverage b446828 b446939)) (joinCoverage (joinCoverage b447050 b447161) (joinCoverage b447273 b447384)))) (joinCoverage (joinCoverage (joinCoverage b447495 (joinCoverage b447606 b447718)) (joinCoverage (joinCoverage b447829 b447940) (joinCoverage b448051 b448163))) (joinCoverage (joinCoverage (joinCoverage b448274 b448386) (joinCoverage b448497 b448609)) (joinCoverage (joinCoverage b448720 b448831) (joinCoverage b448942 b449054)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b449165 (joinCoverage b449276 b449387)) (joinCoverage (joinCoverage b449499 b449610) (joinCoverage b449721 b449832))) (joinCoverage (joinCoverage b449944 (joinCoverage b450055 b450166)) (joinCoverage (joinCoverage b450277 b450389) (joinCoverage b450500 b450611)))) (joinCoverage (joinCoverage (joinCoverage b450722 (joinCoverage b450834 b450945)) (joinCoverage (joinCoverage b451056 b451167) (joinCoverage b451279 b451390))) (joinCoverage (joinCoverage (joinCoverage b451501 b451612) (joinCoverage b451724 b451835)) (joinCoverage (joinCoverage b451946 b452057) (joinCoverage b452169 b452280))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b452391 (joinCoverage b452502 b452614)) (joinCoverage (joinCoverage b452725 b452836) (joinCoverage b452947 b453059))) (joinCoverage (joinCoverage (joinCoverage b453170 b453281) (joinCoverage b453392 b453504)) (joinCoverage (joinCoverage b453615 b453726) (joinCoverage b453837 b453949)))) (joinCoverage (joinCoverage (joinCoverage b454060 (joinCoverage b454171 b454282)) (joinCoverage (joinCoverage b454394 b454505) (joinCoverage b454616 b454727))) (joinCoverage (joinCoverage (joinCoverage b454839 b454950) (joinCoverage b455061 b455172)) (joinCoverage (joinCoverage b455284 b455395) (joinCoverage b455507 b455618)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 442600 ≤ index 850000000/512 := by decide +kernel
private theorem starting_value : fast 850000000=43581966 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 850000000=43581966) (n : ℕ) (low : 850000000≤n) (bound : n≤875000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=850000000
    · rw [first,anchor]
      exact starting_value
    · have past : 850000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤875000000 by omega)
        have within : index n / 512 < 455730 := by omega
        have lower : index 850000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤875000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ850000000To875000000
