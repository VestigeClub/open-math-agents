import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ650000000To675000000

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




private def radical : ℕ := 0x3fb16abc56ab2620c381a34eda42ee722fa4a6e37ea24b2b62916cda1f76c190076544e34b33f25a8177c6153352655365470ef755e29335a746ae89b57e98df31e2569ccdad951c6ac98cb0243e382486cbffc2abf9e8b213126630c18a6247f1c66de82087c057e6ce47ff6111626f5952cc083869f1d146a490371098560e74cb9a9d09ba92373ec3a6d324d2391bcf35262bc2a897fdc00830d65ddb5ff13ebea9fd6325f84b2bb45a2de7f224d50bbe1b35657147dc65f5564768e5cdbacaf8cdd0b9e134d0d4dabc16c9bdacdeb379e679643f10cccbe408ea6e22d029e10234262acc96198877cb45b3edbce03ba89066bf9bc0eb170df020da9a52d5444ee22c4a303bd2b1556f350abf3cba41ad1563b85c80782eb265b26bbebfa5e0fd6f16bf36074d13434307b931773a6e75bb191967f61c0333b26e53f95dcbbb3476b27a95185d0f5baebb1e3ebd2c1321a4e0b3fdef6a2349772c8f262d4e69dde3c444af393c9b128a92fdd2f079d431e5b792a5e7db431a38a09f3c89360f8640871fd72855c490a4576b7780877f38afa3e771aa69cf29706fee1df85e9be97aec8e931faf1273bf437a631fa320a721af089d5286da51e8e80ebd108614d33a04c732514427d13cb70b39543e851999742d4b7a1e2f2d54ea686ac086a288241d6cac9bf93ae61813af591d82192c2ade0f8086364387e3fd0e7acc5337c987db59f291c18f0af941b4bdfc2ee168f20b6914e78b365aa18c2b669d3543fc57d704cf5c547fe7b0129618228991eeb074acb8c0fe905ba37fd8401fa9091b69d07c5f268a0d75c6725b662eb88d1579ec019de507d2cdbd0816beb598bc69771ed967b6d6f4cc4cda49278051f5b8f3949e1bc88eb43c7d99bbd16ca1c68a7fce4944bf77b4e41bfafdbfbb42e83328d7b52b7721df4ee0d26403a16a88d2b5cfbafe611aeb61bdac066598c4bcc28b79f4989a2757fbb0a7db295ebc3fdfc3931123d4753bb6468f9f4ef57f2be86aacaebe2e9f45afa0b3c19728bb7ae7c472b931eaaad4cde8a2ed46507dc8cf193e732d78e9299c0300703cd520bd092684e3c8460889557a69131ab2f1dd712a47bf8a5eb1da9960c51573ecc4f7d70730a494dc219893efbada8df8f9cbb721bed1d57010ea87a76a817945afefe6765719adc0119f41e7141d4b160d92502dc5cc3741b3efaa69eb20209a42fb56bd8207a6674b930af064b997498d8dbfac9079fa42069dc4ce4d3efa8dea1dfee3666080b8e46a6ba9abe9f1feccb80be5f92f2ea3e3c83328c3ca3434192c4ffc428fcf3888782255a60e30e69b8f4545e40d7eae7dade30f023f794de0dd70397bae7cf1f312ab10cf6479c28a1eb492e49ed1046beb0339605d02410953d85d8e305b6bd0a4daf3cb7c1d5086e706f332b2be58d3b1f30468c5b6f6c0b42a754eae6564e612ccd4c51c9a86497a7186092bd47b670a48d0dfe20b3601dc6540537b77e2dcd6047b2646ade511984d1ed119323bc31128a56bdbec4f17fffbb20f3ea07d599d72b11b48c86722eb5f52b506e5598bc443aa8d4375696833d003e9adffb0a015a37d799ec77e07894a8545d0339ece9546e0eea6a0213980af351c53d4a6a4c70fffd1f87be8251fd6da4bfaa83f4b454dff04961ccb7ec491a27253aac8a49f0fa25b52c159815c2df5a5261cedadda6cecd69c0b8cc4ca57fdee26ed14c76288f1db7e6e693ad3d5c8f7da3b0e4e02488a9461d6b191c84e03a5298145846f5f30eb3467901b9a7e3f559bcde047918b28a988ae91fdfa956416f7ac33fadc252592b3ca22e48e1cade410c8de8fd36dc7bd0962a08122b71a94c693c582a9243775afb145db5c8efc230f39763b9d2111f3f369f9da5463d4a20303c1aab1a04d1491a13a621b4f40b541222ad5ff21ff88a4ec3c2112a7d19622e0a983d8885ced8e6e097b69d92a3da831f10bb52f2cb6e822832d0531821332b3e608f338baf069e3389ab7899121d601be506b29f3fcc8bc0980601e67fea224a4f92dce6f016e122a9acb68080f5a268e446329645355a067b681772011fe591ad646d701839e86258e6d9be8cb5e9f3408a261b42d346e48cfd32a1ac9b0da2cc7269ace5065877502ff2095553422f7198ef167cbb0d83bbe73bb3c65b56bc938946fa14b18a1d0e7ec07fb6adf1cf61105edaae8473986bf0229c89ad31bb2963407586ad780af60744419bb62061431832e3e2b94f37e821a74d2ee0bd518ce5ae65404350bca4cd510633f646caddc1e22b0df6d26ff5584d028b35cae69e71503ba708523090c21465dcbcb7a9a831e05165ee905ad51fd664797c7707b7988467607d9de5e2a5a8cd9c84dd0698ef3b103113cd4a54bc7d441eabfc29eecd5d8c451ef8037ef3bf2d4dc0fbf191dfe6da9f6c69f1e2fcd05e2f38baecd455d93691e984f706da32fe14e579e550f4ff7a3d0d134107a3c337ec9d4b9cc5c980b6149f540a80b61e09b308405fad53e04508996fcfdca2888d061734a4a70dfffc113604e8f0b97a3264a6cddb2c0844f836ec2e37d7049b6a2d05f1a40d1af5583fd959063b70d0bb386b6e41ec92923da4011b7d234b73e85886bf3abde24c483fe8d2a20ab7738f9a50768a709746c4cb23a57a6387f9ad7784a88bfc03598537f9dd0948461b566286ad39b83d5c4f361b59b58c7c9d496d0a3113ef681a16c6a6ea23360cbfb3c298ccefa898e37aa099e2c9c403ce33d78a0f4e7f2bb8433e596582d6c7a30e38c7e7d7132b93352db5bc9de5b1bfc1ed0a057e82765d8175902f3dee754a6cc1c8ebb0e04d965d47623895aa6fa03dfa496008cad6166a4b89791ee0e5aacc0505c1c7b60bebcb4a83025b19822149ba60b70f90dd6116f48da7b53c1db12499dbab338d5eb9f03c898ffe36f1ec6febe3f64306d344329c147fa5f9bed2f2023c06555275037d329758478272492895779ac2dcbaf80b39c5ca889b1494538cf2e1f9fc8096e9c58cd5ce8e7776f662081331688ce637f6db55b1635b0cefc186033e6d340d3fa8f20ed04a4e185e6b1454ce5005602d2f07dfdc70ae60e1dbb91e0115b600482246faa83736e34ee8103505856f41ccfaef412dfe4324670535cc27ddf4412bdfaed8721d7f033d7c623e83c0ead56fbea993dfbdfe6faf80b8af9fae1983f443bacda2e03ab373cfdf867d8027bd47bc457a2bc9522b1ba7abc493f8ca5f59afdc3adfde84499fcce4e95fc0f2cc6586a3caf614ad313cda419fcdefd9b02fb414c0d37aafb68d0999dcb434d9e32f24b891e535aba6cb01a5e2178ba1355bef49ec21c418778dd324aa07c2467964c5d5323fecbec1b4525c9842140f723450165fdcb934eacefcaae5fadcbcc18c8764eacc96d0178829bedf9414419621733f39e3b292f8a8ad3f4adb2f4aa597657610cb534ff9c38418749d787e2a2c515ffd11c33f977ae6df7fb7542736bc21ab579180e8caca710f5fdfd9b0ee707edc4a418ce90c34c758318b58a411563ffcea0d836051a83fab907ce1a6c62eb1f2e4423e18f49c5bca8d9752ffbbd5d647a6e3f117ada24a5b99ded28596c8b9fbb7b66b81511c104ed10ee7f1e695b97d9a37cc735dde1e4cf196c5aa26f5968d5488ba8668a761a38b4c498fad6ad7b9fca65de979f08daea4fdc7ff1f87c97a4255e5e5acd773bd121cf1580bc54061418fe937df799bbff3e122b9ccce30221dfea5c8ff60a8d11206f56240ce720bf3f73bec9fc0bf463b44c906128c3fe9d5bcd61e26367c4530bfce23d5505d91afebdbf39a3590c8c282d246d6e246481345484521cec0630c74804c23151e7a370a1f2bcaa93b916ae8c123548d7ce0a204eec3922e39c7d0ef50bd61179d1a11a359de2f42c2c4ca961aad73f557da018e1b5529dc2ebcd1eb26ddd380824ba1aae41e0afdf3bab086301b39bce068139bd0bc279e12ef3aee60796b139aaabb567fd522d8db171748626bd436988935998b5fa71c8d02f5cd0947d948eff36ac5772af5c0ab6126aab6874c63e73ac2a58a7d77aae9cd06c79b79daab1ee3c4cd5cd33ab1a45654262ae88a803009a072134c35f697057505afeda5b9d1d6d1186908a767148e692eaffd97f958d5c927ea55d96af017d8127dd2e242762ac5e347af233ca44e9cfba7c29cb7ee344830f62d95aa1924270cfe37073c7175c22ccd1e34a8f9a792bda8d2ea1e80b86c4c37e4682a10de1418f067fa14e7f6f87eed40c039d9e29063949c1a5c665de039383668948446cbce83ff15081bb85b259a368bade1439dab3c2712783f86c045bd51adfd6a0b14c2419ee682c51ecb5943217772fb6d8e6962741cb0a0e7961b64dc6e8cf033a091082802592409edf0e7eb4bc5c83e642da1a43b1ba801e3f3886c6c351911f8476304c098a9154c29c044171caa184bcd4069eb9e6b42eed80b468d45b8e0b82aca761f4a6bbd5ac9c5864cf4703805dcf000a97ebf51cf0db9b1cf7ae1c6316cccec2252e67fdab6c4c12983519d699082a407d684be868687ff7a6b1058901ddc909911dd5823069940197ea29be6e4d2c4bbf8ef64d0a54cbb88dbefe4a9246856965fccc0b00ee7664609c5e14bbcb56c358412e475ba7c246f1d162c616117370ca4678281e04ff49d1c2d37f6ec6725a729721ad8aae5e9af59067bf13b156d63771f55899f38f7ae0c66836e319929e59871b47908dfa5da4b4463a1fcab47946321761fdad868b3ec143b904ff5afc36d0b855fcde4cd5d9caea7ba98372cc64675b1913879425b2484b30d3619122a144a7e5278fd9a6e4e289d1ac6cef1e58e3712117f2425751c39ef6c09df485442ddaf23391ee3af304efb2a5602f6f593b407cfae6be3a86813efb675ef56cd8b57f2113a0943c7a16f7884f3b6ed7a34c4c4ffb7907032f04e3c4b7af5606a935de7136e544557dc21efecee862fce3b32c75d375ffce9139e71ac391ccfec87c2a40e762a7b13766ba53919e8711f410780c7d554b540afe9d90c61bdc9916685ee0e73368b3c160ae554216eb4d9aa1b4e1f5d541cafcbb50009069be7d141defed2f0ae181392d0f6287f95fbb517023d303a58ece2b12f408b537cab792f2627fab4dd7fee9c05625b7b214fa06271a346d648537a27f4ec1dc4b616c435fadd54b18818f948389ce08731388b593588dcdeb64ebeecabc0a5d11a3961ad1a7567deb29b02d6b732bce62b23be67c06e6f25e7ce16a93c6a8efec6d3a8e26c45937b463220c06581225b699aeb00b196dc91acf3a0ee3649c2231a698dc5c9bd0c3b9ea25cd3657d67ef2328c764c2eabd1c788fa52c4576a2187f8b61eb5858da41ba0af31377279e7242cebc09f226af90e63c71f30078041b325e5a9e70b8207852ca52a7781b40e013724d23ffb348cf76b54385caf5d3e41d82d6bc990c56bae9aa9dd30df0ad905b6ed869f80d6be3d01b3c4d4d0addb85fe05a3c4ff0ba40f28e3c15edf3c3419ea720bdf28b19025c0ae1f8d3a49c0a7faf7643b4eaae2b0d5bd1441d4a4c4ecb9ce1635a075db12f1753dbfcc9c62f72aa329554d7d4f02690b17cae2ef269cae4f42af3c2b3e79bc4edd7f3d22a9fb19e7eb67e2a4aaecd0e8322817d794358b6388d96c4394313712e7cf793b34d7511022a8747f71a897f6aec36d90af725adf3368cc25e54ab364cfb9c2bffa8d4ac2799be8d3868f24501c68a88663ac1f866ecec0ea5ce406b3525472a3dd1a41a5fe36665f3836c118f59153b61f10d0ed2fbeafde409754e2630f37cd4dbe8009c03b87428d9b5b249530695767e9f7d611cc71a52b0c3c87f4291c94dd7e9fee1770f0f630d5a2b554aa0d839fabc8ce73fca5a17976b4c36a9ac023dfcfeb8aae2c085b98ec5179054940bc7038e6b88c702fce392ccfdd047c724a89bfbc890a90b5850db127763a3951834534d55c1f8cf6f905306653fec8c71e57c724e4505ea350d8c892006e4f3e0685686460a119cb86357707f6a169dffafa3bbaffbbef82a5f1585c984e12d3b88416423251de25e977cfec67f53096389cfbaf19c0d6e0005cacddaa2e2755d198f5adc074fe3a2cf16f900893d6c2ab52b6d820c569429ca7179f9d541e30740edf759adfc588e481498685a10ed5f6cea1d81dc5f373303a0f94a00b64152d134f52cf9c0f5c20b370645ad4311653410cdf3c6272be32748ae92c62f49a050314fdc1e280fb80de17206f435c423a54593f95eaf277b837246217f09f02698e25c0f26e3ef590d2702bfb1bc0f22755493e9a3863be175af7ebd724edf6c3ceb61bdebe82b191fc323f87407fb22a7014119ac7bd5dda8cdb566ff3f6e2cae7dfa414e435d7a721cd254f95a3d8100aa9404f14456a9386a2902b529f1c2044ed284f466236a6d87d5d54430a8aba9bd15823a6335cb4b6a64faf07422bcf21ddaf5c0987c8e436bd2e2e55e36e8730e6feedf7d20bc1af1c445dd680769a90947f1dc4120c809f6d753e07fef375c5b1814136622c4899f7310c2b225e3f72df6f9e

private def light (n : ℕ) : Bool :=
  if n≤161 then decide n.Prime else n.gcd 75907050539472187290751785709367294850142012310319093001281637109124354328254874435863462868336514307629599224875954998199218529677928181579808491945059049643495805791487187086484320607292781408814365272803092482649411787748723446459202305005715456000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤25980) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 161 = 75907050539472187290751785709367294850142012310319093001281637109124354328254874435863462868336514307629599224875954998199218529677928181579808491945059049643495805791487187086484320607292781408814365272803092482649411787748723446459202305005715456000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 161 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤25980 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 50 := by unfold smallValid; decide +kernel

private theorem sp50 : smallValid 50 51 := by unfold smallValid; decide +kernel

private theorem sp101 : smallValid 101 50 := by unfold smallValid; decide +kernel

private theorem sp151 : smallValid 151 51 := by unfold smallValid; decide +kernel

private theorem sp202 : smallValid 202 50 := by unfold smallValid; decide +kernel

private theorem sp252 : smallValid 252 51 := by unfold smallValid; decide +kernel

private theorem sp303 : smallValid 303 51 := by unfold smallValid; decide +kernel

private theorem sp354 : smallValid 354 51 := by unfold smallValid; decide +kernel

private theorem sp405 : smallValid 405 50 := by unfold smallValid; decide +kernel

private theorem sp455 : smallValid 455 51 := by unfold smallValid; decide +kernel

private theorem sp506 : smallValid 506 51 := by unfold smallValid; decide +kernel

private theorem sp557 : smallValid 557 51 := by unfold smallValid; decide +kernel

private theorem sp608 : smallValid 608 50 := by unfold smallValid; decide +kernel

private theorem sp658 : smallValid 658 51 := by unfold smallValid; decide +kernel

private theorem sp709 : smallValid 709 51 := by unfold smallValid; decide +kernel

private theorem sp760 : smallValid 760 51 := by unfold smallValid; decide +kernel

private theorem sp811 : smallValid 811 50 := by unfold smallValid; decide +kernel

private theorem sp861 : smallValid 861 51 := by unfold smallValid; decide +kernel

private theorem sp912 : smallValid 912 51 := by unfold smallValid; decide +kernel

private theorem sp963 : smallValid 963 51 := by unfold smallValid; decide +kernel

private theorem sp1014 : smallValid 1014 50 := by unfold smallValid; decide +kernel

private theorem sp1064 : smallValid 1064 51 := by unfold smallValid; decide +kernel

private theorem sp1115 : smallValid 1115 51 := by unfold smallValid; decide +kernel

private theorem sp1166 : smallValid 1166 51 := by unfold smallValid; decide +kernel

private theorem sp1217 : smallValid 1217 50 := by unfold smallValid; decide +kernel

private theorem sp1267 : smallValid 1267 51 := by unfold smallValid; decide +kernel

private theorem sp1318 : smallValid 1318 51 := by unfold smallValid; decide +kernel

private theorem sp1369 : smallValid 1369 51 := by unfold smallValid; decide +kernel

private theorem sp1420 : smallValid 1420 50 := by unfold smallValid; decide +kernel

private theorem sp1470 : smallValid 1470 51 := by unfold smallValid; decide +kernel

private theorem sp1521 : smallValid 1521 51 := by unfold smallValid; decide +kernel

private theorem sp1572 : smallValid 1572 51 := by unfold smallValid; decide +kernel

private theorem sp1623 : smallValid 1623 50 := by unfold smallValid; decide +kernel

private theorem sp1673 : smallValid 1673 51 := by unfold smallValid; decide +kernel

private theorem sp1724 : smallValid 1724 51 := by unfold smallValid; decide +kernel

private theorem sp1775 : smallValid 1775 51 := by unfold smallValid; decide +kernel

private theorem sp1826 : smallValid 1826 50 := by unfold smallValid; decide +kernel

private theorem sp1876 : smallValid 1876 51 := by unfold smallValid; decide +kernel

private theorem sp1927 : smallValid 1927 51 := by unfold smallValid; decide +kernel

private theorem sp1978 : smallValid 1978 51 := by unfold smallValid; decide +kernel

private theorem sp2029 : smallValid 2029 50 := by unfold smallValid; decide +kernel

private theorem sp2079 : smallValid 2079 51 := by unfold smallValid; decide +kernel

private theorem sp2130 : smallValid 2130 51 := by unfold smallValid; decide +kernel

private theorem sp2181 : smallValid 2181 51 := by unfold smallValid; decide +kernel

private theorem sp2232 : smallValid 2232 50 := by unfold smallValid; decide +kernel

private theorem sp2282 : smallValid 2282 51 := by unfold smallValid; decide +kernel

private theorem sp2333 : smallValid 2333 51 := by unfold smallValid; decide +kernel

private theorem sp2384 : smallValid 2384 51 := by unfold smallValid; decide +kernel

private theorem sp2435 : smallValid 2435 50 := by unfold smallValid; decide +kernel

private theorem sp2485 : smallValid 2485 51 := by unfold smallValid; decide +kernel

private theorem sp2536 : smallValid 2536 51 := by unfold smallValid; decide +kernel

private theorem sp2587 : smallValid 2587 51 := by unfold smallValid; decide +kernel

private theorem sp2638 : smallValid 2638 50 := by unfold smallValid; decide +kernel

private theorem sp2688 : smallValid 2688 51 := by unfold smallValid; decide +kernel

private theorem sp2739 : smallValid 2739 51 := by unfold smallValid; decide +kernel

private theorem sp2790 : smallValid 2790 51 := by unfold smallValid; decide +kernel

private theorem sp2841 : smallValid 2841 50 := by unfold smallValid; decide +kernel

private theorem sp2891 : smallValid 2891 51 := by unfold smallValid; decide +kernel

private theorem sp2942 : smallValid 2942 51 := by unfold smallValid; decide +kernel

private theorem sp2993 : smallValid 2993 51 := by unfold smallValid; decide +kernel

private theorem sp3044 : smallValid 3044 50 := by unfold smallValid; decide +kernel

private theorem sp3094 : smallValid 3094 51 := by unfold smallValid; decide +kernel

private theorem sp3145 : smallValid 3145 51 := by unfold smallValid; decide +kernel

private theorem sp3196 : smallValid 3196 51 := by unfold smallValid; decide +kernel

private theorem sp3247 : smallValid 3247 50 := by unfold smallValid; decide +kernel

private theorem sp3297 : smallValid 3297 51 := by unfold smallValid; decide +kernel

private theorem sp3348 : smallValid 3348 51 := by unfold smallValid; decide +kernel

private theorem sp3399 : smallValid 3399 51 := by unfold smallValid; decide +kernel

private theorem sp3450 : smallValid 3450 50 := by unfold smallValid; decide +kernel

private theorem sp3500 : smallValid 3500 51 := by unfold smallValid; decide +kernel

private theorem sp3551 : smallValid 3551 51 := by unfold smallValid; decide +kernel

private theorem sp3602 : smallValid 3602 51 := by unfold smallValid; decide +kernel

private theorem sp3653 : smallValid 3653 50 := by unfold smallValid; decide +kernel

private theorem sp3703 : smallValid 3703 51 := by unfold smallValid; decide +kernel

private theorem sp3754 : smallValid 3754 51 := by unfold smallValid; decide +kernel

private theorem sp3805 : smallValid 3805 51 := by unfold smallValid; decide +kernel

private theorem sp3856 : smallValid 3856 50 := by unfold smallValid; decide +kernel

private theorem sp3906 : smallValid 3906 51 := by unfold smallValid; decide +kernel

private theorem sp3957 : smallValid 3957 51 := by unfold smallValid; decide +kernel

private theorem sp4008 : smallValid 4008 51 := by unfold smallValid; decide +kernel

private theorem sp4059 : smallValid 4059 50 := by unfold smallValid; decide +kernel

private theorem sp4109 : smallValid 4109 51 := by unfold smallValid; decide +kernel

private theorem sp4160 : smallValid 4160 51 := by unfold smallValid; decide +kernel

private theorem sp4211 : smallValid 4211 51 := by unfold smallValid; decide +kernel

private theorem sp4262 : smallValid 4262 50 := by unfold smallValid; decide +kernel

private theorem sp4312 : smallValid 4312 51 := by unfold smallValid; decide +kernel

private theorem sp4363 : smallValid 4363 51 := by unfold smallValid; decide +kernel

private theorem sp4414 : smallValid 4414 51 := by unfold smallValid; decide +kernel

private theorem sp4465 : smallValid 4465 50 := by unfold smallValid; decide +kernel

private theorem sp4515 : smallValid 4515 51 := by unfold smallValid; decide +kernel

private theorem sp4566 : smallValid 4566 51 := by unfold smallValid; decide +kernel

private theorem sp4617 : smallValid 4617 51 := by unfold smallValid; decide +kernel

private theorem sp4668 : smallValid 4668 50 := by unfold smallValid; decide +kernel

private theorem sp4718 : smallValid 4718 51 := by unfold smallValid; decide +kernel

private theorem sp4769 : smallValid 4769 51 := by unfold smallValid; decide +kernel

private theorem sp4820 : smallValid 4820 51 := by unfold smallValid; decide +kernel

private theorem sp4871 : smallValid 4871 50 := by unfold smallValid; decide +kernel

private theorem sp4921 : smallValid 4921 51 := by unfold smallValid; decide +kernel

private theorem sp4972 : smallValid 4972 51 := by unfold smallValid; decide +kernel

private theorem sp5023 : smallValid 5023 51 := by unfold smallValid; decide +kernel

private theorem sp5074 : smallValid 5074 50 := by unfold smallValid; decide +kernel

private theorem sp5124 : smallValid 5124 51 := by unfold smallValid; decide +kernel

private theorem sp5175 : smallValid 5175 51 := by unfold smallValid; decide +kernel

private theorem sp5226 : smallValid 5226 51 := by unfold smallValid; decide +kernel

private theorem sp5277 : smallValid 5277 50 := by unfold smallValid; decide +kernel

private theorem sp5327 : smallValid 5327 51 := by unfold smallValid; decide +kernel

private theorem sp5378 : smallValid 5378 51 := by unfold smallValid; decide +kernel

private theorem sp5429 : smallValid 5429 51 := by unfold smallValid; decide +kernel

private theorem sp5480 : smallValid 5480 50 := by unfold smallValid; decide +kernel

private theorem sp5530 : smallValid 5530 51 := by unfold smallValid; decide +kernel

private theorem sp5581 : smallValid 5581 51 := by unfold smallValid; decide +kernel

private theorem sp5632 : smallValid 5632 51 := by unfold smallValid; decide +kernel

private theorem sp5683 : smallValid 5683 50 := by unfold smallValid; decide +kernel

private theorem sp5733 : smallValid 5733 51 := by unfold smallValid; decide +kernel

private theorem sp5784 : smallValid 5784 51 := by unfold smallValid; decide +kernel

private theorem sp5835 : smallValid 5835 51 := by unfold smallValid; decide +kernel

private theorem sp5886 : smallValid 5886 50 := by unfold smallValid; decide +kernel

private theorem sp5936 : smallValid 5936 51 := by unfold smallValid; decide +kernel

private theorem sp5987 : smallValid 5987 51 := by unfold smallValid; decide +kernel

private theorem sp6038 : smallValid 6038 51 := by unfold smallValid; decide +kernel

private theorem sp6089 : smallValid 6089 50 := by unfold smallValid; decide +kernel

private theorem sp6139 : smallValid 6139 51 := by unfold smallValid; decide +kernel

private theorem sp6190 : smallValid 6190 51 := by unfold smallValid; decide +kernel

private theorem sp6241 : smallValid 6241 51 := by unfold smallValid; decide +kernel

private theorem sp6292 : smallValid 6292 50 := by unfold smallValid; decide +kernel

private theorem sp6342 : smallValid 6342 51 := by unfold smallValid; decide +kernel

private theorem sp6393 : smallValid 6393 51 := by unfold smallValid; decide +kernel

private theorem sp6444 : smallValid 6444 51 := by unfold smallValid; decide +kernel

private theorem sp6495 : smallValid 6495 50 := by unfold smallValid; decide +kernel

private theorem sp6545 : smallValid 6545 51 := by unfold smallValid; decide +kernel

private theorem sp6596 : smallValid 6596 50 := by unfold smallValid; decide +kernel

private theorem sp6646 : smallValid 6646 51 := by unfold smallValid; decide +kernel

private theorem sp6697 : smallValid 6697 50 := by unfold smallValid; decide +kernel

private theorem sp6747 : smallValid 6747 51 := by unfold smallValid; decide +kernel

private theorem sp6798 : smallValid 6798 51 := by unfold smallValid; decide +kernel

private theorem sp6849 : smallValid 6849 51 := by unfold smallValid; decide +kernel

private theorem sp6900 : smallValid 6900 50 := by unfold smallValid; decide +kernel

private theorem sp6950 : smallValid 6950 51 := by unfold smallValid; decide +kernel

private theorem sp7001 : smallValid 7001 51 := by unfold smallValid; decide +kernel

private theorem sp7052 : smallValid 7052 51 := by unfold smallValid; decide +kernel

private theorem sp7103 : smallValid 7103 50 := by unfold smallValid; decide +kernel

private theorem sp7153 : smallValid 7153 51 := by unfold smallValid; decide +kernel

private theorem sp7204 : smallValid 7204 51 := by unfold smallValid; decide +kernel

private theorem sp7255 : smallValid 7255 51 := by unfold smallValid; decide +kernel

private theorem sp7306 : smallValid 7306 50 := by unfold smallValid; decide +kernel

private theorem sp7356 : smallValid 7356 51 := by unfold smallValid; decide +kernel

private theorem sp7407 : smallValid 7407 51 := by unfold smallValid; decide +kernel

private theorem sp7458 : smallValid 7458 51 := by unfold smallValid; decide +kernel

private theorem sp7509 : smallValid 7509 50 := by unfold smallValid; decide +kernel

private theorem sp7559 : smallValid 7559 51 := by unfold smallValid; decide +kernel

private theorem sp7610 : smallValid 7610 51 := by unfold smallValid; decide +kernel

private theorem sp7661 : smallValid 7661 51 := by unfold smallValid; decide +kernel

private theorem sp7712 : smallValid 7712 50 := by unfold smallValid; decide +kernel

private theorem sp7762 : smallValid 7762 51 := by unfold smallValid; decide +kernel

private theorem sp7813 : smallValid 7813 51 := by unfold smallValid; decide +kernel

private theorem sp7864 : smallValid 7864 51 := by unfold smallValid; decide +kernel

private theorem sp7915 : smallValid 7915 50 := by unfold smallValid; decide +kernel

private theorem sp7965 : smallValid 7965 51 := by unfold smallValid; decide +kernel

private theorem sp8016 : smallValid 8016 51 := by unfold smallValid; decide +kernel

private theorem sp8067 : smallValid 8067 51 := by unfold smallValid; decide +kernel

private theorem sp8118 : smallValid 8118 50 := by unfold smallValid; decide +kernel

private theorem sp8168 : smallValid 8168 51 := by unfold smallValid; decide +kernel

private theorem sp8219 : smallValid 8219 51 := by unfold smallValid; decide +kernel

private theorem sp8270 : smallValid 8270 51 := by unfold smallValid; decide +kernel

private theorem sp8321 : smallValid 8321 50 := by unfold smallValid; decide +kernel

private theorem sp8371 : smallValid 8371 51 := by unfold smallValid; decide +kernel

private theorem sp8422 : smallValid 8422 51 := by unfold smallValid; decide +kernel

private theorem sp8473 : smallValid 8473 51 := by unfold smallValid; decide +kernel

private theorem sp8524 : smallValid 8524 50 := by unfold smallValid; decide +kernel

private theorem sp8574 : smallValid 8574 51 := by unfold smallValid; decide +kernel

private theorem sp8625 : smallValid 8625 51 := by unfold smallValid; decide +kernel

private theorem sp8676 : smallValid 8676 51 := by unfold smallValid; decide +kernel

private theorem sp8727 : smallValid 8727 50 := by unfold smallValid; decide +kernel

private theorem sp8777 : smallValid 8777 51 := by unfold smallValid; decide +kernel

private theorem sp8828 : smallValid 8828 51 := by unfold smallValid; decide +kernel

private theorem sp8879 : smallValid 8879 51 := by unfold smallValid; decide +kernel

private theorem sp8930 : smallValid 8930 50 := by unfold smallValid; decide +kernel

private theorem sp8980 : smallValid 8980 51 := by unfold smallValid; decide +kernel

private theorem sp9031 : smallValid 9031 51 := by unfold smallValid; decide +kernel

private theorem sp9082 : smallValid 9082 51 := by unfold smallValid; decide +kernel

private theorem sp9133 : smallValid 9133 50 := by unfold smallValid; decide +kernel

private theorem sp9183 : smallValid 9183 51 := by unfold smallValid; decide +kernel

private theorem sp9234 : smallValid 9234 51 := by unfold smallValid; decide +kernel

private theorem sp9285 : smallValid 9285 51 := by unfold smallValid; decide +kernel

private theorem sp9336 : smallValid 9336 50 := by unfold smallValid; decide +kernel

private theorem sp9386 : smallValid 9386 51 := by unfold smallValid; decide +kernel

private theorem sp9437 : smallValid 9437 51 := by unfold smallValid; decide +kernel

private theorem sp9488 : smallValid 9488 51 := by unfold smallValid; decide +kernel

private theorem sp9539 : smallValid 9539 50 := by unfold smallValid; decide +kernel

private theorem sp9589 : smallValid 9589 51 := by unfold smallValid; decide +kernel

private theorem sp9640 : smallValid 9640 51 := by unfold smallValid; decide +kernel

private theorem sp9691 : smallValid 9691 51 := by unfold smallValid; decide +kernel

private theorem sp9742 : smallValid 9742 50 := by unfold smallValid; decide +kernel

private theorem sp9792 : smallValid 9792 51 := by unfold smallValid; decide +kernel

private theorem sp9843 : smallValid 9843 51 := by unfold smallValid; decide +kernel

private theorem sp9894 : smallValid 9894 51 := by unfold smallValid; decide +kernel

private theorem sp9945 : smallValid 9945 50 := by unfold smallValid; decide +kernel

private theorem sp9995 : smallValid 9995 51 := by unfold smallValid; decide +kernel

private theorem sp10046 : smallValid 10046 51 := by unfold smallValid; decide +kernel

private theorem sp10097 : smallValid 10097 51 := by unfold smallValid; decide +kernel

private theorem sp10148 : smallValid 10148 50 := by unfold smallValid; decide +kernel

private theorem sp10198 : smallValid 10198 51 := by unfold smallValid; decide +kernel

private theorem sp10249 : smallValid 10249 51 := by unfold smallValid; decide +kernel

private theorem sp10300 : smallValid 10300 51 := by unfold smallValid; decide +kernel

private theorem sp10351 : smallValid 10351 50 := by unfold smallValid; decide +kernel

private theorem sp10401 : smallValid 10401 51 := by unfold smallValid; decide +kernel

private theorem sp10452 : smallValid 10452 51 := by unfold smallValid; decide +kernel

private theorem sp10503 : smallValid 10503 51 := by unfold smallValid; decide +kernel

private theorem sp10554 : smallValid 10554 50 := by unfold smallValid; decide +kernel

private theorem sp10604 : smallValid 10604 51 := by unfold smallValid; decide +kernel

private theorem sp10655 : smallValid 10655 51 := by unfold smallValid; decide +kernel

private theorem sp10706 : smallValid 10706 51 := by unfold smallValid; decide +kernel

private theorem sp10757 : smallValid 10757 50 := by unfold smallValid; decide +kernel

private theorem sp10807 : smallValid 10807 51 := by unfold smallValid; decide +kernel

private theorem sp10858 : smallValid 10858 51 := by unfold smallValid; decide +kernel

private theorem sp10909 : smallValid 10909 51 := by unfold smallValid; decide +kernel

private theorem sp10960 : smallValid 10960 50 := by unfold smallValid; decide +kernel

private theorem sp11010 : smallValid 11010 51 := by unfold smallValid; decide +kernel

private theorem sp11061 : smallValid 11061 51 := by unfold smallValid; decide +kernel

private theorem sp11112 : smallValid 11112 51 := by unfold smallValid; decide +kernel

private theorem sp11163 : smallValid 11163 50 := by unfold smallValid; decide +kernel

private theorem sp11213 : smallValid 11213 51 := by unfold smallValid; decide +kernel

private theorem sp11264 : smallValid 11264 51 := by unfold smallValid; decide +kernel

private theorem sp11315 : smallValid 11315 51 := by unfold smallValid; decide +kernel

private theorem sp11366 : smallValid 11366 50 := by unfold smallValid; decide +kernel

private theorem sp11416 : smallValid 11416 51 := by unfold smallValid; decide +kernel

private theorem sp11467 : smallValid 11467 51 := by unfold smallValid; decide +kernel

private theorem sp11518 : smallValid 11518 51 := by unfold smallValid; decide +kernel

private theorem sp11569 : smallValid 11569 50 := by unfold smallValid; decide +kernel

private theorem sp11619 : smallValid 11619 51 := by unfold smallValid; decide +kernel

private theorem sp11670 : smallValid 11670 51 := by unfold smallValid; decide +kernel

private theorem sp11721 : smallValid 11721 51 := by unfold smallValid; decide +kernel

private theorem sp11772 : smallValid 11772 50 := by unfold smallValid; decide +kernel

private theorem sp11822 : smallValid 11822 51 := by unfold smallValid; decide +kernel

private theorem sp11873 : smallValid 11873 51 := by unfold smallValid; decide +kernel

private theorem sp11924 : smallValid 11924 51 := by unfold smallValid; decide +kernel

private theorem sp11975 : smallValid 11975 50 := by unfold smallValid; decide +kernel

private theorem sp12025 : smallValid 12025 51 := by unfold smallValid; decide +kernel

private theorem sp12076 : smallValid 12076 51 := by unfold smallValid; decide +kernel

private theorem sp12127 : smallValid 12127 51 := by unfold smallValid; decide +kernel

private theorem sp12178 : smallValid 12178 50 := by unfold smallValid; decide +kernel

private theorem sp12228 : smallValid 12228 51 := by unfold smallValid; decide +kernel

private theorem sp12279 : smallValid 12279 51 := by unfold smallValid; decide +kernel

private theorem sp12330 : smallValid 12330 51 := by unfold smallValid; decide +kernel

private theorem sp12381 : smallValid 12381 50 := by unfold smallValid; decide +kernel

private theorem sp12431 : smallValid 12431 51 := by unfold smallValid; decide +kernel

private theorem sp12482 : smallValid 12482 51 := by unfold smallValid; decide +kernel

private theorem sp12533 : smallValid 12533 51 := by unfold smallValid; decide +kernel

private theorem sp12584 : smallValid 12584 50 := by unfold smallValid; decide +kernel

private theorem sp12634 : smallValid 12634 51 := by unfold smallValid; decide +kernel

private theorem sp12685 : smallValid 12685 51 := by unfold smallValid; decide +kernel

private theorem sp12736 : smallValid 12736 51 := by unfold smallValid; decide +kernel

private theorem sp12787 : smallValid 12787 50 := by unfold smallValid; decide +kernel

private theorem sp12837 : smallValid 12837 51 := by unfold smallValid; decide +kernel

private theorem sp12888 : smallValid 12888 51 := by unfold smallValid; decide +kernel

private theorem sp12939 : smallValid 12939 51 := by unfold smallValid; decide +kernel

private theorem sp12990 : smallValid 12990 50 := by unfold smallValid; decide +kernel

private theorem sp13040 : smallValid 13040 51 := by unfold smallValid; decide +kernel

private theorem sp13091 : smallValid 13091 50 := by unfold smallValid; decide +kernel

private theorem sp13141 : smallValid 13141 51 := by unfold smallValid; decide +kernel

private theorem sp13192 : smallValid 13192 50 := by unfold smallValid; decide +kernel

private theorem sp13242 : smallValid 13242 51 := by unfold smallValid; decide +kernel

private theorem sp13293 : smallValid 13293 51 := by unfold smallValid; decide +kernel

private theorem sp13344 : smallValid 13344 51 := by unfold smallValid; decide +kernel

private theorem sp13395 : smallValid 13395 50 := by unfold smallValid; decide +kernel

private theorem sp13445 : smallValid 13445 51 := by unfold smallValid; decide +kernel

private theorem sp13496 : smallValid 13496 51 := by unfold smallValid; decide +kernel

private theorem sp13547 : smallValid 13547 51 := by unfold smallValid; decide +kernel

private theorem sp13598 : smallValid 13598 50 := by unfold smallValid; decide +kernel

private theorem sp13648 : smallValid 13648 51 := by unfold smallValid; decide +kernel

private theorem sp13699 : smallValid 13699 51 := by unfold smallValid; decide +kernel

private theorem sp13750 : smallValid 13750 51 := by unfold smallValid; decide +kernel

private theorem sp13801 : smallValid 13801 50 := by unfold smallValid; decide +kernel

private theorem sp13851 : smallValid 13851 51 := by unfold smallValid; decide +kernel

private theorem sp13902 : smallValid 13902 51 := by unfold smallValid; decide +kernel

private theorem sp13953 : smallValid 13953 51 := by unfold smallValid; decide +kernel

private theorem sp14004 : smallValid 14004 50 := by unfold smallValid; decide +kernel

private theorem sp14054 : smallValid 14054 51 := by unfold smallValid; decide +kernel

private theorem sp14105 : smallValid 14105 51 := by unfold smallValid; decide +kernel

private theorem sp14156 : smallValid 14156 51 := by unfold smallValid; decide +kernel

private theorem sp14207 : smallValid 14207 50 := by unfold smallValid; decide +kernel

private theorem sp14257 : smallValid 14257 51 := by unfold smallValid; decide +kernel

private theorem sp14308 : smallValid 14308 51 := by unfold smallValid; decide +kernel

private theorem sp14359 : smallValid 14359 51 := by unfold smallValid; decide +kernel

private theorem sp14410 : smallValid 14410 50 := by unfold smallValid; decide +kernel

private theorem sp14460 : smallValid 14460 51 := by unfold smallValid; decide +kernel

private theorem sp14511 : smallValid 14511 51 := by unfold smallValid; decide +kernel

private theorem sp14562 : smallValid 14562 51 := by unfold smallValid; decide +kernel

private theorem sp14613 : smallValid 14613 50 := by unfold smallValid; decide +kernel

private theorem sp14663 : smallValid 14663 51 := by unfold smallValid; decide +kernel

private theorem sp14714 : smallValid 14714 51 := by unfold smallValid; decide +kernel

private theorem sp14765 : smallValid 14765 51 := by unfold smallValid; decide +kernel

private theorem sp14816 : smallValid 14816 50 := by unfold smallValid; decide +kernel

private theorem sp14866 : smallValid 14866 51 := by unfold smallValid; decide +kernel

private theorem sp14917 : smallValid 14917 51 := by unfold smallValid; decide +kernel

private theorem sp14968 : smallValid 14968 51 := by unfold smallValid; decide +kernel

private theorem sp15019 : smallValid 15019 50 := by unfold smallValid; decide +kernel

private theorem sp15069 : smallValid 15069 51 := by unfold smallValid; decide +kernel

private theorem sp15120 : smallValid 15120 51 := by unfold smallValid; decide +kernel

private theorem sp15171 : smallValid 15171 51 := by unfold smallValid; decide +kernel

private theorem sp15222 : smallValid 15222 50 := by unfold smallValid; decide +kernel

private theorem sp15272 : smallValid 15272 51 := by unfold smallValid; decide +kernel

private theorem sp15323 : smallValid 15323 51 := by unfold smallValid; decide +kernel

private theorem sp15374 : smallValid 15374 51 := by unfold smallValid; decide +kernel

private theorem sp15425 : smallValid 15425 50 := by unfold smallValid; decide +kernel

private theorem sp15475 : smallValid 15475 51 := by unfold smallValid; decide +kernel

private theorem sp15526 : smallValid 15526 51 := by unfold smallValid; decide +kernel

private theorem sp15577 : smallValid 15577 51 := by unfold smallValid; decide +kernel

private theorem sp15628 : smallValid 15628 50 := by unfold smallValid; decide +kernel

private theorem sp15678 : smallValid 15678 51 := by unfold smallValid; decide +kernel

private theorem sp15729 : smallValid 15729 51 := by unfold smallValid; decide +kernel

private theorem sp15780 : smallValid 15780 51 := by unfold smallValid; decide +kernel

private theorem sp15831 : smallValid 15831 50 := by unfold smallValid; decide +kernel

private theorem sp15881 : smallValid 15881 51 := by unfold smallValid; decide +kernel

private theorem sp15932 : smallValid 15932 51 := by unfold smallValid; decide +kernel

private theorem sp15983 : smallValid 15983 51 := by unfold smallValid; decide +kernel

private theorem sp16034 : smallValid 16034 50 := by unfold smallValid; decide +kernel

private theorem sp16084 : smallValid 16084 51 := by unfold smallValid; decide +kernel

private theorem sp16135 : smallValid 16135 51 := by unfold smallValid; decide +kernel

private theorem sp16186 : smallValid 16186 51 := by unfold smallValid; decide +kernel

private theorem sp16237 : smallValid 16237 50 := by unfold smallValid; decide +kernel

private theorem sp16287 : smallValid 16287 51 := by unfold smallValid; decide +kernel

private theorem sp16338 : smallValid 16338 51 := by unfold smallValid; decide +kernel

private theorem sp16389 : smallValid 16389 51 := by unfold smallValid; decide +kernel

private theorem sp16440 : smallValid 16440 50 := by unfold smallValid; decide +kernel

private theorem sp16490 : smallValid 16490 51 := by unfold smallValid; decide +kernel

private theorem sp16541 : smallValid 16541 51 := by unfold smallValid; decide +kernel

private theorem sp16592 : smallValid 16592 51 := by unfold smallValid; decide +kernel

private theorem sp16643 : smallValid 16643 50 := by unfold smallValid; decide +kernel

private theorem sp16693 : smallValid 16693 51 := by unfold smallValid; decide +kernel

private theorem sp16744 : smallValid 16744 51 := by unfold smallValid; decide +kernel

private theorem sp16795 : smallValid 16795 51 := by unfold smallValid; decide +kernel

private theorem sp16846 : smallValid 16846 50 := by unfold smallValid; decide +kernel

private theorem sp16896 : smallValid 16896 51 := by unfold smallValid; decide +kernel

private theorem sp16947 : smallValid 16947 51 := by unfold smallValid; decide +kernel

private theorem sp16998 : smallValid 16998 51 := by unfold smallValid; decide +kernel

private theorem sp17049 : smallValid 17049 50 := by unfold smallValid; decide +kernel

private theorem sp17099 : smallValid 17099 51 := by unfold smallValid; decide +kernel

private theorem sp17150 : smallValid 17150 51 := by unfold smallValid; decide +kernel

private theorem sp17201 : smallValid 17201 51 := by unfold smallValid; decide +kernel

private theorem sp17252 : smallValid 17252 50 := by unfold smallValid; decide +kernel

private theorem sp17302 : smallValid 17302 51 := by unfold smallValid; decide +kernel

private theorem sp17353 : smallValid 17353 51 := by unfold smallValid; decide +kernel

private theorem sp17404 : smallValid 17404 51 := by unfold smallValid; decide +kernel

private theorem sp17455 : smallValid 17455 50 := by unfold smallValid; decide +kernel

private theorem sp17505 : smallValid 17505 51 := by unfold smallValid; decide +kernel

private theorem sp17556 : smallValid 17556 51 := by unfold smallValid; decide +kernel

private theorem sp17607 : smallValid 17607 51 := by unfold smallValid; decide +kernel

private theorem sp17658 : smallValid 17658 50 := by unfold smallValid; decide +kernel

private theorem sp17708 : smallValid 17708 51 := by unfold smallValid; decide +kernel

private theorem sp17759 : smallValid 17759 51 := by unfold smallValid; decide +kernel

private theorem sp17810 : smallValid 17810 51 := by unfold smallValid; decide +kernel

private theorem sp17861 : smallValid 17861 50 := by unfold smallValid; decide +kernel

private theorem sp17911 : smallValid 17911 51 := by unfold smallValid; decide +kernel

private theorem sp17962 : smallValid 17962 51 := by unfold smallValid; decide +kernel

private theorem sp18013 : smallValid 18013 51 := by unfold smallValid; decide +kernel

private theorem sp18064 : smallValid 18064 50 := by unfold smallValid; decide +kernel

private theorem sp18114 : smallValid 18114 51 := by unfold smallValid; decide +kernel

private theorem sp18165 : smallValid 18165 51 := by unfold smallValid; decide +kernel

private theorem sp18216 : smallValid 18216 51 := by unfold smallValid; decide +kernel

private theorem sp18267 : smallValid 18267 50 := by unfold smallValid; decide +kernel

private theorem sp18317 : smallValid 18317 51 := by unfold smallValid; decide +kernel

private theorem sp18368 : smallValid 18368 51 := by unfold smallValid; decide +kernel

private theorem sp18419 : smallValid 18419 51 := by unfold smallValid; decide +kernel

private theorem sp18470 : smallValid 18470 50 := by unfold smallValid; decide +kernel

private theorem sp18520 : smallValid 18520 51 := by unfold smallValid; decide +kernel

private theorem sp18571 : smallValid 18571 51 := by unfold smallValid; decide +kernel

private theorem sp18622 : smallValid 18622 51 := by unfold smallValid; decide +kernel

private theorem sp18673 : smallValid 18673 50 := by unfold smallValid; decide +kernel

private theorem sp18723 : smallValid 18723 51 := by unfold smallValid; decide +kernel

private theorem sp18774 : smallValid 18774 51 := by unfold smallValid; decide +kernel

private theorem sp18825 : smallValid 18825 51 := by unfold smallValid; decide +kernel

private theorem sp18876 : smallValid 18876 50 := by unfold smallValid; decide +kernel

private theorem sp18926 : smallValid 18926 51 := by unfold smallValid; decide +kernel

private theorem sp18977 : smallValid 18977 51 := by unfold smallValid; decide +kernel

private theorem sp19028 : smallValid 19028 51 := by unfold smallValid; decide +kernel

private theorem sp19079 : smallValid 19079 50 := by unfold smallValid; decide +kernel

private theorem sp19129 : smallValid 19129 51 := by unfold smallValid; decide +kernel

private theorem sp19180 : smallValid 19180 51 := by unfold smallValid; decide +kernel

private theorem sp19231 : smallValid 19231 51 := by unfold smallValid; decide +kernel

private theorem sp19282 : smallValid 19282 50 := by unfold smallValid; decide +kernel

private theorem sp19332 : smallValid 19332 51 := by unfold smallValid; decide +kernel

private theorem sp19383 : smallValid 19383 51 := by unfold smallValid; decide +kernel

private theorem sp19434 : smallValid 19434 51 := by unfold smallValid; decide +kernel

private theorem sp19485 : smallValid 19485 50 := by unfold smallValid; decide +kernel

private theorem sp19535 : smallValid 19535 51 := by unfold smallValid; decide +kernel

private theorem sp19586 : smallValid 19586 51 := by unfold smallValid; decide +kernel

private theorem sp19637 : smallValid 19637 51 := by unfold smallValid; decide +kernel

private theorem sp19688 : smallValid 19688 50 := by unfold smallValid; decide +kernel

private theorem sp19738 : smallValid 19738 51 := by unfold smallValid; decide +kernel

private theorem sp19789 : smallValid 19789 51 := by unfold smallValid; decide +kernel

private theorem sp19840 : smallValid 19840 51 := by unfold smallValid; decide +kernel

private theorem sp19891 : smallValid 19891 50 := by unfold smallValid; decide +kernel

private theorem sp19941 : smallValid 19941 51 := by unfold smallValid; decide +kernel

private theorem sp19992 : smallValid 19992 51 := by unfold smallValid; decide +kernel

private theorem sp20043 : smallValid 20043 51 := by unfold smallValid; decide +kernel

private theorem sp20094 : smallValid 20094 50 := by unfold smallValid; decide +kernel

private theorem sp20144 : smallValid 20144 51 := by unfold smallValid; decide +kernel

private theorem sp20195 : smallValid 20195 51 := by unfold smallValid; decide +kernel

private theorem sp20246 : smallValid 20246 51 := by unfold smallValid; decide +kernel

private theorem sp20297 : smallValid 20297 50 := by unfold smallValid; decide +kernel

private theorem sp20347 : smallValid 20347 51 := by unfold smallValid; decide +kernel

private theorem sp20398 : smallValid 20398 51 := by unfold smallValid; decide +kernel

private theorem sp20449 : smallValid 20449 51 := by unfold smallValid; decide +kernel

private theorem sp20500 : smallValid 20500 50 := by unfold smallValid; decide +kernel

private theorem sp20550 : smallValid 20550 51 := by unfold smallValid; decide +kernel

private theorem sp20601 : smallValid 20601 51 := by unfold smallValid; decide +kernel

private theorem sp20652 : smallValid 20652 51 := by unfold smallValid; decide +kernel

private theorem sp20703 : smallValid 20703 50 := by unfold smallValid; decide +kernel

private theorem sp20753 : smallValid 20753 51 := by unfold smallValid; decide +kernel

private theorem sp20804 : smallValid 20804 51 := by unfold smallValid; decide +kernel

private theorem sp20855 : smallValid 20855 51 := by unfold smallValid; decide +kernel

private theorem sp20906 : smallValid 20906 50 := by unfold smallValid; decide +kernel

private theorem sp20956 : smallValid 20956 51 := by unfold smallValid; decide +kernel

private theorem sp21007 : smallValid 21007 51 := by unfold smallValid; decide +kernel

private theorem sp21058 : smallValid 21058 51 := by unfold smallValid; decide +kernel

private theorem sp21109 : smallValid 21109 50 := by unfold smallValid; decide +kernel

private theorem sp21159 : smallValid 21159 51 := by unfold smallValid; decide +kernel

private theorem sp21210 : smallValid 21210 51 := by unfold smallValid; decide +kernel

private theorem sp21261 : smallValid 21261 51 := by unfold smallValid; decide +kernel

private theorem sp21312 : smallValid 21312 50 := by unfold smallValid; decide +kernel

private theorem sp21362 : smallValid 21362 51 := by unfold smallValid; decide +kernel

private theorem sp21413 : smallValid 21413 51 := by unfold smallValid; decide +kernel

private theorem sp21464 : smallValid 21464 51 := by unfold smallValid; decide +kernel

private theorem sp21515 : smallValid 21515 50 := by unfold smallValid; decide +kernel

private theorem sp21565 : smallValid 21565 51 := by unfold smallValid; decide +kernel

private theorem sp21616 : smallValid 21616 51 := by unfold smallValid; decide +kernel

private theorem sp21667 : smallValid 21667 51 := by unfold smallValid; decide +kernel

private theorem sp21718 : smallValid 21718 50 := by unfold smallValid; decide +kernel

private theorem sp21768 : smallValid 21768 51 := by unfold smallValid; decide +kernel

private theorem sp21819 : smallValid 21819 51 := by unfold smallValid; decide +kernel

private theorem sp21870 : smallValid 21870 51 := by unfold smallValid; decide +kernel

private theorem sp21921 : smallValid 21921 50 := by unfold smallValid; decide +kernel

private theorem sp21971 : smallValid 21971 51 := by unfold smallValid; decide +kernel

private theorem sp22022 : smallValid 22022 51 := by unfold smallValid; decide +kernel

private theorem sp22073 : smallValid 22073 51 := by unfold smallValid; decide +kernel

private theorem sp22124 : smallValid 22124 50 := by unfold smallValid; decide +kernel

private theorem sp22174 : smallValid 22174 51 := by unfold smallValid; decide +kernel

private theorem sp22225 : smallValid 22225 51 := by unfold smallValid; decide +kernel

private theorem sp22276 : smallValid 22276 51 := by unfold smallValid; decide +kernel

private theorem sp22327 : smallValid 22327 50 := by unfold smallValid; decide +kernel

private theorem sp22377 : smallValid 22377 51 := by unfold smallValid; decide +kernel

private theorem sp22428 : smallValid 22428 51 := by unfold smallValid; decide +kernel

private theorem sp22479 : smallValid 22479 51 := by unfold smallValid; decide +kernel

private theorem sp22530 : smallValid 22530 50 := by unfold smallValid; decide +kernel

private theorem sp22580 : smallValid 22580 51 := by unfold smallValid; decide +kernel

private theorem sp22631 : smallValid 22631 51 := by unfold smallValid; decide +kernel

private theorem sp22682 : smallValid 22682 51 := by unfold smallValid; decide +kernel

private theorem sp22733 : smallValid 22733 50 := by unfold smallValid; decide +kernel

private theorem sp22783 : smallValid 22783 51 := by unfold smallValid; decide +kernel

private theorem sp22834 : smallValid 22834 51 := by unfold smallValid; decide +kernel

private theorem sp22885 : smallValid 22885 51 := by unfold smallValid; decide +kernel

private theorem sp22936 : smallValid 22936 50 := by unfold smallValid; decide +kernel

private theorem sp22986 : smallValid 22986 51 := by unfold smallValid; decide +kernel

private theorem sp23037 : smallValid 23037 51 := by unfold smallValid; decide +kernel

private theorem sp23088 : smallValid 23088 51 := by unfold smallValid; decide +kernel

private theorem sp23139 : smallValid 23139 50 := by unfold smallValid; decide +kernel

private theorem sp23189 : smallValid 23189 51 := by unfold smallValid; decide +kernel

private theorem sp23240 : smallValid 23240 51 := by unfold smallValid; decide +kernel

private theorem sp23291 : smallValid 23291 51 := by unfold smallValid; decide +kernel

private theorem sp23342 : smallValid 23342 50 := by unfold smallValid; decide +kernel

private theorem sp23392 : smallValid 23392 51 := by unfold smallValid; decide +kernel

private theorem sp23443 : smallValid 23443 51 := by unfold smallValid; decide +kernel

private theorem sp23494 : smallValid 23494 51 := by unfold smallValid; decide +kernel

private theorem sp23545 : smallValid 23545 50 := by unfold smallValid; decide +kernel

private theorem sp23595 : smallValid 23595 51 := by unfold smallValid; decide +kernel

private theorem sp23646 : smallValid 23646 51 := by unfold smallValid; decide +kernel

private theorem sp23697 : smallValid 23697 51 := by unfold smallValid; decide +kernel

private theorem sp23748 : smallValid 23748 50 := by unfold smallValid; decide +kernel

private theorem sp23798 : smallValid 23798 51 := by unfold smallValid; decide +kernel

private theorem sp23849 : smallValid 23849 51 := by unfold smallValid; decide +kernel

private theorem sp23900 : smallValid 23900 51 := by unfold smallValid; decide +kernel

private theorem sp23951 : smallValid 23951 50 := by unfold smallValid; decide +kernel

private theorem sp24001 : smallValid 24001 51 := by unfold smallValid; decide +kernel

private theorem sp24052 : smallValid 24052 51 := by unfold smallValid; decide +kernel

private theorem sp24103 : smallValid 24103 51 := by unfold smallValid; decide +kernel

private theorem sp24154 : smallValid 24154 50 := by unfold smallValid; decide +kernel

private theorem sp24204 : smallValid 24204 51 := by unfold smallValid; decide +kernel

private theorem sp24255 : smallValid 24255 51 := by unfold smallValid; decide +kernel

private theorem sp24306 : smallValid 24306 51 := by unfold smallValid; decide +kernel

private theorem sp24357 : smallValid 24357 50 := by unfold smallValid; decide +kernel

private theorem sp24407 : smallValid 24407 51 := by unfold smallValid; decide +kernel

private theorem sp24458 : smallValid 24458 51 := by unfold smallValid; decide +kernel

private theorem sp24509 : smallValid 24509 51 := by unfold smallValid; decide +kernel

private theorem sp24560 : smallValid 24560 50 := by unfold smallValid; decide +kernel

private theorem sp24610 : smallValid 24610 51 := by unfold smallValid; decide +kernel

private theorem sp24661 : smallValid 24661 51 := by unfold smallValid; decide +kernel

private theorem sp24712 : smallValid 24712 51 := by unfold smallValid; decide +kernel

private theorem sp24763 : smallValid 24763 50 := by unfold smallValid; decide +kernel

private theorem sp24813 : smallValid 24813 51 := by unfold smallValid; decide +kernel

private theorem sp24864 : smallValid 24864 51 := by unfold smallValid; decide +kernel

private theorem sp24915 : smallValid 24915 51 := by unfold smallValid; decide +kernel

private theorem sp24966 : smallValid 24966 50 := by unfold smallValid; decide +kernel

private theorem sp25016 : smallValid 25016 51 := by unfold smallValid; decide +kernel

private theorem sp25067 : smallValid 25067 51 := by unfold smallValid; decide +kernel

private theorem sp25118 : smallValid 25118 51 := by unfold smallValid; decide +kernel

private theorem sp25169 : smallValid 25169 50 := by unfold smallValid; decide +kernel

private theorem sp25219 : smallValid 25219 51 := by unfold smallValid; decide +kernel

private theorem sp25270 : smallValid 25270 51 := by unfold smallValid; decide +kernel

private theorem sp25321 : smallValid 25321 51 := by unfold smallValid; decide +kernel

private theorem sp25372 : smallValid 25372 50 := by unfold smallValid; decide +kernel

private theorem sp25422 : smallValid 25422 51 := by unfold smallValid; decide +kernel

private theorem sp25473 : smallValid 25473 51 := by unfold smallValid; decide +kernel

private theorem sp25524 : smallValid 25524 51 := by unfold smallValid; decide +kernel

private theorem sp25575 : smallValid 25575 50 := by unfold smallValid; decide +kernel

private theorem sp25625 : smallValid 25625 51 := by unfold smallValid; decide +kernel

private theorem sp25676 : smallValid 25676 51 := by unfold smallValid; decide +kernel

private theorem sp25727 : smallValid 25727 51 := by unfold smallValid; decide +kernel

private theorem sp25778 : smallValid 25778 50 := by unfold smallValid; decide +kernel

private theorem sp25828 : smallValid 25828 51 := by unfold smallValid; decide +kernel

private theorem sp25879 : smallValid 25879 51 := by unfold smallValid; decide +kernel

private theorem sp25930 : smallValid 25930 51 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤25980) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 25981 := (joinSmall (lo:=0) (a:=12990) (b:=12991) (joinSmall (lo:=0) (a:=6495) (b:=6495) (joinSmall (lo:=0) (a:=3247) (b:=3248) (joinSmall (lo:=0) (a:=1623) (b:=1624) (joinSmall (lo:=0) (a:=811) (b:=812) (joinSmall (lo:=0) (a:=405) (b:=406) (joinSmall (lo:=0) (a:=202) (b:=203) (joinSmall (lo:=0) (a:=101) (b:=101) (joinSmall (lo:=0) (a:=50) (b:=51) sp0 sp50) (joinSmall (lo:=101) (a:=50) (b:=51) sp101 sp151)) (joinSmall (lo:=202) (a:=101) (b:=102) (joinSmall (lo:=202) (a:=50) (b:=51) sp202 sp252) (joinSmall (lo:=303) (a:=51) (b:=51) sp303 sp354))) (joinSmall (lo:=405) (a:=203) (b:=203) (joinSmall (lo:=405) (a:=101) (b:=102) (joinSmall (lo:=405) (a:=50) (b:=51) sp405 sp455) (joinSmall (lo:=506) (a:=51) (b:=51) sp506 sp557)) (joinSmall (lo:=608) (a:=101) (b:=102) (joinSmall (lo:=608) (a:=50) (b:=51) sp608 sp658) (joinSmall (lo:=709) (a:=51) (b:=51) sp709 sp760)))) (joinSmall (lo:=811) (a:=406) (b:=406) (joinSmall (lo:=811) (a:=203) (b:=203) (joinSmall (lo:=811) (a:=101) (b:=102) (joinSmall (lo:=811) (a:=50) (b:=51) sp811 sp861) (joinSmall (lo:=912) (a:=51) (b:=51) sp912 sp963)) (joinSmall (lo:=1014) (a:=101) (b:=102) (joinSmall (lo:=1014) (a:=50) (b:=51) sp1014 sp1064) (joinSmall (lo:=1115) (a:=51) (b:=51) sp1115 sp1166))) (joinSmall (lo:=1217) (a:=203) (b:=203) (joinSmall (lo:=1217) (a:=101) (b:=102) (joinSmall (lo:=1217) (a:=50) (b:=51) sp1217 sp1267) (joinSmall (lo:=1318) (a:=51) (b:=51) sp1318 sp1369)) (joinSmall (lo:=1420) (a:=101) (b:=102) (joinSmall (lo:=1420) (a:=50) (b:=51) sp1420 sp1470) (joinSmall (lo:=1521) (a:=51) (b:=51) sp1521 sp1572))))) (joinSmall (lo:=1623) (a:=812) (b:=812) (joinSmall (lo:=1623) (a:=406) (b:=406) (joinSmall (lo:=1623) (a:=203) (b:=203) (joinSmall (lo:=1623) (a:=101) (b:=102) (joinSmall (lo:=1623) (a:=50) (b:=51) sp1623 sp1673) (joinSmall (lo:=1724) (a:=51) (b:=51) sp1724 sp1775)) (joinSmall (lo:=1826) (a:=101) (b:=102) (joinSmall (lo:=1826) (a:=50) (b:=51) sp1826 sp1876) (joinSmall (lo:=1927) (a:=51) (b:=51) sp1927 sp1978))) (joinSmall (lo:=2029) (a:=203) (b:=203) (joinSmall (lo:=2029) (a:=101) (b:=102) (joinSmall (lo:=2029) (a:=50) (b:=51) sp2029 sp2079) (joinSmall (lo:=2130) (a:=51) (b:=51) sp2130 sp2181)) (joinSmall (lo:=2232) (a:=101) (b:=102) (joinSmall (lo:=2232) (a:=50) (b:=51) sp2232 sp2282) (joinSmall (lo:=2333) (a:=51) (b:=51) sp2333 sp2384)))) (joinSmall (lo:=2435) (a:=406) (b:=406) (joinSmall (lo:=2435) (a:=203) (b:=203) (joinSmall (lo:=2435) (a:=101) (b:=102) (joinSmall (lo:=2435) (a:=50) (b:=51) sp2435 sp2485) (joinSmall (lo:=2536) (a:=51) (b:=51) sp2536 sp2587)) (joinSmall (lo:=2638) (a:=101) (b:=102) (joinSmall (lo:=2638) (a:=50) (b:=51) sp2638 sp2688) (joinSmall (lo:=2739) (a:=51) (b:=51) sp2739 sp2790))) (joinSmall (lo:=2841) (a:=203) (b:=203) (joinSmall (lo:=2841) (a:=101) (b:=102) (joinSmall (lo:=2841) (a:=50) (b:=51) sp2841 sp2891) (joinSmall (lo:=2942) (a:=51) (b:=51) sp2942 sp2993)) (joinSmall (lo:=3044) (a:=101) (b:=102) (joinSmall (lo:=3044) (a:=50) (b:=51) sp3044 sp3094) (joinSmall (lo:=3145) (a:=51) (b:=51) sp3145 sp3196)))))) (joinSmall (lo:=3247) (a:=1624) (b:=1624) (joinSmall (lo:=3247) (a:=812) (b:=812) (joinSmall (lo:=3247) (a:=406) (b:=406) (joinSmall (lo:=3247) (a:=203) (b:=203) (joinSmall (lo:=3247) (a:=101) (b:=102) (joinSmall (lo:=3247) (a:=50) (b:=51) sp3247 sp3297) (joinSmall (lo:=3348) (a:=51) (b:=51) sp3348 sp3399)) (joinSmall (lo:=3450) (a:=101) (b:=102) (joinSmall (lo:=3450) (a:=50) (b:=51) sp3450 sp3500) (joinSmall (lo:=3551) (a:=51) (b:=51) sp3551 sp3602))) (joinSmall (lo:=3653) (a:=203) (b:=203) (joinSmall (lo:=3653) (a:=101) (b:=102) (joinSmall (lo:=3653) (a:=50) (b:=51) sp3653 sp3703) (joinSmall (lo:=3754) (a:=51) (b:=51) sp3754 sp3805)) (joinSmall (lo:=3856) (a:=101) (b:=102) (joinSmall (lo:=3856) (a:=50) (b:=51) sp3856 sp3906) (joinSmall (lo:=3957) (a:=51) (b:=51) sp3957 sp4008)))) (joinSmall (lo:=4059) (a:=406) (b:=406) (joinSmall (lo:=4059) (a:=203) (b:=203) (joinSmall (lo:=4059) (a:=101) (b:=102) (joinSmall (lo:=4059) (a:=50) (b:=51) sp4059 sp4109) (joinSmall (lo:=4160) (a:=51) (b:=51) sp4160 sp4211)) (joinSmall (lo:=4262) (a:=101) (b:=102) (joinSmall (lo:=4262) (a:=50) (b:=51) sp4262 sp4312) (joinSmall (lo:=4363) (a:=51) (b:=51) sp4363 sp4414))) (joinSmall (lo:=4465) (a:=203) (b:=203) (joinSmall (lo:=4465) (a:=101) (b:=102) (joinSmall (lo:=4465) (a:=50) (b:=51) sp4465 sp4515) (joinSmall (lo:=4566) (a:=51) (b:=51) sp4566 sp4617)) (joinSmall (lo:=4668) (a:=101) (b:=102) (joinSmall (lo:=4668) (a:=50) (b:=51) sp4668 sp4718) (joinSmall (lo:=4769) (a:=51) (b:=51) sp4769 sp4820))))) (joinSmall (lo:=4871) (a:=812) (b:=812) (joinSmall (lo:=4871) (a:=406) (b:=406) (joinSmall (lo:=4871) (a:=203) (b:=203) (joinSmall (lo:=4871) (a:=101) (b:=102) (joinSmall (lo:=4871) (a:=50) (b:=51) sp4871 sp4921) (joinSmall (lo:=4972) (a:=51) (b:=51) sp4972 sp5023)) (joinSmall (lo:=5074) (a:=101) (b:=102) (joinSmall (lo:=5074) (a:=50) (b:=51) sp5074 sp5124) (joinSmall (lo:=5175) (a:=51) (b:=51) sp5175 sp5226))) (joinSmall (lo:=5277) (a:=203) (b:=203) (joinSmall (lo:=5277) (a:=101) (b:=102) (joinSmall (lo:=5277) (a:=50) (b:=51) sp5277 sp5327) (joinSmall (lo:=5378) (a:=51) (b:=51) sp5378 sp5429)) (joinSmall (lo:=5480) (a:=101) (b:=102) (joinSmall (lo:=5480) (a:=50) (b:=51) sp5480 sp5530) (joinSmall (lo:=5581) (a:=51) (b:=51) sp5581 sp5632)))) (joinSmall (lo:=5683) (a:=406) (b:=406) (joinSmall (lo:=5683) (a:=203) (b:=203) (joinSmall (lo:=5683) (a:=101) (b:=102) (joinSmall (lo:=5683) (a:=50) (b:=51) sp5683 sp5733) (joinSmall (lo:=5784) (a:=51) (b:=51) sp5784 sp5835)) (joinSmall (lo:=5886) (a:=101) (b:=102) (joinSmall (lo:=5886) (a:=50) (b:=51) sp5886 sp5936) (joinSmall (lo:=5987) (a:=51) (b:=51) sp5987 sp6038))) (joinSmall (lo:=6089) (a:=203) (b:=203) (joinSmall (lo:=6089) (a:=101) (b:=102) (joinSmall (lo:=6089) (a:=50) (b:=51) sp6089 sp6139) (joinSmall (lo:=6190) (a:=51) (b:=51) sp6190 sp6241)) (joinSmall (lo:=6292) (a:=101) (b:=102) (joinSmall (lo:=6292) (a:=50) (b:=51) sp6292 sp6342) (joinSmall (lo:=6393) (a:=51) (b:=51) sp6393 sp6444))))))) (joinSmall (lo:=6495) (a:=3247) (b:=3248) (joinSmall (lo:=6495) (a:=1623) (b:=1624) (joinSmall (lo:=6495) (a:=811) (b:=812) (joinSmall (lo:=6495) (a:=405) (b:=406) (joinSmall (lo:=6495) (a:=202) (b:=203) (joinSmall (lo:=6495) (a:=101) (b:=101) (joinSmall (lo:=6495) (a:=50) (b:=51) sp6495 sp6545) (joinSmall (lo:=6596) (a:=50) (b:=51) sp6596 sp6646)) (joinSmall (lo:=6697) (a:=101) (b:=102) (joinSmall (lo:=6697) (a:=50) (b:=51) sp6697 sp6747) (joinSmall (lo:=6798) (a:=51) (b:=51) sp6798 sp6849))) (joinSmall (lo:=6900) (a:=203) (b:=203) (joinSmall (lo:=6900) (a:=101) (b:=102) (joinSmall (lo:=6900) (a:=50) (b:=51) sp6900 sp6950) (joinSmall (lo:=7001) (a:=51) (b:=51) sp7001 sp7052)) (joinSmall (lo:=7103) (a:=101) (b:=102) (joinSmall (lo:=7103) (a:=50) (b:=51) sp7103 sp7153) (joinSmall (lo:=7204) (a:=51) (b:=51) sp7204 sp7255)))) (joinSmall (lo:=7306) (a:=406) (b:=406) (joinSmall (lo:=7306) (a:=203) (b:=203) (joinSmall (lo:=7306) (a:=101) (b:=102) (joinSmall (lo:=7306) (a:=50) (b:=51) sp7306 sp7356) (joinSmall (lo:=7407) (a:=51) (b:=51) sp7407 sp7458)) (joinSmall (lo:=7509) (a:=101) (b:=102) (joinSmall (lo:=7509) (a:=50) (b:=51) sp7509 sp7559) (joinSmall (lo:=7610) (a:=51) (b:=51) sp7610 sp7661))) (joinSmall (lo:=7712) (a:=203) (b:=203) (joinSmall (lo:=7712) (a:=101) (b:=102) (joinSmall (lo:=7712) (a:=50) (b:=51) sp7712 sp7762) (joinSmall (lo:=7813) (a:=51) (b:=51) sp7813 sp7864)) (joinSmall (lo:=7915) (a:=101) (b:=102) (joinSmall (lo:=7915) (a:=50) (b:=51) sp7915 sp7965) (joinSmall (lo:=8016) (a:=51) (b:=51) sp8016 sp8067))))) (joinSmall (lo:=8118) (a:=812) (b:=812) (joinSmall (lo:=8118) (a:=406) (b:=406) (joinSmall (lo:=8118) (a:=203) (b:=203) (joinSmall (lo:=8118) (a:=101) (b:=102) (joinSmall (lo:=8118) (a:=50) (b:=51) sp8118 sp8168) (joinSmall (lo:=8219) (a:=51) (b:=51) sp8219 sp8270)) (joinSmall (lo:=8321) (a:=101) (b:=102) (joinSmall (lo:=8321) (a:=50) (b:=51) sp8321 sp8371) (joinSmall (lo:=8422) (a:=51) (b:=51) sp8422 sp8473))) (joinSmall (lo:=8524) (a:=203) (b:=203) (joinSmall (lo:=8524) (a:=101) (b:=102) (joinSmall (lo:=8524) (a:=50) (b:=51) sp8524 sp8574) (joinSmall (lo:=8625) (a:=51) (b:=51) sp8625 sp8676)) (joinSmall (lo:=8727) (a:=101) (b:=102) (joinSmall (lo:=8727) (a:=50) (b:=51) sp8727 sp8777) (joinSmall (lo:=8828) (a:=51) (b:=51) sp8828 sp8879)))) (joinSmall (lo:=8930) (a:=406) (b:=406) (joinSmall (lo:=8930) (a:=203) (b:=203) (joinSmall (lo:=8930) (a:=101) (b:=102) (joinSmall (lo:=8930) (a:=50) (b:=51) sp8930 sp8980) (joinSmall (lo:=9031) (a:=51) (b:=51) sp9031 sp9082)) (joinSmall (lo:=9133) (a:=101) (b:=102) (joinSmall (lo:=9133) (a:=50) (b:=51) sp9133 sp9183) (joinSmall (lo:=9234) (a:=51) (b:=51) sp9234 sp9285))) (joinSmall (lo:=9336) (a:=203) (b:=203) (joinSmall (lo:=9336) (a:=101) (b:=102) (joinSmall (lo:=9336) (a:=50) (b:=51) sp9336 sp9386) (joinSmall (lo:=9437) (a:=51) (b:=51) sp9437 sp9488)) (joinSmall (lo:=9539) (a:=101) (b:=102) (joinSmall (lo:=9539) (a:=50) (b:=51) sp9539 sp9589) (joinSmall (lo:=9640) (a:=51) (b:=51) sp9640 sp9691)))))) (joinSmall (lo:=9742) (a:=1624) (b:=1624) (joinSmall (lo:=9742) (a:=812) (b:=812) (joinSmall (lo:=9742) (a:=406) (b:=406) (joinSmall (lo:=9742) (a:=203) (b:=203) (joinSmall (lo:=9742) (a:=101) (b:=102) (joinSmall (lo:=9742) (a:=50) (b:=51) sp9742 sp9792) (joinSmall (lo:=9843) (a:=51) (b:=51) sp9843 sp9894)) (joinSmall (lo:=9945) (a:=101) (b:=102) (joinSmall (lo:=9945) (a:=50) (b:=51) sp9945 sp9995) (joinSmall (lo:=10046) (a:=51) (b:=51) sp10046 sp10097))) (joinSmall (lo:=10148) (a:=203) (b:=203) (joinSmall (lo:=10148) (a:=101) (b:=102) (joinSmall (lo:=10148) (a:=50) (b:=51) sp10148 sp10198) (joinSmall (lo:=10249) (a:=51) (b:=51) sp10249 sp10300)) (joinSmall (lo:=10351) (a:=101) (b:=102) (joinSmall (lo:=10351) (a:=50) (b:=51) sp10351 sp10401) (joinSmall (lo:=10452) (a:=51) (b:=51) sp10452 sp10503)))) (joinSmall (lo:=10554) (a:=406) (b:=406) (joinSmall (lo:=10554) (a:=203) (b:=203) (joinSmall (lo:=10554) (a:=101) (b:=102) (joinSmall (lo:=10554) (a:=50) (b:=51) sp10554 sp10604) (joinSmall (lo:=10655) (a:=51) (b:=51) sp10655 sp10706)) (joinSmall (lo:=10757) (a:=101) (b:=102) (joinSmall (lo:=10757) (a:=50) (b:=51) sp10757 sp10807) (joinSmall (lo:=10858) (a:=51) (b:=51) sp10858 sp10909))) (joinSmall (lo:=10960) (a:=203) (b:=203) (joinSmall (lo:=10960) (a:=101) (b:=102) (joinSmall (lo:=10960) (a:=50) (b:=51) sp10960 sp11010) (joinSmall (lo:=11061) (a:=51) (b:=51) sp11061 sp11112)) (joinSmall (lo:=11163) (a:=101) (b:=102) (joinSmall (lo:=11163) (a:=50) (b:=51) sp11163 sp11213) (joinSmall (lo:=11264) (a:=51) (b:=51) sp11264 sp11315))))) (joinSmall (lo:=11366) (a:=812) (b:=812) (joinSmall (lo:=11366) (a:=406) (b:=406) (joinSmall (lo:=11366) (a:=203) (b:=203) (joinSmall (lo:=11366) (a:=101) (b:=102) (joinSmall (lo:=11366) (a:=50) (b:=51) sp11366 sp11416) (joinSmall (lo:=11467) (a:=51) (b:=51) sp11467 sp11518)) (joinSmall (lo:=11569) (a:=101) (b:=102) (joinSmall (lo:=11569) (a:=50) (b:=51) sp11569 sp11619) (joinSmall (lo:=11670) (a:=51) (b:=51) sp11670 sp11721))) (joinSmall (lo:=11772) (a:=203) (b:=203) (joinSmall (lo:=11772) (a:=101) (b:=102) (joinSmall (lo:=11772) (a:=50) (b:=51) sp11772 sp11822) (joinSmall (lo:=11873) (a:=51) (b:=51) sp11873 sp11924)) (joinSmall (lo:=11975) (a:=101) (b:=102) (joinSmall (lo:=11975) (a:=50) (b:=51) sp11975 sp12025) (joinSmall (lo:=12076) (a:=51) (b:=51) sp12076 sp12127)))) (joinSmall (lo:=12178) (a:=406) (b:=406) (joinSmall (lo:=12178) (a:=203) (b:=203) (joinSmall (lo:=12178) (a:=101) (b:=102) (joinSmall (lo:=12178) (a:=50) (b:=51) sp12178 sp12228) (joinSmall (lo:=12279) (a:=51) (b:=51) sp12279 sp12330)) (joinSmall (lo:=12381) (a:=101) (b:=102) (joinSmall (lo:=12381) (a:=50) (b:=51) sp12381 sp12431) (joinSmall (lo:=12482) (a:=51) (b:=51) sp12482 sp12533))) (joinSmall (lo:=12584) (a:=203) (b:=203) (joinSmall (lo:=12584) (a:=101) (b:=102) (joinSmall (lo:=12584) (a:=50) (b:=51) sp12584 sp12634) (joinSmall (lo:=12685) (a:=51) (b:=51) sp12685 sp12736)) (joinSmall (lo:=12787) (a:=101) (b:=102) (joinSmall (lo:=12787) (a:=50) (b:=51) sp12787 sp12837) (joinSmall (lo:=12888) (a:=51) (b:=51) sp12888 sp12939)))))))) (joinSmall (lo:=12990) (a:=6495) (b:=6496) (joinSmall (lo:=12990) (a:=3247) (b:=3248) (joinSmall (lo:=12990) (a:=1623) (b:=1624) (joinSmall (lo:=12990) (a:=811) (b:=812) (joinSmall (lo:=12990) (a:=405) (b:=406) (joinSmall (lo:=12990) (a:=202) (b:=203) (joinSmall (lo:=12990) (a:=101) (b:=101) (joinSmall (lo:=12990) (a:=50) (b:=51) sp12990 sp13040) (joinSmall (lo:=13091) (a:=50) (b:=51) sp13091 sp13141)) (joinSmall (lo:=13192) (a:=101) (b:=102) (joinSmall (lo:=13192) (a:=50) (b:=51) sp13192 sp13242) (joinSmall (lo:=13293) (a:=51) (b:=51) sp13293 sp13344))) (joinSmall (lo:=13395) (a:=203) (b:=203) (joinSmall (lo:=13395) (a:=101) (b:=102) (joinSmall (lo:=13395) (a:=50) (b:=51) sp13395 sp13445) (joinSmall (lo:=13496) (a:=51) (b:=51) sp13496 sp13547)) (joinSmall (lo:=13598) (a:=101) (b:=102) (joinSmall (lo:=13598) (a:=50) (b:=51) sp13598 sp13648) (joinSmall (lo:=13699) (a:=51) (b:=51) sp13699 sp13750)))) (joinSmall (lo:=13801) (a:=406) (b:=406) (joinSmall (lo:=13801) (a:=203) (b:=203) (joinSmall (lo:=13801) (a:=101) (b:=102) (joinSmall (lo:=13801) (a:=50) (b:=51) sp13801 sp13851) (joinSmall (lo:=13902) (a:=51) (b:=51) sp13902 sp13953)) (joinSmall (lo:=14004) (a:=101) (b:=102) (joinSmall (lo:=14004) (a:=50) (b:=51) sp14004 sp14054) (joinSmall (lo:=14105) (a:=51) (b:=51) sp14105 sp14156))) (joinSmall (lo:=14207) (a:=203) (b:=203) (joinSmall (lo:=14207) (a:=101) (b:=102) (joinSmall (lo:=14207) (a:=50) (b:=51) sp14207 sp14257) (joinSmall (lo:=14308) (a:=51) (b:=51) sp14308 sp14359)) (joinSmall (lo:=14410) (a:=101) (b:=102) (joinSmall (lo:=14410) (a:=50) (b:=51) sp14410 sp14460) (joinSmall (lo:=14511) (a:=51) (b:=51) sp14511 sp14562))))) (joinSmall (lo:=14613) (a:=812) (b:=812) (joinSmall (lo:=14613) (a:=406) (b:=406) (joinSmall (lo:=14613) (a:=203) (b:=203) (joinSmall (lo:=14613) (a:=101) (b:=102) (joinSmall (lo:=14613) (a:=50) (b:=51) sp14613 sp14663) (joinSmall (lo:=14714) (a:=51) (b:=51) sp14714 sp14765)) (joinSmall (lo:=14816) (a:=101) (b:=102) (joinSmall (lo:=14816) (a:=50) (b:=51) sp14816 sp14866) (joinSmall (lo:=14917) (a:=51) (b:=51) sp14917 sp14968))) (joinSmall (lo:=15019) (a:=203) (b:=203) (joinSmall (lo:=15019) (a:=101) (b:=102) (joinSmall (lo:=15019) (a:=50) (b:=51) sp15019 sp15069) (joinSmall (lo:=15120) (a:=51) (b:=51) sp15120 sp15171)) (joinSmall (lo:=15222) (a:=101) (b:=102) (joinSmall (lo:=15222) (a:=50) (b:=51) sp15222 sp15272) (joinSmall (lo:=15323) (a:=51) (b:=51) sp15323 sp15374)))) (joinSmall (lo:=15425) (a:=406) (b:=406) (joinSmall (lo:=15425) (a:=203) (b:=203) (joinSmall (lo:=15425) (a:=101) (b:=102) (joinSmall (lo:=15425) (a:=50) (b:=51) sp15425 sp15475) (joinSmall (lo:=15526) (a:=51) (b:=51) sp15526 sp15577)) (joinSmall (lo:=15628) (a:=101) (b:=102) (joinSmall (lo:=15628) (a:=50) (b:=51) sp15628 sp15678) (joinSmall (lo:=15729) (a:=51) (b:=51) sp15729 sp15780))) (joinSmall (lo:=15831) (a:=203) (b:=203) (joinSmall (lo:=15831) (a:=101) (b:=102) (joinSmall (lo:=15831) (a:=50) (b:=51) sp15831 sp15881) (joinSmall (lo:=15932) (a:=51) (b:=51) sp15932 sp15983)) (joinSmall (lo:=16034) (a:=101) (b:=102) (joinSmall (lo:=16034) (a:=50) (b:=51) sp16034 sp16084) (joinSmall (lo:=16135) (a:=51) (b:=51) sp16135 sp16186)))))) (joinSmall (lo:=16237) (a:=1624) (b:=1624) (joinSmall (lo:=16237) (a:=812) (b:=812) (joinSmall (lo:=16237) (a:=406) (b:=406) (joinSmall (lo:=16237) (a:=203) (b:=203) (joinSmall (lo:=16237) (a:=101) (b:=102) (joinSmall (lo:=16237) (a:=50) (b:=51) sp16237 sp16287) (joinSmall (lo:=16338) (a:=51) (b:=51) sp16338 sp16389)) (joinSmall (lo:=16440) (a:=101) (b:=102) (joinSmall (lo:=16440) (a:=50) (b:=51) sp16440 sp16490) (joinSmall (lo:=16541) (a:=51) (b:=51) sp16541 sp16592))) (joinSmall (lo:=16643) (a:=203) (b:=203) (joinSmall (lo:=16643) (a:=101) (b:=102) (joinSmall (lo:=16643) (a:=50) (b:=51) sp16643 sp16693) (joinSmall (lo:=16744) (a:=51) (b:=51) sp16744 sp16795)) (joinSmall (lo:=16846) (a:=101) (b:=102) (joinSmall (lo:=16846) (a:=50) (b:=51) sp16846 sp16896) (joinSmall (lo:=16947) (a:=51) (b:=51) sp16947 sp16998)))) (joinSmall (lo:=17049) (a:=406) (b:=406) (joinSmall (lo:=17049) (a:=203) (b:=203) (joinSmall (lo:=17049) (a:=101) (b:=102) (joinSmall (lo:=17049) (a:=50) (b:=51) sp17049 sp17099) (joinSmall (lo:=17150) (a:=51) (b:=51) sp17150 sp17201)) (joinSmall (lo:=17252) (a:=101) (b:=102) (joinSmall (lo:=17252) (a:=50) (b:=51) sp17252 sp17302) (joinSmall (lo:=17353) (a:=51) (b:=51) sp17353 sp17404))) (joinSmall (lo:=17455) (a:=203) (b:=203) (joinSmall (lo:=17455) (a:=101) (b:=102) (joinSmall (lo:=17455) (a:=50) (b:=51) sp17455 sp17505) (joinSmall (lo:=17556) (a:=51) (b:=51) sp17556 sp17607)) (joinSmall (lo:=17658) (a:=101) (b:=102) (joinSmall (lo:=17658) (a:=50) (b:=51) sp17658 sp17708) (joinSmall (lo:=17759) (a:=51) (b:=51) sp17759 sp17810))))) (joinSmall (lo:=17861) (a:=812) (b:=812) (joinSmall (lo:=17861) (a:=406) (b:=406) (joinSmall (lo:=17861) (a:=203) (b:=203) (joinSmall (lo:=17861) (a:=101) (b:=102) (joinSmall (lo:=17861) (a:=50) (b:=51) sp17861 sp17911) (joinSmall (lo:=17962) (a:=51) (b:=51) sp17962 sp18013)) (joinSmall (lo:=18064) (a:=101) (b:=102) (joinSmall (lo:=18064) (a:=50) (b:=51) sp18064 sp18114) (joinSmall (lo:=18165) (a:=51) (b:=51) sp18165 sp18216))) (joinSmall (lo:=18267) (a:=203) (b:=203) (joinSmall (lo:=18267) (a:=101) (b:=102) (joinSmall (lo:=18267) (a:=50) (b:=51) sp18267 sp18317) (joinSmall (lo:=18368) (a:=51) (b:=51) sp18368 sp18419)) (joinSmall (lo:=18470) (a:=101) (b:=102) (joinSmall (lo:=18470) (a:=50) (b:=51) sp18470 sp18520) (joinSmall (lo:=18571) (a:=51) (b:=51) sp18571 sp18622)))) (joinSmall (lo:=18673) (a:=406) (b:=406) (joinSmall (lo:=18673) (a:=203) (b:=203) (joinSmall (lo:=18673) (a:=101) (b:=102) (joinSmall (lo:=18673) (a:=50) (b:=51) sp18673 sp18723) (joinSmall (lo:=18774) (a:=51) (b:=51) sp18774 sp18825)) (joinSmall (lo:=18876) (a:=101) (b:=102) (joinSmall (lo:=18876) (a:=50) (b:=51) sp18876 sp18926) (joinSmall (lo:=18977) (a:=51) (b:=51) sp18977 sp19028))) (joinSmall (lo:=19079) (a:=203) (b:=203) (joinSmall (lo:=19079) (a:=101) (b:=102) (joinSmall (lo:=19079) (a:=50) (b:=51) sp19079 sp19129) (joinSmall (lo:=19180) (a:=51) (b:=51) sp19180 sp19231)) (joinSmall (lo:=19282) (a:=101) (b:=102) (joinSmall (lo:=19282) (a:=50) (b:=51) sp19282 sp19332) (joinSmall (lo:=19383) (a:=51) (b:=51) sp19383 sp19434))))))) (joinSmall (lo:=19485) (a:=3248) (b:=3248) (joinSmall (lo:=19485) (a:=1624) (b:=1624) (joinSmall (lo:=19485) (a:=812) (b:=812) (joinSmall (lo:=19485) (a:=406) (b:=406) (joinSmall (lo:=19485) (a:=203) (b:=203) (joinSmall (lo:=19485) (a:=101) (b:=102) (joinSmall (lo:=19485) (a:=50) (b:=51) sp19485 sp19535) (joinSmall (lo:=19586) (a:=51) (b:=51) sp19586 sp19637)) (joinSmall (lo:=19688) (a:=101) (b:=102) (joinSmall (lo:=19688) (a:=50) (b:=51) sp19688 sp19738) (joinSmall (lo:=19789) (a:=51) (b:=51) sp19789 sp19840))) (joinSmall (lo:=19891) (a:=203) (b:=203) (joinSmall (lo:=19891) (a:=101) (b:=102) (joinSmall (lo:=19891) (a:=50) (b:=51) sp19891 sp19941) (joinSmall (lo:=19992) (a:=51) (b:=51) sp19992 sp20043)) (joinSmall (lo:=20094) (a:=101) (b:=102) (joinSmall (lo:=20094) (a:=50) (b:=51) sp20094 sp20144) (joinSmall (lo:=20195) (a:=51) (b:=51) sp20195 sp20246)))) (joinSmall (lo:=20297) (a:=406) (b:=406) (joinSmall (lo:=20297) (a:=203) (b:=203) (joinSmall (lo:=20297) (a:=101) (b:=102) (joinSmall (lo:=20297) (a:=50) (b:=51) sp20297 sp20347) (joinSmall (lo:=20398) (a:=51) (b:=51) sp20398 sp20449)) (joinSmall (lo:=20500) (a:=101) (b:=102) (joinSmall (lo:=20500) (a:=50) (b:=51) sp20500 sp20550) (joinSmall (lo:=20601) (a:=51) (b:=51) sp20601 sp20652))) (joinSmall (lo:=20703) (a:=203) (b:=203) (joinSmall (lo:=20703) (a:=101) (b:=102) (joinSmall (lo:=20703) (a:=50) (b:=51) sp20703 sp20753) (joinSmall (lo:=20804) (a:=51) (b:=51) sp20804 sp20855)) (joinSmall (lo:=20906) (a:=101) (b:=102) (joinSmall (lo:=20906) (a:=50) (b:=51) sp20906 sp20956) (joinSmall (lo:=21007) (a:=51) (b:=51) sp21007 sp21058))))) (joinSmall (lo:=21109) (a:=812) (b:=812) (joinSmall (lo:=21109) (a:=406) (b:=406) (joinSmall (lo:=21109) (a:=203) (b:=203) (joinSmall (lo:=21109) (a:=101) (b:=102) (joinSmall (lo:=21109) (a:=50) (b:=51) sp21109 sp21159) (joinSmall (lo:=21210) (a:=51) (b:=51) sp21210 sp21261)) (joinSmall (lo:=21312) (a:=101) (b:=102) (joinSmall (lo:=21312) (a:=50) (b:=51) sp21312 sp21362) (joinSmall (lo:=21413) (a:=51) (b:=51) sp21413 sp21464))) (joinSmall (lo:=21515) (a:=203) (b:=203) (joinSmall (lo:=21515) (a:=101) (b:=102) (joinSmall (lo:=21515) (a:=50) (b:=51) sp21515 sp21565) (joinSmall (lo:=21616) (a:=51) (b:=51) sp21616 sp21667)) (joinSmall (lo:=21718) (a:=101) (b:=102) (joinSmall (lo:=21718) (a:=50) (b:=51) sp21718 sp21768) (joinSmall (lo:=21819) (a:=51) (b:=51) sp21819 sp21870)))) (joinSmall (lo:=21921) (a:=406) (b:=406) (joinSmall (lo:=21921) (a:=203) (b:=203) (joinSmall (lo:=21921) (a:=101) (b:=102) (joinSmall (lo:=21921) (a:=50) (b:=51) sp21921 sp21971) (joinSmall (lo:=22022) (a:=51) (b:=51) sp22022 sp22073)) (joinSmall (lo:=22124) (a:=101) (b:=102) (joinSmall (lo:=22124) (a:=50) (b:=51) sp22124 sp22174) (joinSmall (lo:=22225) (a:=51) (b:=51) sp22225 sp22276))) (joinSmall (lo:=22327) (a:=203) (b:=203) (joinSmall (lo:=22327) (a:=101) (b:=102) (joinSmall (lo:=22327) (a:=50) (b:=51) sp22327 sp22377) (joinSmall (lo:=22428) (a:=51) (b:=51) sp22428 sp22479)) (joinSmall (lo:=22530) (a:=101) (b:=102) (joinSmall (lo:=22530) (a:=50) (b:=51) sp22530 sp22580) (joinSmall (lo:=22631) (a:=51) (b:=51) sp22631 sp22682)))))) (joinSmall (lo:=22733) (a:=1624) (b:=1624) (joinSmall (lo:=22733) (a:=812) (b:=812) (joinSmall (lo:=22733) (a:=406) (b:=406) (joinSmall (lo:=22733) (a:=203) (b:=203) (joinSmall (lo:=22733) (a:=101) (b:=102) (joinSmall (lo:=22733) (a:=50) (b:=51) sp22733 sp22783) (joinSmall (lo:=22834) (a:=51) (b:=51) sp22834 sp22885)) (joinSmall (lo:=22936) (a:=101) (b:=102) (joinSmall (lo:=22936) (a:=50) (b:=51) sp22936 sp22986) (joinSmall (lo:=23037) (a:=51) (b:=51) sp23037 sp23088))) (joinSmall (lo:=23139) (a:=203) (b:=203) (joinSmall (lo:=23139) (a:=101) (b:=102) (joinSmall (lo:=23139) (a:=50) (b:=51) sp23139 sp23189) (joinSmall (lo:=23240) (a:=51) (b:=51) sp23240 sp23291)) (joinSmall (lo:=23342) (a:=101) (b:=102) (joinSmall (lo:=23342) (a:=50) (b:=51) sp23342 sp23392) (joinSmall (lo:=23443) (a:=51) (b:=51) sp23443 sp23494)))) (joinSmall (lo:=23545) (a:=406) (b:=406) (joinSmall (lo:=23545) (a:=203) (b:=203) (joinSmall (lo:=23545) (a:=101) (b:=102) (joinSmall (lo:=23545) (a:=50) (b:=51) sp23545 sp23595) (joinSmall (lo:=23646) (a:=51) (b:=51) sp23646 sp23697)) (joinSmall (lo:=23748) (a:=101) (b:=102) (joinSmall (lo:=23748) (a:=50) (b:=51) sp23748 sp23798) (joinSmall (lo:=23849) (a:=51) (b:=51) sp23849 sp23900))) (joinSmall (lo:=23951) (a:=203) (b:=203) (joinSmall (lo:=23951) (a:=101) (b:=102) (joinSmall (lo:=23951) (a:=50) (b:=51) sp23951 sp24001) (joinSmall (lo:=24052) (a:=51) (b:=51) sp24052 sp24103)) (joinSmall (lo:=24154) (a:=101) (b:=102) (joinSmall (lo:=24154) (a:=50) (b:=51) sp24154 sp24204) (joinSmall (lo:=24255) (a:=51) (b:=51) sp24255 sp24306))))) (joinSmall (lo:=24357) (a:=812) (b:=812) (joinSmall (lo:=24357) (a:=406) (b:=406) (joinSmall (lo:=24357) (a:=203) (b:=203) (joinSmall (lo:=24357) (a:=101) (b:=102) (joinSmall (lo:=24357) (a:=50) (b:=51) sp24357 sp24407) (joinSmall (lo:=24458) (a:=51) (b:=51) sp24458 sp24509)) (joinSmall (lo:=24560) (a:=101) (b:=102) (joinSmall (lo:=24560) (a:=50) (b:=51) sp24560 sp24610) (joinSmall (lo:=24661) (a:=51) (b:=51) sp24661 sp24712))) (joinSmall (lo:=24763) (a:=203) (b:=203) (joinSmall (lo:=24763) (a:=101) (b:=102) (joinSmall (lo:=24763) (a:=50) (b:=51) sp24763 sp24813) (joinSmall (lo:=24864) (a:=51) (b:=51) sp24864 sp24915)) (joinSmall (lo:=24966) (a:=101) (b:=102) (joinSmall (lo:=24966) (a:=50) (b:=51) sp24966 sp25016) (joinSmall (lo:=25067) (a:=51) (b:=51) sp25067 sp25118)))) (joinSmall (lo:=25169) (a:=406) (b:=406) (joinSmall (lo:=25169) (a:=203) (b:=203) (joinSmall (lo:=25169) (a:=101) (b:=102) (joinSmall (lo:=25169) (a:=50) (b:=51) sp25169 sp25219) (joinSmall (lo:=25270) (a:=51) (b:=51) sp25270 sp25321)) (joinSmall (lo:=25372) (a:=101) (b:=102) (joinSmall (lo:=25372) (a:=50) (b:=51) sp25372 sp25422) (joinSmall (lo:=25473) (a:=51) (b:=51) sp25473 sp25524))) (joinSmall (lo:=25575) (a:=203) (b:=203) (joinSmall (lo:=25575) (a:=101) (b:=102) (joinSmall (lo:=25575) (a:=50) (b:=51) sp25575 sp25625) (joinSmall (lo:=25676) (a:=51) (b:=51) sp25676 sp25727)) (joinSmall (lo:=25778) (a:=101) (b:=102) (joinSmall (lo:=25778) (a:=50) (b:=51) sp25778 sp25828) (joinSmall (lo:=25879) (a:=51) (b:=51) sp25879 sp25930)))))))))
  have good : (List.range 25981).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 675000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 25980 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 25980 := by
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


private def packet (i : ℕ) : ℕ := (if i < 172 then (if i < 86 then (if i < 43 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 7 then (if i < 6 then 0 else 0) else (if i < 8 then 0 else (if i < 9 then 0 else 0)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 0))) else (if i < 18 then (if i < 16 then 0 else (if i < 17 then 0 else 0)) else (if i < 19 then 0 else (if i < 20 then 0 else 0))))) else (if i < 32 then (if i < 26 then (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else (if i < 25 then 0 else 0))) else (if i < 29 then (if i < 27 then 0 else (if i < 28 then 0 else 0)) else (if i < 30 then 0 else (if i < 31 then 0 else 0)))) else (if i < 37 then (if i < 34 then (if i < 33 then 0 else 0) else (if i < 35 then 0 else (if i < 36 then 0 else 0))) else (if i < 40 then (if i < 38 then 0 else (if i < 39 then 0 else 0)) else (if i < 41 then 0 else (if i < 42 then 0 else 0)))))) else (if i < 64 then (if i < 53 then (if i < 48 then (if i < 45 then (if i < 44 then 0 else 0) else (if i < 46 then 0 else (if i < 47 then 0 else 0))) else (if i < 50 then (if i < 49 then 0 else 0) else (if i < 51 then 0 else (if i < 52 then 0 else 0)))) else (if i < 58 then (if i < 55 then (if i < 54 then 0 else 0) else (if i < 56 then 0 else (if i < 57 then 0 else 0))) else (if i < 61 then (if i < 59 then 0 else (if i < 60 then 0 else 0)) else (if i < 62 then 0 else (if i < 63 then 0 else 0))))) else (if i < 75 then (if i < 69 then (if i < 66 then (if i < 65 then 0 else 0) else (if i < 67 then 0 else (if i < 68 then 0 else 0))) else (if i < 72 then (if i < 70 then 0 else (if i < 71 then 0 else 0)) else (if i < 73 then 0 else (if i < 74 then 0 else 0)))) else (if i < 80 then (if i < 77 then (if i < 76 then 0 else 0) else (if i < 78 then 0 else (if i < 79 then 0 else 0))) else (if i < 83 then (if i < 81 then 0 else (if i < 82 then 0 else 0)) else (if i < 84 then 0 else (if i < 85 then 0 else 0))))))) else (if i < 129 then (if i < 107 then (if i < 96 then (if i < 91 then (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else (if i < 90 then 0 else 0))) else (if i < 93 then (if i < 92 then 0 else 0) else (if i < 94 then 0 else (if i < 95 then 0 else 0)))) else (if i < 101 then (if i < 98 then (if i < 97 then 0 else 0) else (if i < 99 then 0 else (if i < 100 then 0 else 0))) else (if i < 104 then (if i < 102 then 0 else (if i < 103 then 0 else 0)) else (if i < 105 then 0 else (if i < 106 then 0 else 0))))) else (if i < 118 then (if i < 112 then (if i < 109 then (if i < 108 then 0 else 0) else (if i < 110 then 0 else (if i < 111 then 0 else 0))) else (if i < 115 then (if i < 113 then 0 else (if i < 114 then 0 else 0)) else (if i < 116 then 0 else (if i < 117 then 0 else 0)))) else (if i < 123 then (if i < 120 then (if i < 119 then 0 else 0) else (if i < 121 then 0 else (if i < 122 then 0 else 0))) else (if i < 126 then (if i < 124 then 0 else (if i < 125 then 0 else 0)) else (if i < 127 then 0 else (if i < 128 then 0 else 0)))))) else (if i < 150 then (if i < 139 then (if i < 134 then (if i < 131 then (if i < 130 then 0 else 0) else (if i < 132 then 0 else (if i < 133 then 0 else 0))) else (if i < 136 then (if i < 135 then 0 else 0) else (if i < 137 then 0 else (if i < 138 then 0 else 0)))) else (if i < 144 then (if i < 141 then (if i < 140 then 0 else 0) else (if i < 142 then 0 else (if i < 143 then 0 else 0))) else (if i < 147 then (if i < 145 then 0 else (if i < 146 then 0 else 0)) else (if i < 148 then 0 else (if i < 149 then 0 else 0))))) else (if i < 161 then (if i < 155 then (if i < 152 then (if i < 151 then 0 else 0) else (if i < 153 then 0 else (if i < 154 then 0 else 0))) else (if i < 158 then (if i < 156 then 0 else (if i < 157 then 0 else 0)) else (if i < 159 then 0 else (if i < 160 then 0 else 0)))) else (if i < 166 then (if i < 163 then (if i < 162 then 0 else 0) else (if i < 164 then 0 else (if i < 165 then 0 else 0))) else (if i < 169 then (if i < 167 then 0 else (if i < 168 then 0 else 0)) else (if i < 170 then 0 else (if i < 171 then 0 else 0)))))))) else (if i < 258 then (if i < 215 then (if i < 193 then (if i < 182 then (if i < 177 then (if i < 174 then (if i < 173 then 0 else 0) else (if i < 175 then 0 else (if i < 176 then 0 else 0))) else (if i < 179 then (if i < 178 then 0 else 0) else (if i < 180 then 0 else (if i < 181 then 0 else 0)))) else (if i < 187 then (if i < 184 then (if i < 183 then 0 else 0) else (if i < 185 then 0 else (if i < 186 then 0 else 0))) else (if i < 190 then (if i < 188 then 0 else (if i < 189 then 0 else 0)) else (if i < 191 then 0 else (if i < 192 then 0 else 0))))) else (if i < 204 then (if i < 198 then (if i < 195 then (if i < 194 then 0 else 0) else (if i < 196 then 0 else (if i < 197 then 0 else 0))) else (if i < 201 then (if i < 199 then 0 else (if i < 200 then 0 else 0)) else (if i < 202 then 0 else (if i < 203 then 0 else 0)))) else (if i < 209 then (if i < 206 then (if i < 205 then 0 else 0) else (if i < 207 then 0 else (if i < 208 then 0 else 0))) else (if i < 212 then (if i < 210 then 0 else (if i < 211 then 0 else 0)) else (if i < 213 then 0 else (if i < 214 then 0 else 0)))))) else (if i < 236 then (if i < 225 then (if i < 220 then (if i < 217 then (if i < 216 then 0 else 0) else (if i < 218 then 0 else (if i < 219 then 0 else 0))) else (if i < 222 then (if i < 221 then 0 else 0) else (if i < 223 then 0 else (if i < 224 then 0 else 0)))) else (if i < 230 then (if i < 227 then (if i < 226 then 0 else 0) else (if i < 228 then 0 else (if i < 229 then 0 else 0))) else (if i < 233 then (if i < 231 then 0 else (if i < 232 then 0 else 0)) else (if i < 234 then 0 else (if i < 235 then 0 else 0))))) else (if i < 247 then (if i < 241 then (if i < 238 then (if i < 237 then 0 else 0) else (if i < 239 then 0 else (if i < 240 then 0 else 0))) else (if i < 244 then (if i < 242 then 0 else (if i < 243 then 0 else 0)) else (if i < 245 then 0 else (if i < 246 then 0 else 0)))) else (if i < 252 then (if i < 249 then (if i < 248 then 0 else 0) else (if i < 250 then 0 else (if i < 251 then 0 else 0))) else (if i < 255 then (if i < 253 then 0 else (if i < 254 then 0 else 0)) else (if i < 256 then 0 else (if i < 257 then 0 else 0))))))) else (if i < 301 then (if i < 279 then (if i < 268 then (if i < 263 then (if i < 260 then (if i < 259 then 0 else 0) else (if i < 261 then 0 else (if i < 262 then 0 else 0))) else (if i < 265 then (if i < 264 then 0 else 0) else (if i < 266 then 0 else (if i < 267 then 0 else 0)))) else (if i < 273 then (if i < 270 then (if i < 269 then 0 else 0) else (if i < 271 then 0 else (if i < 272 then 0 else 0))) else (if i < 276 then (if i < 274 then 0 else (if i < 275 then 0 else 0)) else (if i < 277 then 0 else (if i < 278 then 0 else 0))))) else (if i < 290 then (if i < 284 then (if i < 281 then (if i < 280 then 0 else 0) else (if i < 282 then 0 else (if i < 283 then 0 else 0))) else (if i < 287 then (if i < 285 then 0 else (if i < 286 then 0 else 0)) else (if i < 288 then 0 else (if i < 289 then 0 else 0)))) else (if i < 295 then (if i < 292 then (if i < 291 then 0 else 0) else (if i < 293 then 0 else (if i < 294 then 0 else 0))) else (if i < 298 then (if i < 296 then 0 else (if i < 297 then 0 else 0)) else (if i < 299 then 0 else (if i < 300 then 0 else 0)))))) else (if i < 322 then (if i < 311 then (if i < 306 then (if i < 303 then (if i < 302 then 0 else 0) else (if i < 304 then 0 else (if i < 305 then 0 else 0))) else (if i < 308 then (if i < 307 then 0 else 0) else (if i < 309 then 0 else (if i < 310 then 0 else 0)))) else (if i < 316 then (if i < 313 then (if i < 312 then 0 else 0) else (if i < 314 then 0 else (if i < 315 then 0 else 0))) else (if i < 319 then (if i < 317 then 0 else (if i < 318 then 0 else 0)) else (if i < 320 then 0 else (if i < 321 then 0 else 0))))) else (if i < 333 then (if i < 327 then (if i < 324 then (if i < 323 then 0 else 0) else (if i < 325 then 0 else (if i < 326 then 0 else 0))) else (if i < 330 then (if i < 328 then 0 else (if i < 329 then 0 else 0)) else (if i < 331 then 0x20434fe2c814e09c448d2140f506f630e15f89643de18e09503380b800002042ef62d094f49aa4812100f1c6e430815b89483c418009202fc0b60000204290e2c2147096e45c1fd8e946a22ed14108d83ac17a09583140ba000020422f22e315809ea4952180f206be2f815108f43ba17908903000cc00002041d102c394d09b247f2128f206be30a15389103d018c09783580cc0000204174c2b193ec94a44e1fb8e6466c2de14588e43d218209302e40ce0000204114c2cf15149bc48520d0edc6b02ef14c08c439816d08a82f80ca00002040b712c114bc99846a2020e486622e0145889c39a17f09483080ba000020405842ca14d09ac47020d8ee86bc2fc15709503dc19109a034c0d80000203ff882d415149e24852178f406d630415489303c4180097831c0ca0000203f9772d514fc9b647d2118f206d030314e08f43b418909503440da0000203f3a92b714689804672020ea069a2ef145889839c17208b02e40b80000203edc32c294a899847920e0ef46ac30014e09283b018008e03080c40000203e7d22c3149c98e46d2058ea86a02f214b08e83a217b08d02e00b40000203e2052b4143895e45c1f90e306542d814288e03c017c09402e80be0000203dc022d114f49bc47b2138f286c62fa15189003cc18109082f80b60000203d6162c294a49824692090f106c830814f88fc3c217a08d83040ba0000203d0202bf94a49be48120a8edc6c6301154093c3de19309903380c20000203c9fc2de956c9f649821d8f846f431315b09443d018408f82fc0c20000203c4312b7944c9544581fd0e606842e214008b03c217d08c02f40b00000203be4f2c614d898a4692078ee06b830014f89083ce18b09703080b80000203b86c2c4149c99246a2088eb86a62ef14908c83b617908b02bc0a80000203b25b2d095049be47c2120f006b62f014608d03aa176087029c0b00000203ac612cc14cc9a44752090efc6dc30114f89043d018209083080bc0000203a6552d715189ce48120c0ef06c230714f08fc3c018108d03000ce0000203a0792c0148497e4642050eb06802e714288ac39c17108d02e00c800002039a952c594bc9924671f70e446722db13f088c39016408782ac0a8000020394a12ce14f89c44862130f146d830515308f03b817908982ec0c200002038eac2ce94f49b44832108f286ce30714f88f83b017e09083100ca000020388cf2bd148098e47020a0ec86c22fe15189143da18709383340cc000020382f62bc94a099046a2098ef06c830315109183bc18309403300ce00002037ced2d6952c9e849421b8f386b430414e88f83b217a08c02e40ac0000203771b2bb944896044b1f50e4066a2d9140088838016b08202d80bc000020371422be948c98846b2050ea86a430215309003ac18109002d00b600002036b712bb94449664531fc0e8468a2e7143089039216f08c03280c80000203656d2d014ec9b047b2108f146d231015589343d618509002f00ae00002035f802c814d89b647520e0edc6b22ee14788b039a17308682b80b0000020359b12b8146c9664551f68e406682e214288a43a617608b82d00c8000020353b62cc14b09b047120b8e986842df14688e43a617308f82b80bc00002034dc82c714b89ae47d20e8ee06c831215789183cc18008d83100b8000020347a42de15849f04a021b8f5c6e031215b09443e619409303080ca000020341a82d095089bc4832158f1c6d630f15688fc3c2183094031c0d000002033bce2bf94649824632040e9c68a2e8144089039217708602cc0c4000020335ca2d214f89c248520c8f006b430315008f43d018709503300de0000203302d2a293ac9284441f20e3c65c2d013e888439017108882cc0b200002032a542b614409664551f70e446782ef14d89043c418308f82d40b0000020324462da95089ba47020e0eec6b82f014a88a03aa16f08d82e40b000002031e5e2c914bc98e47420b8ef46a22e614588ac39417408602d80c6000020318762c2149099a47020c8ef06be2fa14a08d83ac17908d02e00c0000020312812cd14f89b847a2060ebc68c2e013e88b03aa17909083140ce00002030c8c2c914f49d04902188f3c6fc32616509a03ec19f09b03680d2000020306ba2b6140c94c4491fa0e4865a2d413c088037a16408282b00aa000020300ac2d515189d048520d8ed86c02f914d08c83a2182099032c0c60000202fadb2b794549764561fe0e6c67e2ea147888c39216f08602b40aa0000202f4e92ca94c09944702040e8c68e2eb14908d43d0185099832c0ce0000202ef1d2b4943096a4572010e946902eb14788c83a217d090831c0ce0000202e9172d415149bc47820a0ecc6b22f0145088039416208802ec0ae0000202e32b2c414b89a647520c8ed86a230014f09043ca17f09403180b40000202dd3a2ca94c09de4842118f206a42f415188e439a17609083140c20000202d7452c694c499246a20c8f006c430915389183ba18308e83000c00000202d1742b493f494c4481f88e586762da14608c439e17908a02d00c60000202cb6a2dc1580a0c4a72200f386ee30614f890c3b818709183280c40000202c57f2c914f49ac47f2118f146bc30415409003d018409603440e00000202bfbb2b5142096e4601fc0e746862e614888d83b817f08e82e00ba000 else (if i < 332 then 0x205aeb52d795749f249e2208f906f431a157093c3e418f09603380c60000205a8d82c014789724511fd0ea46882e914188c43bc182092031c0ce0000205a2ff2b8944897e45b1f90e506862ec14788ac3ac17908e82f80b200002059cf52d115149ce4822120f306cc30f15a09443da19509383000b8000020597122c714a897c4692078ea86a42eb14708d43a617708902d40a0000020591162ca94dc9b44752140f106c82ff14b08dc39e18209183200b800002058b232c794d898446b2050ea06922ef14588c83ac18609282f00ae000020585172d6152c9d44852130f186c2306151090c3c4185098031c0cc00002057f512b6146096e45a1ff8e946a62f314988d439817608e82e00c40000205794c2cc95089a24762090ee46a82f014b08f43a817c08982f40bc0000205735d2ca94a099246920e0f2c6da30a15288e83ba17e091831c0ca00002056da32b3143495444a1fa8e5c67e2e313f888839a17908c82f80c4000020567b72c6148898c46d2018e8c6882dd142889439016b08b82f40aa000020561e92bb14949804551ff8e706942e714a88ac38a16908882d40b400002055bfe2c914c49a847420d0ed46b830015008e83ba18c09483140d40000205562d2be148496e4621fe0e7066a2d713d88843a017a08c82e80b80000205504c2c294ac98e4612000e9468c2cf13a886438e17408a02f00be00002054a6c2bf14ac99e4712070ec46b22fe14d88ec3b017208703240b4000020544932c1147896c4572000ea06882ec14408903a017008a82e40b200002053e9d2cb14c499a4762080ec86b22f714e88ec39e17808c03040c2000020538ba2c394b49ac4852120efc6be307150091c3d618608d03080c2000020532c22ce950c9d24842100f106c4308156092c3d618e09783280c400002052cd52c814c89b04772100ec06a02f414788a038c17d08f030c0b2000020526d52d095189ce47c2140f346c430a158891c3ce18809383000ba000020520ef2c014b09a04622040eb869e2e814608a838e16808782d40b000002051b0a2c394a899e47820b8ef86b82f914b08cc3aa17308a02c00b0000020515272c414bc9a246c20d0ee86a42ee141887839216c08b02cc0a800002050f442c394a099c46c2060ee06ac2e313f886837816608782d40b20000205095e2c014b49984752090ea469c2ed14508a83b017408702f80a8000020503732c1147497c4631ff8e7068e2f414d89043bc18209103080c60000204fdb02b1944096a4531fb8e6c6762dc143889839816d08c82e00be0000204f7b12ce94d09b847d2160f346e230515a89503da18309903380c40000204f1d32ba946897446b2010e8c6802f214a08e039c17508d82e80c20000204ebe92c714e09a247820f8f146ca30915109103d418308f82f80b60000204e6162b4946896845b1f70e5867c2d813a087437e16308a82cc0be0000204e02c2cb94cc9a247820e0ee46b430114c08d03c218d09282f80ba0000204da332cf15009ba47520d8efc6d030a15289243c4186095031c0c80000204d4472cb14cc9a04652078ebc69e2ee14b88c439016908a82f40be0000204ce792b7142496e4632058ec06ac30014e092c3ce18608d02e80bc0000204c8ba2af94089544521fc0e746782df13d088038e16508282a409c0000204c2c62ce14c49b04722090ee46a82f514b08f43b217b08f82f00d00000204bd062ae93f893c43c1f08e1864e2d613d886c37a16008302e40be0000204b7302be94b098046c2070eac6962fd14d08f43ba17608a03000ca0000204b1292d3953c9e649021c8f486d630c15609183d018709283240c60000204ab442c0948c99c4702088edc6b230815709343d018908f83040b40000204a5632bd94989824662038e706742db14b88f43c217d09283140b800002049f742cc14a89a64782038e946942ef14b88e43a616608382b009c000020499772cd14c49a047020b8eb86b42fa14b890c3d618c09503240d00000204936e2cf15189d448a20c8efc6be2fd15088c43b018109002e40bc00002048d7f2c914e49c24882160f2c6ce31215208e83ae17608b82d00a6000020487a02c194a898e4661fe8e8468c2e013f887c39016c08402d80bc000020481942d995609ea49521e0f6c6e430d15408fc3cc18609283040c200002047bbd2c194809864692098edc6a22f514c08d83a617708982d80a8000020475dc2c494ac99a4782090edc6aa2ee14488d83aa17a08f03040ae00002046ff52c514c89a24752080ea869e2f814d08fc3ba18b09203100d200002046a032c714bc9a64672030eb468a2dd14488bc3a217608c02ec0c2000020464152cb14c49b04712058eb06b230415109143ea19109203000ba00002045e2e2c414b09a64712088eb86942fa149089039e17f08982c40920000204582c2d295289ce48320c8efc6b62fa15109243d417d09083080b40000204526c2af141095a44e1f90e646662cf13b086c38c17408c83040ae00002044c942ba946497c45c1ff8eac6b62ef14408b039e16e08a82e00c4000020446ad2be148896e4521fc0e846822e814888d03c017708702b80aa000020440d92bc148497e45a2060e9c6902e5141888838816808502d00c400002043ae32d215189ca4802130f146d031115489283d018f09a83680e0000 else 0x20729aa2c694d099446d20f0f106ce30615509183bc18608e03180ca000020723ba2c2149497e4572038e846942e114288983b018308e02e40b600002071db92d614f49be48b2158f246c82ff15489403d818e09383180c4000020717db2c114c49a04762098ee46be30715a09003cc18108e02f40c0000020711f32c514bc9a446c2038e8867a2de14308c03a817d08e831c0ca00002070c0a2c714dc9a046f20a0eb468c2da14688b439e17008802b009e000020706042d3151c9d04852120f106ca30715289083c217d08f82e80b6000020700282be148496e45e1ff0e7066e2e014208b439016f08982d40ba0000206fa492c194649904632020e986aa2fa14c88ec3ba17d08982f40ba0000206f47d2b6143897245d1fd8e7c67e2ec14a08ec3c218309183080b20000206eecd2ad13dc93a4491fa8e6067e2e514408883a017708d82f80ca0000206e8e12c314b898e47520b8ef06c02fa14908dc3c218209183000ce0000206e2e12d895209d848c2190f146ca2fe15189243d618308f82f80a80000206dcf12c2949897c4682030eb869c2ed14788d03c818709203200be0000206d70c2be14789844712038eac6a82ea14408c83b017b08d030c0c80000206d1282c394f49a646e2048e8c69e2e614108a83a217f09003380c80000206cb482c114889a24712078ee86b230215809283dc19209483040c00000206c58f2b2141895844c1fb8e446562d713e088438c16e08882f00b40000206bf912c994e49ba4872140f206d430b15509403e018608f02e00b80000206b9702dd153c9c647c20f8f206ca30c15389183cc19008f03180ce0000206b38a2c1148897e45d2000e706822ed14988a83a617d09383140c80000206ad7f2da95309ce4812120ed06cc30515489283d6188093030c0c40000206a76b2dc15649fe49721c8f486ee32b16089783e018b09002e40c40000206a16f2d3150c9d64812108f3c6de31415b894c3d819309b032c0c200002069b9a2bb948c9824611ff8e8c68a2ed14c08f43b617908f02f00cc0000206959c2cd14d09ac4762068ed46c030114d88d43be18409303080c600002068fbf2c1147c9744661fe0ea86b82f814c08e839a16b08782f80b2000020689e02c0948097c4652008ec86a42eb14d08c83bc175095832c0c8000020683f12cb14dc9a44692078eb46902e314408c43ba17c09183140c400002067de72d815209c647c2120ef46b42f614b08dc3aa17108902cc0bc000020677ed2c894c49a647b2130f006c630315008e03a417909002e80ca000020672062c2149c99a46f2018ea46982f714788a83a217308f82f80ae00002066bed2d9957ca0049e2218f6c6e430815c09603f219709983340c2000020666042cb94ec9ae47520b8ef86ca30714d09103cc18108983100c6000020660262c414c099c46b2068ee06ac30014988f83c818a09783180c000002065a472bd94689924742088edc6b22fc14d08d43a817508a02c40aa000020654452d294fc9ba47120a8ee86b82f514f88fc3ce18409282fc0c600002064e612c5947c98846920a8ebc69e2e813f88b439c17708c02c80bc000020648862c194709784611fc8e7068e2e313e88a839216008302b40b00000206429e2c994c49be47520b8efc6b630a157094c3e819409883440c600002063c9f2d115449de49c21a0f506e830f15389143de18a09003100c6000020636b92c114b09944692060ed06b82fe14408d83ac17d09003000b4000020630d02c314e49b847f20e8f106b22fd14e08c03a617308c02c40a600002062aec2bd14789764601fc0e6866c2d9133882c36415207e02bc0ac000020625082bf94909924682098eac69e2f0147887c38c17808e82d00a600002061f092d514e89aa4732058ef06c830315008e83d618309403380ba000020619392ba144897e45a1fe8eac6a42ef14c88f03b418209503080d4000020613492cc14d09b047220b0ec86aa2f914e08e83a617208602b80b000002060d892ae93f495844b1fe8e646722eb14988bc3aa17908e03000ba0000206078b2d315289dc47e2098ee06bc2f814d08c839016708a82a40a60000206015e2e795c8a0249e2240f8c70431b15c091c3e218509503040bc0000205fb862c0149898446c2058ea069c2ee14908f43c818709103080ca0000205f59f2c894989944692068ed06b42f814c88ec3ac17f09203180c80000205efc92bd947497e46a2058eac6902e414a88d03b817909083080c60000205ea0e2ad13ec9504491f68e706882da14188d439a16d08b02ec0b20000205e4372c014c89944632018ea46902dc143888038616608a02bc0ac0000205de462c914c89ae4732098e9469a2f014b88e43b417d08e82f80be0000205d8532cf14f89b047520d8ee06a82f814788d03be17e08902c40ae0000205d26e2c194b099647220a0f006ca2fa14b08e439617109002f40b00000205cc842c8949897c4602008e6468c2eb14688dc3a017808a82ec0b40000205c6b02b6942c9604571fc8e646782e414408a43a817d08f82f40bc0000205c0bd2c914e49aa46d2080ec86b02fd15188e43a017308903000bc0000205bac82c894d49a646d20a0ee86ba2f814a087c38416f08502cc0bc0000205b4cd2ce14d89b84832118efc6c830d15589203da18609683400d0000)))) else (if i < 338 then (if i < 335 then (if i < 334 then 0x208a3762c214809764571fe8e8869a2f114e09103ba17008b02f40d200002089d792d014c89924712028ea067a2dd13c085838416708902d80a4000020897752d295189d44942170f1c6ce30315509283de18709403140d4000020891872d014f89bc4792080ec86a02e514588ac39816f08902d40b000002088b9f2c3149898c4652058ebc6882ee14908cc3c217f08d03080c8000020885cd2bc14849884662010eac68a2f314708d43b818808d02d80c600002087fe12c0149899246c2058e7467e2e814908c03a618008c82dc0ac00002087a1a2b5146096444f1f78e5466e2df142087838a16408382ac0a60000208742b2cb15049de48d21b8f646e430415589403f419009683180be00002086e412c714b89a247920a8ed06b02f414908c839a16d09083100c80000208688d2b4144c96c4531fc8e6467c2f214a88c43a817a09303040c2000020862842d215089be47720c0ed06a82fa14f08ec3b416b08682c80a400002085c872cd14d09a247a20b8ed86d231315709203ce18409203040c0000020856a42bf94649824652010e786902eb14988943a216f08382a00a8000020850b32c5149499c4732098ec869e2f214c08b039a17608b83040c600002084ad32c294a099a46c2038e8866e2e714588ac3a816c08d82ec0c0000020845002ba143897045a1fe8e8c6982e7144889839217d08f03100d000002083f082cc94e89a646e2080e9869e2e914388d03a417108b82d40b8000020839182ca94e899c46d20a8ebc6b430014c08f03ba17a08982f00b6000020833262c894e09b447220e8ef46bc2fd15288fc3b017708f83180cc00002082d332cc94f09ae46e2058ed06a82f914f09483e019009502e40b40000208270b2e395b0a1649f2178f646da31615609303cc18c09b03340dc0000208210e2c914d49b04752038eb869a2ee14b08e83ae18109002f80ba00002081b472b8946097845f1ff0e9068a2e5142889c39a17b09182d80aa000020815602c614f09c247b2118f1c6be30915209083ba17108702e80cc00002080f532d195249e648d2148f0c6b42fb15389043ba17a09103200ce000020809792ba146498045b2050eb468e2e214508d83b618609383080c2000020803742d395049c447420d0efc6b42f514f08d83ae17508982c00c20000207fd912c5948899846f2078eec6a62f014a88c03aa17908a02e40b40000207f78b2d4150c9c647420d8efc6dc30f15909143c617808d031c0c60000207f17e2d5153c9ec4922238f606e431015b89283ce18808f02e40ba0000207eb962c5949098446c2010e986802e414909103b616d08082b00a80000207e5e42b113f49504501fc0ea068a2ed14588e43b817c08c82fc0aa0000207e0302a593b492c4431f40e6867a2db13c086c38416308002bc0b60000207da432c894d89aa47a20a8ee86a22f914c88ec3c818109302f00c40000207d4722b7143896e45f1fb8e586802dd13f08a839a17108f83180be0000207ce982be14a09b447d2150f486f232316089703e418909383100b00000207c8a92c714bc99846d2080ed86b22ff14d88f83b417909003440ca0000207c2c62c814d499c47820e0f1c6c630b15689343e0188090030c0c40000207bcc22d295109c848020f0f146c830615689243cc18a091030c0ca0000207b6e22c2148498446a2020e686762dd14308b039e16508102b40b40000207b10c2bd14549644582018e8c6902eb140888838615e08802ec0d00000207ab3a2b7949c98c4702100ecc6b630615509443e419409c034c0d60000207a5632ba945095c44e1f60e406562cd136085c38e16608782d80be00002079f8d2bb946096e4581f60e106502d1140889438e17509082f80ae0000207999e2c694bc98c46d2028e846822e214608bc3aa17e08f830c0be000020793a72c994f09c648620e8f186e631515b091c3ce18108c02e00aa00002078da02d215289d248b2160f146bc2f414988d43ae17a08882f00c0000020787bc2bf147c96e4651fc8e806882e713e887838816e08903000b6000020781dd2c3149897a4632048e986922f014688d03c017a08e82f40c600002077bfb2bb949097445a2038ed86a22f614888c43b817808b82ec0c00000207761e2c314809864661fe0e5066e2cd13b086438016808502b00aa0000207703e2be94a099c47820c8edc6b02f715089203c818609603140ce00002076a3f2ce94e09cc4802118f1c6cc30b14c88e03a617508e83240ce000020764382d3950c9b64872148f1c6c830415008f83c618209002e80c200002075e472c614a899e47520e0ed46962ec14708d83aa17508c02fc0c0000020758812b7946498045b2000e806842ed14488b038c17508282bc0c8000020752bb2b994689744622040eac6a22f014c08e83bc18009203480ce00002074cc52cb94c098e46e2078eb068a2ee14f89003c017a08d830c0ce000020746ed2c094a499e46a2028ebc6942eb14508d03ae16208182e40aa000020741122c314c09a64712080ef06d230015309103b817b08c02dc0be00002073b3c2b714489644551ff8ea46982f414908cc39216f08902d40ae0000207356f2b6144c94644e1fb8e3866c2d5141088039016808802d40b400002072f942bc946096e4572048ea06a42f615109083be17c08e83180c0000 else 0x20a1dd42cc14cc9ce4962150f346e231015289203da18c096030c0cc000020a17b72e195749fe4a52210f9870e32516189b44041a509d03340b4000020a12052b014089584521fe8e506662d513a086c37215907c82d40ca000020a0c372b6144495644b1f58e506862dd13e88803a016b08902e80c6000020a06452c814cc9a446c1fe8e8468a2ef14a88dc39e17908983040b2000020a005f2c894d09ac47720f8f346e631215189103c4187097832c0c60000209fa6d2c494a89a846f2098eec6ca30515509243d218709203140c80000209f49c2be146c97e4652030ea86982f514888c839817608b82ec0b00000209eec62c1146097c4591fd0e746922ec14708cc3bc17908d02ec0b60000209e8cb2d2950c9d04772090ef46b630315289143d218609483080bc0000209e2dc2c794b49924672068ebc69e2eb14688cc3ae18308c02e00b60000209dcf12c694b09964712098ef06c430615389243d619009403040cc0000209d7122be147098045c2078ec46822ea14508b439c17509082f00b40000209d0ed2e495609e64902138ef46c430c15909383e018d09483140ba0000209cb122c014909924722080eb06a22f514a88b83b218709583140be0000209c5582ab13cc9304451f90e506722db136085c36416108382d00b80000209bf692c214cc9b24782148f446d430315388f03b817408f02e00ac0000209b9872bb947c9744601fc0e7468a2e7141089839a16708382ac0a60000209b38b2cb15009ce48920c8f0c6c02f314988d83c017608d03000c80000209add22a813d49544541fd8e306542dc13b888438016508982cc0b60000209a7ea2c394a898e4621fc8e946902ee14788c038e16708e83080b60000209a2082c314a099446f20d0edc6be30114f89083c818208c03180ca00002099c2b2be94ac99a4732048ec86a82f014b89003c418809603200ba0000209964d2ba148098245a1fa8e8868e2ee14408bc3c617f092830c0c6000020990592cb14cc9a847a20d0ec06ae2f914388b43a817e09603280d000002098aa22a914049344461ee0e2c6582c613c089c3a616e08b83140d8000020984982d615389d449521b8f586fa31b15f896c3ee18f09683100c000002097eb02c594ac99c47720e0ec46b22fa15209103be187097033c0d60000209789a2d715309be47620c8ef46be30114f08e43b217709203140c2000020972972d415609ea4882160f1c6ce30815208e03b218609703200c800002096cbd2c0146c98845e1fe0e8468e2f715089003aa17608d82f40b8000020966fd2aa93ec93e4491fa0e7067e2de13d08603a017a08f82fc0be000020961122c614e09a246a2088efc6b62fc14c08ec3b217f09082ec0c000002095b222c814b099a46d2090ed86d630c15589403e2185095831c0b0000020955272ce94fc9b847620a8ef06c62fe14b88f03ac17108a02fc0bc00002094f2e2cf94fc9c447f20e8ec06b230414e08fc3c218408a82dc0ae000020949432c994f89b84822100f0c6c830515609403d618a09002f40ce000020943762b493fc9564421f78e4c65e2d213b888437c15f08482e00ba00002093d832d094f49be4852148f186ac2f614c88f83ce17908c82f80ba000020937a82bc146c97e4632068eb46b030214a08cc3ba17508782a00a60000209319e2d714fc9c248a2190f346d030514e08fc3b017d08a82d80c600002092bb52c294c49a046f2090ec46ba2ff14f09243cc17b08c82e40b6000020925c22cb14a89a44732078ef86d2305151894c3d2187093832c0d400002091fc02d295049c648320f8efc6de30514d88e03b617608d03040c0000020919ee2bc146c9804642028ebc6822e514608c03a017208883100cc000020913ee2d115109ca4862120ef06b430014b08f03ba18a09202fc0b600002090de72d114fc9c24932170f586ea31c15b09603de19b09b03540cc000020908242b2142496a45f1fe0e806842e3141088838815e08182a40b0000020902162d8154c9f24932190f646f230c15989403e018f09282e40c20000208fc2e2c894c499846b2010e846982f915088fc3ba183097833c0be0000208f6442c594c89a24712108edc6ac2ee14688c83b217908d82d40bc0000208f0762b694709644591ff0ea46902ef14a08a43a416108382a40a80000208ea7d2cd94f09c44892158f106ce30214d08f03a816e08b82e00ae0000208e4c32a913dc92e4381eb0e006422ca137084437a16d08182cc0b20000208deab2df9590a124a021e8f586e230615408d83b618609102f40ba0000208d8d22bd948498a47420b8ee06a82ff14c88fc3b817b08c02d00b40000208d2db2cd15149d44872128f0c6ca30014f88e03a817508e02fc0c80000208ccd92d194fc9d44832148f3c6d230e15189343ce18e099033c0ca0000208c6e32c714c49a646c2030ed46ba2fe15308ec3cc18409403380c60000208c1132bf946097645c2020e7869a2f514b88dc3a817208c82d80b80000208bb3d2bf14609604591fc8ea46962ef14988cc3a417108402d40c60000208b52b2d915709f649d2150f186ce309150892c3ce19409503340c80000208af4d2c5149c99a47220a8eec6b830015089203da19409883180b20000208a95f2c714b49ac47c2048ea06982e614988c03a618008f82c40b8000) else (if i < 336 then 0x20b98872b5946c9784622010ea46822d913e088438a16d08502bc0ba000020b92a32c894b89a847b20e8ef86b02fe14f08e43b816f08c82d40b4000020b8caa2c894e09ae47420a0ec06b62f815189083c817c08982ec0bc000020b86e32b0940c93e4481f68e4c6762e114408b839a16d08c82f40b6000020b80de2d4150c9dc49821d0f4c6e831416109703f619709883400c8000020b7afc2c1149098e4692008e8467c2e914488d83a617208982c40b4000020b74e22e195649f449821c0f4c6dc30214d09043c618108c03000c4000020b6f082be148c97845a2000e8c6982eb14708dc3ae17108e02f80ba000020b69412b9946c9704611ff0e9069e2ef14888d83a417c08982d40a0000020b634c2c4948c97e4652080ec46aa2fc15009003bc18008c02f00ba000020b5d802b6143095844e1fa0e8c68c2e614808c438e17608d03000d4000020b57702dd156ca024a42220f846fe31915a097c40a1a00a083540de000020b517a2ca94d49c046e2010ebc6b02f914a88c039616108782e00ce000020b4bce2a493c490c4381f00e146642d813c089439c17709282f80c4000020b45e62c314889804662058ea86902e714688d03a817708b03040d6000020b3ffb2c794909764632028eac6a22eb13f086c37816408982d80c4000020b39db2d595189b648d2190f546e031215a09383e018809283340ce000020b33e92c795089c44812120ef86be30014e88f83ac17408d02e40b6000020b2df02c994f09d448a2138f0c6b62fe15189203ea18d09102f80cc000020b283a2b2941c95244d1f90e506642ce137887436a16508902b80b6000020b226b2bc948098c47120d0efc6b62f614e89083d0190099033c0e0000020b1c662ca94e09e248220e0ecc6bc2f214808cc3a816d08b82d80d4000020b16a02b7943c95444f1fd8e5c67a2e914808fc3a618309683300c6000020b10bc2c714909944722090ee06a42eb15009143c217d08c02ec0c2000020b0aad2d915649f248e2110f1c6c830a157091c3cc18709302f40be000020b04c02ca94e09a646c20b8ed06882e314188b83a017408882d00bc000020afede2bb14809764662050e986922f514909183b218008c02e00b0000020af90f2ba94289404541fb8e5067c2d5140889039217508b82d80a0000020af3132cf15049ca48720e0ee06aa30015208d43b217908a83040aa000020aed1f2cb94ac99446a2070ea468c2e314388dc3b417608b02f00c0000020ae7312c794c49924672038ea86aa2f814c08c439c16a08a02b80ba000020ae1292cd95009b64702080eb46a02f214b88b83b417508d82e80c8000020adb352cb15189d248120c8ee06b630b15189243e4181094031c0d0000020ad5492ca94d09a04772060ea46a22e814488b03a817e08f82e40ba000020acf8e2b6142495844f1f58e306662d913f08a838e16b08b82e00b0000020ac9b32be94809804612008e686922ee14c88e03a617a08f830c0c6000020ac3ce2c494c09a447320e8efc6ae2fc14c08d439015d08982e00bc000020abdc32d395149c847c2090f006ca2fa14988e43aa17708c02e40b2000020ab7fb2b8947496845b1ff0e986902e113f88a03a4169087828c0aa000020ab2012c994cc9b047320d8f086c8305157894c3e218b09082d40b0000020aac172c994d09b047f2108f106d030415a894c3e417c08d82e80b6000020aa64d2b914449704591fb0e786822ed148088c39a17908b82e40a8000020aa04b2ca14c89a44682028ea06982e814008b03a417408e82fc0b8000020a9a402d495389c648520a8ed46ba2f614c09083b617d08f03080c8000020a944e2cb14d49a447f20a0eb86a42f214a08f43d219109903500d2000020a8e272e31574a104a72240f986ea31315989503f618b09803100c6000020a88512be146896845f1fe0e5467c2ee14688c03a617309003380ca000020a82362d915749f24a121f8f6c70232115d096c3ea18709583200c8000020a7c532c114a09a447920d0f046da30614c08d03a417708b02f80c4000020a76802ba94449644541fd8e7866c2d813a085437a15f08202d00ae000020a70a92bd94b498e4682060e7867a2e714288bc3bc17b08d03140d2000020a6ab92cb14c49ae47820e0edc6b02f114688e83bc17d09683080ba000020a64f42ae143496845a1fd8e846802dd13e887039017808c82e00b2000020a5ee42d3952c9e84942170f286de31315789203d218c09803200ca000020a58e42ca94b899846d2078ec86ac2f814888d03a816908802b009c000020a52c22e4156ca0049e21f0fa06f231c15509343b616e08c02e40ae000020a4cbf2d214f89be48120d0f1c6d430014c08d03b417b08c02ec0b2000020a46db2c314a89a846f2088eb06a42f214b88b839817008e02f00c2000020a411a2b514909904611fe8e786882e514488d43ba177090830c0d2000020a3b1e2c894a89964732110f246dc302154893c3d818f09603580c6000020a35512bc947098e45c2010e8c6822d3139082c37a17208b02d80ac000020a2fac2a393cc92c43c1f18e006502da13f886037415f08302e00c0000020a29922d9154c9d248d2130f186ce30a15909303e819a09e03380e2000020a23d52b4142094244f1f40e286582d7138087438817608702c80ac000 else (if i < 337 then 0x20d13442c1948897a4662068ef46b42ed141089038e16f08802d80ae000020d0d5a2c314cc9ae47620c0ee86cc30915188dc39e17e09083200ce000020d075b2ce94ec9ba4822100f046c230115088d438e16e08882e00c2000020d016d2c714b09a846c20c0ee06a82f8152892c3ee19609903440c4000020cfb722ca14dc9ac47420b8ed86bc30715089143c218108b82e80bc000020cf58f2c0146898e45f2008e9068e2e314508c03b217a08f02d40b8000020cefc92b4943894a4481f88e646702d8140087038616508702c00ba000020ce9ca2d394ec9c448520d8eac6a02e7140887439416808302a40ac000020ce4062b5142c94a44c1f88e3065c2cb138887c39616508802c40b2000020cde392b4144496a4631fe0e586722dc144089437e16808502b00b4000020cd83e2cc94f89c248520d0ef06a02f113f088039a16b08f82e40b0000020cd2462cd15009e048e2158f286d030c15689243be18208e02f40c2000020ccc272e495c4a144ad2210f846f231715f89303e619909883200c6000020cc63b2c494f09b24762110f186da30815289083be186090831c0c4000020cc0682b7143897c45d2078ee06a82f114d08e839a16908a82d00c0000020cba8a2ba146498246b2020ea869e2f115088d83c017f08e02d40b8000020cb4912c7149899647620e8e886922e614808a43a617708d82ec0be000020caea32c5149897045c1fc0e546842e714308c43a017208f83180c8000020ca89f2d415589e248a2158f406d831015689443e2193094031c0c6000020ca2be2bc94809844682048e9868e2e313f087838416208502c80b2000020c9cd62be948499246720a8ee86b230315509283d018d08f82c80bc000020c96cb2d7153c9e449d2208f686de318161098c3f819609a83300ec000020c910a2b5942094a4491f40e086622cf140889439617008d82d80c0000020c8b182c914e49ae47620c8ed069e2e6142088c38c17008782ac0a2000020c85362be148c9764541fb0e546622da140089838e16e08782ec0c4000020c7f722b3141c95a4521f80e586742cc138084c38216508782d40a6000020c798d2c514b89864652088ee06a02f114a08c03a817208882e00ba000020c73ca2b3941c96045e2008eb86962ea14508e039416d08882e00b4000020c6ddb2c714ac9a847520f0eec6c030114a88f03b217f09503200c4000020c67e62c714a899847420d8ec86942f714c08d838c16f08282a80a6000020c61e22d195209be4832180f3c6e431615a89803e219709503280e0000020c5bfc2cb94c09b24802118ef46aa2fe151091c3c818c09783280be000020c55f32da15489da49b2158f006b82ff14f89243d0183092831c0b8000020c50052c614bc9a646f2028e9869c2ee14288a039c16c08682d80b4000020c49e62df1554a0249b21a0f3c6da31b16289643e01a509b03340cc000020c44162bd944c9684521fe0e9c6802ee14788dc39816308682d80ac000020c3e252cd94dc9aa4772108ecc6aa2f514608b839c16c08c02fc0a8000020c38412c1149c9a647920c0f106da30f157092c3de18e09182ec0b4000020c32772b8143c9504441f48e3868a2ee14208bc38e17108702e40c6000020c2c8e2c614b09a64802130f1c6d431c15b09403f819209303380bc000020c267c2df152c9c448020c8f0c6b82fc15209043c017808c82f80b8000020c20b32bf947495c44d1f68e5c6882e614988e83b218709003040b2000020c1abd2c714ac98846f2080ee06b02fd14e08e83b618109283000b8000020c14db2be94749744642008e986882ee14808a438216408502e00cc000020c0ef72c714c09b247e2110ed06be30514f08ec3b417608d03100b6000020c09252bb949099246a2060ebc6982e913d088839e16f08b02fc0ba000020c03492bd947c98846c2048e8068c2ea14688a43a217b08d83000ba000020bfd332de15889fc4942188f2c6e831515388f03d018309183080b0000020bf7482d114fc9a847e20d8ef46d230e15309383de19409503180c4000020bf13a2d795289d24832178f2c6ea30f15909583e218f09483200ae000020beb552be94849824632010eac69a2f814988fc3bc18609003080b8000020be5582cd950c9be4702078edc6aa2f114708b839e17708d02e80b8000020bdf942b4942893c4441f38e3466c2da13b888038a16e08a02c40aa000020bd9b22be947c98e46e20d0ee06ae2f814988e83ce18308d82f40be000020bd3af2d215209d44812130f086c82fb14e88f03aa18308f83080ce000020bcdd02c494889804682038e886922f014b88e43ae18709383040c4000020bc7bf2d995409f849621d0f406f0314159897c3e618e09583280da000020bc1f22bc14489564521f80e446762e014308b03a817d08f03040bc000020bbc152be94989764501f10e3c67a2de144087839017308a02f40c2000020bb6142cd14e09a84762068ed86c62f615288d43bc17708a82d40b2000020bb0302c1148c97445e2028e906962e714b88ac3a016e08a82c00aa000020baa442c514ac99846c20c0ec46aa2f414608b839416c08882d40b4000020ba43b2d214d89ac4762130f086ca2fa152090c3cc17a08f82f80c2000020b9e492ca14f49ac46f20c8ecc6a42f814e89103b217c08d02f40b0000 else 0x20e8d242cd94b09964672030e906782db13f087038c16b08702cc0b6000020e87452c1149097c4591fb8e4866e2d4138886c38817008582bc0ae000020e81662be147897e46d2098ee06ba2fd14e891c3ac17e09002f80ba000020e7bab2b0143496245c2048ecc6b42fe14b88e43aa18609482fc0b8000020e75bd2cd94f89a247f2140f286d430915288f83ae17a09283200d8000020e6fd52c2149899446a2050eec69c2f714e88c03a617a08c02f40bc000020e69fd2ba145c9724572050ecc6ac2f114a08e83c018409483140ca000020e641b2c414ac9984732090ee86d02fd14f88f43b218509202f40be000020e5e172ce94d499047120d0efc6b62ec14788dc3bc182092031c0e6000020e58152cf95249e44a02208f9870832916b09c04261aa0a4034c0d0000020e52242cb14d899647a20e0ef06aa30215509103d217f09203100d2000020e4c2c2cc14cc9a247b20e8f206e631415b096c40019009903280d0000020e46692ae93fc95e44b1fd8e7467a2d1137887037016008582b40b4000020e40ad2ae94149564541ff0e8468a2f514808bc39216e08882d80b8000020e3ac42c594a097c4601ff0e5c6802dc14088a438e16708682b40a4000020e34ca2ca948498e4682078ef86b62fc14f092c3e019709483100cc000020e2edc2c594c89b847520c0ef06c22f614a88d83cc183091830c0c6000020e29042be14a49a64752080ee06a830615789303ca18d09403180c8000020e230f2c494bc9b647d2108f146d831115789383d018609382f80c2000020e1d1e2c894c49be47e20d0f046bc30715089083d219009603240d0000020e17342c394bc98e4682060ebc69a2e414508a839c16c08982f80bc000020e11522bf148897e4602018e9869e2ee14608a83a017a09102fc0ae000020e0b392db95709e04852118f0c6bc30b15d89603ee190098831c0ba000020e05632be946896a4502008e8067e2e1142089839e17708b02f00ca000020dff822c514c49c848a2160f3c6ec31915b09343c217a09203180c4000020df99c2c194a099046f20d8edc6ba30215809443c017408602b40c4000020df3a02ce94e89ac48220a8efc6de30414d89103ca17f08d82f40d0000020deda52d014ec9ba47d20f0f086b62f715689303e618e09583200c2000020de7dd2b6944095c4591fc8e606602d113f086437415d08182c80b8000020de1ee2c914d09ac4752030e9c6c02f914988d43b017b08882e80b8000020ddbf02ce94f89b447c20f8f146d230614b08fc3b618309082fc0c0000020dd6212b694509684642000e8c68e2dc142086c36815a08102b40a4000020dd0152d7151c9ca47720b8ed46aa2e814b08dc3b017b08e82f80b8000020dca332c0949c9864662080ea86a02f714788bc39c17308f030c0c0000020dc43d2ce94d89a847020a8ec86ac2ed14c08c43ae17308d02d40c6000020dbe6a2c0147c98045e2020e5867e2eb145088c38e16908602e00b6000020db8962b8142896c45c1fb0e5c66c2da13d886437a16608582e80aa000020db27f2d615509f049a21f0f5870032215a09643e419009283180ca000020dacc02ac93f895c44b1fc8e686602cc138086438816408402ac0bc000020da6bb2d015009d24872140f1c6ea30a15689303d218508f02ec0c4000020da0d22c694b898447020a0eb06a42fd14e88f03a017209082dc0b4000020d9ad52c914f89cc4882108f006ca30714f09043aa18008f02f40b2000020d95032ba148c97445b1fa8e986842ec14608b03ae18008882b00ba000020d8f1b2c594a09a446e2098ec86ae30015108e83b617a08a030c0bc000020d891a2d194dc9b247420b8ecc6a02ec148088438c16a08602a40ac000020d830e2d7954c9dc4882118f246c430114a08cc39217708d831c0c2000020d7d322c114789984752020e7c6862e414588b039e17a09083180c6000020d77462c714bc99e47320d0f0c6b22ef14b08c43b817a08902d80aa000020d716a2bf147899647520e0f006cc2ff14f88f43c617b08f83000ca000020d6b8f2ba946c9724602028eb46a22f614788c83a417e08d03000b8000020d65d12ad941495a4591f90e886882f114a88c439e16507e82a40b6000020d60042ba145c97c45c2028e9068e2e813f88ac39c17308c02f40b6000020d5a212be943895c4461fc8e7c6822e914788b83a617208982cc09e000020d54342cd14d89b84832190f586e430915509303ce18609002ec0be000020d4e692b0140494644a1f60e646722d3136087c39416708482d40ac000020d487d2c6949c9884611fc0e7067a2eb140887438216708602c00ac000020d42a22b9946897a45f2010ec06922f814d88e03ba17608d83100bc000020d3ca42d114ec99a4692008e906982fe15209043c218608c82dc0bc000020d36c22c414b09964712050e906722f214888b839e16a08802f80b4000020d30c22d215289c046d2118f046cc30415509303b817f08e02e00c0000020d2aa62dc15049b84812110f006d030515709243c4192098033c0c6000020d24d22bc146c9884692030e8468e2f214988d03b218008d02b40b4000020d1f0c2b293e492c43d1f30e246622e214008a038e16708a82f00c8000020d191e2c414989ae4752090ee06c0306150891c3b017c08e82d40b2000))) else (if i < 341 then (if i < 339 then 0x21006b52c8150c9c847f20e0f046c030314e88ec3bc18509283180be000021001052a713c89284341ee8e306622d413f888c376169085029c0ae000020ffafd2d3951c9d84962188f186e630915089083b417e09082e80c0000020ff5302b9144c96a4551ff8e6c66c2e214588c439817208e02fc0be000020fef2c2d595589f249321a0f346e430715a090c3da18b09102fc0cc000020fe9612ba147496e45e2018e7c6862e314088a039016308482d00b8000020fe37f2be14389744692068ec06902ec14188d439e16f08c03040c0000020fdd7b2d195309e248c2178f1c6de30a15c89403e819109783280d8000020fd7a02bb947097e4682040eb06982f614d08fc3c417c09182f80ac000020fd1a42ca14c09be47e2110f046c630a15b89583d8197099030c0c8000020fcbcf2c194b099c47820b0ecc6a42ee14688cc3a617308c82f40b4000020fc5e02c694ac99c4722080ea86ac2ef14b08a83a217208402e00a4000020fc01e2b2142895845a2030e6466a2dc13c085c37616208802e00b2000020fba112d615289d448920d0ed869a2e814788c439616b08803180ca000020fb4562b714409544531f40e3c6742e213f08a839616108582ec0b8000020fae8c2ba14809804662038ed06be301155891c3ca18508f82dc0d2000020fa8902cc94b09a447e20e8edc6d230c15a09183d417b08582b40aa000020fa2ae2c014b49944642020eac69a2ee14488a43a817e09082f40b6000020f9cb82cc14c09b44702038e8468e2e214888b839016b08782b80ba000020f96aa2d594fc9cc4852138f306ba2f814d08ac3a017208a02d80ac000020f90c32c2949c98046b20d0ed46b22ff15189383ca18508f82d80b8000020f8acb2cb14c098c4622060eb86a22f514c88e83b017c08d82d40a4000020f85062b5144097845b1fd0e606922e414488983a417908a82bc0ac000020f7f502b093f89664531fa0e7066c2db14408b839a16d08d82f80b8000020f796e2bf145c98a47220d0f086b82f515089083c218608e83140d8000020f737e2cf15309c64902120f406f431215689183c418408b02d00be000020f6d6f2d515349d448920f0edc6ba2fb14b08e83b618108d03040b6000020f67672cb94cc9ae46c2068ecc6ac2e914508b039416c084028c0a4000020f61892be947c9744591fa0e646802e614488cc39816808902e40ba000020f5b9a2cb14dc9c047b2108ed46ba30015308f83b217a08d03100a8000020f55b22c3949098e4652028ed46a02ff15409103b817a092031c0ca000020f4fb62cc94ec9a84662080ea86942ee14608e43b818008f03080b8000020f49b42d014e49c44862180f346ec30e155892c3c817f091831c0ba000020f43bb2cf950c9e249321a8f806fa31e15c894c3e018f096033c0cc000020f3dfa2b6143c9664541fe8e346762d813e889838617208b82cc0b8000020f381c2c0147c98646d2040ea06a22e914388bc3ba17b08802c80ac000020f32272cf14d099846c2078eb86ae30314e88d43cc17a09002f00aa000020f2c5a2b6946098445d2038ec069c2eb14188a039a17408e03200b8000020f26b12a8940893a4471f10e346642db13d08b83b817609183200c6000020f20d22c394a098e4702058eb86c02fc14e88fc3aa17208f02ec0bc000020f1ade2c994c499a4772050e9867c2e514508a83a017208782e00b2000020f14ea2d094ec9b647f2168f4870031515d896c3f419b099033c0c2000020f0ece2de959ca244ae2290fac6fa31d15989643e218b09203080c0000020f09042b114209564501f88e406822e814b88f03ce18c09203080b4000020f030a2ce94e49c64742078edc6bc2f814a89043d818409003100c2000020efd082d014d09b247f20c8f006d030615509343d819009302f40be000020ef70b2cf14b899047420e0f006ca30314f88d83a217b08782e00ba000020ef1092d014f89b047f2108f206d030015008dc3ae17c09383140d8000020eeb1a2c694a49b446f2058ebc6b42fa14b08ec3aa17f08e82d80c0000020ee5382c914ac9a24732040e8c69c2f714a88fc3ba17e08c03280dc000020edf532c414709924632058ef46b430215008d83b817808e02e40be000020ed9712c014849644501fa0e4c6762e014388c039616808582ac0b4000020ed37e2cd14e49a847320d0ed46be30914d08d83a017308c02d00b0000020ecdc02b013fc93444a1fd0e7467e2e914708a039015a08202b40a2000020ec7f92b4143896e4621fe0e886862ed14a88e83dc18409402fc0c0000020ec2272b814609784612028e686882eb145889c38c17808b83080b8000020ebc492b8146c97445e1fc0e906942e214208b43bc18309683200c6000020eb6622ca14a499646b2050ed46aa2fa14c09043d417908a83000b8000020eb0962b5143495a4531f50e3465a2d413e887838216c08902e80b0000020eaaae2c2948c98c4742100f006c22ff14d09083b016e08a82e40b6000020ea4e92b3940496044c1fa0e3c64c2c813a085c37e16508983000c6000020e9f102c194a49a44732078e9c69e2f514788c43a617c08d02d00ae000020e99062d395209ce4842138f1c6d030315208f83b017e08a83040c0000020e93212c1147c9824612040ea869c2e614c08c03b817e08d83000c0000 else (if i < 340 then 0x21180cc2d395389cc48d20f0ee86ca30c15209083ac17608d030c0c800002117adc2cb14dc99646f2078ee06ae2f014988c03a216d08d82e00ce000021174d92d114f89b647720a0ed06b62fc14f88fc3d6194092831c0da00002116ef22c294a09904601fd8e7c6742e014888f03c418709583180be000021168fe2d295109be4742088ec069e2eb14708b439817408c03100cc000021163372b394249684561fd0e7067a2e914888d03a217009002a80b400002115d272d515509d84982190f506ca30015309043c818108e02f00be0000211572b2d014fc9be4862128f006be2ff15488fc3b817a08d02c80ca000021151282d3954c9d64922150f306cc30a15008f83c217308e82ec0a400002114b342cc14f89ba47c2100ee06b62ff15489343c818109502e80b8000021145882a513fc9444531fd0e806862f314c08c43c217108502c80be00002113f962d214ec9ac46e2070ed869c2fa14e89003b618509303080d0000021139a52c794c09b24842128ef86b82ff14d09103b417508c02e40b2000021133b82ca94d89a246a2028e9067e2d7140086438416a08702a40a000002112db42d6954c9da4892180f1c6da31415509243e018909303240ce000021127e42be149499045f1fd0e7868a2f914a08d03ac17408b82cc0a6000021121f42c914bc9a647d20a0e906802e6142087438e16708802bc0bc00002111c272b594549724562040ea06982ec14788a439817008c02ec0b8000021116552b8946096445c1fd8eac6b430215188fc3b017c08c02dc0ce000021110822b614549804622060eb06922f314a08f03ac174090030c0ce00002110aba2b0141097245b1fe0e686802e914608c83bc17808e82f00b4000021104e12be949898a4672068ecc6b82fe14e08c83bc18308982f00be0000210ff0f2c0146c99446e20c0ec46a22ef14888b83a217f08e03200c40000210f9222c4949898c46c2048e9c6a62f414888e439c16d090030c0c60000210f3482b814549604531fb0e546622d3139087438817508c82dc0ba0000210ed872b614449684601fd0e7c6842db13d88a039017108782cc0b40000210e7b82b8941895c4551fe8e806782dd13b08a43ac17a09182e80ae0000210e1b62cf95089ba47d2110f186c22fe14d890c3c018009102fc0b40000210dbdb2bf948098846e2058ea069c2f114788b439817a08982f40aa0000210d5f22c0148898e45c2028eac6922ea14a88c83a417608582d80b80000210d01d2b0943c9684612018ea06842e1140088039617508782d00c00000210c9fe2e01590a0c4902180f446d230815288f83ac17f092031c0be0000210c40d2cf15049b847220d8ee06ac2f714788a039817208d83080c60000210be152cf94e49b247e2110ee46b22f914c08e83c418309483300ce0000210b8302c694c499c4712078eb86a02ef14a88d43ae17708c82dc0be0000210b22a2d095289e048e20f8ed06c630215309103ce18f09b832c0c20000210ac652b394249664561fc0ea46a82f714d09003ba181093031c0ca0000210a6802c5148097e4642018e8c67e2e113f088439016d08b83000be0000210a0b02b7945c9724541fd8e646722df14108b03a817108b03000ba00002109a9f2d995489ee49a21f8f8c6e830a157096c3e818709383240c4000021094ca2bc948097c4642028e946942f614908b039016708482d40b200002108ed92c194bc99c48420d8ed46b42f7150090c3d018208e02f80c8000021088c82e015889f24972180f546ee30e15689603ec19109c83680e2000021082f32b413e09464471f88e3465a2cb13d888c38216908702d40b200002107d0f2c114bc9ac4722098ed06b82f915008d83ba17b09383100e2000021077312c394789a24792040e946942f814b08ec3ac17408902e00b0000021071532bd94789a647d2098eb86a22f214908d439a17508a83040b000002106b7a2c1948c97c4622040e9c6a02ef14908dc3b217608802cc0b00000210656d2d5950c9bc47d20a8eec6ae2ea143889c3a817008882dc0c200002105f772c5949c9a046d2098edc6bc30015309183da18609283000bc000021059962c194789904692008eb468e2e814688ac39c16c08a02f40d0000021053b62ba94349524571fa0e4466c2d514108a039617208703000be00002104dda2c0948c98246a20a8edc6a42f314808bc3aa16e08a03140b8000021047fe2bd949c99047320e8ee06a82ef14888b83b418909103000be0000210421a2bf14a49944612040ee06a22f714888b03a817208d832c0d400002103c0f2cf95009b647a2108f186d430915509203c018d099033c0ce000021036312c1147097645b1fa0e9068a2e814e08d83aa17e08f02d80b4000021030302d415309d84872158f286da30215089203e218a09603240d000002102a3d2ca14ac9ae4812120ef86d6308158092c3d218f09583140c8000021024602b994809a846a2080eb46a02eb14b88d03b417a08f02ec0ba00002101e872c194549744582038ea46aa2ea14688b83b4182091830c0ca000021018992ce94e09b647c20e8ee46ba30214e88cc3b617d08982fc0c6000021012852df155c9f04a021f8f7871c32615a898040018f096831c0ce00002100c912c914d899c46f2018eb86aa30315388f83c018209483280ca000 else 0x212fa8b2c394b09984672050ec06962ee14c088439c17408882a40ba0000212f4ba2b9144c97045d1ff0e5c6882eb14c08d83b018309383180c60000212eec92c494a09964652068eb86ac2f514e08f03c618709183400ce0000212e8ef2be14989a84712038ea069e2f814c090c3c018508e02f80cc0000212e2fe2cf14ac9824682058ec06a82f014a88d03be19009a032c0d20000212dd272b5945497445f2008e6c6782e2140087039416508682e80c40000212d74b2c214a099646b2068ebc6a630015009103c018809003040b40000212d1302de153c9d84912188f686ec31a15c09403f619209283100c00000212cb3f2ca94e49bc47e2128f2c6ba30215389343ce17e08e02e00b60000212c54c2c4949898646e20c8ef86b62fd14f08f43b217608b82e80bc0000212bf262e995aca0448f2178f486da30615609383d818809282ec0b80000212b9352c594b89a647720a8f006d02ff14f88ec3c818d09383100c40000212b3442c594dc9bc47a20e0ef86c430514e08f43d017c09003180d60000212ad772b6942096444d1f78e8867c2e514308c83ac17908f02ec0ae0000212a76d2d014e89b04822160f146d431415809183c818408f82f00ba0000212a19c2bb94689624551fe8e786842d813f08983a417708502a40ba00002129bbb2c4949499c4782110f246d230915889103ae17508e02f40bc000021295de2c094a899846a2078eb469e2fb14c08ec3bc18909403300d200002128ffa2c5949c99e47320c0ec06a42e814b08c839a17808682d00bc000021289fa2cf15109ca48b2108f186c231315909403c218108e03180ce0000212841d2bb143897a4611fc8e8068a2e914508c83ac17008482cc0b000002127e362c214b09a447720a8ed068e2ee14e08e03b217408d83180c20000212785e2ba94709764531ff8eb069e2ee14c88e43be18e095030c0c0000021272782c5149c98e4632008eac6a22ee14b08d43a217309183680e000002126ca12bf947098446e2020eac6ba2f914f89003b217808c82ec0a6000021266b42c994bc99e46c20c0ed06ac2f414a88c03b817708e82fc0ba000021260af2d014f89d648a2148efc6bc30215109283c8181094030c0ae00002125ad82bd947c99246f2048e8c68c2f914e08f43c6180094032c0bc000021255002c3149098645f1fe8e746862f514e09283da18e09383140ca00002124f1d2c414989a84762090eb46802e914208b83a016a08082b40a80000212492f2c614b89aa47f2118f0c6ba304154890c3ae17e08b03080bc000021243452c514a098c46a2068eb469e2f814c08cc39e17808c03000cc00002123d4b2cb14ec9c24862140f0c6ca2ff15308f03ce18209002fc0cc000021237792bb944896a4541fa0e5c6862e514708e43ac17808e83040ac000021231a92b814409744662070ec46b230315188d03b417a08a82b40a200002122bcc2c314589804611ff8ea86982f314808c43b417f08f03100c6000021225cf2d015209ce48c2148f846ee31115889343d618c09003080ba00002121fdf2c594c499247220a0ee46b22f715088f43b017b09003100b4000021219ec2ca94ec9ae46b1fe0e7866a2d513a886837e16808782d80a6000021214072c614a898c4692040e986b22f914c08f43c217b08d830c0d200002120e092d3151c9be47b20a0ed46a42f714e090c3d218a091031c0c80000212083d2b414289504431f48e2866e2df140888038a16f08b82e40c4000021202652c114b499e46c20b0ed46a82fc14e08c839816d08382c80b60000211fc912bd944897045e2028ea46862d8142088437816008882d00b00000211f6aa2c614b89a447120a0ecc6982ef14888d83be17f091030c0ce0000211f09b2d114e89c248d2108f3c6d230915209343c218c09983000be0000211eac72b9943896a45a2048e9868c2f914808b03a417108c82f00c20000211e4dd2c794cc9b447a2098ed86ae2fb14a08a039816c08c02dc0a40000211deeb2ce14f89ba47d20e8eec6922e214808c83be17608a02a409e0000211d8fd2cf95049d04872100f006a830414f89043d619509603380d80000211d32b2b914509604612038ea46aa2f514a88ac3a816f08a02f40ba0000211cd492c114a89864601fe8e8868e2ec14708dc3ba17308c03080ba0000211c7832b1942894a44e1f60e7466e2e2146889039417008c82e00be0000211c1942cb14d09a647c20b0eb869a2ec14788e83d218c08f82fc0d60000211bbae2bf149897e46b20f8f446f230e15489183ca18609583400ca0000211b5f12b013ec95a45d1fe0e506562cf14108b839c16c08e82e00ac0000211afff2c494789824652038e906942ec14508b039817708a82f00b00000211aa272bd148098e45d2038e9468a2e114108a838c16a08a02c80b40000211a4372c394b498e4652000eb06962e814c88ec3b617a09203000c200002119e4c2c7949899c46c2090ec86be2fb14a08ec3b217808802d00b0000021198682bf149c99c4672028e9c6802e0143089838a16708782bc0b4000021192962bc947898645c2040e9c6962ed14f09043c417608802d40a800002118cc62b5143c96e4501fe8e706902ee14788ac39617308702c00b8000021186cc2ce15189ca4822128ee06bc2f914d89003d419409282f80be000)) else (if i < 342 then 0x21473bb2c714c49a446b2090ed86b42f214a08e43bc18408f82f00b800002146ddd2bb948498a4652080eb06a82ea14788b83a216f08b82e40c4000021467fa2c3948098a46e2050eac6a42f614408c839e17608a82c80ba0000214620a2c894dc9b247e2118f046dc30e14f09043bc178090832c0ba00002145c402ba947097645b1fe0e506602d613b888438e17308f03040b40000214566d2b7145896e45d2010e8869c2eb143088438616308903080c6000021450af2b1941c94a43f1f18e1c65c2d113b887038216b08882e40c000002144ae22b3140c94a4431f80e6467c2dc13d888439816a08b02f40ba000021444f82be947497645e1fc8ea06902fb14f88fc3bc17e08d82e80b000002143eff2d115209dc4802098ed06a82f514e09043da18d09683280c40000214390e2c514c899a4752088ea46962ef14908d43bc18309583100c4000021433412ba146c98645a2018e986922de147088c39a16c08b82e00c000002142d3f2ce15109c047f2118ef46da30515289083c019509283200d6000021427492cc94e89a24772060ee46ca30c154894c3d419809a833c0c6000021421662c0946497045a2000eb469c2f314888c43b417208982e80b800002141b772c714c899647620c8f106ca306156892c3e218d09102dc09e0000214159b2bd94709864692060ea868e2e8144888839a16f08e83140d200002140fac2ca94a498a4622088ecc6a22e714108903ae18009183100c8000021409bf2cd95109d848d2168f386d831315509443e018e09382ec0ba000021404222a393b49244401f30e1c6602d0137083835a15507d029c0a60000213fe0b2d9952c9c848220e0ecc6982fb14808d03c017d09183100c40000213f8252be146498246a2078ee46b02fa14c08f43bc17408b830c0c00000213f22a2d195289ca48a2140f306dc2fe14e09243c818709303200c60000213ec702ad13e49484491f38e4c6602dc13a88843b018109003300d40000213e6752ce14e499a4752060eac6902f614b08b03a417108783040b80000213e07b2ce95049b447420f0f1c6ce307156892c3da18a09182dc0c60000213daaf2b8944897245a2018e606742dc13b886c39216a08582e00ba0000213d4e12b694649844642000ea86982dd14808b83a817a08882d00b40000213cee72d2152c9d247f20e0ee06c02f9147089c3a017708e03080c60000213c9102c014689844662098eb86ac2f914d08c83ac17708e02f00ce0000213c33d2c114a89a446d20d8eac6982ea14708c03a017108982d80a20000213bd792b5144495c44f1fe0e7c68c2e714088bc3a417308e830c0d20000213b7b22b7945897c4672038e9469a2eb14a08e43ae17c08f82f80ca0000213b1c62c814d89d448020e0ee86be2fb14c890c3d018709403240d80000213abe12c1147099246d2080ed86a02f214a88c43a417008682e40b80000213a5dd2cf14e89b447720e8ef46a62ef14988d03a417609003140c00000213a0212b194089424491f58e2c6682ce13e889c3a017b09283300d200002139a4a2b994489724551fb0e646742dc14408c03ba17d08b82f00c6000021394642c1146c98e46b2090ee06b22f814e08f03b217408a02fc0b600002138e582cf14fc9aa47a2118f0c6be30614f89283bc18209283140d20000213888a2b9946897245a1fe8e8c6902f514e08fc3c018c09082dc0bc0000213827f2d215289c24742048ea46962f214b08e83c217d08a82d80b600002137caf2c094889904612010e9869c2ee146089439c17308a83080c8000021376e22bb94589744631fc8e546702d3137085c38616008a82e00b0000021370f62cb94b89ac4772078e9c6842e714508bc39216a08782d40b200002136ad52e215a89f049a2180f446ca30c157090c3bc17e09103000ce000021364fa2bf948496e45a1ff8e6c6742e614708a438417908682e00c000002135f1e2ba94509764612048ea46a22ee14408b43ae17d08c02d40ae000021359312c614b09a246d2080ee86be2f414b08fc39a16308b82a809a000021353122de156c9ec4912168f246d031115409143dc19309d03180c000002134d3d2b8143096244c1fb8e686a02f914d08fc3ca17d09102ec0ba000021347562c594a49964652018ea068c2df13f888438e16b08d02f00c8000021341822b694549704612020e9c6922e814788ac3aa17908f02f40b800002133b7e2cd95189ce48120f8edc6b02fc14d88f83bc18909483080c80000213359b2c3947c9704591fe0ea46842e414408c439416809003280da00002132fab2c594c09a246c2090eb069a2eb14508ac38017008b82c009a000021329c82c514b89ac47c2130f3c6e031815c094c3dc19209282f40d4000021323ff2b414289664441f90e4466c2de13f08ac39e17408802a40a800002131e082cd14e49c047c2118f086c230315109183c818409583080c2000021317fc2d6156ca0849f21a8f686fa31a159092c3d018308f02d00be000021312012cf94ec9aa46f20b0ef06a82f014b88c439c17608d82ec0c400002130c222bc943c96a45b1fe8e786842ee14c08ac39416b08c02d00b00000213064a2b7145096c4511fd8e7068c2de14088ac3a417308702e00b00000213007d2bd94a499c4632060eb46aa2f814d89243e618e095034c0c8000 else (if i < 343 then 0x215ede22c494b49a847220f8f086b830215609383e8192096834c0d60000215e7f02c994f49ba47f2120f0c6ce2f414a88e03c018c09402f40bc0000215e1e42d6154c9f24902180f706f431315409303d018d09783180c40000215dc342ac940493e43a1f40e4067a2d7137087037c15e08382ac0bc0000215d6792ab140492e43d1f58e206582cd135886036e16608682a409e0000215d0b22b194389484511ff0e806802e914588c83aa18209083040c00000215cac32c314bc99c4692048e846982ec14b88e43a817f08e82e00ba0000215c4db2cd14e89b847320a0f146d430915509143c017b08f031c0c00000215bee72c914d499e46b2070eb46962e213e087838216b08982ec0b80000215b90d2c194849744641fe8e7069c2f914d89003c417b08c83040b80000215b3362bf147c97244f1fd0e8067e2e614588c03ac17a08f82cc0c00000215ad482c394a89964742098ebc6ae2f015008f43b217e09183140ce0000215a7642c514a899446a2028ea868a2e414708f83aa17f09203240c40000215a1802c3947c97c4571fa0e7468c2ef14808b039e17508b02d009a00002159ba22c194b098e4632018e8c67a2e4145887838c17308b82dc0c2000021595b82c594ac9a44712098ee86ba30015088fc3bc18109083280c600002158fec2b9142c9684541fa0e4466c2cd133084436e15207e82b80b000002158a342b0141094844d1ff0e8c6a62f914f08d43b418109203000c80000215842a2ce94f49bc4892110f0c6ce30f15609243de19e095031c0ce00002157e4d2c1946c9804561fc8e5c6762d8143885837816108382c40ba000021578502cd94c89ae47b20b0ee06a22fc14f08f03c618309103140be0000215725b2cc94c499e46b2060eb86982ee14a08d839e17508782b80a800002156c6e2c614b498a4632070ef86bc30115088e83bc17c08882dc0a4000021566862c914c89cc4882160ef46b42f914808c83c217908d83040bc000021560a22bd149098845d1ff8e7468c2ef14888cc3ae17708c02c00b600002155ace2be949c9844642048e986962e714388a439616508202b40ac000021554ee2c614b898e4622008eb46aa2fa14b88e03b817c09183140a800002154f112be14a898a4692030e846902f0149090c3c417b08b02f00bc000021549242c2947c98c45b1fb0e5c6842e714308c03b617908b02dc0bc0000215434c2bd147c98a4612038ea06982f014608a83a616b08702dc0a400002153d632c594bc9924622048e946862d913f087c38416a08b03040c40000215377f2c414b498646d20b8f186c430515309383dc18809483000c2000021531922c494ac99e46a2038ea869e2f714688d43a017008982a40a600002152bae2ba14749884672008e586782d614508b43aa18308d02fc0ca000021525cf2c414b099a47820c8eb06ac2f814a08e83c018409203040c400002151fdd2c614dc9a84672078ed46a42f814a88d43b217508b82d00ba000021519f52c014b89a447120c0f006b02fe14d88dc3ba18809383300c8000021514012ce150c9c047a20b8ee46a22fe14e891c3d217f09082f00bc00002150e132c895009ba48420b0ee06a230315589243dc18b094031c0d6000021508322c895049c44842118ee46c030315109143be17a08b02d80b20000215022a2d715349dc49621f0f3c6d230b15589443e818b09703400dc0000214fc5b2c014a099a4641fe8e706842e414a88e83b617c08c82f80d20000214f6672d095009c24872190f606e830714f88d43b218308e83040ce0000214f0632d5154c9ce48320d8f206dc30f15989483c817208a02e00b60000214ea932be146498046520b0ed86c030b15709303c218a09683200c60000214e48e2cd94fc9b44732090ec46b62ee14a08e839e17808e03180ca0000214de8f2ce14c49c247b20f0f186d430e154894c3ec18608f82f00b80000214d8c12bb141c94e4571fd0e7465a2d414208c439617409002d40bc0000214d2cd2c994c89aa4742048eb06922de14008a83a017108502d00be0000214ccfc2bb14509704652008ec86962e414508b439617108b82e80a80000214c7222bd948499046a2068ed46a82f714708ac38416b08602d00b60000214c11a2d614f89c048620d0ef86c62fb14f08cc3ac16d08e82f80ae0000214baf72e415a4a0849e2230f6c6e830f15308f43b4180093830c0cc0000214b5312b3940894e43f1f90e646902e213f88a039a17608a82e40b00000214af4d2c294a09a84772090f0c6cc30114a88f03c018408f82f40ba0000214a9612c2949899246f1fd0e9067e2e6142087438c15608582e00b00000214a3352e0158ca044a52268f8870431b15809283ce184094832c0c000002149d3b2cf14f89ce48e2128edc69c2f214888e03a616f08b82b80ba0000214975b2bc14949a44712080ebc68a2e7142889438c16c08502c00a8000021491872bb145c97c4632010ebc6922e2140089c39e16c08a82e80ae00002148b742d715289c04802130f006b02f914888cc3bc17d08f82e00a4000021485612d9952c9ce47f2168f006b62fa14d88d43b618608f83240bc00002147f802bf94b49a647d20b0edc6c030615009043c017808c03000b2000021479ae2bd94549704581fd8e806622d513b887838617008982b809e000 else 0x2166a0400000000000002048ea06942e414388b439216808b02dc0ae000021664172ca14ec9be4782060ecc6a22eb14808d43aa17908b82f40b400002165e0e2d315189b64802148f246b230215509303d819409683400c4000021658432ba146c9664581ff8eac6942f514a88e03b818309282e80c4000021652572c214989924702078ea86982e814308b43ac17808e82fc0c200002164c642cc14d49ac47e20d8ed06b42fd14f89083b617c09603200d8000021646892c1949498e46e20a8ec46aa2e814088c439217208f02e40c40000216408e2cd14f09b448a20d8ee46b62fd14b88e43b017c08d02d80c000002163a9d2c4148098a4602010e8c6942e814c08b83a416b08c82d40be000021634cb2ba946496c45d2030e786862e614088c43aa17008482d80ca00002162f032b7946094c44c1f30e3465a2d313b887c38215507d82900aa000021629322bb94889924622058ebc6962ed14d88e83be17f08882e00ba000021623372cd94a49824682068ea868e2dc14408a43b617808d03080d800002161d402cc14f09c046f2070ec069e2fe14b08cc3b817a08e02dc0b8000021617502c894d89b647420d8ef46c4308156093c3c218109203140c2000021611582cc94c899446f2030e9469c2f414708c43ac17d094831c0a400002160b452d815209d44862108f286b22f814f08d039e17808d03000c0000021605482ce15009ca48120f8f0c6dc31215909383d618909783280c00000215ff782b8145097845c1fa0e7467e2e513b884437616108782a40ac0000215f9a42ba945896c4572010e846802e5142087838e16f08982c00b60000215f3c72c294b097e45f2000e9868c2e2143088038c16a08482b409c000)))))))))

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



private theorem b338515 : covered 338515 338600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338600 : covered 338600 338686 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338686 : covered 338686 338772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338772 : covered 338772 338858 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338858 : covered 338858 338944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338944 : covered 338944 339030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339030 : covered 339030 339116 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339116 : covered 339116 339202 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339202 : covered 339202 339287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339287 : covered 339287 339373 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339373 : covered 339373 339459 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339459 : covered 339459 339545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339545 : covered 339545 339631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339631 : covered 339631 339717 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339717 : covered 339717 339803 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339803 : covered 339803 339889 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339889 : covered 339889 339974 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b339974 : covered 339974 340060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340060 : covered 340060 340146 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340146 : covered 340146 340232 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340232 : covered 340232 340318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340318 : covered 340318 340404 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340404 : covered 340404 340490 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340490 : covered 340490 340576 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340576 : covered 340576 340661 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340661 : covered 340661 340747 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340747 : covered 340747 340833 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340833 : covered 340833 340919 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b340919 : covered 340919 341004 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341004 : covered 341004 341090 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341090 : covered 341090 341176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341176 : covered 341176 341262 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341262 : covered 341262 341347 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341347 : covered 341347 341433 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341433 : covered 341433 341519 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341519 : covered 341519 341605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341605 : covered 341605 341691 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341691 : covered 341691 341777 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341777 : covered 341777 341863 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341863 : covered 341863 341949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b341949 : covered 341949 342034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342034 : covered 342034 342120 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342120 : covered 342120 342206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342206 : covered 342206 342292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342292 : covered 342292 342377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342377 : covered 342377 342463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342463 : covered 342463 342549 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342549 : covered 342549 342635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342635 : covered 342635 342720 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342720 : covered 342720 342806 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342806 : covered 342806 342892 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342892 : covered 342892 342978 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b342978 : covered 342978 343064 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343064 : covered 343064 343150 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343150 : covered 343150 343236 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343236 : covered 343236 343322 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343322 : covered 343322 343407 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343407 : covered 343407 343493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343493 : covered 343493 343579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343579 : covered 343579 343665 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343665 : covered 343665 343750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343750 : covered 343750 343836 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343836 : covered 343836 343922 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b343922 : covered 343922 344008 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344008 : covered 344008 344093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344093 : covered 344093 344179 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344179 : covered 344179 344265 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344265 : covered 344265 344351 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344351 : covered 344351 344437 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344437 : covered 344437 344523 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344523 : covered 344523 344609 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344609 : covered 344609 344695 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344695 : covered 344695 344780 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344780 : covered 344780 344866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344866 : covered 344866 344952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b344952 : covered 344952 345038 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345038 : covered 345038 345124 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345124 : covered 345124 345210 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345210 : covered 345210 345296 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345296 : covered 345296 345382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345382 : covered 345382 345467 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345467 : covered 345467 345553 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345553 : covered 345553 345639 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345639 : covered 345639 345725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345725 : covered 345725 345811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345811 : covered 345811 345897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345897 : covered 345897 345983 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b345983 : covered 345983 346069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346069 : covered 346069 346154 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346154 : covered 346154 346240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346240 : covered 346240 346326 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346326 : covered 346326 346412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346412 : covered 346412 346497 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346497 : covered 346497 346583 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346583 : covered 346583 346669 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346669 : covered 346669 346755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346755 : covered 346755 346840 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346840 : covered 346840 346926 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b346926 : covered 346926 347012 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347012 : covered 347012 347098 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347098 : covered 347098 347184 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347184 : covered 347184 347270 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347270 : covered 347270 347356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347356 : covered 347356 347442 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347442 : covered 347442 347527 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347527 : covered 347527 347613 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347613 : covered 347613 347699 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347699 : covered 347699 347785 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347785 : covered 347785 347871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347871 : covered 347871 347957 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b347957 : covered 347957 348043 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348043 : covered 348043 348129 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348129 : covered 348129 348214 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348214 : covered 348214 348300 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348300 : covered 348300 348386 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348386 : covered 348386 348472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348472 : covered 348472 348558 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348558 : covered 348558 348644 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348644 : covered 348644 348730 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348730 : covered 348730 348816 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348816 : covered 348816 348901 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348901 : covered 348901 348987 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b348987 : covered 348987 349073 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349073 : covered 349073 349159 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349159 : covered 349159 349244 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349244 : covered 349244 349330 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349330 : covered 349330 349416 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349416 : covered 349416 349502 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349502 : covered 349502 349587 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349587 : covered 349587 349673 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349673 : covered 349673 349759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349759 : covered 349759 349845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349845 : covered 349845 349931 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b349931 : covered 349931 350017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350017 : covered 350017 350103 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350103 : covered 350103 350189 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350189 : covered 350189 350274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350274 : covered 350274 350360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350360 : covered 350360 350446 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350446 : covered 350446 350532 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350532 : covered 350532 350618 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350618 : covered 350618 350704 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350704 : covered 350704 350790 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350790 : covered 350790 350876 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350876 : covered 350876 350961 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b350961 : covered 350961 351047 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351047 : covered 351047 351133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351133 : covered 351133 351219 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351219 : covered 351219 351305 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351305 : covered 351305 351391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351391 : covered 351391 351477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351477 : covered 351477 351563 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 338515 351563 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b338515 b338600) (joinCoverage b338686 b338772)) (joinCoverage (joinCoverage b338858 b338944) (joinCoverage b339030 (joinCoverage b339116 b339202)))) (joinCoverage (joinCoverage (joinCoverage b339287 b339373) (joinCoverage b339459 (joinCoverage b339545 b339631))) (joinCoverage (joinCoverage b339717 b339803) (joinCoverage b339889 (joinCoverage b339974 b340060))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b340146 b340232) (joinCoverage b340318 b340404)) (joinCoverage (joinCoverage b340490 b340576) (joinCoverage b340661 (joinCoverage b340747 b340833)))) (joinCoverage (joinCoverage (joinCoverage b340919 b341004) (joinCoverage b341090 (joinCoverage b341176 b341262))) (joinCoverage (joinCoverage b341347 b341433) (joinCoverage b341519 (joinCoverage b341605 b341691)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b341777 b341863) (joinCoverage b341949 b342034)) (joinCoverage (joinCoverage b342120 b342206) (joinCoverage b342292 (joinCoverage b342377 b342463)))) (joinCoverage (joinCoverage (joinCoverage b342549 b342635) (joinCoverage b342720 (joinCoverage b342806 b342892))) (joinCoverage (joinCoverage b342978 b343064) (joinCoverage b343150 (joinCoverage b343236 b343322))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b343407 b343493) (joinCoverage b343579 b343665)) (joinCoverage (joinCoverage b343750 b343836) (joinCoverage b343922 (joinCoverage b344008 b344093)))) (joinCoverage (joinCoverage (joinCoverage b344179 b344265) (joinCoverage b344351 (joinCoverage b344437 b344523))) (joinCoverage (joinCoverage b344609 b344695) (joinCoverage b344780 (joinCoverage b344866 b344952))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b345038 b345124) (joinCoverage b345210 b345296)) (joinCoverage (joinCoverage b345382 b345467) (joinCoverage b345553 (joinCoverage b345639 b345725)))) (joinCoverage (joinCoverage (joinCoverage b345811 b345897) (joinCoverage b345983 (joinCoverage b346069 b346154))) (joinCoverage (joinCoverage b346240 b346326) (joinCoverage b346412 (joinCoverage b346497 b346583))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b346669 b346755) (joinCoverage b346840 b346926)) (joinCoverage (joinCoverage b347012 b347098) (joinCoverage b347184 (joinCoverage b347270 b347356)))) (joinCoverage (joinCoverage (joinCoverage b347442 b347527) (joinCoverage b347613 (joinCoverage b347699 b347785))) (joinCoverage (joinCoverage b347871 b347957) (joinCoverage b348043 (joinCoverage b348129 b348214)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b348300 b348386) (joinCoverage b348472 b348558)) (joinCoverage (joinCoverage b348644 b348730) (joinCoverage b348816 (joinCoverage b348901 b348987)))) (joinCoverage (joinCoverage (joinCoverage b349073 b349159) (joinCoverage b349244 (joinCoverage b349330 b349416))) (joinCoverage (joinCoverage b349502 b349587) (joinCoverage b349673 (joinCoverage b349759 b349845))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b349931 b350017) (joinCoverage b350103 b350189)) (joinCoverage (joinCoverage b350274 b350360) (joinCoverage b350446 (joinCoverage b350532 b350618)))) (joinCoverage (joinCoverage (joinCoverage b350704 b350790) (joinCoverage b350876 (joinCoverage b350961 b351047))) (joinCoverage (joinCoverage b351133 b351219) (joinCoverage b351305 (joinCoverage b351391 b351477))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 338515 ≤ index 650000000/512 := by decide +kernel
private theorem starting_value : fast 650000000=33793395 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 650000000=33793395) (n : ℕ) (low : 650000000≤n) (bound : n≤675000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=650000000
    · rw [first,anchor]
      exact starting_value
    · have past : 650000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤675000000 by omega)
        have within : index n / 512 < 351563 := by omega
        have lower : index 650000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤675000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ650000000To675000000
