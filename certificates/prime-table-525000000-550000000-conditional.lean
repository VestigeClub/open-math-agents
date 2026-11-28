import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ525000000To550000000

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




private def radical : ℕ := 0x3e3962408ad15f2a1e74f3f7dfac1d5171e665262a2da8a2e3fb68ba3ecefdcea24a68314f509ac2a75ae56283c4223fbf2c8d8ed5d46dc573982cc8abe31cb75399921167b753f6334db2ec08eae0bdf933a5b286ce39ab883883bd44fa9ccb0b85fff9f07eed0df6849534ee9233c0e2fbb7e979739984ef920719790d3adadd23f8c9d0691acfa4bc5e066abae8e72965ec881709172f9b7622d136997e8ee16a020af50d71cc71b5ec31acc5117ce98705244142f860012573360edeb761e0f373f811d23e5718c134548d2b26c85779b519049299253d3d3e3ffe2973ff4c21d86eae8ef6a72035bcd898a279b541a4d44c1c89c9022b4c2a0d17a20a7dea0fc93f8f8dbf68c0ad61994c32b8953b172aa084c2b75f89a7baa4dd4b0dba4d76ae675b020122f4b5dcf988004707dabd8827dfd6fcaa2bc7bb1c4a53a726040f1ba4f54c415d4c6bf1e3a50585fdb698cef43aa20e4df3650ffbd1cb66ef1c502a38810cdea796e3f39d3acf385b037c7a8325f6d2401483d59b75406542b6b93238f1755ffc3236a0f04d9dab5be4f2cdf9eb999aea1b916ae9d13c3dbb59657d57848652b98a5e3a0eea6bcec49e5141d0145e22b2f65a19aa60bd9959bce8c474653a782a8c6072e9513719978176700b9598568a159da6540909fc2101da9068cac917862f4a4b551d40c80aa9afe146cbad4f52a08d83914fde0525f383f40bcad2b97e1de0fdcefacb2ef5c2abe54fe0eeb9fa51bd5eacc177d449dffeb76635aff4e803edfb3442004349db8ae495178fdda8bfbde9b9fd8b79f0f9ffea5835d0f4ba87c427dc0d52e93a79475f19f0239cfd9bb15eb0a944b2c88e11b4cfc82f6cde93eff340a895f816a5c91e9a781ac1be36ae368b282648e782b0536c8f4bde16291645dca48a56163778672bfb7353c984192f2c8d7536cd9514cd6944772df76f58f57d8d7c26d31b36f35737d3e1467c282f17b6e705416131a8239764dbfcefecc06719d5ff4f2e9425432d89fa1ce8a26ec8aaf6c8e83dc4b586b58faa45bb951c29a7a38fd34b4f382fec29875e8635d853ce7f6a9d614c699e744adb65e74c7546a1003ce75f6fe733c982f31f7fcf2c19017bccd0d6965ab8e5e5d656b4970d07138150312910314a1c8daad12e3d1dc5ce7911fab7aafa561eccbf0aa2c2bc1b3f3f43bce624e37ea9e23832f9266af49524167f095cdd303e8e6694469a5a5803b742ea4b21f00628a95435e6d4b60117c7a0bf53422c07036a990fb7dec420546b05a35aaeb86f2a3bdb56472bc3f3e99a12d059ef78a6c3aa7690d79db71313cf78ecdc60d9d862e9b5bdca1a0c8a5b0085be33907c10c26b074d08bdbedecc461129d5e5727b3f12199388a01c237249828ea782e7a0a5489be937578914b514671c73894da32ed0e3565f8f184c3a84f23964c2efb8548fd664b541c5fafedc89c4f87c81dc0446979e34bc6491f7a11b77fc5b8e8d36f94c85865e6f958576d36a4fa325274c16641cafd262ba388318b98541ac490cc2c7639d3463168ff5bd8bee9a1cf753622e85e551382fe1f140635ea908b8c666f266ccd34883bfad655cc715ed79e9954ca57d18c597ef4e28fc0e21f08a559e8be1e6b1af2d13384b2b2e0417a4a4490a2695a58c9d52e79d8036a3fe6d98e105a2473792f02d7c8f429fe7770d60e169a581ea77cdf6ed9c95bd50ca19a6fd8f855bf69fad44d7476d9875c0f29965522ac5df03c551665f1dc33bac5b7b4fdcce7ac9c8b4d0eca0a33a60b83566726db4a6f69eb10f35e23bf248d64fee066fd1d5751b28ab48fa13e89e4c28fc17e5c9626a0fa125efd7d9daab42ead60d92a58f743aa20343dc1043c39df15196aff68a6c79b7ad402aaa440e900b672b0d4170c57ec65b40dd11608a181602fb88c27fc5f029895ef27862670f5702f839218d41a645645472804c14be34c95e299873f4f35f191cc27e5b75dcdd529f8f811d770ac6e5aa075fe13e1eb297d7c90d466ebc507a2e0d51482f989b3a9be6f21ceeef2123d21d3b88cdad2d62ae4bed7eafaf7c15276c961fd73ff0db09b4b66e86db2c9d644bfdf251d4bcb3863b44fcb70cc6d48d82beafb755f171e9312e54fd08f8d336f9d1d0db7db6d3cc74a101517a92624e61d9634ef35d32c75657cf8cee738f089f7f8852ee178a00332ce608e79374630d9bff6625a65fe073b053f9ca1d6338e0aa0919efacb3c4c64415c8d1695e11467e1e7191eb1dc4a62a56bdae2726fa322ec6141d119d43cf7c844f7aa4a3fc80ed7002dec56c9312f99b9b7abb3f9bec5411f42f45e9d9ecb49ec45431addf5e5aa4fa46bcf797aa23cd1e7102f589ea160a925e230f5e4c7ec93620fb70ee1cdd5b9e6a2187ba9f32408d2c9dce1b959279cda14a34584f7d827d992cc6c5fd57835d6431c96088915fc1dce411a3fab30fc58529e8f95d168324ab264fb205872b7a735584537557932e5af557fbcfa30f30ca7e24dadf15645ff1f69d0862683282bf025d23a8d8d597659e7f15ce0b31b08dda41b24502de5173ded60cb9e1c5f800652bfba455a2ff0b6107a1b7f0522a606d9d051251ca5b7e7332236cf8de2552cfef1b453011dd1984ba5606cdf4fa53b1203afb33b4a7eb0f021afcd5695fcea8e388da8564e431829f1884146e2543e5fac31ef1d7d849e43944dd0639aa7bf8c81edbab81030bcd56ed9b996466274374d69764016ad32f06193b3e853544ba7614a57c37bda83301bf9f64f9b9b3aad8cd80044f074e1cd9a13a5644968a0c1420709bc55d7a417a35d0929770bb8a1f355507a6c302b57b49131af5cb17caac0131fcc40ac233c8b65d86b786da3f9caff83cced4a1d4dcd564677dc5c953e0cf6fb701020ec4164e0c5dfbc0b21bceb5ee6fd9fa78221034f4c25800f364715d6781978685eb4f16f35f465a12b097c713e28b14034bd98f836bb6c74a913d124f662e8b13e7b4ed6137c74c5c81beda4b6da168d36b68893b8fdaf0b1c2a9b4df3d2089f3d998c7b6a49bcbc8c0237d94bf93e197457b66d15590442aef5a5d0cb8db9a46f98fbe0b85b2b0aed169530309124d8c7d39e7401d6d98c06367311ed2305b18f5752d00e90aae5124628e34557410789f133f0439e0154b3b7ba27857d33ee32b1abcfb0b65919e12119d6e0a73504f3ea2e9ead082bfc0242752a6efcbbeace7d81fb041ce2d6f1741b59b54fe91f26f3e3e4417edd132f3f5c4023445a31ab9afc89d0a940f28629478869d4e9b1b16aeee2e5c8c62ea25038f1e80f1b4e8376e6428252c33c42ef6159b5f616aafa122eb428a8bc8491e07064877de0f4af4a7a9a7971b87e7fd991f3c4c7521c6133f85bdb472782375a673ad5f61b6637c1a23ff504a048ea2bd9f632b11d6fdec33eba4ff38de6f64e67e3961a62e01417e4110820dedb717ff560897ab90886e75ed4244dcb4e4a24ebfffb6d1f52c1549b3c02aa294f6ceb6f04f83c6513b185b712d00048efe687134040d628ad4d26bdc58c57338a18e51f1dce122a349c0b5a1a92bd7df80a45d91337c3563520b23daf390d8665f280dfc6301c8e10c1b89704486f6754a2b605a375a861e10defc57744e79b004a8ec68565024ef438b2f10b8a0d12f7b359bdb4bbea3444fe210307e1b9d01834430eb7bafd6f1dc302aa59898b38ca6e5392abe7828302226feebd1cfd5d9eb3bb8e260e30bb639ff2e48926a7e1545af4c253057f66d80a22648ced6d1e39d81147042c049f88ed631ebdc6e751ed770d1595a41b41bdddd6a9793bf69c8a7d79e133987a615b0305dc8ffaafd33db9afe89b23b91138317a336ec474814b9ab786a6adcbbbc1933682da023cdb9203fee8c34dc859dc81ba5fbe258ee8e90d467dfabd2296903838b6bf93172dd15a02820a204202e77499087d5175ad24611bca9bd406c3f56b72c3098ba0ff73a89b89d96c4c3c6f5097bbdda73a162672e413e2f75756dea8f3122a0e0740fd98d0796653a34bccd191b42574c31d79e0c4ea5056b3d7ea5e5e6f2a571110fb6b50c1556a1ea1712aa0b0795a99769c240339212bc08a54ec3b16c2b5fea7ea5079e7ce3d532ff6b4bb7c81dc4e5be3578a3a7e5c866772106911e83c0da63c052ffdbf834aa850429a74b11ae828d10147d7b40ad701a58f024c3cf82537f5cccaddaec67c8ffc78707ba62c85f4d718748fdf6ea8572a4e5d0f2c4a158763465eebdea11254b334da4d863dab28c2e04cb6df4be6c8e633897b6836e3d5ca16963cd605d4c577e5f841ee91bfaae5faeb193e5cb03ded1edfd2fef196df6d300cab7c9dede0141bcd476905c972c35e45bb2e1a14196e1a142dfe437d198c0300cd45e9a0795225adca9a158351b52b8e5ad8868cf7fa1b7d3915f679f4d420f62ecb45437a590b10aa7d7925f045810341ddd0f3cc48282541016c4089b249b83ba654b4c17a9f7f9c55b866f1f9c0144f8fc22d0d9ffea364d54920d97205efb3d047e4ec39171225a27f659f18a379ead618c52cdf71f7f84112bbfb223dd958d9ccdabfe2e621bcdd2200d5ca04735a0e1f1a103248e7545a675e9c21f51144ef7fadd974506cd4c2d8a33dfdd5ff344f44eabd4df99ad0e55d6496bcd4b9b3e59c7f23d273978ea0410eea4d22579da7e5521f6d8251261ed123d1ccc93e6ca9932f51972822fd78c90ef05e6f87fc18a322d22d3ed35f5d25e45c20fa842581a05537a9d55104feb8000add835f05d46a3a465ca9a1056318d1fb19dcba88a19902aee48f471bd5d1e3bb4796706745cbc394f64febeecb7b185be5165fa7fcbde751bc26a7a030705744f8795d4396e7866e87b43c613b2b101e9b3c5b075be2f84a0fed182b3f54e25a52612ca0d4409bfe8a6a6445aa47a95de7bde28626c80dffa084dac5ad38f7d6b5b52c4c307147d3f8025b0ec1ead65c67d851eb60208d8f42a2ab3679d7ed762c7725f5c817c44e55067421fe43e5b5581d2d3637aa8a4334757a6030cb673aa745b19b33978568458680d30b9d829c2859d97f1876c8d9d0ed8f2e39b8ce4e6e89e183519734c563aa5cac3a9f19ce43a65c5d6a1659492370f8c69dcaa49d3a67c3961877a6c4651be81008c0dc420d69969c4b979546439d36c829a7a3e734793ef27477229c883df046dce883f3be6d16270a732ee0de76b048c937264bc505b87f6be474e144cce16a9e68188a2cca29429e5c49632c4df235dc0d354c3dddb3cf1897226b49a3aa2bb01f4e5891700f2d4dd7190e475036e1251a7f44025d1f2947182d364c8e4b312cefbcdc541d3f3d0cc4b998c689bbc46c69d87acf7fc54ae703fb954ad2ff9343b3e887fd779a7309b70f44615e56b7505f05ff50b5319818f22ea353fe35a0a697bd297dea074868a48ec3ec01aa52ae361f4df8c0f0868195f3dbca622db523cd3975974b2c4b8c4eea9bd8d62047ebb6423568906bf2139a067832340ea1f2553ff8c16449d55abbd6469e350c36c2ef4582f5cc658a0541aa705c35f920e2b00e02cb274a6e9fdad2d5523760cb851c1cf5c5f0280b2048ccaf5ff19760f9255bd6f7b18cb0cb31c248b7bb16dea3d603f03b79b66061fa70acc64520479d8c652712c3e51506c6f491da10614e55d0f53d44f1b93ae48e500ca29e3d1f042d2912c0391f3c2127ab40659fd5f12fd570e1ced83ce96b5d4848fa0f306eab37edb1bdb96c2a7d86d21115fd0e6938de31fdcd98388a66b6fc93798ac9ded77a1df6bf89ed8fef81034b116e86a29164312f276bae06909950beb39244672b13d4e3029325485dc57cf89ba1cd20201e15abeec90a6691cafefbf302863bfd85ee7ad1f5bca7cda0be04135c19d4108572fafcbd1550e5b268af24a1ea7fb87239fe2e46acf182

private def light (n : ℕ) : Bool :=
  if n≤153 then decide n.Prime else n.gcd 200634390509568239477828874698911718566246149616161171934231099284840946025238092339613294062603588435530393145048663047173051913507711632216305667129554900620296603188543122491838966881134795135997316305640071571629943041039657861120000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤23452) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 153 = 200634390509568239477828874698911718566246149616161171934231099284840946025238092339613294062603588435530393145048663047173051913507711632216305667129554900620296603188543122491838966881134795135997316305640071571629943041039657861120000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 153 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤23452 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 45 := by unfold smallValid; decide +kernel

private theorem sp45 : smallValid 45 46 := by unfold smallValid; decide +kernel

private theorem sp91 : smallValid 91 46 := by unfold smallValid; decide +kernel

private theorem sp137 : smallValid 137 46 := by unfold smallValid; decide +kernel

private theorem sp183 : smallValid 183 45 := by unfold smallValid; decide +kernel

private theorem sp228 : smallValid 228 46 := by unfold smallValid; decide +kernel

private theorem sp274 : smallValid 274 46 := by unfold smallValid; decide +kernel

private theorem sp320 : smallValid 320 46 := by unfold smallValid; decide +kernel

private theorem sp366 : smallValid 366 45 := by unfold smallValid; decide +kernel

private theorem sp411 : smallValid 411 46 := by unfold smallValid; decide +kernel

private theorem sp457 : smallValid 457 46 := by unfold smallValid; decide +kernel

private theorem sp503 : smallValid 503 46 := by unfold smallValid; decide +kernel

private theorem sp549 : smallValid 549 45 := by unfold smallValid; decide +kernel

private theorem sp594 : smallValid 594 46 := by unfold smallValid; decide +kernel

private theorem sp640 : smallValid 640 46 := by unfold smallValid; decide +kernel

private theorem sp686 : smallValid 686 46 := by unfold smallValid; decide +kernel

private theorem sp732 : smallValid 732 45 := by unfold smallValid; decide +kernel

private theorem sp777 : smallValid 777 46 := by unfold smallValid; decide +kernel

private theorem sp823 : smallValid 823 46 := by unfold smallValid; decide +kernel

private theorem sp869 : smallValid 869 46 := by unfold smallValid; decide +kernel

private theorem sp915 : smallValid 915 45 := by unfold smallValid; decide +kernel

private theorem sp960 : smallValid 960 46 := by unfold smallValid; decide +kernel

private theorem sp1006 : smallValid 1006 46 := by unfold smallValid; decide +kernel

private theorem sp1052 : smallValid 1052 46 := by unfold smallValid; decide +kernel

private theorem sp1098 : smallValid 1098 45 := by unfold smallValid; decide +kernel

private theorem sp1143 : smallValid 1143 46 := by unfold smallValid; decide +kernel

private theorem sp1189 : smallValid 1189 46 := by unfold smallValid; decide +kernel

private theorem sp1235 : smallValid 1235 46 := by unfold smallValid; decide +kernel

private theorem sp1281 : smallValid 1281 46 := by unfold smallValid; decide +kernel

private theorem sp1327 : smallValid 1327 46 := by unfold smallValid; decide +kernel

private theorem sp1373 : smallValid 1373 46 := by unfold smallValid; decide +kernel

private theorem sp1419 : smallValid 1419 46 := by unfold smallValid; decide +kernel

private theorem sp1465 : smallValid 1465 45 := by unfold smallValid; decide +kernel

private theorem sp1510 : smallValid 1510 46 := by unfold smallValid; decide +kernel

private theorem sp1556 : smallValid 1556 46 := by unfold smallValid; decide +kernel

private theorem sp1602 : smallValid 1602 46 := by unfold smallValid; decide +kernel

private theorem sp1648 : smallValid 1648 45 := by unfold smallValid; decide +kernel

private theorem sp1693 : smallValid 1693 46 := by unfold smallValid; decide +kernel

private theorem sp1739 : smallValid 1739 46 := by unfold smallValid; decide +kernel

private theorem sp1785 : smallValid 1785 46 := by unfold smallValid; decide +kernel

private theorem sp1831 : smallValid 1831 45 := by unfold smallValid; decide +kernel

private theorem sp1876 : smallValid 1876 46 := by unfold smallValid; decide +kernel

private theorem sp1922 : smallValid 1922 46 := by unfold smallValid; decide +kernel

private theorem sp1968 : smallValid 1968 46 := by unfold smallValid; decide +kernel

private theorem sp2014 : smallValid 2014 46 := by unfold smallValid; decide +kernel

private theorem sp2060 : smallValid 2060 46 := by unfold smallValid; decide +kernel

private theorem sp2106 : smallValid 2106 46 := by unfold smallValid; decide +kernel

private theorem sp2152 : smallValid 2152 46 := by unfold smallValid; decide +kernel

private theorem sp2198 : smallValid 2198 45 := by unfold smallValid; decide +kernel

private theorem sp2243 : smallValid 2243 46 := by unfold smallValid; decide +kernel

private theorem sp2289 : smallValid 2289 46 := by unfold smallValid; decide +kernel

private theorem sp2335 : smallValid 2335 46 := by unfold smallValid; decide +kernel

private theorem sp2381 : smallValid 2381 45 := by unfold smallValid; decide +kernel

private theorem sp2426 : smallValid 2426 46 := by unfold smallValid; decide +kernel

private theorem sp2472 : smallValid 2472 46 := by unfold smallValid; decide +kernel

private theorem sp2518 : smallValid 2518 46 := by unfold smallValid; decide +kernel

private theorem sp2564 : smallValid 2564 45 := by unfold smallValid; decide +kernel

private theorem sp2609 : smallValid 2609 46 := by unfold smallValid; decide +kernel

private theorem sp2655 : smallValid 2655 46 := by unfold smallValid; decide +kernel

private theorem sp2701 : smallValid 2701 46 := by unfold smallValid; decide +kernel

private theorem sp2747 : smallValid 2747 46 := by unfold smallValid; decide +kernel

private theorem sp2793 : smallValid 2793 46 := by unfold smallValid; decide +kernel

private theorem sp2839 : smallValid 2839 46 := by unfold smallValid; decide +kernel

private theorem sp2885 : smallValid 2885 46 := by unfold smallValid; decide +kernel

private theorem sp2931 : smallValid 2931 45 := by unfold smallValid; decide +kernel

private theorem sp2976 : smallValid 2976 46 := by unfold smallValid; decide +kernel

private theorem sp3022 : smallValid 3022 46 := by unfold smallValid; decide +kernel

private theorem sp3068 : smallValid 3068 46 := by unfold smallValid; decide +kernel

private theorem sp3114 : smallValid 3114 45 := by unfold smallValid; decide +kernel

private theorem sp3159 : smallValid 3159 46 := by unfold smallValid; decide +kernel

private theorem sp3205 : smallValid 3205 46 := by unfold smallValid; decide +kernel

private theorem sp3251 : smallValid 3251 46 := by unfold smallValid; decide +kernel

private theorem sp3297 : smallValid 3297 45 := by unfold smallValid; decide +kernel

private theorem sp3342 : smallValid 3342 46 := by unfold smallValid; decide +kernel

private theorem sp3388 : smallValid 3388 46 := by unfold smallValid; decide +kernel

private theorem sp3434 : smallValid 3434 46 := by unfold smallValid; decide +kernel

private theorem sp3480 : smallValid 3480 46 := by unfold smallValid; decide +kernel

private theorem sp3526 : smallValid 3526 46 := by unfold smallValid; decide +kernel

private theorem sp3572 : smallValid 3572 46 := by unfold smallValid; decide +kernel

private theorem sp3618 : smallValid 3618 46 := by unfold smallValid; decide +kernel

private theorem sp3664 : smallValid 3664 45 := by unfold smallValid; decide +kernel

private theorem sp3709 : smallValid 3709 46 := by unfold smallValid; decide +kernel

private theorem sp3755 : smallValid 3755 46 := by unfold smallValid; decide +kernel

private theorem sp3801 : smallValid 3801 46 := by unfold smallValid; decide +kernel

private theorem sp3847 : smallValid 3847 45 := by unfold smallValid; decide +kernel

private theorem sp3892 : smallValid 3892 46 := by unfold smallValid; decide +kernel

private theorem sp3938 : smallValid 3938 46 := by unfold smallValid; decide +kernel

private theorem sp3984 : smallValid 3984 46 := by unfold smallValid; decide +kernel

private theorem sp4030 : smallValid 4030 45 := by unfold smallValid; decide +kernel

private theorem sp4075 : smallValid 4075 46 := by unfold smallValid; decide +kernel

private theorem sp4121 : smallValid 4121 46 := by unfold smallValid; decide +kernel

private theorem sp4167 : smallValid 4167 46 := by unfold smallValid; decide +kernel

private theorem sp4213 : smallValid 4213 46 := by unfold smallValid; decide +kernel

private theorem sp4259 : smallValid 4259 46 := by unfold smallValid; decide +kernel

private theorem sp4305 : smallValid 4305 46 := by unfold smallValid; decide +kernel

private theorem sp4351 : smallValid 4351 46 := by unfold smallValid; decide +kernel

private theorem sp4397 : smallValid 4397 45 := by unfold smallValid; decide +kernel

private theorem sp4442 : smallValid 4442 46 := by unfold smallValid; decide +kernel

private theorem sp4488 : smallValid 4488 46 := by unfold smallValid; decide +kernel

private theorem sp4534 : smallValid 4534 46 := by unfold smallValid; decide +kernel

private theorem sp4580 : smallValid 4580 45 := by unfold smallValid; decide +kernel

private theorem sp4625 : smallValid 4625 46 := by unfold smallValid; decide +kernel

private theorem sp4671 : smallValid 4671 46 := by unfold smallValid; decide +kernel

private theorem sp4717 : smallValid 4717 46 := by unfold smallValid; decide +kernel

private theorem sp4763 : smallValid 4763 45 := by unfold smallValid; decide +kernel

private theorem sp4808 : smallValid 4808 46 := by unfold smallValid; decide +kernel

private theorem sp4854 : smallValid 4854 46 := by unfold smallValid; decide +kernel

private theorem sp4900 : smallValid 4900 46 := by unfold smallValid; decide +kernel

private theorem sp4946 : smallValid 4946 46 := by unfold smallValid; decide +kernel

private theorem sp4992 : smallValid 4992 46 := by unfold smallValid; decide +kernel

private theorem sp5038 : smallValid 5038 46 := by unfold smallValid; decide +kernel

private theorem sp5084 : smallValid 5084 46 := by unfold smallValid; decide +kernel

private theorem sp5130 : smallValid 5130 45 := by unfold smallValid; decide +kernel

private theorem sp5175 : smallValid 5175 46 := by unfold smallValid; decide +kernel

private theorem sp5221 : smallValid 5221 46 := by unfold smallValid; decide +kernel

private theorem sp5267 : smallValid 5267 46 := by unfold smallValid; decide +kernel

private theorem sp5313 : smallValid 5313 45 := by unfold smallValid; decide +kernel

private theorem sp5358 : smallValid 5358 46 := by unfold smallValid; decide +kernel

private theorem sp5404 : smallValid 5404 46 := by unfold smallValid; decide +kernel

private theorem sp5450 : smallValid 5450 46 := by unfold smallValid; decide +kernel

private theorem sp5496 : smallValid 5496 45 := by unfold smallValid; decide +kernel

private theorem sp5541 : smallValid 5541 46 := by unfold smallValid; decide +kernel

private theorem sp5587 : smallValid 5587 46 := by unfold smallValid; decide +kernel

private theorem sp5633 : smallValid 5633 46 := by unfold smallValid; decide +kernel

private theorem sp5679 : smallValid 5679 46 := by unfold smallValid; decide +kernel

private theorem sp5725 : smallValid 5725 46 := by unfold smallValid; decide +kernel

private theorem sp5771 : smallValid 5771 46 := by unfold smallValid; decide +kernel

private theorem sp5817 : smallValid 5817 46 := by unfold smallValid; decide +kernel

private theorem sp5863 : smallValid 5863 45 := by unfold smallValid; decide +kernel

private theorem sp5908 : smallValid 5908 46 := by unfold smallValid; decide +kernel

private theorem sp5954 : smallValid 5954 46 := by unfold smallValid; decide +kernel

private theorem sp6000 : smallValid 6000 46 := by unfold smallValid; decide +kernel

private theorem sp6046 : smallValid 6046 45 := by unfold smallValid; decide +kernel

private theorem sp6091 : smallValid 6091 46 := by unfold smallValid; decide +kernel

private theorem sp6137 : smallValid 6137 46 := by unfold smallValid; decide +kernel

private theorem sp6183 : smallValid 6183 46 := by unfold smallValid; decide +kernel

private theorem sp6229 : smallValid 6229 45 := by unfold smallValid; decide +kernel

private theorem sp6274 : smallValid 6274 46 := by unfold smallValid; decide +kernel

private theorem sp6320 : smallValid 6320 46 := by unfold smallValid; decide +kernel

private theorem sp6366 : smallValid 6366 46 := by unfold smallValid; decide +kernel

private theorem sp6412 : smallValid 6412 45 := by unfold smallValid; decide +kernel

private theorem sp6457 : smallValid 6457 46 := by unfold smallValid; decide +kernel

private theorem sp6503 : smallValid 6503 46 := by unfold smallValid; decide +kernel

private theorem sp6549 : smallValid 6549 46 := by unfold smallValid; decide +kernel

private theorem sp6595 : smallValid 6595 45 := by unfold smallValid; decide +kernel

private theorem sp6640 : smallValid 6640 46 := by unfold smallValid; decide +kernel

private theorem sp6686 : smallValid 6686 46 := by unfold smallValid; decide +kernel

private theorem sp6732 : smallValid 6732 46 := by unfold smallValid; decide +kernel

private theorem sp6778 : smallValid 6778 45 := by unfold smallValid; decide +kernel

private theorem sp6823 : smallValid 6823 46 := by unfold smallValid; decide +kernel

private theorem sp6869 : smallValid 6869 46 := by unfold smallValid; decide +kernel

private theorem sp6915 : smallValid 6915 46 := by unfold smallValid; decide +kernel

private theorem sp6961 : smallValid 6961 45 := by unfold smallValid; decide +kernel

private theorem sp7006 : smallValid 7006 46 := by unfold smallValid; decide +kernel

private theorem sp7052 : smallValid 7052 46 := by unfold smallValid; decide +kernel

private theorem sp7098 : smallValid 7098 46 := by unfold smallValid; decide +kernel

private theorem sp7144 : smallValid 7144 46 := by unfold smallValid; decide +kernel

private theorem sp7190 : smallValid 7190 46 := by unfold smallValid; decide +kernel

private theorem sp7236 : smallValid 7236 46 := by unfold smallValid; decide +kernel

private theorem sp7282 : smallValid 7282 46 := by unfold smallValid; decide +kernel

private theorem sp7328 : smallValid 7328 45 := by unfold smallValid; decide +kernel

private theorem sp7373 : smallValid 7373 46 := by unfold smallValid; decide +kernel

private theorem sp7419 : smallValid 7419 46 := by unfold smallValid; decide +kernel

private theorem sp7465 : smallValid 7465 46 := by unfold smallValid; decide +kernel

private theorem sp7511 : smallValid 7511 45 := by unfold smallValid; decide +kernel

private theorem sp7556 : smallValid 7556 46 := by unfold smallValid; decide +kernel

private theorem sp7602 : smallValid 7602 46 := by unfold smallValid; decide +kernel

private theorem sp7648 : smallValid 7648 46 := by unfold smallValid; decide +kernel

private theorem sp7694 : smallValid 7694 45 := by unfold smallValid; decide +kernel

private theorem sp7739 : smallValid 7739 46 := by unfold smallValid; decide +kernel

private theorem sp7785 : smallValid 7785 46 := by unfold smallValid; decide +kernel

private theorem sp7831 : smallValid 7831 46 := by unfold smallValid; decide +kernel

private theorem sp7877 : smallValid 7877 46 := by unfold smallValid; decide +kernel

private theorem sp7923 : smallValid 7923 46 := by unfold smallValid; decide +kernel

private theorem sp7969 : smallValid 7969 46 := by unfold smallValid; decide +kernel

private theorem sp8015 : smallValid 8015 46 := by unfold smallValid; decide +kernel

private theorem sp8061 : smallValid 8061 45 := by unfold smallValid; decide +kernel

private theorem sp8106 : smallValid 8106 46 := by unfold smallValid; decide +kernel

private theorem sp8152 : smallValid 8152 46 := by unfold smallValid; decide +kernel

private theorem sp8198 : smallValid 8198 46 := by unfold smallValid; decide +kernel

private theorem sp8244 : smallValid 8244 45 := by unfold smallValid; decide +kernel

private theorem sp8289 : smallValid 8289 46 := by unfold smallValid; decide +kernel

private theorem sp8335 : smallValid 8335 46 := by unfold smallValid; decide +kernel

private theorem sp8381 : smallValid 8381 46 := by unfold smallValid; decide +kernel

private theorem sp8427 : smallValid 8427 45 := by unfold smallValid; decide +kernel

private theorem sp8472 : smallValid 8472 46 := by unfold smallValid; decide +kernel

private theorem sp8518 : smallValid 8518 46 := by unfold smallValid; decide +kernel

private theorem sp8564 : smallValid 8564 46 := by unfold smallValid; decide +kernel

private theorem sp8610 : smallValid 8610 46 := by unfold smallValid; decide +kernel

private theorem sp8656 : smallValid 8656 46 := by unfold smallValid; decide +kernel

private theorem sp8702 : smallValid 8702 46 := by unfold smallValid; decide +kernel

private theorem sp8748 : smallValid 8748 46 := by unfold smallValid; decide +kernel

private theorem sp8794 : smallValid 8794 45 := by unfold smallValid; decide +kernel

private theorem sp8839 : smallValid 8839 46 := by unfold smallValid; decide +kernel

private theorem sp8885 : smallValid 8885 46 := by unfold smallValid; decide +kernel

private theorem sp8931 : smallValid 8931 46 := by unfold smallValid; decide +kernel

private theorem sp8977 : smallValid 8977 45 := by unfold smallValid; decide +kernel

private theorem sp9022 : smallValid 9022 46 := by unfold smallValid; decide +kernel

private theorem sp9068 : smallValid 9068 46 := by unfold smallValid; decide +kernel

private theorem sp9114 : smallValid 9114 46 := by unfold smallValid; decide +kernel

private theorem sp9160 : smallValid 9160 45 := by unfold smallValid; decide +kernel

private theorem sp9205 : smallValid 9205 46 := by unfold smallValid; decide +kernel

private theorem sp9251 : smallValid 9251 46 := by unfold smallValid; decide +kernel

private theorem sp9297 : smallValid 9297 46 := by unfold smallValid; decide +kernel

private theorem sp9343 : smallValid 9343 46 := by unfold smallValid; decide +kernel

private theorem sp9389 : smallValid 9389 46 := by unfold smallValid; decide +kernel

private theorem sp9435 : smallValid 9435 46 := by unfold smallValid; decide +kernel

private theorem sp9481 : smallValid 9481 46 := by unfold smallValid; decide +kernel

private theorem sp9527 : smallValid 9527 45 := by unfold smallValid; decide +kernel

private theorem sp9572 : smallValid 9572 46 := by unfold smallValid; decide +kernel

private theorem sp9618 : smallValid 9618 46 := by unfold smallValid; decide +kernel

private theorem sp9664 : smallValid 9664 46 := by unfold smallValid; decide +kernel

private theorem sp9710 : smallValid 9710 45 := by unfold smallValid; decide +kernel

private theorem sp9755 : smallValid 9755 46 := by unfold smallValid; decide +kernel

private theorem sp9801 : smallValid 9801 46 := by unfold smallValid; decide +kernel

private theorem sp9847 : smallValid 9847 46 := by unfold smallValid; decide +kernel

private theorem sp9893 : smallValid 9893 45 := by unfold smallValid; decide +kernel

private theorem sp9938 : smallValid 9938 46 := by unfold smallValid; decide +kernel

private theorem sp9984 : smallValid 9984 46 := by unfold smallValid; decide +kernel

private theorem sp10030 : smallValid 10030 46 := by unfold smallValid; decide +kernel

private theorem sp10076 : smallValid 10076 46 := by unfold smallValid; decide +kernel

private theorem sp10122 : smallValid 10122 46 := by unfold smallValid; decide +kernel

private theorem sp10168 : smallValid 10168 46 := by unfold smallValid; decide +kernel

private theorem sp10214 : smallValid 10214 46 := by unfold smallValid; decide +kernel

private theorem sp10260 : smallValid 10260 45 := by unfold smallValid; decide +kernel

private theorem sp10305 : smallValid 10305 46 := by unfold smallValid; decide +kernel

private theorem sp10351 : smallValid 10351 46 := by unfold smallValid; decide +kernel

private theorem sp10397 : smallValid 10397 46 := by unfold smallValid; decide +kernel

private theorem sp10443 : smallValid 10443 45 := by unfold smallValid; decide +kernel

private theorem sp10488 : smallValid 10488 46 := by unfold smallValid; decide +kernel

private theorem sp10534 : smallValid 10534 46 := by unfold smallValid; decide +kernel

private theorem sp10580 : smallValid 10580 46 := by unfold smallValid; decide +kernel

private theorem sp10626 : smallValid 10626 45 := by unfold smallValid; decide +kernel

private theorem sp10671 : smallValid 10671 46 := by unfold smallValid; decide +kernel

private theorem sp10717 : smallValid 10717 46 := by unfold smallValid; decide +kernel

private theorem sp10763 : smallValid 10763 46 := by unfold smallValid; decide +kernel

private theorem sp10809 : smallValid 10809 46 := by unfold smallValid; decide +kernel

private theorem sp10855 : smallValid 10855 46 := by unfold smallValid; decide +kernel

private theorem sp10901 : smallValid 10901 46 := by unfold smallValid; decide +kernel

private theorem sp10947 : smallValid 10947 46 := by unfold smallValid; decide +kernel

private theorem sp10993 : smallValid 10993 45 := by unfold smallValid; decide +kernel

private theorem sp11038 : smallValid 11038 46 := by unfold smallValid; decide +kernel

private theorem sp11084 : smallValid 11084 46 := by unfold smallValid; decide +kernel

private theorem sp11130 : smallValid 11130 46 := by unfold smallValid; decide +kernel

private theorem sp11176 : smallValid 11176 45 := by unfold smallValid; decide +kernel

private theorem sp11221 : smallValid 11221 46 := by unfold smallValid; decide +kernel

private theorem sp11267 : smallValid 11267 46 := by unfold smallValid; decide +kernel

private theorem sp11313 : smallValid 11313 46 := by unfold smallValid; decide +kernel

private theorem sp11359 : smallValid 11359 45 := by unfold smallValid; decide +kernel

private theorem sp11404 : smallValid 11404 46 := by unfold smallValid; decide +kernel

private theorem sp11450 : smallValid 11450 46 := by unfold smallValid; decide +kernel

private theorem sp11496 : smallValid 11496 46 := by unfold smallValid; decide +kernel

private theorem sp11542 : smallValid 11542 46 := by unfold smallValid; decide +kernel

private theorem sp11588 : smallValid 11588 46 := by unfold smallValid; decide +kernel

private theorem sp11634 : smallValid 11634 46 := by unfold smallValid; decide +kernel

private theorem sp11680 : smallValid 11680 46 := by unfold smallValid; decide +kernel

private theorem sp11726 : smallValid 11726 45 := by unfold smallValid; decide +kernel

private theorem sp11771 : smallValid 11771 46 := by unfold smallValid; decide +kernel

private theorem sp11817 : smallValid 11817 46 := by unfold smallValid; decide +kernel

private theorem sp11863 : smallValid 11863 46 := by unfold smallValid; decide +kernel

private theorem sp11909 : smallValid 11909 45 := by unfold smallValid; decide +kernel

private theorem sp11954 : smallValid 11954 46 := by unfold smallValid; decide +kernel

private theorem sp12000 : smallValid 12000 46 := by unfold smallValid; decide +kernel

private theorem sp12046 : smallValid 12046 46 := by unfold smallValid; decide +kernel

private theorem sp12092 : smallValid 12092 45 := by unfold smallValid; decide +kernel

private theorem sp12137 : smallValid 12137 46 := by unfold smallValid; decide +kernel

private theorem sp12183 : smallValid 12183 46 := by unfold smallValid; decide +kernel

private theorem sp12229 : smallValid 12229 46 := by unfold smallValid; decide +kernel

private theorem sp12275 : smallValid 12275 45 := by unfold smallValid; decide +kernel

private theorem sp12320 : smallValid 12320 46 := by unfold smallValid; decide +kernel

private theorem sp12366 : smallValid 12366 46 := by unfold smallValid; decide +kernel

private theorem sp12412 : smallValid 12412 46 := by unfold smallValid; decide +kernel

private theorem sp12458 : smallValid 12458 45 := by unfold smallValid; decide +kernel

private theorem sp12503 : smallValid 12503 46 := by unfold smallValid; decide +kernel

private theorem sp12549 : smallValid 12549 46 := by unfold smallValid; decide +kernel

private theorem sp12595 : smallValid 12595 46 := by unfold smallValid; decide +kernel

private theorem sp12641 : smallValid 12641 45 := by unfold smallValid; decide +kernel

private theorem sp12686 : smallValid 12686 46 := by unfold smallValid; decide +kernel

private theorem sp12732 : smallValid 12732 46 := by unfold smallValid; decide +kernel

private theorem sp12778 : smallValid 12778 46 := by unfold smallValid; decide +kernel

private theorem sp12824 : smallValid 12824 45 := by unfold smallValid; decide +kernel

private theorem sp12869 : smallValid 12869 46 := by unfold smallValid; decide +kernel

private theorem sp12915 : smallValid 12915 46 := by unfold smallValid; decide +kernel

private theorem sp12961 : smallValid 12961 46 := by unfold smallValid; decide +kernel

private theorem sp13007 : smallValid 13007 46 := by unfold smallValid; decide +kernel

private theorem sp13053 : smallValid 13053 46 := by unfold smallValid; decide +kernel

private theorem sp13099 : smallValid 13099 46 := by unfold smallValid; decide +kernel

private theorem sp13145 : smallValid 13145 46 := by unfold smallValid; decide +kernel

private theorem sp13191 : smallValid 13191 45 := by unfold smallValid; decide +kernel

private theorem sp13236 : smallValid 13236 46 := by unfold smallValid; decide +kernel

private theorem sp13282 : smallValid 13282 46 := by unfold smallValid; decide +kernel

private theorem sp13328 : smallValid 13328 46 := by unfold smallValid; decide +kernel

private theorem sp13374 : smallValid 13374 45 := by unfold smallValid; decide +kernel

private theorem sp13419 : smallValid 13419 46 := by unfold smallValid; decide +kernel

private theorem sp13465 : smallValid 13465 46 := by unfold smallValid; decide +kernel

private theorem sp13511 : smallValid 13511 46 := by unfold smallValid; decide +kernel

private theorem sp13557 : smallValid 13557 45 := by unfold smallValid; decide +kernel

private theorem sp13602 : smallValid 13602 46 := by unfold smallValid; decide +kernel

private theorem sp13648 : smallValid 13648 46 := by unfold smallValid; decide +kernel

private theorem sp13694 : smallValid 13694 46 := by unfold smallValid; decide +kernel

private theorem sp13740 : smallValid 13740 46 := by unfold smallValid; decide +kernel

private theorem sp13786 : smallValid 13786 46 := by unfold smallValid; decide +kernel

private theorem sp13832 : smallValid 13832 46 := by unfold smallValid; decide +kernel

private theorem sp13878 : smallValid 13878 46 := by unfold smallValid; decide +kernel

private theorem sp13924 : smallValid 13924 45 := by unfold smallValid; decide +kernel

private theorem sp13969 : smallValid 13969 46 := by unfold smallValid; decide +kernel

private theorem sp14015 : smallValid 14015 46 := by unfold smallValid; decide +kernel

private theorem sp14061 : smallValid 14061 46 := by unfold smallValid; decide +kernel

private theorem sp14107 : smallValid 14107 45 := by unfold smallValid; decide +kernel

private theorem sp14152 : smallValid 14152 46 := by unfold smallValid; decide +kernel

private theorem sp14198 : smallValid 14198 46 := by unfold smallValid; decide +kernel

private theorem sp14244 : smallValid 14244 46 := by unfold smallValid; decide +kernel

private theorem sp14290 : smallValid 14290 45 := by unfold smallValid; decide +kernel

private theorem sp14335 : smallValid 14335 46 := by unfold smallValid; decide +kernel

private theorem sp14381 : smallValid 14381 46 := by unfold smallValid; decide +kernel

private theorem sp14427 : smallValid 14427 46 := by unfold smallValid; decide +kernel

private theorem sp14473 : smallValid 14473 46 := by unfold smallValid; decide +kernel

private theorem sp14519 : smallValid 14519 46 := by unfold smallValid; decide +kernel

private theorem sp14565 : smallValid 14565 46 := by unfold smallValid; decide +kernel

private theorem sp14611 : smallValid 14611 46 := by unfold smallValid; decide +kernel

private theorem sp14657 : smallValid 14657 45 := by unfold smallValid; decide +kernel

private theorem sp14702 : smallValid 14702 46 := by unfold smallValid; decide +kernel

private theorem sp14748 : smallValid 14748 46 := by unfold smallValid; decide +kernel

private theorem sp14794 : smallValid 14794 46 := by unfold smallValid; decide +kernel

private theorem sp14840 : smallValid 14840 45 := by unfold smallValid; decide +kernel

private theorem sp14885 : smallValid 14885 46 := by unfold smallValid; decide +kernel

private theorem sp14931 : smallValid 14931 46 := by unfold smallValid; decide +kernel

private theorem sp14977 : smallValid 14977 46 := by unfold smallValid; decide +kernel

private theorem sp15023 : smallValid 15023 45 := by unfold smallValid; decide +kernel

private theorem sp15068 : smallValid 15068 46 := by unfold smallValid; decide +kernel

private theorem sp15114 : smallValid 15114 46 := by unfold smallValid; decide +kernel

private theorem sp15160 : smallValid 15160 46 := by unfold smallValid; decide +kernel

private theorem sp15206 : smallValid 15206 46 := by unfold smallValid; decide +kernel

private theorem sp15252 : smallValid 15252 46 := by unfold smallValid; decide +kernel

private theorem sp15298 : smallValid 15298 46 := by unfold smallValid; decide +kernel

private theorem sp15344 : smallValid 15344 46 := by unfold smallValid; decide +kernel

private theorem sp15390 : smallValid 15390 45 := by unfold smallValid; decide +kernel

private theorem sp15435 : smallValid 15435 46 := by unfold smallValid; decide +kernel

private theorem sp15481 : smallValid 15481 46 := by unfold smallValid; decide +kernel

private theorem sp15527 : smallValid 15527 46 := by unfold smallValid; decide +kernel

private theorem sp15573 : smallValid 15573 45 := by unfold smallValid; decide +kernel

private theorem sp15618 : smallValid 15618 46 := by unfold smallValid; decide +kernel

private theorem sp15664 : smallValid 15664 46 := by unfold smallValid; decide +kernel

private theorem sp15710 : smallValid 15710 46 := by unfold smallValid; decide +kernel

private theorem sp15756 : smallValid 15756 45 := by unfold smallValid; decide +kernel

private theorem sp15801 : smallValid 15801 46 := by unfold smallValid; decide +kernel

private theorem sp15847 : smallValid 15847 46 := by unfold smallValid; decide +kernel

private theorem sp15893 : smallValid 15893 46 := by unfold smallValid; decide +kernel

private theorem sp15939 : smallValid 15939 46 := by unfold smallValid; decide +kernel

private theorem sp15985 : smallValid 15985 46 := by unfold smallValid; decide +kernel

private theorem sp16031 : smallValid 16031 46 := by unfold smallValid; decide +kernel

private theorem sp16077 : smallValid 16077 46 := by unfold smallValid; decide +kernel

private theorem sp16123 : smallValid 16123 45 := by unfold smallValid; decide +kernel

private theorem sp16168 : smallValid 16168 46 := by unfold smallValid; decide +kernel

private theorem sp16214 : smallValid 16214 46 := by unfold smallValid; decide +kernel

private theorem sp16260 : smallValid 16260 46 := by unfold smallValid; decide +kernel

private theorem sp16306 : smallValid 16306 45 := by unfold smallValid; decide +kernel

private theorem sp16351 : smallValid 16351 46 := by unfold smallValid; decide +kernel

private theorem sp16397 : smallValid 16397 46 := by unfold smallValid; decide +kernel

private theorem sp16443 : smallValid 16443 46 := by unfold smallValid; decide +kernel

private theorem sp16489 : smallValid 16489 45 := by unfold smallValid; decide +kernel

private theorem sp16534 : smallValid 16534 46 := by unfold smallValid; decide +kernel

private theorem sp16580 : smallValid 16580 46 := by unfold smallValid; decide +kernel

private theorem sp16626 : smallValid 16626 46 := by unfold smallValid; decide +kernel

private theorem sp16672 : smallValid 16672 46 := by unfold smallValid; decide +kernel

private theorem sp16718 : smallValid 16718 46 := by unfold smallValid; decide +kernel

private theorem sp16764 : smallValid 16764 46 := by unfold smallValid; decide +kernel

private theorem sp16810 : smallValid 16810 46 := by unfold smallValid; decide +kernel

private theorem sp16856 : smallValid 16856 45 := by unfold smallValid; decide +kernel

private theorem sp16901 : smallValid 16901 46 := by unfold smallValid; decide +kernel

private theorem sp16947 : smallValid 16947 46 := by unfold smallValid; decide +kernel

private theorem sp16993 : smallValid 16993 46 := by unfold smallValid; decide +kernel

private theorem sp17039 : smallValid 17039 45 := by unfold smallValid; decide +kernel

private theorem sp17084 : smallValid 17084 46 := by unfold smallValid; decide +kernel

private theorem sp17130 : smallValid 17130 46 := by unfold smallValid; decide +kernel

private theorem sp17176 : smallValid 17176 46 := by unfold smallValid; decide +kernel

private theorem sp17222 : smallValid 17222 45 := by unfold smallValid; decide +kernel

private theorem sp17267 : smallValid 17267 46 := by unfold smallValid; decide +kernel

private theorem sp17313 : smallValid 17313 46 := by unfold smallValid; decide +kernel

private theorem sp17359 : smallValid 17359 46 := by unfold smallValid; decide +kernel

private theorem sp17405 : smallValid 17405 46 := by unfold smallValid; decide +kernel

private theorem sp17451 : smallValid 17451 46 := by unfold smallValid; decide +kernel

private theorem sp17497 : smallValid 17497 46 := by unfold smallValid; decide +kernel

private theorem sp17543 : smallValid 17543 46 := by unfold smallValid; decide +kernel

private theorem sp17589 : smallValid 17589 45 := by unfold smallValid; decide +kernel

private theorem sp17634 : smallValid 17634 46 := by unfold smallValid; decide +kernel

private theorem sp17680 : smallValid 17680 46 := by unfold smallValid; decide +kernel

private theorem sp17726 : smallValid 17726 46 := by unfold smallValid; decide +kernel

private theorem sp17772 : smallValid 17772 45 := by unfold smallValid; decide +kernel

private theorem sp17817 : smallValid 17817 46 := by unfold smallValid; decide +kernel

private theorem sp17863 : smallValid 17863 46 := by unfold smallValid; decide +kernel

private theorem sp17909 : smallValid 17909 46 := by unfold smallValid; decide +kernel

private theorem sp17955 : smallValid 17955 45 := by unfold smallValid; decide +kernel

private theorem sp18000 : smallValid 18000 46 := by unfold smallValid; decide +kernel

private theorem sp18046 : smallValid 18046 46 := by unfold smallValid; decide +kernel

private theorem sp18092 : smallValid 18092 46 := by unfold smallValid; decide +kernel

private theorem sp18138 : smallValid 18138 46 := by unfold smallValid; decide +kernel

private theorem sp18184 : smallValid 18184 46 := by unfold smallValid; decide +kernel

private theorem sp18230 : smallValid 18230 46 := by unfold smallValid; decide +kernel

private theorem sp18276 : smallValid 18276 46 := by unfold smallValid; decide +kernel

private theorem sp18322 : smallValid 18322 45 := by unfold smallValid; decide +kernel

private theorem sp18367 : smallValid 18367 46 := by unfold smallValid; decide +kernel

private theorem sp18413 : smallValid 18413 46 := by unfold smallValid; decide +kernel

private theorem sp18459 : smallValid 18459 46 := by unfold smallValid; decide +kernel

private theorem sp18505 : smallValid 18505 45 := by unfold smallValid; decide +kernel

private theorem sp18550 : smallValid 18550 46 := by unfold smallValid; decide +kernel

private theorem sp18596 : smallValid 18596 46 := by unfold smallValid; decide +kernel

private theorem sp18642 : smallValid 18642 46 := by unfold smallValid; decide +kernel

private theorem sp18688 : smallValid 18688 45 := by unfold smallValid; decide +kernel

private theorem sp18733 : smallValid 18733 46 := by unfold smallValid; decide +kernel

private theorem sp18779 : smallValid 18779 46 := by unfold smallValid; decide +kernel

private theorem sp18825 : smallValid 18825 46 := by unfold smallValid; decide +kernel

private theorem sp18871 : smallValid 18871 46 := by unfold smallValid; decide +kernel

private theorem sp18917 : smallValid 18917 46 := by unfold smallValid; decide +kernel

private theorem sp18963 : smallValid 18963 46 := by unfold smallValid; decide +kernel

private theorem sp19009 : smallValid 19009 46 := by unfold smallValid; decide +kernel

private theorem sp19055 : smallValid 19055 45 := by unfold smallValid; decide +kernel

private theorem sp19100 : smallValid 19100 46 := by unfold smallValid; decide +kernel

private theorem sp19146 : smallValid 19146 46 := by unfold smallValid; decide +kernel

private theorem sp19192 : smallValid 19192 46 := by unfold smallValid; decide +kernel

private theorem sp19238 : smallValid 19238 45 := by unfold smallValid; decide +kernel

private theorem sp19283 : smallValid 19283 46 := by unfold smallValid; decide +kernel

private theorem sp19329 : smallValid 19329 46 := by unfold smallValid; decide +kernel

private theorem sp19375 : smallValid 19375 46 := by unfold smallValid; decide +kernel

private theorem sp19421 : smallValid 19421 45 := by unfold smallValid; decide +kernel

private theorem sp19466 : smallValid 19466 46 := by unfold smallValid; decide +kernel

private theorem sp19512 : smallValid 19512 46 := by unfold smallValid; decide +kernel

private theorem sp19558 : smallValid 19558 46 := by unfold smallValid; decide +kernel

private theorem sp19604 : smallValid 19604 46 := by unfold smallValid; decide +kernel

private theorem sp19650 : smallValid 19650 46 := by unfold smallValid; decide +kernel

private theorem sp19696 : smallValid 19696 46 := by unfold smallValid; decide +kernel

private theorem sp19742 : smallValid 19742 46 := by unfold smallValid; decide +kernel

private theorem sp19788 : smallValid 19788 45 := by unfold smallValid; decide +kernel

private theorem sp19833 : smallValid 19833 46 := by unfold smallValid; decide +kernel

private theorem sp19879 : smallValid 19879 46 := by unfold smallValid; decide +kernel

private theorem sp19925 : smallValid 19925 46 := by unfold smallValid; decide +kernel

private theorem sp19971 : smallValid 19971 45 := by unfold smallValid; decide +kernel

private theorem sp20016 : smallValid 20016 46 := by unfold smallValid; decide +kernel

private theorem sp20062 : smallValid 20062 46 := by unfold smallValid; decide +kernel

private theorem sp20108 : smallValid 20108 46 := by unfold smallValid; decide +kernel

private theorem sp20154 : smallValid 20154 45 := by unfold smallValid; decide +kernel

private theorem sp20199 : smallValid 20199 46 := by unfold smallValid; decide +kernel

private theorem sp20245 : smallValid 20245 46 := by unfold smallValid; decide +kernel

private theorem sp20291 : smallValid 20291 46 := by unfold smallValid; decide +kernel

private theorem sp20337 : smallValid 20337 46 := by unfold smallValid; decide +kernel

private theorem sp20383 : smallValid 20383 46 := by unfold smallValid; decide +kernel

private theorem sp20429 : smallValid 20429 46 := by unfold smallValid; decide +kernel

private theorem sp20475 : smallValid 20475 46 := by unfold smallValid; decide +kernel

private theorem sp20521 : smallValid 20521 45 := by unfold smallValid; decide +kernel

private theorem sp20566 : smallValid 20566 46 := by unfold smallValid; decide +kernel

private theorem sp20612 : smallValid 20612 46 := by unfold smallValid; decide +kernel

private theorem sp20658 : smallValid 20658 46 := by unfold smallValid; decide +kernel

private theorem sp20704 : smallValid 20704 45 := by unfold smallValid; decide +kernel

private theorem sp20749 : smallValid 20749 46 := by unfold smallValid; decide +kernel

private theorem sp20795 : smallValid 20795 46 := by unfold smallValid; decide +kernel

private theorem sp20841 : smallValid 20841 46 := by unfold smallValid; decide +kernel

private theorem sp20887 : smallValid 20887 45 := by unfold smallValid; decide +kernel

private theorem sp20932 : smallValid 20932 46 := by unfold smallValid; decide +kernel

private theorem sp20978 : smallValid 20978 46 := by unfold smallValid; decide +kernel

private theorem sp21024 : smallValid 21024 46 := by unfold smallValid; decide +kernel

private theorem sp21070 : smallValid 21070 46 := by unfold smallValid; decide +kernel

private theorem sp21116 : smallValid 21116 46 := by unfold smallValid; decide +kernel

private theorem sp21162 : smallValid 21162 46 := by unfold smallValid; decide +kernel

private theorem sp21208 : smallValid 21208 46 := by unfold smallValid; decide +kernel

private theorem sp21254 : smallValid 21254 45 := by unfold smallValid; decide +kernel

private theorem sp21299 : smallValid 21299 46 := by unfold smallValid; decide +kernel

private theorem sp21345 : smallValid 21345 46 := by unfold smallValid; decide +kernel

private theorem sp21391 : smallValid 21391 46 := by unfold smallValid; decide +kernel

private theorem sp21437 : smallValid 21437 45 := by unfold smallValid; decide +kernel

private theorem sp21482 : smallValid 21482 46 := by unfold smallValid; decide +kernel

private theorem sp21528 : smallValid 21528 46 := by unfold smallValid; decide +kernel

private theorem sp21574 : smallValid 21574 46 := by unfold smallValid; decide +kernel

private theorem sp21620 : smallValid 21620 45 := by unfold smallValid; decide +kernel

private theorem sp21665 : smallValid 21665 46 := by unfold smallValid; decide +kernel

private theorem sp21711 : smallValid 21711 46 := by unfold smallValid; decide +kernel

private theorem sp21757 : smallValid 21757 46 := by unfold smallValid; decide +kernel

private theorem sp21803 : smallValid 21803 46 := by unfold smallValid; decide +kernel

private theorem sp21849 : smallValid 21849 46 := by unfold smallValid; decide +kernel

private theorem sp21895 : smallValid 21895 46 := by unfold smallValid; decide +kernel

private theorem sp21941 : smallValid 21941 46 := by unfold smallValid; decide +kernel

private theorem sp21987 : smallValid 21987 45 := by unfold smallValid; decide +kernel

private theorem sp22032 : smallValid 22032 46 := by unfold smallValid; decide +kernel

private theorem sp22078 : smallValid 22078 46 := by unfold smallValid; decide +kernel

private theorem sp22124 : smallValid 22124 46 := by unfold smallValid; decide +kernel

private theorem sp22170 : smallValid 22170 45 := by unfold smallValid; decide +kernel

private theorem sp22215 : smallValid 22215 46 := by unfold smallValid; decide +kernel

private theorem sp22261 : smallValid 22261 46 := by unfold smallValid; decide +kernel

private theorem sp22307 : smallValid 22307 46 := by unfold smallValid; decide +kernel

private theorem sp22353 : smallValid 22353 45 := by unfold smallValid; decide +kernel

private theorem sp22398 : smallValid 22398 46 := by unfold smallValid; decide +kernel

private theorem sp22444 : smallValid 22444 46 := by unfold smallValid; decide +kernel

private theorem sp22490 : smallValid 22490 46 := by unfold smallValid; decide +kernel

private theorem sp22536 : smallValid 22536 46 := by unfold smallValid; decide +kernel

private theorem sp22582 : smallValid 22582 46 := by unfold smallValid; decide +kernel

private theorem sp22628 : smallValid 22628 46 := by unfold smallValid; decide +kernel

private theorem sp22674 : smallValid 22674 46 := by unfold smallValid; decide +kernel

private theorem sp22720 : smallValid 22720 45 := by unfold smallValid; decide +kernel

private theorem sp22765 : smallValid 22765 46 := by unfold smallValid; decide +kernel

private theorem sp22811 : smallValid 22811 46 := by unfold smallValid; decide +kernel

private theorem sp22857 : smallValid 22857 46 := by unfold smallValid; decide +kernel

private theorem sp22903 : smallValid 22903 45 := by unfold smallValid; decide +kernel

private theorem sp22948 : smallValid 22948 46 := by unfold smallValid; decide +kernel

private theorem sp22994 : smallValid 22994 46 := by unfold smallValid; decide +kernel

private theorem sp23040 : smallValid 23040 46 := by unfold smallValid; decide +kernel

private theorem sp23086 : smallValid 23086 45 := by unfold smallValid; decide +kernel

private theorem sp23131 : smallValid 23131 46 := by unfold smallValid; decide +kernel

private theorem sp23177 : smallValid 23177 46 := by unfold smallValid; decide +kernel

private theorem sp23223 : smallValid 23223 46 := by unfold smallValid; decide +kernel

private theorem sp23269 : smallValid 23269 46 := by unfold smallValid; decide +kernel

private theorem sp23315 : smallValid 23315 46 := by unfold smallValid; decide +kernel

private theorem sp23361 : smallValid 23361 46 := by unfold smallValid; decide +kernel

private theorem sp23407 : smallValid 23407 46 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤23452) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 23453 := (joinSmall (lo:=0) (a:=11726) (b:=11727) (joinSmall (lo:=0) (a:=5863) (b:=5863) (joinSmall (lo:=0) (a:=2931) (b:=2932) (joinSmall (lo:=0) (a:=1465) (b:=1466) (joinSmall (lo:=0) (a:=732) (b:=733) (joinSmall (lo:=0) (a:=366) (b:=366) (joinSmall (lo:=0) (a:=183) (b:=183) (joinSmall (lo:=0) (a:=91) (b:=92) (joinSmall (lo:=0) (a:=45) (b:=46) sp0 sp45) (joinSmall (lo:=91) (a:=46) (b:=46) sp91 sp137)) (joinSmall (lo:=183) (a:=91) (b:=92) (joinSmall (lo:=183) (a:=45) (b:=46) sp183 sp228) (joinSmall (lo:=274) (a:=46) (b:=46) sp274 sp320))) (joinSmall (lo:=366) (a:=183) (b:=183) (joinSmall (lo:=366) (a:=91) (b:=92) (joinSmall (lo:=366) (a:=45) (b:=46) sp366 sp411) (joinSmall (lo:=457) (a:=46) (b:=46) sp457 sp503)) (joinSmall (lo:=549) (a:=91) (b:=92) (joinSmall (lo:=549) (a:=45) (b:=46) sp549 sp594) (joinSmall (lo:=640) (a:=46) (b:=46) sp640 sp686)))) (joinSmall (lo:=732) (a:=366) (b:=367) (joinSmall (lo:=732) (a:=183) (b:=183) (joinSmall (lo:=732) (a:=91) (b:=92) (joinSmall (lo:=732) (a:=45) (b:=46) sp732 sp777) (joinSmall (lo:=823) (a:=46) (b:=46) sp823 sp869)) (joinSmall (lo:=915) (a:=91) (b:=92) (joinSmall (lo:=915) (a:=45) (b:=46) sp915 sp960) (joinSmall (lo:=1006) (a:=46) (b:=46) sp1006 sp1052))) (joinSmall (lo:=1098) (a:=183) (b:=184) (joinSmall (lo:=1098) (a:=91) (b:=92) (joinSmall (lo:=1098) (a:=45) (b:=46) sp1098 sp1143) (joinSmall (lo:=1189) (a:=46) (b:=46) sp1189 sp1235)) (joinSmall (lo:=1281) (a:=92) (b:=92) (joinSmall (lo:=1281) (a:=46) (b:=46) sp1281 sp1327) (joinSmall (lo:=1373) (a:=46) (b:=46) sp1373 sp1419))))) (joinSmall (lo:=1465) (a:=733) (b:=733) (joinSmall (lo:=1465) (a:=366) (b:=367) (joinSmall (lo:=1465) (a:=183) (b:=183) (joinSmall (lo:=1465) (a:=91) (b:=92) (joinSmall (lo:=1465) (a:=45) (b:=46) sp1465 sp1510) (joinSmall (lo:=1556) (a:=46) (b:=46) sp1556 sp1602)) (joinSmall (lo:=1648) (a:=91) (b:=92) (joinSmall (lo:=1648) (a:=45) (b:=46) sp1648 sp1693) (joinSmall (lo:=1739) (a:=46) (b:=46) sp1739 sp1785))) (joinSmall (lo:=1831) (a:=183) (b:=184) (joinSmall (lo:=1831) (a:=91) (b:=92) (joinSmall (lo:=1831) (a:=45) (b:=46) sp1831 sp1876) (joinSmall (lo:=1922) (a:=46) (b:=46) sp1922 sp1968)) (joinSmall (lo:=2014) (a:=92) (b:=92) (joinSmall (lo:=2014) (a:=46) (b:=46) sp2014 sp2060) (joinSmall (lo:=2106) (a:=46) (b:=46) sp2106 sp2152)))) (joinSmall (lo:=2198) (a:=366) (b:=367) (joinSmall (lo:=2198) (a:=183) (b:=183) (joinSmall (lo:=2198) (a:=91) (b:=92) (joinSmall (lo:=2198) (a:=45) (b:=46) sp2198 sp2243) (joinSmall (lo:=2289) (a:=46) (b:=46) sp2289 sp2335)) (joinSmall (lo:=2381) (a:=91) (b:=92) (joinSmall (lo:=2381) (a:=45) (b:=46) sp2381 sp2426) (joinSmall (lo:=2472) (a:=46) (b:=46) sp2472 sp2518))) (joinSmall (lo:=2564) (a:=183) (b:=184) (joinSmall (lo:=2564) (a:=91) (b:=92) (joinSmall (lo:=2564) (a:=45) (b:=46) sp2564 sp2609) (joinSmall (lo:=2655) (a:=46) (b:=46) sp2655 sp2701)) (joinSmall (lo:=2747) (a:=92) (b:=92) (joinSmall (lo:=2747) (a:=46) (b:=46) sp2747 sp2793) (joinSmall (lo:=2839) (a:=46) (b:=46) sp2839 sp2885)))))) (joinSmall (lo:=2931) (a:=1466) (b:=1466) (joinSmall (lo:=2931) (a:=733) (b:=733) (joinSmall (lo:=2931) (a:=366) (b:=367) (joinSmall (lo:=2931) (a:=183) (b:=183) (joinSmall (lo:=2931) (a:=91) (b:=92) (joinSmall (lo:=2931) (a:=45) (b:=46) sp2931 sp2976) (joinSmall (lo:=3022) (a:=46) (b:=46) sp3022 sp3068)) (joinSmall (lo:=3114) (a:=91) (b:=92) (joinSmall (lo:=3114) (a:=45) (b:=46) sp3114 sp3159) (joinSmall (lo:=3205) (a:=46) (b:=46) sp3205 sp3251))) (joinSmall (lo:=3297) (a:=183) (b:=184) (joinSmall (lo:=3297) (a:=91) (b:=92) (joinSmall (lo:=3297) (a:=45) (b:=46) sp3297 sp3342) (joinSmall (lo:=3388) (a:=46) (b:=46) sp3388 sp3434)) (joinSmall (lo:=3480) (a:=92) (b:=92) (joinSmall (lo:=3480) (a:=46) (b:=46) sp3480 sp3526) (joinSmall (lo:=3572) (a:=46) (b:=46) sp3572 sp3618)))) (joinSmall (lo:=3664) (a:=366) (b:=367) (joinSmall (lo:=3664) (a:=183) (b:=183) (joinSmall (lo:=3664) (a:=91) (b:=92) (joinSmall (lo:=3664) (a:=45) (b:=46) sp3664 sp3709) (joinSmall (lo:=3755) (a:=46) (b:=46) sp3755 sp3801)) (joinSmall (lo:=3847) (a:=91) (b:=92) (joinSmall (lo:=3847) (a:=45) (b:=46) sp3847 sp3892) (joinSmall (lo:=3938) (a:=46) (b:=46) sp3938 sp3984))) (joinSmall (lo:=4030) (a:=183) (b:=184) (joinSmall (lo:=4030) (a:=91) (b:=92) (joinSmall (lo:=4030) (a:=45) (b:=46) sp4030 sp4075) (joinSmall (lo:=4121) (a:=46) (b:=46) sp4121 sp4167)) (joinSmall (lo:=4213) (a:=92) (b:=92) (joinSmall (lo:=4213) (a:=46) (b:=46) sp4213 sp4259) (joinSmall (lo:=4305) (a:=46) (b:=46) sp4305 sp4351))))) (joinSmall (lo:=4397) (a:=733) (b:=733) (joinSmall (lo:=4397) (a:=366) (b:=367) (joinSmall (lo:=4397) (a:=183) (b:=183) (joinSmall (lo:=4397) (a:=91) (b:=92) (joinSmall (lo:=4397) (a:=45) (b:=46) sp4397 sp4442) (joinSmall (lo:=4488) (a:=46) (b:=46) sp4488 sp4534)) (joinSmall (lo:=4580) (a:=91) (b:=92) (joinSmall (lo:=4580) (a:=45) (b:=46) sp4580 sp4625) (joinSmall (lo:=4671) (a:=46) (b:=46) sp4671 sp4717))) (joinSmall (lo:=4763) (a:=183) (b:=184) (joinSmall (lo:=4763) (a:=91) (b:=92) (joinSmall (lo:=4763) (a:=45) (b:=46) sp4763 sp4808) (joinSmall (lo:=4854) (a:=46) (b:=46) sp4854 sp4900)) (joinSmall (lo:=4946) (a:=92) (b:=92) (joinSmall (lo:=4946) (a:=46) (b:=46) sp4946 sp4992) (joinSmall (lo:=5038) (a:=46) (b:=46) sp5038 sp5084)))) (joinSmall (lo:=5130) (a:=366) (b:=367) (joinSmall (lo:=5130) (a:=183) (b:=183) (joinSmall (lo:=5130) (a:=91) (b:=92) (joinSmall (lo:=5130) (a:=45) (b:=46) sp5130 sp5175) (joinSmall (lo:=5221) (a:=46) (b:=46) sp5221 sp5267)) (joinSmall (lo:=5313) (a:=91) (b:=92) (joinSmall (lo:=5313) (a:=45) (b:=46) sp5313 sp5358) (joinSmall (lo:=5404) (a:=46) (b:=46) sp5404 sp5450))) (joinSmall (lo:=5496) (a:=183) (b:=184) (joinSmall (lo:=5496) (a:=91) (b:=92) (joinSmall (lo:=5496) (a:=45) (b:=46) sp5496 sp5541) (joinSmall (lo:=5587) (a:=46) (b:=46) sp5587 sp5633)) (joinSmall (lo:=5679) (a:=92) (b:=92) (joinSmall (lo:=5679) (a:=46) (b:=46) sp5679 sp5725) (joinSmall (lo:=5771) (a:=46) (b:=46) sp5771 sp5817))))))) (joinSmall (lo:=5863) (a:=2931) (b:=2932) (joinSmall (lo:=5863) (a:=1465) (b:=1466) (joinSmall (lo:=5863) (a:=732) (b:=733) (joinSmall (lo:=5863) (a:=366) (b:=366) (joinSmall (lo:=5863) (a:=183) (b:=183) (joinSmall (lo:=5863) (a:=91) (b:=92) (joinSmall (lo:=5863) (a:=45) (b:=46) sp5863 sp5908) (joinSmall (lo:=5954) (a:=46) (b:=46) sp5954 sp6000)) (joinSmall (lo:=6046) (a:=91) (b:=92) (joinSmall (lo:=6046) (a:=45) (b:=46) sp6046 sp6091) (joinSmall (lo:=6137) (a:=46) (b:=46) sp6137 sp6183))) (joinSmall (lo:=6229) (a:=183) (b:=183) (joinSmall (lo:=6229) (a:=91) (b:=92) (joinSmall (lo:=6229) (a:=45) (b:=46) sp6229 sp6274) (joinSmall (lo:=6320) (a:=46) (b:=46) sp6320 sp6366)) (joinSmall (lo:=6412) (a:=91) (b:=92) (joinSmall (lo:=6412) (a:=45) (b:=46) sp6412 sp6457) (joinSmall (lo:=6503) (a:=46) (b:=46) sp6503 sp6549)))) (joinSmall (lo:=6595) (a:=366) (b:=367) (joinSmall (lo:=6595) (a:=183) (b:=183) (joinSmall (lo:=6595) (a:=91) (b:=92) (joinSmall (lo:=6595) (a:=45) (b:=46) sp6595 sp6640) (joinSmall (lo:=6686) (a:=46) (b:=46) sp6686 sp6732)) (joinSmall (lo:=6778) (a:=91) (b:=92) (joinSmall (lo:=6778) (a:=45) (b:=46) sp6778 sp6823) (joinSmall (lo:=6869) (a:=46) (b:=46) sp6869 sp6915))) (joinSmall (lo:=6961) (a:=183) (b:=184) (joinSmall (lo:=6961) (a:=91) (b:=92) (joinSmall (lo:=6961) (a:=45) (b:=46) sp6961 sp7006) (joinSmall (lo:=7052) (a:=46) (b:=46) sp7052 sp7098)) (joinSmall (lo:=7144) (a:=92) (b:=92) (joinSmall (lo:=7144) (a:=46) (b:=46) sp7144 sp7190) (joinSmall (lo:=7236) (a:=46) (b:=46) sp7236 sp7282))))) (joinSmall (lo:=7328) (a:=733) (b:=733) (joinSmall (lo:=7328) (a:=366) (b:=367) (joinSmall (lo:=7328) (a:=183) (b:=183) (joinSmall (lo:=7328) (a:=91) (b:=92) (joinSmall (lo:=7328) (a:=45) (b:=46) sp7328 sp7373) (joinSmall (lo:=7419) (a:=46) (b:=46) sp7419 sp7465)) (joinSmall (lo:=7511) (a:=91) (b:=92) (joinSmall (lo:=7511) (a:=45) (b:=46) sp7511 sp7556) (joinSmall (lo:=7602) (a:=46) (b:=46) sp7602 sp7648))) (joinSmall (lo:=7694) (a:=183) (b:=184) (joinSmall (lo:=7694) (a:=91) (b:=92) (joinSmall (lo:=7694) (a:=45) (b:=46) sp7694 sp7739) (joinSmall (lo:=7785) (a:=46) (b:=46) sp7785 sp7831)) (joinSmall (lo:=7877) (a:=92) (b:=92) (joinSmall (lo:=7877) (a:=46) (b:=46) sp7877 sp7923) (joinSmall (lo:=7969) (a:=46) (b:=46) sp7969 sp8015)))) (joinSmall (lo:=8061) (a:=366) (b:=367) (joinSmall (lo:=8061) (a:=183) (b:=183) (joinSmall (lo:=8061) (a:=91) (b:=92) (joinSmall (lo:=8061) (a:=45) (b:=46) sp8061 sp8106) (joinSmall (lo:=8152) (a:=46) (b:=46) sp8152 sp8198)) (joinSmall (lo:=8244) (a:=91) (b:=92) (joinSmall (lo:=8244) (a:=45) (b:=46) sp8244 sp8289) (joinSmall (lo:=8335) (a:=46) (b:=46) sp8335 sp8381))) (joinSmall (lo:=8427) (a:=183) (b:=184) (joinSmall (lo:=8427) (a:=91) (b:=92) (joinSmall (lo:=8427) (a:=45) (b:=46) sp8427 sp8472) (joinSmall (lo:=8518) (a:=46) (b:=46) sp8518 sp8564)) (joinSmall (lo:=8610) (a:=92) (b:=92) (joinSmall (lo:=8610) (a:=46) (b:=46) sp8610 sp8656) (joinSmall (lo:=8702) (a:=46) (b:=46) sp8702 sp8748)))))) (joinSmall (lo:=8794) (a:=1466) (b:=1466) (joinSmall (lo:=8794) (a:=733) (b:=733) (joinSmall (lo:=8794) (a:=366) (b:=367) (joinSmall (lo:=8794) (a:=183) (b:=183) (joinSmall (lo:=8794) (a:=91) (b:=92) (joinSmall (lo:=8794) (a:=45) (b:=46) sp8794 sp8839) (joinSmall (lo:=8885) (a:=46) (b:=46) sp8885 sp8931)) (joinSmall (lo:=8977) (a:=91) (b:=92) (joinSmall (lo:=8977) (a:=45) (b:=46) sp8977 sp9022) (joinSmall (lo:=9068) (a:=46) (b:=46) sp9068 sp9114))) (joinSmall (lo:=9160) (a:=183) (b:=184) (joinSmall (lo:=9160) (a:=91) (b:=92) (joinSmall (lo:=9160) (a:=45) (b:=46) sp9160 sp9205) (joinSmall (lo:=9251) (a:=46) (b:=46) sp9251 sp9297)) (joinSmall (lo:=9343) (a:=92) (b:=92) (joinSmall (lo:=9343) (a:=46) (b:=46) sp9343 sp9389) (joinSmall (lo:=9435) (a:=46) (b:=46) sp9435 sp9481)))) (joinSmall (lo:=9527) (a:=366) (b:=367) (joinSmall (lo:=9527) (a:=183) (b:=183) (joinSmall (lo:=9527) (a:=91) (b:=92) (joinSmall (lo:=9527) (a:=45) (b:=46) sp9527 sp9572) (joinSmall (lo:=9618) (a:=46) (b:=46) sp9618 sp9664)) (joinSmall (lo:=9710) (a:=91) (b:=92) (joinSmall (lo:=9710) (a:=45) (b:=46) sp9710 sp9755) (joinSmall (lo:=9801) (a:=46) (b:=46) sp9801 sp9847))) (joinSmall (lo:=9893) (a:=183) (b:=184) (joinSmall (lo:=9893) (a:=91) (b:=92) (joinSmall (lo:=9893) (a:=45) (b:=46) sp9893 sp9938) (joinSmall (lo:=9984) (a:=46) (b:=46) sp9984 sp10030)) (joinSmall (lo:=10076) (a:=92) (b:=92) (joinSmall (lo:=10076) (a:=46) (b:=46) sp10076 sp10122) (joinSmall (lo:=10168) (a:=46) (b:=46) sp10168 sp10214))))) (joinSmall (lo:=10260) (a:=733) (b:=733) (joinSmall (lo:=10260) (a:=366) (b:=367) (joinSmall (lo:=10260) (a:=183) (b:=183) (joinSmall (lo:=10260) (a:=91) (b:=92) (joinSmall (lo:=10260) (a:=45) (b:=46) sp10260 sp10305) (joinSmall (lo:=10351) (a:=46) (b:=46) sp10351 sp10397)) (joinSmall (lo:=10443) (a:=91) (b:=92) (joinSmall (lo:=10443) (a:=45) (b:=46) sp10443 sp10488) (joinSmall (lo:=10534) (a:=46) (b:=46) sp10534 sp10580))) (joinSmall (lo:=10626) (a:=183) (b:=184) (joinSmall (lo:=10626) (a:=91) (b:=92) (joinSmall (lo:=10626) (a:=45) (b:=46) sp10626 sp10671) (joinSmall (lo:=10717) (a:=46) (b:=46) sp10717 sp10763)) (joinSmall (lo:=10809) (a:=92) (b:=92) (joinSmall (lo:=10809) (a:=46) (b:=46) sp10809 sp10855) (joinSmall (lo:=10901) (a:=46) (b:=46) sp10901 sp10947)))) (joinSmall (lo:=10993) (a:=366) (b:=367) (joinSmall (lo:=10993) (a:=183) (b:=183) (joinSmall (lo:=10993) (a:=91) (b:=92) (joinSmall (lo:=10993) (a:=45) (b:=46) sp10993 sp11038) (joinSmall (lo:=11084) (a:=46) (b:=46) sp11084 sp11130)) (joinSmall (lo:=11176) (a:=91) (b:=92) (joinSmall (lo:=11176) (a:=45) (b:=46) sp11176 sp11221) (joinSmall (lo:=11267) (a:=46) (b:=46) sp11267 sp11313))) (joinSmall (lo:=11359) (a:=183) (b:=184) (joinSmall (lo:=11359) (a:=91) (b:=92) (joinSmall (lo:=11359) (a:=45) (b:=46) sp11359 sp11404) (joinSmall (lo:=11450) (a:=46) (b:=46) sp11450 sp11496)) (joinSmall (lo:=11542) (a:=92) (b:=92) (joinSmall (lo:=11542) (a:=46) (b:=46) sp11542 sp11588) (joinSmall (lo:=11634) (a:=46) (b:=46) sp11634 sp11680)))))))) (joinSmall (lo:=11726) (a:=5863) (b:=5864) (joinSmall (lo:=11726) (a:=2931) (b:=2932) (joinSmall (lo:=11726) (a:=1465) (b:=1466) (joinSmall (lo:=11726) (a:=732) (b:=733) (joinSmall (lo:=11726) (a:=366) (b:=366) (joinSmall (lo:=11726) (a:=183) (b:=183) (joinSmall (lo:=11726) (a:=91) (b:=92) (joinSmall (lo:=11726) (a:=45) (b:=46) sp11726 sp11771) (joinSmall (lo:=11817) (a:=46) (b:=46) sp11817 sp11863)) (joinSmall (lo:=11909) (a:=91) (b:=92) (joinSmall (lo:=11909) (a:=45) (b:=46) sp11909 sp11954) (joinSmall (lo:=12000) (a:=46) (b:=46) sp12000 sp12046))) (joinSmall (lo:=12092) (a:=183) (b:=183) (joinSmall (lo:=12092) (a:=91) (b:=92) (joinSmall (lo:=12092) (a:=45) (b:=46) sp12092 sp12137) (joinSmall (lo:=12183) (a:=46) (b:=46) sp12183 sp12229)) (joinSmall (lo:=12275) (a:=91) (b:=92) (joinSmall (lo:=12275) (a:=45) (b:=46) sp12275 sp12320) (joinSmall (lo:=12366) (a:=46) (b:=46) sp12366 sp12412)))) (joinSmall (lo:=12458) (a:=366) (b:=367) (joinSmall (lo:=12458) (a:=183) (b:=183) (joinSmall (lo:=12458) (a:=91) (b:=92) (joinSmall (lo:=12458) (a:=45) (b:=46) sp12458 sp12503) (joinSmall (lo:=12549) (a:=46) (b:=46) sp12549 sp12595)) (joinSmall (lo:=12641) (a:=91) (b:=92) (joinSmall (lo:=12641) (a:=45) (b:=46) sp12641 sp12686) (joinSmall (lo:=12732) (a:=46) (b:=46) sp12732 sp12778))) (joinSmall (lo:=12824) (a:=183) (b:=184) (joinSmall (lo:=12824) (a:=91) (b:=92) (joinSmall (lo:=12824) (a:=45) (b:=46) sp12824 sp12869) (joinSmall (lo:=12915) (a:=46) (b:=46) sp12915 sp12961)) (joinSmall (lo:=13007) (a:=92) (b:=92) (joinSmall (lo:=13007) (a:=46) (b:=46) sp13007 sp13053) (joinSmall (lo:=13099) (a:=46) (b:=46) sp13099 sp13145))))) (joinSmall (lo:=13191) (a:=733) (b:=733) (joinSmall (lo:=13191) (a:=366) (b:=367) (joinSmall (lo:=13191) (a:=183) (b:=183) (joinSmall (lo:=13191) (a:=91) (b:=92) (joinSmall (lo:=13191) (a:=45) (b:=46) sp13191 sp13236) (joinSmall (lo:=13282) (a:=46) (b:=46) sp13282 sp13328)) (joinSmall (lo:=13374) (a:=91) (b:=92) (joinSmall (lo:=13374) (a:=45) (b:=46) sp13374 sp13419) (joinSmall (lo:=13465) (a:=46) (b:=46) sp13465 sp13511))) (joinSmall (lo:=13557) (a:=183) (b:=184) (joinSmall (lo:=13557) (a:=91) (b:=92) (joinSmall (lo:=13557) (a:=45) (b:=46) sp13557 sp13602) (joinSmall (lo:=13648) (a:=46) (b:=46) sp13648 sp13694)) (joinSmall (lo:=13740) (a:=92) (b:=92) (joinSmall (lo:=13740) (a:=46) (b:=46) sp13740 sp13786) (joinSmall (lo:=13832) (a:=46) (b:=46) sp13832 sp13878)))) (joinSmall (lo:=13924) (a:=366) (b:=367) (joinSmall (lo:=13924) (a:=183) (b:=183) (joinSmall (lo:=13924) (a:=91) (b:=92) (joinSmall (lo:=13924) (a:=45) (b:=46) sp13924 sp13969) (joinSmall (lo:=14015) (a:=46) (b:=46) sp14015 sp14061)) (joinSmall (lo:=14107) (a:=91) (b:=92) (joinSmall (lo:=14107) (a:=45) (b:=46) sp14107 sp14152) (joinSmall (lo:=14198) (a:=46) (b:=46) sp14198 sp14244))) (joinSmall (lo:=14290) (a:=183) (b:=184) (joinSmall (lo:=14290) (a:=91) (b:=92) (joinSmall (lo:=14290) (a:=45) (b:=46) sp14290 sp14335) (joinSmall (lo:=14381) (a:=46) (b:=46) sp14381 sp14427)) (joinSmall (lo:=14473) (a:=92) (b:=92) (joinSmall (lo:=14473) (a:=46) (b:=46) sp14473 sp14519) (joinSmall (lo:=14565) (a:=46) (b:=46) sp14565 sp14611)))))) (joinSmall (lo:=14657) (a:=1466) (b:=1466) (joinSmall (lo:=14657) (a:=733) (b:=733) (joinSmall (lo:=14657) (a:=366) (b:=367) (joinSmall (lo:=14657) (a:=183) (b:=183) (joinSmall (lo:=14657) (a:=91) (b:=92) (joinSmall (lo:=14657) (a:=45) (b:=46) sp14657 sp14702) (joinSmall (lo:=14748) (a:=46) (b:=46) sp14748 sp14794)) (joinSmall (lo:=14840) (a:=91) (b:=92) (joinSmall (lo:=14840) (a:=45) (b:=46) sp14840 sp14885) (joinSmall (lo:=14931) (a:=46) (b:=46) sp14931 sp14977))) (joinSmall (lo:=15023) (a:=183) (b:=184) (joinSmall (lo:=15023) (a:=91) (b:=92) (joinSmall (lo:=15023) (a:=45) (b:=46) sp15023 sp15068) (joinSmall (lo:=15114) (a:=46) (b:=46) sp15114 sp15160)) (joinSmall (lo:=15206) (a:=92) (b:=92) (joinSmall (lo:=15206) (a:=46) (b:=46) sp15206 sp15252) (joinSmall (lo:=15298) (a:=46) (b:=46) sp15298 sp15344)))) (joinSmall (lo:=15390) (a:=366) (b:=367) (joinSmall (lo:=15390) (a:=183) (b:=183) (joinSmall (lo:=15390) (a:=91) (b:=92) (joinSmall (lo:=15390) (a:=45) (b:=46) sp15390 sp15435) (joinSmall (lo:=15481) (a:=46) (b:=46) sp15481 sp15527)) (joinSmall (lo:=15573) (a:=91) (b:=92) (joinSmall (lo:=15573) (a:=45) (b:=46) sp15573 sp15618) (joinSmall (lo:=15664) (a:=46) (b:=46) sp15664 sp15710))) (joinSmall (lo:=15756) (a:=183) (b:=184) (joinSmall (lo:=15756) (a:=91) (b:=92) (joinSmall (lo:=15756) (a:=45) (b:=46) sp15756 sp15801) (joinSmall (lo:=15847) (a:=46) (b:=46) sp15847 sp15893)) (joinSmall (lo:=15939) (a:=92) (b:=92) (joinSmall (lo:=15939) (a:=46) (b:=46) sp15939 sp15985) (joinSmall (lo:=16031) (a:=46) (b:=46) sp16031 sp16077))))) (joinSmall (lo:=16123) (a:=733) (b:=733) (joinSmall (lo:=16123) (a:=366) (b:=367) (joinSmall (lo:=16123) (a:=183) (b:=183) (joinSmall (lo:=16123) (a:=91) (b:=92) (joinSmall (lo:=16123) (a:=45) (b:=46) sp16123 sp16168) (joinSmall (lo:=16214) (a:=46) (b:=46) sp16214 sp16260)) (joinSmall (lo:=16306) (a:=91) (b:=92) (joinSmall (lo:=16306) (a:=45) (b:=46) sp16306 sp16351) (joinSmall (lo:=16397) (a:=46) (b:=46) sp16397 sp16443))) (joinSmall (lo:=16489) (a:=183) (b:=184) (joinSmall (lo:=16489) (a:=91) (b:=92) (joinSmall (lo:=16489) (a:=45) (b:=46) sp16489 sp16534) (joinSmall (lo:=16580) (a:=46) (b:=46) sp16580 sp16626)) (joinSmall (lo:=16672) (a:=92) (b:=92) (joinSmall (lo:=16672) (a:=46) (b:=46) sp16672 sp16718) (joinSmall (lo:=16764) (a:=46) (b:=46) sp16764 sp16810)))) (joinSmall (lo:=16856) (a:=366) (b:=367) (joinSmall (lo:=16856) (a:=183) (b:=183) (joinSmall (lo:=16856) (a:=91) (b:=92) (joinSmall (lo:=16856) (a:=45) (b:=46) sp16856 sp16901) (joinSmall (lo:=16947) (a:=46) (b:=46) sp16947 sp16993)) (joinSmall (lo:=17039) (a:=91) (b:=92) (joinSmall (lo:=17039) (a:=45) (b:=46) sp17039 sp17084) (joinSmall (lo:=17130) (a:=46) (b:=46) sp17130 sp17176))) (joinSmall (lo:=17222) (a:=183) (b:=184) (joinSmall (lo:=17222) (a:=91) (b:=92) (joinSmall (lo:=17222) (a:=45) (b:=46) sp17222 sp17267) (joinSmall (lo:=17313) (a:=46) (b:=46) sp17313 sp17359)) (joinSmall (lo:=17405) (a:=92) (b:=92) (joinSmall (lo:=17405) (a:=46) (b:=46) sp17405 sp17451) (joinSmall (lo:=17497) (a:=46) (b:=46) sp17497 sp17543))))))) (joinSmall (lo:=17589) (a:=2932) (b:=2932) (joinSmall (lo:=17589) (a:=1466) (b:=1466) (joinSmall (lo:=17589) (a:=733) (b:=733) (joinSmall (lo:=17589) (a:=366) (b:=367) (joinSmall (lo:=17589) (a:=183) (b:=183) (joinSmall (lo:=17589) (a:=91) (b:=92) (joinSmall (lo:=17589) (a:=45) (b:=46) sp17589 sp17634) (joinSmall (lo:=17680) (a:=46) (b:=46) sp17680 sp17726)) (joinSmall (lo:=17772) (a:=91) (b:=92) (joinSmall (lo:=17772) (a:=45) (b:=46) sp17772 sp17817) (joinSmall (lo:=17863) (a:=46) (b:=46) sp17863 sp17909))) (joinSmall (lo:=17955) (a:=183) (b:=184) (joinSmall (lo:=17955) (a:=91) (b:=92) (joinSmall (lo:=17955) (a:=45) (b:=46) sp17955 sp18000) (joinSmall (lo:=18046) (a:=46) (b:=46) sp18046 sp18092)) (joinSmall (lo:=18138) (a:=92) (b:=92) (joinSmall (lo:=18138) (a:=46) (b:=46) sp18138 sp18184) (joinSmall (lo:=18230) (a:=46) (b:=46) sp18230 sp18276)))) (joinSmall (lo:=18322) (a:=366) (b:=367) (joinSmall (lo:=18322) (a:=183) (b:=183) (joinSmall (lo:=18322) (a:=91) (b:=92) (joinSmall (lo:=18322) (a:=45) (b:=46) sp18322 sp18367) (joinSmall (lo:=18413) (a:=46) (b:=46) sp18413 sp18459)) (joinSmall (lo:=18505) (a:=91) (b:=92) (joinSmall (lo:=18505) (a:=45) (b:=46) sp18505 sp18550) (joinSmall (lo:=18596) (a:=46) (b:=46) sp18596 sp18642))) (joinSmall (lo:=18688) (a:=183) (b:=184) (joinSmall (lo:=18688) (a:=91) (b:=92) (joinSmall (lo:=18688) (a:=45) (b:=46) sp18688 sp18733) (joinSmall (lo:=18779) (a:=46) (b:=46) sp18779 sp18825)) (joinSmall (lo:=18871) (a:=92) (b:=92) (joinSmall (lo:=18871) (a:=46) (b:=46) sp18871 sp18917) (joinSmall (lo:=18963) (a:=46) (b:=46) sp18963 sp19009))))) (joinSmall (lo:=19055) (a:=733) (b:=733) (joinSmall (lo:=19055) (a:=366) (b:=367) (joinSmall (lo:=19055) (a:=183) (b:=183) (joinSmall (lo:=19055) (a:=91) (b:=92) (joinSmall (lo:=19055) (a:=45) (b:=46) sp19055 sp19100) (joinSmall (lo:=19146) (a:=46) (b:=46) sp19146 sp19192)) (joinSmall (lo:=19238) (a:=91) (b:=92) (joinSmall (lo:=19238) (a:=45) (b:=46) sp19238 sp19283) (joinSmall (lo:=19329) (a:=46) (b:=46) sp19329 sp19375))) (joinSmall (lo:=19421) (a:=183) (b:=184) (joinSmall (lo:=19421) (a:=91) (b:=92) (joinSmall (lo:=19421) (a:=45) (b:=46) sp19421 sp19466) (joinSmall (lo:=19512) (a:=46) (b:=46) sp19512 sp19558)) (joinSmall (lo:=19604) (a:=92) (b:=92) (joinSmall (lo:=19604) (a:=46) (b:=46) sp19604 sp19650) (joinSmall (lo:=19696) (a:=46) (b:=46) sp19696 sp19742)))) (joinSmall (lo:=19788) (a:=366) (b:=367) (joinSmall (lo:=19788) (a:=183) (b:=183) (joinSmall (lo:=19788) (a:=91) (b:=92) (joinSmall (lo:=19788) (a:=45) (b:=46) sp19788 sp19833) (joinSmall (lo:=19879) (a:=46) (b:=46) sp19879 sp19925)) (joinSmall (lo:=19971) (a:=91) (b:=92) (joinSmall (lo:=19971) (a:=45) (b:=46) sp19971 sp20016) (joinSmall (lo:=20062) (a:=46) (b:=46) sp20062 sp20108))) (joinSmall (lo:=20154) (a:=183) (b:=184) (joinSmall (lo:=20154) (a:=91) (b:=92) (joinSmall (lo:=20154) (a:=45) (b:=46) sp20154 sp20199) (joinSmall (lo:=20245) (a:=46) (b:=46) sp20245 sp20291)) (joinSmall (lo:=20337) (a:=92) (b:=92) (joinSmall (lo:=20337) (a:=46) (b:=46) sp20337 sp20383) (joinSmall (lo:=20429) (a:=46) (b:=46) sp20429 sp20475)))))) (joinSmall (lo:=20521) (a:=1466) (b:=1466) (joinSmall (lo:=20521) (a:=733) (b:=733) (joinSmall (lo:=20521) (a:=366) (b:=367) (joinSmall (lo:=20521) (a:=183) (b:=183) (joinSmall (lo:=20521) (a:=91) (b:=92) (joinSmall (lo:=20521) (a:=45) (b:=46) sp20521 sp20566) (joinSmall (lo:=20612) (a:=46) (b:=46) sp20612 sp20658)) (joinSmall (lo:=20704) (a:=91) (b:=92) (joinSmall (lo:=20704) (a:=45) (b:=46) sp20704 sp20749) (joinSmall (lo:=20795) (a:=46) (b:=46) sp20795 sp20841))) (joinSmall (lo:=20887) (a:=183) (b:=184) (joinSmall (lo:=20887) (a:=91) (b:=92) (joinSmall (lo:=20887) (a:=45) (b:=46) sp20887 sp20932) (joinSmall (lo:=20978) (a:=46) (b:=46) sp20978 sp21024)) (joinSmall (lo:=21070) (a:=92) (b:=92) (joinSmall (lo:=21070) (a:=46) (b:=46) sp21070 sp21116) (joinSmall (lo:=21162) (a:=46) (b:=46) sp21162 sp21208)))) (joinSmall (lo:=21254) (a:=366) (b:=367) (joinSmall (lo:=21254) (a:=183) (b:=183) (joinSmall (lo:=21254) (a:=91) (b:=92) (joinSmall (lo:=21254) (a:=45) (b:=46) sp21254 sp21299) (joinSmall (lo:=21345) (a:=46) (b:=46) sp21345 sp21391)) (joinSmall (lo:=21437) (a:=91) (b:=92) (joinSmall (lo:=21437) (a:=45) (b:=46) sp21437 sp21482) (joinSmall (lo:=21528) (a:=46) (b:=46) sp21528 sp21574))) (joinSmall (lo:=21620) (a:=183) (b:=184) (joinSmall (lo:=21620) (a:=91) (b:=92) (joinSmall (lo:=21620) (a:=45) (b:=46) sp21620 sp21665) (joinSmall (lo:=21711) (a:=46) (b:=46) sp21711 sp21757)) (joinSmall (lo:=21803) (a:=92) (b:=92) (joinSmall (lo:=21803) (a:=46) (b:=46) sp21803 sp21849) (joinSmall (lo:=21895) (a:=46) (b:=46) sp21895 sp21941))))) (joinSmall (lo:=21987) (a:=733) (b:=733) (joinSmall (lo:=21987) (a:=366) (b:=367) (joinSmall (lo:=21987) (a:=183) (b:=183) (joinSmall (lo:=21987) (a:=91) (b:=92) (joinSmall (lo:=21987) (a:=45) (b:=46) sp21987 sp22032) (joinSmall (lo:=22078) (a:=46) (b:=46) sp22078 sp22124)) (joinSmall (lo:=22170) (a:=91) (b:=92) (joinSmall (lo:=22170) (a:=45) (b:=46) sp22170 sp22215) (joinSmall (lo:=22261) (a:=46) (b:=46) sp22261 sp22307))) (joinSmall (lo:=22353) (a:=183) (b:=184) (joinSmall (lo:=22353) (a:=91) (b:=92) (joinSmall (lo:=22353) (a:=45) (b:=46) sp22353 sp22398) (joinSmall (lo:=22444) (a:=46) (b:=46) sp22444 sp22490)) (joinSmall (lo:=22536) (a:=92) (b:=92) (joinSmall (lo:=22536) (a:=46) (b:=46) sp22536 sp22582) (joinSmall (lo:=22628) (a:=46) (b:=46) sp22628 sp22674)))) (joinSmall (lo:=22720) (a:=366) (b:=367) (joinSmall (lo:=22720) (a:=183) (b:=183) (joinSmall (lo:=22720) (a:=91) (b:=92) (joinSmall (lo:=22720) (a:=45) (b:=46) sp22720 sp22765) (joinSmall (lo:=22811) (a:=46) (b:=46) sp22811 sp22857)) (joinSmall (lo:=22903) (a:=91) (b:=92) (joinSmall (lo:=22903) (a:=45) (b:=46) sp22903 sp22948) (joinSmall (lo:=22994) (a:=46) (b:=46) sp22994 sp23040))) (joinSmall (lo:=23086) (a:=183) (b:=184) (joinSmall (lo:=23086) (a:=91) (b:=92) (joinSmall (lo:=23086) (a:=45) (b:=46) sp23086 sp23131) (joinSmall (lo:=23177) (a:=46) (b:=46) sp23177 sp23223)) (joinSmall (lo:=23269) (a:=92) (b:=92) (joinSmall (lo:=23269) (a:=46) (b:=46) sp23269 sp23315) (joinSmall (lo:=23361) (a:=46) (b:=46) sp23361 sp23407)))))))))
  have good : (List.range 23453).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 550000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 23452 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 23452 := by
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


private def packet (i : ℕ) : ℕ := (if i < 140 then (if i < 70 then (if i < 35 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else 0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0 else 0) else (if i < 11 then 0 else 0)) else (if i < 14 then (if i < 13 then 0 else 0) else (if i < 15 then 0 else (if i < 16 then 0 else 0))))) else (if i < 26 then (if i < 21 then (if i < 19 then (if i < 18 then 0 else 0) else (if i < 20 then 0 else 0)) else (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else (if i < 25 then 0 else 0)))) else (if i < 30 then (if i < 28 then (if i < 27 then 0 else 0) else (if i < 29 then 0 else 0)) else (if i < 32 then (if i < 31 then 0 else 0) else (if i < 33 then 0 else (if i < 34 then 0 else 0)))))) else (if i < 52 then (if i < 43 then (if i < 39 then (if i < 37 then (if i < 36 then 0 else 0) else (if i < 38 then 0 else 0)) else (if i < 41 then (if i < 40 then 0 else 0) else (if i < 42 then 0 else 0))) else (if i < 47 then (if i < 45 then (if i < 44 then 0 else 0) else (if i < 46 then 0 else 0)) else (if i < 49 then (if i < 48 then 0 else 0) else (if i < 50 then 0 else (if i < 51 then 0 else 0))))) else (if i < 61 then (if i < 56 then (if i < 54 then (if i < 53 then 0 else 0) else (if i < 55 then 0 else 0)) else (if i < 58 then (if i < 57 then 0 else 0) else (if i < 59 then 0 else (if i < 60 then 0 else 0)))) else (if i < 65 then (if i < 63 then (if i < 62 then 0 else 0) else (if i < 64 then 0 else 0)) else (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else (if i < 69 then 0 else 0))))))) else (if i < 105 then (if i < 87 then (if i < 78 then (if i < 74 then (if i < 72 then (if i < 71 then 0 else 0) else (if i < 73 then 0 else 0)) else (if i < 76 then (if i < 75 then 0 else 0) else (if i < 77 then 0 else 0))) else (if i < 82 then (if i < 80 then (if i < 79 then 0 else 0) else (if i < 81 then 0 else 0)) else (if i < 84 then (if i < 83 then 0 else 0) else (if i < 85 then 0 else (if i < 86 then 0 else 0))))) else (if i < 96 then (if i < 91 then (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else 0)) else (if i < 93 then (if i < 92 then 0 else 0) else (if i < 94 then 0 else (if i < 95 then 0 else 0)))) else (if i < 100 then (if i < 98 then (if i < 97 then 0 else 0) else (if i < 99 then 0 else 0)) else (if i < 102 then (if i < 101 then 0 else 0) else (if i < 103 then 0 else (if i < 104 then 0 else 0)))))) else (if i < 122 then (if i < 113 then (if i < 109 then (if i < 107 then (if i < 106 then 0 else 0) else (if i < 108 then 0 else 0)) else (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else 0))) else (if i < 117 then (if i < 115 then (if i < 114 then 0 else 0) else (if i < 116 then 0 else 0)) else (if i < 119 then (if i < 118 then 0 else 0) else (if i < 120 then 0 else (if i < 121 then 0 else 0))))) else (if i < 131 then (if i < 126 then (if i < 124 then (if i < 123 then 0 else 0) else (if i < 125 then 0 else 0)) else (if i < 128 then (if i < 127 then 0 else 0) else (if i < 129 then 0 else (if i < 130 then 0 else 0)))) else (if i < 135 then (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else 0)) else (if i < 137 then (if i < 136 then 0 else 0) else (if i < 138 then 0 else (if i < 139 then 0 else 0)))))))) else (if i < 210 then (if i < 175 then (if i < 157 then (if i < 148 then (if i < 144 then (if i < 142 then (if i < 141 then 0 else 0) else (if i < 143 then 0 else 0)) else (if i < 146 then (if i < 145 then 0 else 0) else (if i < 147 then 0 else 0))) else (if i < 152 then (if i < 150 then (if i < 149 then 0 else 0) else (if i < 151 then 0 else 0)) else (if i < 154 then (if i < 153 then 0 else 0) else (if i < 155 then 0 else (if i < 156 then 0 else 0))))) else (if i < 166 then (if i < 161 then (if i < 159 then (if i < 158 then 0 else 0) else (if i < 160 then 0 else 0)) else (if i < 163 then (if i < 162 then 0 else 0) else (if i < 164 then 0 else (if i < 165 then 0 else 0)))) else (if i < 170 then (if i < 168 then (if i < 167 then 0 else 0) else (if i < 169 then 0 else 0)) else (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else (if i < 174 then 0 else 0)))))) else (if i < 192 then (if i < 183 then (if i < 179 then (if i < 177 then (if i < 176 then 0 else 0) else (if i < 178 then 0 else 0)) else (if i < 181 then (if i < 180 then 0 else 0) else (if i < 182 then 0 else 0))) else (if i < 187 then (if i < 185 then (if i < 184 then 0 else 0) else (if i < 186 then 0 else 0)) else (if i < 189 then (if i < 188 then 0 else 0) else (if i < 190 then 0 else (if i < 191 then 0 else 0))))) else (if i < 201 then (if i < 196 then (if i < 194 then (if i < 193 then 0 else 0) else (if i < 195 then 0 else 0)) else (if i < 198 then (if i < 197 then 0 else 0) else (if i < 199 then 0 else (if i < 200 then 0 else 0)))) else (if i < 205 then (if i < 203 then (if i < 202 then 0 else 0) else (if i < 204 then 0 else 0)) else (if i < 207 then (if i < 206 then 0 else 0) else (if i < 208 then 0 else (if i < 209 then 0 else 0))))))) else (if i < 245 then (if i < 227 then (if i < 218 then (if i < 214 then (if i < 212 then (if i < 211 then 0 else 0) else (if i < 213 then 0 else 0)) else (if i < 216 then (if i < 215 then 0 else 0) else (if i < 217 then 0 else 0))) else (if i < 222 then (if i < 220 then (if i < 219 then 0 else 0) else (if i < 221 then 0 else 0)) else (if i < 224 then (if i < 223 then 0 else 0) else (if i < 225 then 0 else (if i < 226 then 0 else 0))))) else (if i < 236 then (if i < 231 then (if i < 229 then (if i < 228 then 0 else 0) else (if i < 230 then 0 else 0)) else (if i < 233 then (if i < 232 then 0 else 0) else (if i < 234 then 0 else (if i < 235 then 0 else 0)))) else (if i < 240 then (if i < 238 then (if i < 237 then 0 else 0) else (if i < 239 then 0 else 0)) else (if i < 242 then (if i < 241 then 0 else 0) else (if i < 243 then 0 else (if i < 244 then 0 else 0)))))) else (if i < 262 then (if i < 253 then (if i < 249 then (if i < 247 then (if i < 246 then 0 else 0) else (if i < 248 then 0 else 0)) else (if i < 251 then (if i < 250 then 0 else 0) else (if i < 252 then 0 else 0))) else (if i < 257 then (if i < 255 then (if i < 254 then 0 else 0) else (if i < 256 then 0 else 0)) else (if i < 259 then (if i < 258 then 0 else 0) else (if i < 260 then 0 else (if i < 261 then 0 else 0))))) else (if i < 271 then (if i < 266 then (if i < 264 then (if i < 263 then 0 else 0) else (if i < 265 then 0 else 0)) else (if i < 268 then (if i < 267 then 0x1a519c92c614c899a46b2068eb06ac2fc14f89103ea19a09603440d200001a513d02c914f49b447d20f8eec6c230314f09403cc18309102f40c000001a50dd52ce14e49c64872158f286d030115388f83b817f09083300ca00001a507ea2c594b897a4602030e7067c2dc143089c38c16408102a40aa00001a501fa2cd14e49a446720d0eb869c2ee14e88e03b8179090830c0c000001a4fc262c114309664531f90e5c66e2d7141887838c17208902d40c200001a4f6202d415409d847f20c8f006c030a15009083d018d09483200c400001a4eff22e515b0a104aa2210fa070431c15789183d218f097031c0d000001a4ea142c594b899e45d2020ea467c2e314308c439c17608a82dc0b600001a4e4242c894b498447320d8ee46a42e8141089039a17808a82e80be00001a4de212d995589ee4942240fac71231915b09743f219309d835c0d200001a4d8252cd14e49b047b2098ea86ac2f714a08d83b817308e02d80b600001a4d22b2cf95049c248220e8ee86b02ff15088dc3c4184092030c0be00001a4cc432c914ac99c4712078e886822de14188c83a417308d02e00b000001a4c64e2d095289d448d2198f486e6317156890c3aa17d09403200c200001a4c02d2dd15549ee4982198f406d030a15609443ee19a09983300c400001a4ba002e615bca0e4aa2258f8070231f15989383d418b09203180d000001a4b3f52d5953c9d848e21a0f346d830b15188e03ac17708c82f80d000001a4adfe2cc15149d04922190f4c6da30214e08d03a017109082d80c200001a4a80b2ca94d09ac4712090eb468c2e614808e43b016908302bc0a200001a4a22e2ba945c98045a1fc8e5c67c2e914908d43ac17c08f83000b400001a49c4a2c1949499846e20a8ef06ce2fd15209103cc18809683280de00001a4963d2d1952c9ce4802138f2c6dc305157091c3be18109403100b600001a4904e2c994ec99e4712088ee069c2f214d090c3d618709182fc0c200001a48a832b4943097c45a2050f086d231015309183ba18509383080c000001a4849e2c914f09be47b2140f106b630314f89283c617908982d40b600001a47ea62d414f49a647620c8f0c6c02ff14b88c43a817508b82f00c200001a478912d815189d448d20e8f246ca30715309203cc18009303340c600001a472ab2c294a899a46d2078ecc6b62f914788c43a817308c02c809c00001a46c902dc95449ee4962198f3c6d830715789243ee199092030c0c200001a466972ce95149c84842160f386cc30615489343cc187090030c0d200001a4609e2d394f49b24702088ec46a62f814d88e83b217d09002cc0a000001a45a912d3150c9cc48120c8edc6a62f115288ec3ba17b08f83100be00001a454842d895549f04902108eb86a22f414508cc3aa18008d02f00c200001a44e7e2d095109c247f20c8ed86ac2f915289203ca18d09803580d800001a448622db954c9f049a21a8f346c830614d08ec3aa17e09002cc0b400001a442722c494a89764531fe0e706782df146889038c17108902d00b800001a43c9e2b794449744632030ea86a62ee14788c43b018509803480cc00001a436b42c614b49a64742060e9c6c42fd14c08e83ca18709183140d400001a430a92d514f09c048320d0eec6be2fc14d08b83be18909503000ce00001a42ae12b9944496e4581fd8e686762e1146887839816f08302ac0aa00001a424fa2c814b499e46e2050ed06a22e9145089039a17209083080d000001a41f2b2bb143c97e4622018ec86982ee145089439a17008a82cc0ac00001a4190a2dc15249da4952180f5c6d030515389243ca18c096031c0ce00001a413272c194809684511fb8e8c68e2ec14a88a039617408802e00c400001a40d172d8155c9d248c21b0f506da30b15289143ce17e09083000c400001a4075b2b7941094c4461f18e1463c2c413a087439a17208c82e80b000001a401552d195209e44902178f1c6d030115189043b817d09783340d600001a3fb6d2c194cc9a846a2068eb46922e614888a837c15e08482e00c000001a3f5662d695389de4832168f206d630514e08ec3c219009483140b000001a3ef762c994f09b847e20a0eec6ba2fb14a88c83a017208902dc0c400001a3e9722d0951c9cc48a2140f046d42f914c08d83ac178091030c0c800001a3e3732cf14fc9b447920a0ef46b830515089343b418309182d40be00001a3dd792ca14d89a04732068eb86b62f014808e43a417b08e83100c200001a3d7462ea95bca0049c2188f606e631115a09443f619a09803200c800001a3d1542c914d09bc47420c8ed46bc2f414a08ec3ba18609703200d400001a3cb402db957c9ee49e21b8f506f631e161897c3e218e09603240c600001a3c5392d415289d447b20b0ec06a42f214e08d439017309002f00d000001a3bf322ce95009d04902120f286e831015008e83be18208b82fc0c400001a3b9132df155ca0e4a82240fa06fe32516289a441819d09c83540d600001a3b3122d115149c247520d0ee06b2306153891c3ce18409583300c600001a3ad292c1148898045d1ff8e8467e2e614308a838a16308602840a200001a3a7002e995b4a124a62238fa470031915a89343e618e098834c0dc00001a3a1092cb14dc9b447e2108f246ce315159094c3e618a09182d00be000 else 0x1a698842c4948499c4632050ebc6b22f314e09083c618d09683000ce00001a692592e995b0a1c4ad2200f706e231615709203d219509a03340d600001a68c662c814b49a446d2088eb46aa2ef14888ec3b618609282f80ba00001a6865e2cf14d49a44752078ef86c630214c88ec3ae17508f831c0c200001a6808b2ba94a89924622028e7c6862e614488c439c17808f83080c200001a67a6d2e1957c9fe4a021e8f346dc315158897c3ea19109303200ca00001a6748b2c1948098a4612010e806882dd143087c39016f08b82bc0ba00001a66e772d6154ca044a32230fa46f031d15e89703ea18809683140bc00001a668752d194dc9a047720a8e8c6a42fd14d89183ce18909483100b800001a662562e015609e848e2148f286d630e15789503d218d09503300dc00001a65c3f2da15349de48d2140ef46be2f614b88e03b617608d82f40c400001a6565c2c414809844732098ec86a02fa14988c83a216f08b02b00b200001a650522d795549ea48f2190f506e631415409143cc18909002f40be00001a64a262eb95dca364be2260fb870e32315989603ce18108f02e00be00001a6445b2b6945496045b1fc8ea06742e013e888c39217608a82cc0b400001a63e5d2d415189ca4742068edc6b830614d08e03b817a08b030c0ae00001a638612d094f89b847520f0f306d030815289183e219209803380cc00001a632642cb95209cc4852150f1c6dc30c15409203ca17f09082e00a800001a62c542d495009c047d2118f206dc30c15a09403d218a09102fc0ae00001a6265e2cf94f09b647f20f8efc6c02fe14988fc3cc18c093030c0ba00001a6205b2d4151c9d048020e0f086b630114909143dc18b09203100d000001a61a792bf149898a4692060eb869c2e5142889439016508402b00ac00001a6147e2d095089da47f20f0eec6aa2f314e08c03aa17208a02dc0b200001a60e792cc950c9ba47d20b0f086b82f114c08ec3c018209283100c400001a608622d795449ec49d21b8f646c430515389303c817908f82ec0b200001a6025f2ce15049c447920e0ee46b02ea144888c39816608982c40b400001a5fc722c0949898646a20d8edc6c6306155092c3ba17e09103280ca00001a5f6762d695549f848e21f0f9c6f831515809203c0189094031c0ca00001a5f0b72ad940094c4431f48e2865e2de14208983ae16f08a82dc0b400001a5ea8a2e0156c9de4812148f486dc30a15289043d418909303240c800001a5e49d2c794bc9b448020f0eec6ce30f15b09583d418f09783100d000001a5de882d695289d449a21d8f7c6ec31215c093c3d618d09703180c800001a5d8a22c514a49964662030ec46be30815089243dc18308f82c40bc00001a5d2b52c794d49a446b2098eb068e2ec14708ac39c16b08802f00b800001a5ccb22cf14e89aa4782110f306e231a15309103cc18809503180ca00001a5c6ab2d795189ca48e2190f2c6d630a155891c3c618308c82f80d400001a5c0a42d915449ec49521d0f6c6f831c15d89383dc19309503280d200001a5bab62cb94b09a646b2050e9068e2e514088a839217208a02b00a200001a5b4e52b6941095244c1f30e386642d014088a43a017208f82e00c200001a5aede2d215209d448f2148f446e030d15589103d618709283040d800001a5a8e32cc94f09ac47020a0ed86aa2f814988c839a16c08a82ec0ca00001a5a2ea2d094f89b84832120ee46b82fd15589083b618008902f40bc00001a59d102bb144899246b2090eb068a2ea14608ac39a16e08882fc0c200001a5973c2c014b09aa4752088ec86b230415609443e019309503000bc00001a5914b2cd95149d24862140f2c6dc31415589403f019009082e80b800001a58b932af13fc9504471f90e686682df143889c39c174089030c0ba00001a585a22cb14c89aa47f20f8f0c6ca2ff15089243ce18709a03540de00001a57fb72c2946097845e1fe8e6c6802da14008843aa17508a82c00ae00001a579bb2cd94e89b44762050e7c68a2e414208c03a817f092832c0d000001a573d52c214cc9b44812118f006aa2ef14e88e83aa17308982e00c000001a56da22e995bca0049a21c8f646f431b15709203dc18308d83240d800001a567962d715209d449321b0f506e831915689003d018f09383140c000001a561922d3151c9d648f2168f186ca2fc14b08bc3b217808b82ec0b400001a55b782df9590a164a72238f706f431815a09403e418909683340bc00001a555ad2ba148495844f1fd0e786802e013d88bc38416a08882e00b600001a54fb92cb95009dc48c2158f206c82f814d08d43a617908e82e40ac00001a549c82cb94d89a847c20b8ed06ba30215188d03b418509103080c000001a543cf2cc94f49a647920a0ef86b22f914b08e43a417008782fc0b400001a53dd02cf14d49b04772108f0c6da30114f09003bc18808b02d00aa00001a537be2d995449c247c20f8ec46ac2f514b08e83b417f09083140ba00001a531bc2d294f49b646e2068ec46a42f214d89143b818308d830c0c000001a52bb62d595449ea4832138f306e630a14f89183d418409203040b400001a525b32d315149ba47d2098ef86aa2ec14508d03ae16e08582c40ac00001a51fab2d615509f649c21c8f686f831215d09583fc18e08f83140ca000) else (if i < 269 then 0x1a816e92d615189c647a2100f1c6ca30015188f83d018c08f82e80c200001a810d82d4952c9e44932190ef86b630714d88f03ce17d09103240c400001a80af12c494b49944722078eb46ae30315188fc3d218809a03440ca00001a804e72d115189dc4892178f486dc30415409003aa17a08802b80b200001a7ff052c494c89ba47920c8edc6a22f314c88d83aa17308a02f80ce00001a7f90e2c314c49a84692008e706902f214d08fc3c617a08b82d40be00001a7f3402b7146897a4662060e806aa2ec14a88bc3c616e08602b00a200001a7ed702b794409664582068ed86a22ee14a88c83a417a08c82dc0a200001a7e7722d0151c9ba47d2118ef46b630715689443be17a09182f80c600001a7e17c2cb950c9bc48220c8ee46c030e158893c3e018a09503400da00001a7db922c714b89b047a20c0ec46942ef14788d03a017b08f03000b400001a7d59b2c894dc9c247620a0ed06962e0142889439816e08b82dc0b400001a7cf822d595149ba47b20e0ed469e2ef14588bc3ae17e09083040be00001a7c9882c914c89844632028ebc6ac2fe14c08e03be17c08b02f40bc00001a7c36a2e5158ca104a12220f846da31215989583f819e09e03400e400001a7bd692d2951c9ce48d2160efc6d030615588fc3ba17d09083080ba00001a7b7682cb94c89ae4742050ed46b62f314608a439417708802ac09c00001a7b1872c094989724652030e986902dd13e887c3a017508a82d00ce00001a7ab712d7156c9f049921d0f646da30515389203d618b092830c0d000001a7a5a52b7143095444f1fd8e646702d4140088037a15f08382cc0b400001a79f9b2d214d89ba47a2120efc6c02fc15189143be17e09103040c600001a799ba2c0949c98e47320a0ed469e2eb14508b439e17608c82f80b000001a793b82d194dc9ac47820f0ee86d230415389283d217f08f02e00c200001a78db72d415049aa47c20b0e9868e2ea14e09003a616e08502c80ac00001a787ab2d4152c9c247c20e0f046c22ee145087c38616f08c02f80ba00001a781b52cc95089be47d20e0eec6a42fa14e08d03aa17508e03080ba00001a77bd72c394d89a64702088ecc6b42f614d09083ca18109402e00b400001a775e62c714b89a447420d0f086bc2fb14a09003ba17408b02fc0c400001a76fd42d515009aa46f2040ed86ca31315089103d018409603140c400001a769b02e195549f04952198f2c6cc30014a88cc3a017808e02ec0c800001a763c82c694b09b847f20c8ee46a82f814e08f43bc17908b82ec0ce00001a75de52c0148c9864692030e8c6902ec14488c039a17a08e02fc0cc00001a758032c2949498c4642060eb06942ed14788e43c417c08d03140c600001a751ee2da95489fa49821d0f746ea31215689043c618809003000bc00001a74bd62db9554a024a22238fa06f631415a89703f018c08f83000c800001a745b62e515bca0a4a62218f6c6ea31b15f89643e819009503200ce00001a73f8f2e215c0a1c4b52258f946fa30f15809303cc18d09403200d000001a739862d115249d048520f8ee46ba30915188f83ac179091030c0ba00001a733982c814d89c648b2120f106dc31515989683f219f09b03440c000001a72dbe2bd14989964601ff8ea06902e714b88d83b617f09003000ce00001a727c62c894a498c46b20b0ed46a22f215109303d418e08d82e40c000001a721952e5159ca0c4a52268f506d030d15509243d418608c02e80ba00001a71bb22c5148097a45b1ff0e3c6622d0134083836c16408502b40c800001a715c92c914ac9824602018e9c69c2e714088903a217b08b02f00bc00001a710052b2942c9684571fa0e686742d5142888c38816808582b80b200001a70a152c714a098e4682040e846822db14708d83ac17a08b82f80c600001a703f22e595a0a024932190f406ec30915309243ea190096830c0be00001a6fdf02cb94f49cc4862128ee86c22fc150090c3cc18b09482ec0be00001a6f7e32d795549ee4912158f286cc30a15509103cc18508f82ec0be00001a6f1e02d414e89b446d2070eb868e2ed14808b83b818108f02e00ba00001a6ebaa2ee95f0a384ae2218f606da31015709343dc18809203040cc00001a6e5be2c294c89b44802108eec6b82fe14f88f83d218508c83080b800001a6dfb22d815289ce4832160f1c6c4303150890c3c217b09182d00c000001a6d9a82d915509f849621d0f606f4318154091c3c618909002ec0b200001a6d3c52be94a89a247320c8ee06aa2fa15089283c818208f03100c000001a6cdbc2d395389d44882158f246d230315109143ce18408e82d40c200001a6c7d02c4948c97845f1fe8e886862e514688c43a617b09102f80cc00001a6c1fe2b3942496245b1f88e5868e2eb14688a839216708202b00a400001a6bbfc2d014cc9bc47e20d0ecc69c2f714a08b03a817808f830c0b800001a6b6352b0943c9504551fa8e546542ce137884c36a15a08302a40aa00001a6b01d2d595149ea49121b8f546ec31715c89403d818509602f00b800001a6aa3e2bc94a099047320b8f086c230314e08d439c16a08982e40ae00001a6a4582c114a499847520b8ea069a2ee14a88c83a816e08a02ec0be00001a69e662cc94e49bc4882128ee069e2f714988c039e17a08882bc0a4000 else (if i < 270 then 0x1a995502b7144096a4511fc8e4c6862e214308a439216e08502e00c200001a98f622c3149898c45f2060eb469e2f714c88c03ac17a08a02f40c800001a989772ca14d49be47b20c8f006bc30215189143c017e08b02f80d600001a9836c2d0950c9b447a20d8f0c6ba2f314c88f03bc18509102f40be00001a97d8c2c094a897c4642048ebc6a22fc14d88d03b618109082f80be00001a977be2b9944897c46f2068ee06ba2fb14d08ec3a217708882dc0c000001a971d02c694c49a44792040e8469c301149089838216208382bc0ba00001a96bc62d495109d84822130f086c62f914b88dc3a017e09283240d400001a965ea2be144c97245a1fe8e706762e314c08ec3be18009283080c400001a95fd02dc15589d448a2148f086c231015409243ce18309702f40c800001a959d32d3954c9de48b2140f1c6d2309153890c3c818809203100be00001a953ed2c894d49b447e20b8ed86c030c15009103e019009583280cc00001a94de22d915609ee4a52228fbc6fe316158895c3ee19d09f837c0de00001a947d12dd95689f04902190f646f831516089643c418609402f00ac00001a9420e2b314449764551fd8e8c6aa2f214d88e83a617709002dc0b000001a93c0f2ce15009c247c2110f246cc2ff14c88f83b418209103140bc00001a936142cb15009ba46d20c0ed06b430114d88f83bc17a08b82fc0b200001a930132d315409ea4922188f806e831715a89583de18a09503200d600001a92a3f2c214a49924732098efc6ba2fa14808d43ac17e08d82dc0b800001a924502c714cc9a647120b8ee86ac30114c89243be17a09182f40b000001a91e462d415309b648320e0ef86b430014d09003a017108c82e00c600001a918772bd14809804682020e8c68e2ea14a88f83d018208d82e00b800001a912752d314e89b048520c8eb06b62ff14b08ec39e16508682b40b800001a90c832c994fc9da49421b8f406d430c15509303c818208e83280cc00001a906912c614b498e4622040e9c6882ec14b88ec3bc17008782bc0b400001a900852d715009cc4812128f1c6d630515309183cc17f09283380c000001a8fa572e4959ca064ac2228fa471032d16889943e219409383280ca00001a8f4252e815a09f64962188f0c6c6305154090c3c018f09903480ce00001a8ee272d095349d04882180f286da30715509443d618c09603300c800001a8e8452c094a499046f2060eac6b22f614a88e43b618a09483080be00001a8e2422cc94f89c247b20a8ed46a22f714908c83a417108982b40b800001a8dc5a2c194a499846a2048ec068a2f414908dc3a617408c02e40be00001a8d6782c1149499c47f2130f246e02fe14d88f43b217408982ec0c400001a8d0752cd950c9c24802160f046b82f914c09043c217c08c82e00a800001a8ca862cd94c09904682058e9c6a22e2142087c37c16508782e40b800001a8c48e2cf151c9ce48a2138f1c6bc30015289183ae17308482e40be00001a8be5c2ea15a09f449921a0f586e231015688ec3ba18509183080ca00001a8b86e2ca15009b447e2108ed86c22f314908b03a217908b02ec0c600001a8b28a2c2949c98c45b1fe8eb06962e514789003c017a093031c0c400001a8ac832d315089c248420c8ee46b62f2145089839417208b82e40cc00001a8a6732d515249cc47b20e0ecc6b22fc14d08e03d418e09082f80b400001a8a0562d815449de4982170f486ec314154093c3ce17c09402f80ba00001a89a602cc94b499a46d2050ec46a62f214a88cc3c417f09803340b600001a894882b7944896c4552008e846782e114088843a617508982ec0b000001a88e742df95b0a1049a21f8f606f031915b09583de18908e83000aa00001a888802c914e09b247d20b8f0c6d831b15709303da18808f832c0ce00001a8827a2d415449f249c21e0f606e031015c89603e819709803340ce00001a87cad2bb14689724702088ed86a42ec14d88c03a417d08e83380d000001a876972d895409e648e2198f406d6317159894c3ea18309883140c400001a8709d2cb94d09ba47c2198f2c6ce30614f08ec3a817208c82f80b800001a86a9e2cb14f89c04802118f246c830515289083b217009002e40b600001a864912d095149cc48320b8ee06c42f614e88e83b017208902f00bc00001a85eae2bf149499046c2010ea86c02f714a08e43b817c08d82f40bc00001a858b92c794a499846d2018e9c6902e814808e03c818b09082fc0c200001a852e72bd948498645c1fc0e6469a2f6149089839017008782b40be00001a84cef2cc94d89ba47820f8ee46b82fa14188c83ae17d08f82d40b200001a846e92d8153c9bc48420d8ec06a62f614c09203cc17e09002e80b200001a840e42cf94cc9b047620c8efc6b430015208fc3ba18309703080b000001a83afb2c714a898e46f2080ee86bc30715289003c018309203040b800001a835152c794a89964602028e846822e214688c83ae18209603080bc00001a82ee32ec15a4a204ab2268fac70a31b15d89483ea18e09583440de00001a828ec2cb94dc9b047820a0ea86982ed14e88c03ac17908b82ec0aa00001a822d22e2159c9fc48d2170f386be2ed14608c83b417a08982dc0be00001a81cf52bf14849944652048e946902e214508cc39616a08302b80aa000 else 0x1ab13a32c0948899047320a0ef86c630014b88ec3b217809002e40bc00001ab0d842e2956c9f649e21c8f886f432016309804081a70a403840d200001ab07762d615349ea49d2150f1c6ca2f814a08b039816008a02e80b200001ab017e2ca94c89a046720d8ed069c2f314b88cc3aa16c08c82f80b400001aafb9f2be14709804622018e986982ef14408c83a216708582e80c800001aaf5882d995289c84862118ee06c02fe14d08b03b217508982b80ac00001aaefa52c614b897a4621fd0e986722de13f889038a16f08302a409e00001aae9962d214f09c648220f0ee46a82ed143089c3a616708c82c80a400001aae38e2d094e49aa47620c8f0c6b630115189243e218709603080da00001aadd7f2da15749fa49421b8f806fa31a15709343c817908a82d00b600001aad78e2c994c09784602038ec469c2f214488ac3a817208782c40aa00001aad1a12c514a499e47520e0f006ae2f414888c43a417108a82d00be00001aacb9f2d495149b24832100efc6cc305156894c3e218e094831c0be00001aac5b12cb15089bc4782108f206ae2fb15609343c618a09b834c0ce00001aabfb72d114f89b447d20b8ed46a42ea143888439817308d82d80b000001aab9da2bb14609844682058e7c6822e714588c03ba17608782ec0a600001aab3cf2d495349e048e2180f546d630114d88d83b217f09083000d200001aaadf82bf946897c4662078ed06b82ef14908c839a17408a82c00ac00001aaa8132bc147097245e2050e9867e2e7141888438416608782bc0ac00001aaa2212cf14e49a247a20d8ef46ac2f414e08b839816b08702b009400001aa9c132cf14fc9ca47d2150ef86ba30415008fc3ae17d09303340c400001aa96262cc14f89c447d20e8f186d230b15689543f818509202e40b600001aa90222cb94fc9ae47c20d0f046c430915409043b617608b82dc0d200001aa8a1e2db95489de48f2190f3c6ce30214d08e03b817908782c40ba00001aa84152d295209da4872140f246ce307150090c39016b08802d00c600001aa7e0e2cf95209d24872150f1c6c030415088f03b417b08d02f80be00001aa78232cb149897a45d2070ea46702e214708b03a816f08c82e00c000001aa72192d494f49b24852158f146b82f514c08d03ae17f09182c40aa00001aa6c282ce94f099446d20b0ee86a62ee14988e43a217508b82c40bc00001aa662a2cf14d09b047c2100edc6ba2fa14b88e83a217c093031c0c000001aa60152d2950c9b447820c0ec069430015009003b417608e82f00ba00001aa5a022d415009ce48b2128f146f431915c892c3c418008b82e00c400001aa54112ca94d898645f2018eb06922ef15108e43bc17808882c80b600001aa4e362c194bc9a24722058e946902e814688ac39416808982ec0c400001aa484d2c2949c9864632018eb869c2ef14608d83b817f09103000c600001aa42612c214d49b44762080e606882f214808dc3a217a09182c00b400001aa3c6f2c894cc9b247520b8f0c6c62f914c88e43b017508a02dc0a800001aa36792cc94bc9aa47b20c8ee46982f514b08c83ba18408b02e40be00001aa30852d095109ae4772098ecc6bc2fd14d08f43d018609283280c600001aa2a912cb151c9c04822110ef46c030114f09083c618209282f40ae00001aa247b2db95349d449021b0f486e430d15709443b616f08c82fc0bc00001aa1e692d995389e64962170f4c6f231415889583ea18f09282f00b000001aa187a2c794c49c248020e8ee86ac2fb14b88e43c618609003180b800001aa12912c494b097e46a2088ed86a82fa152090c3ba17a08f02d40bc00001aa0c8a2d495209d847920d0ed46922f114d88d43a617608f03100b800001aa068b2d014fc9aa47720f0edc6bc2f815009243c017e090030c0cc00001aa00b92c294a898c4622040ec06a22f814a88c838a17808c82f40c000001a9fae72bb146097c46b2078ee46bc2fa14e09083c418108f82fc0be00001a9f4d42d495289c247720e0ee86c830715108f83c017e08e83280c000001a9eed62ce14f09b84742098ee06b82f914d88f43b418208f02fc0ae00001a9e8ec2cc14d49be47e20e8f146c630315989383f019209883180c800001a9e2c72e415889fc49f2210f886f030f155891c3c6180094831c0b000001a9dca12e715849fa4932128efc6d430e15489483d818b08f830c0ac00001a9d6a92cf14f49c848620b0ebc6a62f414e08b83a217b08e03040c000001a9d0b42cb94cc9ae46b2078eec6c030114d09083d618909403100c800001a9cb0e2aa13fc94844c1fb0e786842df145088839216608682ac0ba00001a9c4e02ea95a4a104b22268f9470a31715b09383e419309783200d400001a9bef32c914dc9b246e20a8ebc6b02f514b88dc3ba17b08d83100b400001a9b9122bd94789964621fd8ea06982f414908ec3c018609483200ba00001a9b2fe2dc157c9e64912180f486de30b154091c3d417e09083080b400001a9ad222c2947c99e4692058edc6bc2f614f08dc3a817e09383000dc00001a9a74f2bc145497445e1fd0e8c68e2f814d88b03a817d08e02e00bc00001a9a13a2de15449d64872160f206e6310154092c3c017508a02c80b200001a99b222dc15509ea4a121b8f606de30c15709083cc17408b02e40ac000)))) else (if i < 275 then (if i < 273 then (if i < 272 then 0x1ac91872cc14ec9ac47920c0ee86ba30b15789443e619e09d03600ca00001ac8b862d395289e048920d8ee06ae2ea14788b038816508582a80ac00001ac85952c614ac9a446f20a0ec069a2f314608a439a17b08802d80ac00001ac7f782de158c9fe49f2160f306d431215609303d418509202fc0ca00001ac797b2cd94e09b847820e8f086ae2f614b09343e419609c83400da00001ac73732d394f89d848b21c0f386de30a15689443ca18309583380c400001ac6d982b9144496645a1f90e546622de13e087439216708302b409a00001ac67892d315109aa4732078eb46aa2fb14808f43c818008d02f00c200001ac61ab2ba149096e4682068eb86902e314788b4394179090030c0b800001ac5bc32c514ac98c46f20d0f006be30214788c039416508702d40be00001ac55f72b314189524461f68e486662cd137889039c16808c82f80c400001ac4fee2d99568a0248e2150f186c62fb15409283e018609102e40be00001ac49e52d715249d648b2190f286b62fb14b0894388160089830c0c200001ac43dd2d115109d84922140f386de31015889403d2189092031c0d000001ac3df82c514e49b047520e0eec6ba30a14d890c3ac17908c03080c200001ac38002d094f89ae46c2028e8c6882f214a88f43c017a08c82f80c600001ac31fa2d1150c9b248420f8efc6c230e15209283d618509482f00c000001ac2c242b7946c9924662090ef06bc30d15609303d618b090030c0bc00001ac26142d8954c9d64862150f146de30515609483d418709883300cc00001ac20342c414cc9a44702030ea86902f514d090c3d418e09303300cc00001ac1a3e2ca14e89be47f20d0ed869e2f414f09043c418209283000c400001ac14212dc15849f64992190f3c6e630f15a09343be18008f82f00c200001ac0e412c594b899a46e20c8ef46aa30214b88f83bc17d08c02e40ca00001ac086c2b894589824512008e986a02ef14988d839816b08982a80b200001ac02722ca94b499245b1ff0e6466e2e0141089438816a08602cc0b000001abfc4e2e315a0a104b22298fd072832916109743ec18d09283080b200001abf6452db15549ee4922190f546dc30f15189103ba17308f82e00ac00001abf0522cb94f09b047a2100f186da307153090c3c2183093830c0d200001abea5f2cb14e89c04822118f246ce30d15289043cc17b09003100c600001abe4652cc94e09bc4862110ed46a82f615509103c418008e02ec0ae00001abde8d2bf948898646420c0ec86ae2ee14c08ec3b417208802a40a000001abd8842d415109b848d2150f246e231a15b89443e418e09883500c600001abd2932cc94f09be4832100efc6c42f414808d83aa16e08b03100ba00001abcc6f2e315689ee49821d0f306e230914f88e43b018509a831c0c800001abc69e2b614209544571fa0e2c6802e9145089838e16b08882f40bc00001abc0ce2bf149098a4642090ef06ac2f814988dc39c16b08882f80b200001abbad12cd94ec9b647520e0edc6b42fa14c88f83aa17408e83040c400001abb4e72c8149c9904702080ecc6a82fd14d09103bc17f08b82e80b800001abaee72cd95209c448320f8ee86ae2fa14b88cc3ac18608e82e40b600001aba8d82cf94e09b848220b0efc6b630415208e83b817c09203240d400001aba2d72d195109d848720e8eec6b62f114e09203e219909f83380d000001ab9cff2bb947895e4541f98e546822f514d89143d0194097831c0c200001ab971d2c5148c9a247a20d0ef06c430115689083c817b08d02ec0b000001ab91042d595209e248e2158f046c02fe15108dc3d218308e82e40b600001ab8b082d294ec9bc4802128efc6ba2f314908e03b218008a02f80b600001ab850d2d395289c847620d0ed869e2e714888cc3b417c08d82dc0b200001ab7f272c894a499c46a2068eac6902e714608f83aa17a09102e40c600001ab791b2d094f09ac47520c0ef86b02f014788c03aa17608a02d00b000001ab73052d895609e64852138ef86b830815988f43a817808b82f40ca00001ab6d0b2cd94f09b446f20d8f146d230614f08ec3cc17e08f83280cc00001ab67242c314bc99c47920b8ec46a62f1140088c38a16808882cc09e00001ab611d2d2152c9d849121e8f6c6d631215989403e819009683240c800001ab5b1d2d315009ca4922160f346ea30d15689383da18c09603240c400001ab55522bb947496e4561fe0e8c68a2e514188903a817408982bc0ac00001ab4f7d2bf145896a45b2018eb06ac2f515109303ba17f08f03000c400001ab496d2d995409ca48220c0ee86d230415109143da18d09103400d400001ab43612cf94dc9ac47820e0ef06ae30815589443c618208d83080d800001ab3d582d194fc9d64882108eec6ba30715309203ba17d09303240c600001ab37672c0948497845e2020e7c6862e714508cc3b818209083140c200001ab31592d4950c9c248b20d0ed46b02f714b08c83a617608c82e40c400001ab2b782c214609944651fe0e9c69a2e5142889439816d08802c80b800001ab25872c994f09ae4822128f046ac2f014f08d43a016d08902dc0b200001ab1f892ce14d89b047c2118f086cc30215188fc3b816d084828c0ae00001ab19802d5152c9e64942188f606ce303153892c3d618809582fc0ba000 else 0x1ae106b2dd15809fe4a02208f8871e328165098c40219d09b03340c200001ae0a812c894cc99e4691fc8e3464c2cb13a881835415908502cc09e00001ae047d2d1950c9aa47d2080ec06c030815389083ce18408c02f00c600001adfe802cc15089c44832120f106cc30115089443ca18809403200c000001adf8852cb15089d849421a0f406d230615888f83c617e08902e40aa00001adf2a72c0146898646a2060ea46a62f914a08a838e16d08682ec0b000001adecb12c914d89ae47b20e0eec6d031315509143c217d09383400d000001ade6a82d215289dc4902140f246ca30415589083c618208f83000c000001ade0b92c994f49c24882110f2c6e6310153891c3b417308882d00c000001addabe2d215209e049221a8f546ec30a14e091c3d218608d83100c600001add4ab2d395189d649120f0ec06b030315208f83a017708c82f40c800001adced02c3149498e4601fd8e786702d814108783a417208882e40c000001adc8d12ce94e89b047e2148efc6c030215009503e218609603080d400001adc2cd2d215209c447f20d0f086c02ff15009203c418109002fc0ca00001adbcaa2db956c9f649d2208f606da2ff14d08ec3b218809283000a800001adb6b62cf950c9bc4862140f2c6e830d15409243c617708702e00a000001adb0bc2cd94ec9ba47d2108f186d430014a88f43c217908b02cc0ae00001adaace2cd94e09b24862108f146c430015109183ba18a09583080bc00001ada4d52d014ec9b248020e0f046c42fb14e08f83bc18409282f40ca00001ad9ec72d315509f449521b0f4c6f2316154093c3ea18509403180be00001ad98ca2d014fc9c44872160f546ca2ff14e88ec3d018b09202fc0be00001ad92cf2ca94d89a047520a8e9069a2e814c88f43a017408902d40a600001ad8cd62ce14e09bc47620d8f086c430915489303d017b08c82ec0ca00001ad86cb2d7952c9de49321c8f586e832115d89843e819809483100da00001ad80c52d295249c04802110f106b42fb14e89043b817c09283080d000001ad7ac52d3151c9cc48d2130ef06a22fb15008f43b417408982f00c400001ad74c92d195189d64932178f346d22fa14608b43ae17a08e03140d600001ad6eb62da95209c447920f0f306c62fb14988a839c17b09083080ca00001ad68cf2c294c89a84662048eac6ae2fa148088c38816f08f82e00bc00001ad62e72c314a899e4792070eb46a22f114508b03a217808f03080d800001ad5cf92c794889804652028ea068e2ea14408b839a17908b82e80d000001ad56ef2d6150c9ce47320d0f1c6e230715489083c618109503440e200001ad510d2c194b499447420f0ef06aa2fc14988e03a616e08302a80aa00001ad4b5c2aa93d493c4401f10e2c6702d4140089839616d08c02e00aa00001ad45722c894ec9b64862108edc6bc30314c88e83b218008d030c0c200001ad3fb02b113ec93c4411f28e3c65e2ce13d088039017308c02fc0c800001ad39c72c314c09b64772088ef86c42ff15208f03c018509303040c600001ad33bd2dc95649e84902170f206ce302150890c3cc18909403280ce00001ad2db82d895509e049321b8f346da30e14e08f03b618009703180c000001ad27c82c614ac99e47720c0ee06ba2f914888cc3a017909182e00b200001ad21ad2df15989fc49921f8f5c6ea314152891c3d018409082e40c400001ad1bb82c914d49ba4732078ee46b42f714f090c3c018208d831c0bc00001ad15c02ce14ec9ba47820c0ec86982f214788cc3b617d09283140ca00001ad0fca2d2952c9da4902198f246de2fe14a88cc39c17e09382e40d200001ad09cd2cf150c9ca48a2150f206c62fe15088e83ca18f09803240d600001ad03b22dd15609d848b2120f086b630015189443dc18f098034c0d600001acfda62d7150c9c247d20c0ef06a42ee14308bc39e16208782e00b200001acf7b62c294b89a047520a0ee069c2e614888dc3b217408d02c40b800001acf1c02c394989a647f2088edc69c2f214888cc3ac16e08a82dc0ae00001acebbd2d515349de4862150f0c6b42fb14e88dc3c017f08f02f80ca00001ace59d2e2159ca0a49f21a0f446f631815c093c3da18c08e02f80b400001acdfa92c694b09a84782080f106be30714a08fc3c218208f83080c000001acd9a22d194f89ca4852108ef06b630115289103ce18909403000ac00001acd3722ec15aca0e49f2180f6c6da30314d090c3d018209182fc0c200001accd612d995489e048b2138f246bc30f15d09643de18409183100ba00001acc7552d995109d84912170f246ce30114d09003b418608e030c0bc00001acc1572d0150c9de48b2100efc6c630214808a039017408782e40c800001acbb422d795309cc47f20f8f146cc30e15709343ca19109903280d800001acb5452cf151c9d64892100f2c6d430515689303e619508f82f00ca00001acaf3d2d715209e049621a0f346de30414788ec3a017708682ac0ae00001aca9582c2947c9864682060ee06a22f614d08e43c218809003280ca00001aca34c2d415489ec4972158f206e631d15c09743ea191098832c0cc00001ac9d6c2bf14549824651fd8e806842e3146889c39c16e08602cc0b000001ac97862c614b89a44722048e9c6882ee14488bc3a617e09282fc0c2000) else (if i < 274 then 0x1af8e772d294fc9b84762120ee06a42ef14908e43e818909202f80d400001af88812d095009c04852158f506d630d15408e43b017709503280dc00001af827a2cd95009ac47520c0ec46ae2f014d08f43b617908d02ec0c600001af7c472e895c4a204ae2238fa8734339168898842219409283100cc00001af765b2c514c899c46b20d8ef06b22fa14f89083c618a09502fc0be00001af706e2c494c89a846e2088ec069e2f714808a839a17208f02e40b600001af6a802c394a899446d2078ec86aa2ef14b08943a416d08502d40b800001af64742d795089a446720b8ec869c2fb15209303dc17a09182e80b000001af5e792c914fc9c24822130f2c6ca307154090c3c618809503240d800001af58a82b8945495844e1fa0e746702de14388a438c16a08302c00b600001af52e02b6947c9644602030ec869e2ea14488a439816f08282a80a800001af4d042c114989884642020eb46a82fb14c08d439c16e08b02dc0b800001af47152c794dc9a04732090eb46962dc14208d83b817908b830c0d400001af410b2d395249ce48b21a0f346dc30b15309183d018a09103080be00001af3b052d695189d648c2180f086c630314d88b83ba18409382f00bc00001af351c2c914f49ce48e2160f286c230014a88f83b017d09082d40b200001af2f082de156c9f64982210fb071232a160096c41019e09f83480da00001af29362b7941c95244b1f90e7468a2f314708dc3b818809803280c800001af23312d815249c44802100f286d830915289583f219a096833c0bc00001af1d392cc14b89ba4882110f246e031215c09643e019309703240c000001af173b2d195089aa46d2098e846822e014488bc3a616708d02e40c000001af11202e11580a204a221c0f986fe31115808f43c417108c03040bc00001af0b2c2c714c099446b2078eb06962e5142887438617108882f40b800001af05482ca94cc9b44772078ed06b630415409183a817f08e02c00a800001aeff492d2951c9b448420d0ed06bc2ff14e09083ac17d08b82f00a600001aef9572c814e09b64862130f406f431916089643e218d09403180d400001aef3412dc95509d64902170f046b030015109143d418809983500d400001aeed352d815709e649721e8f5c6e631815c094c3e619509283000b400001aee7262d615209e64872150f306d630c15489303c818609282f80ca00001aee1292d215309d848e2148f346e031515688f43ac17e09403200c400001aedb322c5149c98e46f2050e8c6a22f614a08d83a817809683340d200001aed53c2cc14e89b64852100eec6b62ff14d89143b417d08c82e40c000001aecf4b2c494949b24752098ec46aa2ee14688b43aa17d08d82d80b400001aec94f2cd14d09a64792080ea06902f114d89143e018909303380b400001aec34c2d515409d04862110f0c6c430314f88d43b617a09283200c600001aebd4c2d5150c9be48d2160f4c6dc31615b894c3f619809a03140c800001aeb7272dd95649d44872170f5c6ec31f15d09743d219309803700d600001aeb14f2bb94789904601fe8e8468e2e414588b838c16a08702cc0a600001aeab4c2d695149d44952190f1c6d430614e08d43a817108e83040ca00001aea5512cf94e49b64812110f146d430c15389403d218609483340c800001ae9f602c514b89a44772028ea46a82fa14f09183c017708f82d80b200001ae99932bb14709704522000eb86b02fb14d88cc3c017e08c82f40ba00001ae93d52b3143896845e1fc0e606762d7140088c38a16b08802cc0b400001ae8dfe2be946c97e4652060ec868a2f215008e03b618209283380d800001ae87f82d715109ce4882100ef46bc2fc14f89043d8186092032c0d000001ae81e22d995289c648120f8ed86982f914988d43a817a09283000cc00001ae7bd12d2952c9cc47820b8eb06a42fd14d88ac3a217c08f83280ce00001ae75d82cd94fc9c848a2108ecc6a02ee14788dc3c617f09003340ce00001ae6fe62ca14d49b247e20c0eb06b02f614788b439617108a82e00bc00001ae69f62c814bc9984662030e906942f414d88d83be17908c83080be00001ae64042c694a89944792098ee06cc304151090c3c818808f03180ce00001ae5e042d114f89b848d2128f006aa2fa14d08f83be17f09482f40ae00001ae57fd2d395209d848520f0ef86b630315509043cc19009482e40b200001ae51fc2d294fc99e47620d8f006b230815189283da18809303100ca00001ae4bd72e89598a1a4ba22c8fc8710328160895c3d419009603240c000001ae46212ab941c95a44a1f30e5066a2dd13c888c3a616e08c83040c800001ae403c2bc94589604522008e9c6842e414788d43c018409102d40b200001ae3a532ca94d09a84772108f086c630815909583d818c09503140ca00001ae344b2da15209e04942140f486ae2fc15109103bc18008b82d00b200001ae2e512cf14ec9b24782080eb06aa30115389143c617a09082f80b600001ae28432cc94a899047220d0f086ba2fe14e09043ba17809002ec0ca00001ae22572c014d89a446920d8efc6ba2f614888a839c17208a82f00be00001ae1c882ba944c97a45c2018e7c6842e513e089438e17008782d40b400001ae16842d114d89ca48020e0ef86ba30615008fc3c618909183040c4000 else 0x1b10c912d615489e048120d8ec06982e2141089839816d08882e40b600001b106692e49574a1a4ab2248fa46f4316157896c3f218f09b83280d400001b100792cc94d49ac4792148f1c6d8314157095c3e618f09402fc0de00001b0fa912c614e49ba48c2110f046be2f014708b43b017508e02d80bc00001b0f4732dd954c9d24822138ef86b02fb14c08f43b417808a02c809e00001b0ee802c514a899e47b20f0f206c631215309143ca194096032c0e000001b0e8742da958c9fc4a121e8f546ee31515809243c818209083240c600001b0e2652db95709fc4982188f3c6d02f514808f43b417c08c02e40b200001b0dc882b7144896645a1f80e3c6702e414688943a217508a82e00b200001b0d6832d4950c9de4882130ef86b830c156893c3d618109403100be00001b0d0912c514d09c847f2118ef46cc30715289143ca18509183000c400001b0caa02c694f09ae4722088ebc68c2e914b08bc3a617608b82f80c200001b0c48b2db954c9e64982218f8c6fc32115c09543dc19008f832c0c400001b0be982c814b898846e2030ec06a82f714b08e83be17e09083300ba00001b0b8ad2c894c89aa47320d0ef86bc2f914b88d83a817308d83040ca00001b0b2dd2b8142c9604591fe0e7866e2d313c087c38817008f02e00b800001b0acef2cf951c9e24922178f306be2f914d08ec3c018609303040d200001b0a70f2ba94889764601ff8ea86b02f614708a839416c08682b40b600001b0a1092d0150c9c24892188f146cc30515309343e6191093031c0ca00001b09b0c2d014d09a846c2038ed46982f714b88bc39c16c08582f00aa00001b095122c894ac98e4762118f386ea31a15889603fe19409c032c0e200001b08f242c994b498c4541fd8e706882f414c88c839c16f08c82d80aa00001b089392ca14cc9a847720b8ebc68e2ef14a88dc3aa17c09183100bc00001b083472ca94d89b848420c8ef86be30014d08dc3b217508983040b400001b07d5e2c314b49a44722078ec06a82ef14e08e83ae17708c82f80c200001b077862bd143c9564581fa0e7c6702df13e887839016608982fc0c200001b071572e39598a144a42198f6870631815e89443ce18b098833c0c800001b06b932b314149464541fc0e7c6a22f314708f83c618108a02d40c800001b0659b2d2151c9d84872108f0c6d630814f88f43d018209603300d000001b05fb42c414c899047220a8ef06c42ff14d88ec3bc18009403340c400001b059bd2c2147899c4792038ec46a82e614108a03ae17c08982d40ba00001b053d82c794a099846d20b8ef06ba30715489183da18f09302ec0be00001b04db92da15749da48d2140f006c22f914b88f43b818009182e40b600001b047d52c694a89a247020c8ef46982e814988cc3aa17308a02ec0c000001b041c12dc95609ea4a22260fa06ee30e15709103ce18908d82d40c000001b03b9b2e71598a104a021e0f606f631f15c094c3ce18d09283240c600001b035c72bb147098e46e2028e986ac2fa14788bc3a017808d83000c000001b02fcd2cc14f09b847220c0ebc6a62fd14f08fc3bc17708b02dc0a800001b029fa2bd943c95e4592038e686722db138085438c17608802d00a600001b023e12dd95689fe4a42230f846f431115689003da19109502f00c000001b01dfa2c2949899a47120e0f086a42f514e09103c818e09302e80c600001b017e42d995649e049521f0f406cc30715389183da187096031c0c600001b012092be148098846e20b0ed86ae2e814608a439016e08a02d00b000001b00c102cd14f49a44762080ee46b42f214608dc3ae16e08302bc0a800001b005fa2d99558a064a82208f406e231215508f03c817808f82e80bc00001afffcd2ee159ca164a121d0f786f231915989243e218b091831c0d200001aff9e22c614b499c47a2088ec46b22ff14a08bc3a817b08d03100b800001aff3da2d395149c448b2158f386c630014e89083b617f08e83000dc00001afedba2e1958ca0e49621a0f606ee31815c89543f219709f83580cc00001afe7a22d995209b44852198f3c6e6312152890c3c818508c82f40c000001afe1962d0950c9c648a2168f406de30414c88e03c217909082e00c000001afdbc42ba947497c4631fd8e706722e8140887438a15c08382a40b200001afd5ce2c694c09ac48020f8f1c6d030d156090c3dc19009403000c000001afcfd62ca14b899c47520e8ecc69e2eb14a88e03ba17f08e83080cc00001afc9e52cc14d49b24722140f286ea314155091c3d017c08c83040c600001afc3fc2c594889924682058e986942ec14988d03ae17608a82e40ba00001afbe2d2b9945c96044e1f78e606742d514008b439017208f02dc0ba00001afb8412c2148c99c4642090ef06a62f214588bc38c17b08f83180b800001afb2382d195189d448c2180f486da2f814c08dc3c016f08882c40ac00001afac242d994fc9be46d2098f086b42f314908c03a617308b02e80ba00001afa6442bc946098445c1f90e2065e2ce142887838616308382c40ba00001afa0682be148499247720c8ed86ae2f514a88cc3ae17409603000b400001af9a6e2cd15189d447e2110f0c6d430f15409343d219109403040b000001af94792c514bc99647a20a0ec86a430214d88b43aa16e08a02c40c2000)) else (if i < 277 then (if i < 276 then 0x1b289bb2cc14c09b247c2118f1c6cc30615709704061a209d834c0d000001b283e72b8144094e44b1fb8e6c6762db13a887838416e08982d409e00001b27dee2ca14a89aa4712078ed46b42f614d08c03a817b08d82f00ae00001b278292b3943896c45e2040ea06902e213e087038217308a02e00da00001b272312c894b89aa4772070e8466e2dc13f888438c17008b82f40ca00001b26c242ce94e89aa4782130f186c6308158091c3ce18a095031c0d000001b266352ca94f49ba47e2110f306dc314156892c3c817e08c82f40b800001b260402c814ec9ce48b2158f406d030b158091c3d218a09583200ce00001b25a302d895349d04882150f2c6ba30514f88e43b817108702c40ba00001b2542c2ce94fc9c04802128f246d830c15489343e619409403300d600001b24e4f2c2147897445d1ff0e586682d413a085838416008382bc0a800001b2485a2c8949c98646a2040eb46982e714c08c03a417408702f00a600001b2426a2ca14f89c04792098ecc6aa2f814c88c43a617808d82f40b200001b23c782ca14b89aa48520f0ec46b62f814808c83ae17909082ec0b200001b236762d395309d047e20c0ef46ba2fb14e09083ae17809102cc0a800001b230592db95549d248e2140eb46ac2f614f88e83b217608a02c809e00001b22a7b2c1947897c45d2060ea46942ee14908b839016f086829409c00001b2248c2c514a899247220a8ee86b22fc14f88fc3dc18409083200c000001b21ead2c114ac98e46c2058ea46922ed146089c39a17108e030c0c200001b218b52d294fc9b647f2128f2c6e231315909683ca18c08f03200c600001b212cc2c3149c9a246b2058ecc69c2ed14388cc3a017708402c40a800001b20ce32c514d099446a20a0ef46ae2f715008f43b217208a82e40b200001b206c82e215a0a0e4ac22a0fa070e32816409883da17b08c82f00c000001b200d12c814c49a847020b0edc6882ec14208b83a816d08782f00c600001b1fabd2dd15609ee49f2210f746f031d15989243cc17d09003000ca00001b1f4d82c714f49cc4892150f2c6e030b156094c3cc18008f03080ce00001b1eed92ce94ec9c447a20b0ee86ba30014f08ec3b017608b02e00ba00001b1e8f12c194e09c64842128f106d430e15309543e018409403080c400001b1e3002c994a899c47020a0eec6b42f414a88c839a17208782c40b000001b1dd2b2bb94689884642030ec869c2f114788d03a817308b02c40b000001b1d6f12e91588a024a22228f8470c325159894c3de19409583240d400001b1d11d2bc947c97c46c2048ec06ae2f114d89003b017c09102f40c000001b1cb1b2d295209cc4872120f146c230715409483d018e09383000bc00001b1c5462bf94889844692090e9467c2e414608c43a017908e032c0d600001b1bf512d2150c9c84882100ef86c02fe14988e83be17b09003080ce00001b1b9752bc948099447320b0ec469a2f114a08fc3c018209183040d000001b1b3662d815189d04882100ef86be30614c89043ce18209103100b400001b1ad7e2c314889a64712018e986842df14408b03a217409103100cc00001b1a79d2c594c099446e2020e7c67e2e514188903a217108782c409e00001b1a1cd2b914389604521fb0e586962f314d08f439617708d82c009c00001b19baf2df957ca004a12288f7071432816689b03fc19f09903400e600001b195be2c614c89a247f2148f306dc307152893c3e819b09803540e400001b18fc72c714e09a04732108ee46b42ff14a08c83cc178087029c0a400001b189e72c194c89b247f2140f206d02fc15089243c818909702ec0ca00001b183f92c614ec9b84892140f186ca30815309443e4190096032c0ce00001b17df62ce95149da48020f8efc6b22fc14d08ec39e17208c031c0d800001b177ed2d915609ec49321d8f746f431b16309743e619309703000c400001b171f22d294fc9ac4712088ef46b82f514b08e83c017e09282fc0ae00001b16c072c894ec9b647220b0ec46a22ec145088837616708f82f40bc00001b166352bc14889844692050e986962f114c88cc3a417608a82dc0ba00001b160252d215209c648e2168f246ba30514e89003bc18608d02e80ae00001b15a272ce94d49be47920b8f086c82fb14b89203cc18809583040ae00001b154342cb94d098a4722100eec6b22f814908e03b417a09003380bc00001b14e2e2d095089b646d2070ea86922e514788d43a217a09083100c400001b148302d295249d648c2158f3c6de305154897c3d018309302fc0b400001b142382cc94e49ca47b2080eb46a62fe15088f83c2180093833c0d000001b13c3c2cd14e89d44892168f586fa31d15f095c4021aa09f83300c000001b1365a2c614cc99846820c0ee06a62f114808e43b017709083080c400001b1305f2ce94e89ac47120b8efc6ba30715088f43bc17a08c02c80ae00001b12a7f2c014749904702028e906a22fb14c88c83ac17108902c40ae00001b124782d615309d04882158f406d82fe14c08e03ae180093832c0d600001b11e852cc150c9dc48d2170f486f631115c89343de18c09283100c400001b118a02c714b899046b2030ed06ba2f914e08d839416508902e40c200001b112a12d1953c9e04902110f046b02f714a88f03b617e08c82ec0ba000 else 0x1b406b22ce94fc9ae4832160f006e031615789383e418609783380ca00001b400b72cd14fc9ac47420c8f306d630a150893c3be18b09683500d200001b3fac32cf150c9c64852138f346de31614f08c839c17b09203040c200001b3f4e32be947c98645e2018eac6a22f014c88c43a016a08102b409e00001b3eec92dd1590a104a421c8f246ec30b15008d43aa17909083100cc00001b3e8d42c4948498a46a2050e986a22f114988f43b817a09082ec0c200001b3e30e2b5143095a4501fc8e846862ed14708b83ac18009082d80c600001b3dd1e2cb95049b647220b8ec46a42ed14a08d439216807e828c0a000001b3d72f2c614c89b047c2128f106c830115209083d419809083280b800001b3d1492cb94cc99e47c2108f086c22ef14b08fc3c618609102dc0ac00001b3cb592c6948499846b20a0f086b42fe14d88f83cc17c08d02e00ba00001b3c58b2be149c9924692040ee06a62e8143889c39616708402b40b200001b3bf962cc14ac99a47520a0eec69e2eb14488b03be18708b02dc0c400001b3b98a2d014e89ae4812160f306b82f714b88dc3b617809583080da00001b3b3772dd15489ce48f2170f506ec31415689403c618109403080b800001b3ad7a2d49564a0049f2210f9870831415509243cc18d08d82f00c600001b3a7b22b3141494643e1f00e0c65c2cf13b085037616108802a40b000001b3a1c02c614c09904722040ecc6a62f714a08d43aa16c08682fc0c000001b39b9b2e095649f649521b0f486e6315158892c3da18f09403040c000001b395962cf15289dc49221b0f686f231a15689343e617b09082f00c600001b38fa32ce14f89cc48d2140f2c6d231015309183c6181093031c0d000001b389a82d115049cc47e2110f386d830214d88ec3ae17708a82a00aa00001b383d22c0148099247420d8ef86c62ff152890c3b417008f83040c200001b37dac2e015609ea4992178f206d831015188cc3a2176090030c0c400001b377a62d9953c9ce48320c8ee06982ef14608f03be17b08e82c80b800001b371cb2bb947098a4672050ee46b42fa14888e83aa17b09283080c200001b36bf82ba14809744642058e9468e2e614708bc3ac18208f83200c600001b365c92e51570a004a021f0f646f030615409203c018409c035c0ce00001b3600d2b3944496c4621fd8e946ac2f614e08d839e17b08d82e80b200001b35a2c2c794bc9c04822138f106da30915209203ce18b09783100c200001b3541f2d195049d04812140f2c6e631d15409043d218c09403240d200001b34e2e2c994d89bc47d20e0ecc6a230015189003cc17e092830c0b600001b348542c014909844672018e746942ea14508b439e17f08d830c0d200001b342522d715349d248c21c8f446de31d15d89703f6194098833c0c600001b33c432e015889f649221a0f506fc31e15e09783f819c09a03440c800001b336332d114f09be47220e0ee86be2fa14488d03b4183093030c0be00001b330442cc14ec9b447620e0f2c6e230415208ec3c818109102f40d800001b32a412d8953c9d848620f0ef46ce30d152893c3e218b09182dc0b800001b324762b7146096e4542078ee46c02f314808c03ae17308a82d00a600001b31e742cf14f49a847c2088ee86b62fd14d890c3d418509303180b600001b318772d195209ca4902198f446c830514f88dc3d418308f83080b600001b312612de15849ee48f2170f446d831315c897c3f4190094031c0c400001b30c9d2b314109524501fb0e7c6822e4144089438c16c08a02d40ce00001b306bf2c214a099446e2030e986902f614a08e43a817d08f02f00a800001b300bb2d295109c847920f0ef46be2ff14b88b03a417a09183080d200001b2fada2c294a099c4692038eb06a82ec14808a03a816d08502d80b200001b2f5182b2942c9624612048ea46a02e9146889439616e08b82cc0be00001b2ef082dd15289d448d2120ef06aa2f014788d839417708d83040b200001b2e9102ca94c09aa4752080e9c6ac2f014c08e43a617908c830c0b600001b2e3252ca94d499e4722030ec06ac2f014488cc39617f08f82f00b600001b2dd202ce14f89ba47f20c8f2c6e230a15388fc3c018709083000bc00001b2d7532b9944095644d1f58e6065c2d814288a03ac17408902c40b200001b2d1772c314709764602020ea06782eb14888bc39017708702e80b400001b2cb502e295a8a104a82270fc070e328163098c3f418f09603080bc00001b2c54f2cf151c9b247820b0ed86b230215509303da19108f030c0c400001b2bf6e2c1948098a46e2020ea46bc30615208fc3b617a08a031c0c800001b2b9712cf94e09b246b2078ec46a62f314c08fc3c218609203100c200001b2b3812c914dc9a647320b8f046c62fe14d08c83a217b08d02ec0d000001b2ad8d2ce15109b44842128f206de30a152091c3ce18108c82e40bc00001b2a78f2d0951c9ca4812130f146d430815288f03b017e09503580ca00001b2a1752dd95589e649921e0f7c6e830d15a09703e819209703040bc00001b29ba42bb945895c4501fa0e346702df14188b83ae17f09202e80ae00001b295bb2c114a49a246d20a8ee46b42f914e88fc3bc18009182fc0ae00001b28faf2d394f09cc4882110ee86ba30914f092c3ca18509102e00b6000) else (if i < 278 then 0x1b5848e2c814dc9984662050ed86a22eb14c08d83a217808983000ac00001b57e932ce15309d849021f0f486dc30a157093c3f819509883180c200001b578c92b4942093e4411f18e2c65c2c9135887837215a08182980a000001b572ee2ba947898a4692060eb469a2f914c88f03c217c08f83080c200001b56cf42ce14f09a246b2060ee46ba2fc14f08d43b218a09003140ce00001b566e52d3152c9b64812108efc6d430e15b894c3e4193098834c0e000001b560e32d215009d248320e8ef46cc30714e88ec3c418109203280ca00001b55ae62cc151c9d04852160f586f031115b891c3da18809383180ba00001b555082be147c98a46e2078ec46982ee14808b839c17708b82ec0be00001b54f072ca94c899c47220e8f006a62f314308b03aa17d08f83000c600001b549002d194fc9c447d2080ec86ae2f514e88e03be17e09002d40bc00001b5432d2b6940c9464521f90e3466e2d0139889837c16408782d40ae00001b53d382c914f89ca4832120f1c6b02f814b88d03c618808f830c0bc00001b537522c414b09aa46b2060ea86962e614108903a017008c02ec0c000001b531922b4141895644b1fd8e8068e2ed14608b43a017408a02d80c400001b52b8b2d295189ce4942178f306c430814f08f03b417708c82d00b600001b5256d2e115889ee4932158f0c6be2ff14c08d03a617b09203200b800001b51f9c2bc943497845e2028ea46a22ef14888a839416908f030c0d800001b519822da15409e44922158f446dc31815b89703ec18409103180c800001b513872c994e89b646c2090ec46ae2f314b08e83bc18108f031c0ba00001b50d8e2cc14d49b447b2098f006ba2f514688c039c16908882d40be00001b507702d815309d84952170f346d6313157094c3e8192095831c0c800001b501812c714a89a847c20c8eb86a430615289343d217f092830c0c000001b4fb7f2ce15089be4852148f306c430615589183d218a09002e00cc00001b4f5b92b4143c96244d1f90e486802e1143089c39216508782bc0b400001b4efb62d215089de4872158f146d830b15309383da19609403200d200001b4e9ec2b7947098846a2030ea068c2eb14408b43b417408802d00b400001b4e3d52df15709ec49b21e0f786ec30f15289483d618309583340be00001b4ddeb2c514fc9904622068e986a02f514d08d83b218209483280cc00001b4d7fd2c894d49bc48b2180f4c6e031515a09503e418f09402f40b400001b4d1e82df95589ec49e2240fa06f0311158891c3ca18008f82f40ce00001b4cbbd2e515c4a0849a21c8fa071a32f169098c3f619d09c83680da00001b4c5a12db15509e64912170f086c22ff14f09003cc19009b03480d800001b4bfc42bf148499c46e20d0f046b830815189483ec192098032c0cc00001b4b9d22ca149c99c4662038ea06a82f615289343d018d09683140ce00001b4b3e72ca14d09b64872120f286d630615609343f219409483180da00001b4ade22ce95109c247e20b8ec869e2f214b08d43b617e09003080cc00001b4a8182b5144895c45b1f98e706702d713d087c39016b08482c80ce00001b4a21c2c694bc9a247720d0ee06a62e914808bc3a217a09003140ba00001b49c222ca94ec9a847320b0ee46c42f914d08d83b418309383000ac00001b4962e2c794d49b44722088f106b02f514c88d83b017a08e830c0a800001b4900b2df15609ea49f2208f4c6de30c156092c3cc18309002f40ba00001b48a362c1947498e46e20b0eb46a82ff14e08e43a617408802a80a600001b484452c414a498646b20b8ecc68e2f314888dc3a016708202b80b000001b47e552ce94e09bc4822108f086bc2fc15008fc3c218208e02f00b800001b478652c314cc9ae47e20c8ed06a22e714b88b43a817109103040c600001b472682cd14f09c04722098ee06a62f214a08c83b817908882f40c400001b46c682cf95009a44712050e986922f114988cc3a017a08e83040c600001b466642d395189c24842118f1c6bc30215208f83ca18308c82c40be00001b460592db95689fc4932200f746ee31215688e43ac17208982f40ba00001b45a622ca94ec9b447b2098ec86b62f914f08d03a618708e83100bc00001b4545f2cd94e09c646d2050ea86982f014688b43a016a08702b80c800001b44e802c294709724541f90e546622d3139884437c16907e82a00ac00001b448792d215209c84832148f346d230215309183d6181092031c0d800001b4429d2bf94749864631ff0e786742db13f08943a417408b82e80b200001b43c8f2cd151c9d84872110f106a82f714b88d03c618209503300cc00001b436812d695289da48d2148f206d030414d88d03b218209603100d200001b430902cf15049bc4862150f286d430d15509183ca17a08b03200cc00001b42a902d015109c248020d8f146d0306155094c3d619009483340de00001b4248b2d495589e24932138f106be30315089103d618408f03000c800001b41ead2bf144895244e1f90e386722d1137084c35215407d82940ba00001b4189c2da15349e248d2140f386b830514f88fc3d018409903180b600001b4128a2d915649e44842108f2c6d030715109203ce18209182fc0d000001b40cad2c3949c98646520a8ed06b82f0146089839e17308e02e00a8000 else (if i < 279 then 0x1b702f22c514849764622038e9069e2f514d88f43ce17e09203000c800001b6fcf42d395209d848620f0ef86ae30315208ec3c017e08e83000e400001b6f6fe2d415389d248b2110f006ca31e15c89343cc18b09303080b200001b6f0ec2d7952c9ca48c2160f346da30915a09643e618e09603000da00001b6eb0c2c314b897e45c2048ea06a22fb14c88dc3ae17a08d030c0b200001b6e5352c114b898a4652080ed86a430615909483d819009a83540e400001b6df2d2d515609e24932118f3c6d030714e09183cc18208e82fc0c200001b6d9442c914d89c44812118ee46a22f014d08e43b618109603140b400001b6d35b2c6949097045e1fe0ec46962e614388a83aa17208b02fc0b600001b6cd2c2e61598a1c4a421d8f4c6f631a15689383d017d09482e00be00001b6c7162dd1564a0a49a2130f146cc30f15409043c818409003000b800001b6c11e2cf15249e448c2100f186cc30715009043b017908e02b00a600001b6bb512b9947497c4662048ea867e2e214308cc39e17208682b40a000001b6b54e2d415309da4972180f486d830c15789183ca18108b02dc0be00001b6af5b2c814b099a47f20c0f046c030115109083cc18108d02d40b600001b6a97d2c3148897e4692028eb06ac2fa14e88f43aa17008c02ec0aa00001b6a3602dc155c9d448b21a8f306be307154893c3e018c09483380c400001b69d1f2e815c0a144aa2248f906fa316152893c3ea194096031c0b400001b6973d2be147897a45f2008e4c6602d113a886c37e15807e02a40a000001b691312d715449e649221b0f546e231715d89483e619a09182f00b000001b68b542bf949098a4621ff0e8469e2f314908b43a817708c830c0d600001b685552ce951c9ce4912188f586f830e15509203d418f09183000c200001b67f942b2143096845a2018e6c6922e414708b839816208482c00a400001b679a52c614c89984712030e946962ee14288b038c17408e82f00ba00001b6738e2d715189ba47f20f0ef86a62f114e88f43ce17e09182f40b600001b66dae2c1145497845a2010ea06a02f714c08c439c17408a03000ca00001b667c12c394b09844642058ed869c2f514e09243e619609d03400d600001b661bc2d695389de4912198f546f4316158891c3e219309c035c0d400001b65bb42d615189d248a2118ee46b42ea14488b439017008602f00c400001b655e22b9947c98e4642098ee86c430515b09183bc17e09103180d000001b64fe52d014e49ae4842130f146d230f15a89303e018d09703380d200001b649f92c494a497a45f2050ea86a42ee14808c83a418109503180c400001b644222ba143c9684551fb8e686802e0146889c3ac17709003300c600001b63e352c914ec9b648520f0f386e031f15e095c3c417909182e40c600001b638292d215389ce4852170f206d430715308f43d017c08d02ec0c800001b632042e095b8a104ac2270fac6ec31715609503ee18f09583280c200001b62c472b3140c95a44f1f98e6068a2e3140886c37c16108482c00a800001b626192eb15d0a2e4a821f8f5c6dc30b157892c3d018609583000c400001b6201c2cd95089ac47320a0ed46962e814388ac39417d09103200d400001b61a122d015049c448c2110efc6ba2f514988a43a617008f830c0be00001b614192cb94d09ba48120f8ef86ba2ff14c092c3c417e09403100b400001b60e1a2d315089a846d20e0ed06a62ee14b08b439416208602bc0ac00001b608182d7153c9dc48b2110f286ce303156895c3ec18f09103000d200001b602112d5951c9be48b2120f146bc30315108fc3c018209683000c800001b5fc082d715009b247b20b8ef06d030b152092c3d018809503240da00001b5f6182ce94d49ae46a2060e9468c2ed14b08e03aa17a08e02f00b800001b5f0182cf94f09ae47e2150f306d431315b09483e618e09482f40cc00001b5e9d72f19610a304b22298fa871232115f89803f6191095031c0cc00001b5e3e62c694c49a447920b8ebc69c2f414888a838616f08c02c40b800001b5dddc2d6150c9c047d2158f106b62fc14888f03c218b09102f00ba00001b5d7f92c1149498a4692060ed86ca2fc14c88e03aa17808f02fc0b600001b5d1f02cf95249e249021e8f5870231a15e89683e618f096030c0c400001b5cbd72d995289ce48a2110f446f831f15e09383de18709303080c400001b5c5c12db9594a024952180f4c70432316109743f019309b03340c800001b5bff52bc14709844652038e886822f114388ac39617108902e40a600001b5b9f72d295189ce48620e0ed46a42ef14708b83a216e08682bc0a600001b5b3f32d1950c9e64852128f306d030015689243c018b08f82e40c400001b5ae2b2b2942496c4562000e8468e2e414288ac3a417208b82e00ae00001b5a8312ca14dc9b847e20d0ef06b22f014708bc3a617408a82c00bc00001b5a24e2c294989ae47a20c0ef06d4308157893c3d018f09683000c800001b59c782b894389704552030e346622d113c887c3a016f08a82e00b400001b5968d2c694b89924662040ec86a82f414708f03c217e08d03040ca00001b590822d095289dc48b2170f446fa317159896c3da18409483200c000001b58a822d195149d44872148f386e831215b89483d418e09002e40b2000 else 0x1b82150000000000000020a8f006d430a15389043ac17c08e82fc0c400001b81b582cd94c499c46d2058ee46be30215409003c218609002ec0ca00001b815742c614b09a447820e8ef46a62f314788cc39c16e08b03100be00001b80f5f2e015509ee49c21b0f446d231015489243c617e08e82fc0c000001b8094c2da95449d24892168f406d030714b08c03aa18a09203040bc00001b803652c114ac9ae4822110f246bc30515689183d019409703100cc00001b7fd9e2b6945495a45a2008e6c6902e514788d83b417608c02e00a800001b7f7a72ca94d09b648d2168f1c6d630a15909003b417a08c82c40ac00001b7f1ba2cb94c899e47c2128f186c02fb14a88e83b016f08982bc0a600001b7eba12dc95789ea49421a8f206ee30c15509343c817e09183080ae00001b7e58b2d495149c447a20d0ef46aa2f414988fc3be184090031c0ca00001b7df852d495089b647a20b0ee86c630f15809703f819709683440ce00001b7d99f2c314d09ca48320d0edc6a030014e88fc3b017d08e82e40c400001b7d3ab2c915009c04842140f246d42fd15309183b818108c02e00ba00001b7cdaa2d295149c047f2118f306de31215489003c417808902e40ac00001b7c7a22d595009c447e2118f2c6d031515c895c3ea18d09683240d200001b7c1a62ce14c499c4682080eb069c2f814a08c43ae17a09203040c000001b7bbb72c8148899046c20b0e9c6aa2ed14a88c03a417308c82f00bc00001b7b5b62ce14f49b247820e8f186de30715008e83ae17e093032c0c000001b7afc12ce94cc9b447720f0f2c6da308153892c3dc19309783280ce00001b7a9be2d295249d248c2168f386de30715509103c217e08e02f00be00001b7a3c72c714a89a647320b0eec6a02ec14a08c03a217508e83080a800001b79dc72cb94ec99e47b20d0ed46c030915308f83c018208e031c0d200001b797ac2dd95689e64902170f046be2f815288fc3cc18308f02e40bc00001b791b02ce951c9be48c2108f2c6b830314e08ec3b617d08d82dc0b200001b78bc52c414ac98c4602040ec069a2fb14988e83bc18208f82ec0cc00001b785de2c3947c98e4652070e8c6922ec14388d03a418108f82fc0b200001b780042bc94c09964652028ee06be30315288fc3a017908902d00ac00001b77a1e2c514b09804692050ee06ba2f314c89043b218309303140b800001b7742a2ce94cc99647320b0eec6ba2fa14d09083c818a09603400c200001b76e352c514b49a44752098ec069c2ef14b88d43c218008f832c0ca00001b768532c2949c97a4622050ea86982f614888b439e17608882e40c000001b762402d495389ea49921f8f386dc31015489203c417c08b82b80aa00001b75c4b2cd94c49a84692080eb46aa2fc15109043b217f09603040c000001b7563e2d295089b247e2150f246ce30615609383e018b091831c0d400001b750662bf14989864642038eac6a42f614f08e43b017708702b40ac00001b74a852c294a49a047720c8ee46b62fe15289143c017808702d40ae00001b744912c614a49a64732090ecc6a62f214508d83be17408d83040aa00001b73e8c2d515249c448b20d0efc6ce2f714a88d43ba17b08a830c0c800001b738a62c514c499e4732090ee06a42ef14988e43b417308a02e40b800001b732ad2d4152c9c447720f8ec46ae2eb14508bc3b218509283080d000001b72caf2d595189c247e2120efc6b42ff14b88c43bc180094832c0ce00001b726bc2c514c09a24792078ec86ba2f214c08c43ae17c09082e80ba00001b720cc2c794d09ac4872160f386de2fc14d08d039c17e08d83080cc00001b71aa42e115609e449421b8f4c6e030f15709003c217708e03040b400001b714cf2bd94709804682038ec86a42e514408c83aa18409482c00a600001b70ebc2d995649ee4902168f206d830315009083d218008d82e40ac00001b708d62c614d09ac47520b0f0c6c02fe14e88cc3c617e08c82f00b6000)))))))))

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



private theorem b273380 : covered 273380 273450 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273450 : covered 273450 273520 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273520 : covered 273520 273590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273590 : covered 273590 273660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273660 : covered 273660 273730 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273730 : covered 273730 273800 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273800 : covered 273800 273870 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273870 : covered 273870 273940 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273940 : covered 273940 274010 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274010 : covered 274010 274080 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274080 : covered 274080 274150 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274150 : covered 274150 274219 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274219 : covered 274219 274289 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274289 : covered 274289 274359 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274359 : covered 274359 274429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274429 : covered 274429 274499 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274499 : covered 274499 274569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274569 : covered 274569 274639 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274639 : covered 274639 274709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274709 : covered 274709 274779 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274779 : covered 274779 274849 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274849 : covered 274849 274919 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274919 : covered 274919 274989 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b274989 : covered 274989 275059 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275059 : covered 275059 275129 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275129 : covered 275129 275199 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275199 : covered 275199 275269 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275269 : covered 275269 275338 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275338 : covered 275338 275408 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275408 : covered 275408 275478 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275478 : covered 275478 275548 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275548 : covered 275548 275618 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275618 : covered 275618 275688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275688 : covered 275688 275758 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275758 : covered 275758 275828 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275828 : covered 275828 275898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275898 : covered 275898 275968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b275968 : covered 275968 276038 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276038 : covered 276038 276108 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276108 : covered 276108 276178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276178 : covered 276178 276248 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276248 : covered 276248 276318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276318 : covered 276318 276388 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276388 : covered 276388 276457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276457 : covered 276457 276527 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276527 : covered 276527 276597 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276597 : covered 276597 276667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276667 : covered 276667 276737 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276737 : covered 276737 276807 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276807 : covered 276807 276877 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276877 : covered 276877 276947 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b276947 : covered 276947 277017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277017 : covered 277017 277087 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277087 : covered 277087 277157 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277157 : covered 277157 277227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277227 : covered 277227 277297 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277297 : covered 277297 277367 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277367 : covered 277367 277437 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277437 : covered 277437 277507 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277507 : covered 277507 277576 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277576 : covered 277576 277646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277646 : covered 277646 277716 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277716 : covered 277716 277786 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277786 : covered 277786 277856 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277856 : covered 277856 277926 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277926 : covered 277926 277996 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b277996 : covered 277996 278066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278066 : covered 278066 278136 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278136 : covered 278136 278206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278206 : covered 278206 278276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278276 : covered 278276 278346 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278346 : covered 278346 278416 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278416 : covered 278416 278486 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278486 : covered 278486 278556 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278556 : covered 278556 278626 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278626 : covered 278626 278695 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278695 : covered 278695 278765 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278765 : covered 278765 278835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278835 : covered 278835 278905 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278905 : covered 278905 278975 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b278975 : covered 278975 279045 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279045 : covered 279045 279115 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279115 : covered 279115 279185 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279185 : covered 279185 279255 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279255 : covered 279255 279325 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279325 : covered 279325 279395 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279395 : covered 279395 279465 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279465 : covered 279465 279535 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279535 : covered 279535 279605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279605 : covered 279605 279675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279675 : covered 279675 279745 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279745 : covered 279745 279814 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279814 : covered 279814 279884 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279884 : covered 279884 279954 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b279954 : covered 279954 280024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280024 : covered 280024 280094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280094 : covered 280094 280164 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280164 : covered 280164 280234 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280234 : covered 280234 280304 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280304 : covered 280304 280374 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280374 : covered 280374 280444 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280444 : covered 280444 280514 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280514 : covered 280514 280584 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280584 : covered 280584 280654 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280654 : covered 280654 280724 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280724 : covered 280724 280794 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280794 : covered 280794 280864 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280864 : covered 280864 280933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b280933 : covered 280933 281003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281003 : covered 281003 281073 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281073 : covered 281073 281143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281143 : covered 281143 281213 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281213 : covered 281213 281283 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281283 : covered 281283 281353 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281353 : covered 281353 281423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281423 : covered 281423 281493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281493 : covered 281493 281563 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281563 : covered 281563 281633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281633 : covered 281633 281703 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281703 : covered 281703 281773 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281773 : covered 281773 281843 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281843 : covered 281843 281913 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281913 : covered 281913 281983 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b281983 : covered 281983 282052 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282052 : covered 282052 282122 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282122 : covered 282122 282192 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282192 : covered 282192 282262 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282262 : covered 282262 282332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282332 : covered 282332 282402 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282402 : covered 282402 282472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282472 : covered 282472 282542 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282542 : covered 282542 282612 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282612 : covered 282612 282682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282682 : covered 282682 282752 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282752 : covered 282752 282822 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282822 : covered 282822 282892 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282892 : covered 282892 282962 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282962 : covered 282962 283032 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283032 : covered 283032 283102 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283102 : covered 283102 283171 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283171 : covered 283171 283241 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283241 : covered 283241 283311 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283311 : covered 283311 283381 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283381 : covered 283381 283451 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283451 : covered 283451 283521 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283521 : covered 283521 283591 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283591 : covered 283591 283661 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283661 : covered 283661 283731 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283731 : covered 283731 283801 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283801 : covered 283801 283871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283871 : covered 283871 283941 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b283941 : covered 283941 284011 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284011 : covered 284011 284081 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284081 : covered 284081 284151 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284151 : covered 284151 284221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284221 : covered 284221 284290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284290 : covered 284290 284360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284360 : covered 284360 284430 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284430 : covered 284430 284500 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284500 : covered 284500 284570 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284570 : covered 284570 284640 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284640 : covered 284640 284710 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284710 : covered 284710 284780 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284780 : covered 284780 284850 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284850 : covered 284850 284920 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284920 : covered 284920 284990 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b284990 : covered 284990 285060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285060 : covered 285060 285130 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285130 : covered 285130 285200 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285200 : covered 285200 285270 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285270 : covered 285270 285340 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285340 : covered 285340 285409 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285409 : covered 285409 285479 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285479 : covered 285479 285549 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285549 : covered 285549 285619 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285619 : covered 285619 285689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285689 : covered 285689 285759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285759 : covered 285759 285829 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285829 : covered 285829 285899 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285899 : covered 285899 285969 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b285969 : covered 285969 286039 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286039 : covered 286039 286109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286109 : covered 286109 286179 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286179 : covered 286179 286249 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286249 : covered 286249 286319 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286319 : covered 286319 286389 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b286389 : covered 286389 286459 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 273380 286459 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b273380 b273450) (joinCoverage b273520 (joinCoverage b273590 b273660))) (joinCoverage (joinCoverage b273730 (joinCoverage b273800 b273870)) (joinCoverage b273940 (joinCoverage b274010 b274080)))) (joinCoverage (joinCoverage (joinCoverage b274150 (joinCoverage b274219 b274289)) (joinCoverage b274359 (joinCoverage b274429 b274499))) (joinCoverage (joinCoverage b274569 (joinCoverage b274639 b274709)) (joinCoverage b274779 (joinCoverage b274849 b274919))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b274989 b275059) (joinCoverage b275129 (joinCoverage b275199 b275269))) (joinCoverage (joinCoverage b275338 (joinCoverage b275408 b275478)) (joinCoverage b275548 (joinCoverage b275618 b275688)))) (joinCoverage (joinCoverage (joinCoverage b275758 (joinCoverage b275828 b275898)) (joinCoverage b275968 (joinCoverage b276038 b276108))) (joinCoverage (joinCoverage b276178 (joinCoverage b276248 b276318)) (joinCoverage b276388 (joinCoverage b276457 b276527)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b276597 b276667) (joinCoverage b276737 (joinCoverage b276807 b276877))) (joinCoverage (joinCoverage b276947 (joinCoverage b277017 b277087)) (joinCoverage b277157 (joinCoverage b277227 b277297)))) (joinCoverage (joinCoverage (joinCoverage b277367 (joinCoverage b277437 b277507)) (joinCoverage b277576 (joinCoverage b277646 b277716))) (joinCoverage (joinCoverage b277786 (joinCoverage b277856 b277926)) (joinCoverage b277996 (joinCoverage b278066 b278136))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b278206 (joinCoverage b278276 b278346)) (joinCoverage b278416 (joinCoverage b278486 b278556))) (joinCoverage (joinCoverage b278626 (joinCoverage b278695 b278765)) (joinCoverage b278835 (joinCoverage b278905 b278975)))) (joinCoverage (joinCoverage (joinCoverage b279045 (joinCoverage b279115 b279185)) (joinCoverage b279255 (joinCoverage b279325 b279395))) (joinCoverage (joinCoverage b279465 (joinCoverage b279535 b279605)) (joinCoverage b279675 (joinCoverage b279745 b279814))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b279884 b279954) (joinCoverage b280024 (joinCoverage b280094 b280164))) (joinCoverage (joinCoverage b280234 (joinCoverage b280304 b280374)) (joinCoverage b280444 (joinCoverage b280514 b280584)))) (joinCoverage (joinCoverage (joinCoverage b280654 (joinCoverage b280724 b280794)) (joinCoverage b280864 (joinCoverage b280933 b281003))) (joinCoverage (joinCoverage b281073 (joinCoverage b281143 b281213)) (joinCoverage b281283 (joinCoverage b281353 b281423))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b281493 (joinCoverage b281563 b281633)) (joinCoverage b281703 (joinCoverage b281773 b281843))) (joinCoverage (joinCoverage b281913 (joinCoverage b281983 b282052)) (joinCoverage b282122 (joinCoverage b282192 b282262)))) (joinCoverage (joinCoverage (joinCoverage b282332 (joinCoverage b282402 b282472)) (joinCoverage b282542 (joinCoverage b282612 b282682))) (joinCoverage (joinCoverage b282752 (joinCoverage b282822 b282892)) (joinCoverage b282962 (joinCoverage b283032 b283102)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b283171 b283241) (joinCoverage b283311 (joinCoverage b283381 b283451))) (joinCoverage (joinCoverage b283521 (joinCoverage b283591 b283661)) (joinCoverage b283731 (joinCoverage b283801 b283871)))) (joinCoverage (joinCoverage (joinCoverage b283941 (joinCoverage b284011 b284081)) (joinCoverage b284151 (joinCoverage b284221 b284290))) (joinCoverage (joinCoverage b284360 (joinCoverage b284430 b284500)) (joinCoverage b284570 (joinCoverage b284640 b284710))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b284780 (joinCoverage b284850 b284920)) (joinCoverage b284990 (joinCoverage b285060 b285130))) (joinCoverage (joinCoverage b285200 (joinCoverage b285270 b285340)) (joinCoverage b285409 (joinCoverage b285479 b285549)))) (joinCoverage (joinCoverage (joinCoverage b285619 (joinCoverage b285689 b285759)) (joinCoverage b285829 (joinCoverage b285899 b285969))) (joinCoverage (joinCoverage b286039 (joinCoverage b286109 b286179)) (joinCoverage b286249 (joinCoverage b286319 b286389))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 273380 ≤ index 525000000/512 := by decide +kernel
private theorem starting_value : fast 525000000=27601606 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 525000000=27601606) (n : ℕ) (low : 525000000≤n) (bound : n≤550000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=525000000
    · rw [first,anchor]
      exact starting_value
    · have past : 525000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤550000000 by omega)
        have within : index n / 512 < 286459 := by omega
        have lower : index 525000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤550000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ525000000To550000000
