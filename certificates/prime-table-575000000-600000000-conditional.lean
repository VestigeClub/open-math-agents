import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ575000000To600000000

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




private def radical : ℕ := 0x6022181410fd1f7059c03967c247f338cdfe05447039155d1f04a1f9d8441adaaaf39fbc7050d5a00a2325ad9833f38c7a3adbe3488027c56ecde49dbb8eb488b239890b076898a6d766520328a019c44d22c6d3d403910ae09055f94268741789b3752914d77ac6853688ab491b06ecee65c5aa09e1da5ba19b9f68f9559c5cd422249a145e8e0a6536f19cd650a50ac93c8f0499e2482b57c243a5bf4c1df43336e3bdd1d066b5d2e228c86d8f8798766eae99808afd2b739d8722d17bbe2300f1df74e70eec376748283682dfd25152b49bccf6506ca9ff5521cde29d23c039b172df970676d8c2817c7eaea8d4ea6db31d4dbb9338ff159ae29a58ede4150d399e3168a47881b4f94b1feedc57aa2805f739495b61fb33d83e4ceece2e4213b1f357dd6bef86ea4c89e0c4d677145e56d8ef44f29ffdd20811160a5a6f956771b54bc687eb4c66a30ba1e84a7cd91feaf83dccc0cf881ec9031fbe8e2fac937ce3d1ce9a0dd2cc8e5d2b396010f0aecfcba7f8fc8b5610549b9b5193ea97e241a3e900df3037c01c3615971bd76932ee1d331dce83fe19fbadbacb2a855dd85d1fc9f062e477ee55452751770e0c6d6c6d30ec2e46cd16d80514962f62e80731050cf3bbde3a5d87a2d2ef804d02ea860673e755a8d0a6ac8ba987915af7cc7e8bf0338e59a821dae3ac77f68e6629b9a9efe3928c1d9a788fa2a98b23f6d8f14ac234d5420857a94923215aa969d5e16034ee7c539ddf07678bd046acc06024f0e3fbfec261b50135cf460569b2b37cd1a41623fceba200656ec44cd5515c4543f32cbbe3f41b4c025641aaba3bfa1fa97c685e4b8ea9bb5c72e955cac16cb362bf2fa90010bf4f936db05dcb0933669c401b2d212e0cd0be04c1ea9f2f951469f5f423f85babfb73e6e29c8e41f55a491d6a99ade243e2f7379383f95f7a20c567d57ab9b288342af719215365e274edd481305ea4feb0b0d4cf94f254eaa72e84059f4587abfc849c18026a2f9469b60a261f0f5c88e19d5f7ed54cc1a2f90c9d64678b83ce3ea25aef7862ed6970281bfc5c152d5195ad3816dd1e83ba6babeb274921b5063679c71fa3dd59e8d2bcaec4897875764aae0d676728af23ba29a442cef43e8c85c2294e55aa4a739f88e8a9ca17fe63820c1eb5c7fbb05e27df58de6818eee3128cb5526945111fc812e787c56f5b950234b88f80db27cd55e273fa0348c1b41d4651e00eb5d97770c1ed51a7580df5c1d411ea92e4507d07505c55dc3b4e67013a1587d0afeb2163a95327eada5caff7cec31101610d9c7ca850a845e013e5e6ee82f79cb654bab39cc61e7e6379c682faa056ca9eea5bdab46bbc2ab2473d1f3479e07853270f530851ed45226a58b0396667e79d74453a9613c3b6d46bd4387288d339b762400f5e2ea9bbe73fd887220b0ccaf8cdf0e5a4f9c78d6f71095e9f350011f2c9c3bb365b695f387757fac1cc96118493bd7a5634c10d1665ff24c4a0741746a7cbd7448573a56af371b4c30b59d22d85235ade545e6a3549711806180ff5dae86165d27174d49c468de8a23f98d597fbace3636ff4471a97a341f41658f5bcdcea60850139faf5f7871a4b291581d083b9d9de4114c765c23e59d296c156d9d077af3bd80240359d2421502d760cb2c951e1fdd8b3384af3763a60730deba73083e511d51a070178907d61ffb2ba881670223ce1e712372a4c2f31618914889e8948c5bc951f7060f299d2da79070cbd32f73ca358db7b98ddf9f09927b434323c121173ec8de6f3e5ada54855c1786a4570c967735f7ed1010e20c09b8437b518298eff26fea11a070f95565714d9ac47c815f015959e2f2c34d7d087c6c6cbb1fbc90d98394c67371a395d893bf0c04b1b53c0058e196e19ba76cee5e8f0140de511510843b113a77f082ad78011a844624404ed04f10abf4eb2fa7f3bd5318922b3c8d09ec19f0504d87e32c37827d2d9fa45aa8d25584eb286e6f54197fe70a1fc0fbddbbdec7cc1d7423855f211e5c510a37f944875693c4e3e31a68e2f8461e7a712e2ba17655fcccda7522db1fd3fba88135d6bc4fbcb08ee78e7de32ca40f15ec377a2db0d68dd6188cf5f8dca8a7eb84640770a5810a895282062b2da6257f0f4eded8f8ab448589ff3db3a95fb57f18489998ba4d39a3700540b2b4e35bed191e647cd0cc61986634b31d614bbd73c67063be3bd5655ce342c67fca67f50e362475927582224085c8a7baada68f4fe61de517da9fe89f6bc8b69a17d1daff6649aea65e6be6122dfd943ddcd04ebe097d9638b72446e67d75048dcb79394a9c7c4d3bf934522300ba33dd15736a64fc4084512fb4d9331ecd51b9dbd446e13710d41096f5df0ff5522530940406a5a7be638b6e48f9b3c9b121c1fd7ffb9a8e48f9d88dede6a38f4d7987d50b3a838d2f85018bd289d2ec6d8712cca11b0170353f5dfc86ae26c4a0855a01ee1ae3e9f04779a90a069ed632b735da59a761f4bb7a6da7da210361e5eee9fd77ee10e2fe9f3073d7f3ec5af823b5b38ba014e6a730a438b350e4aad1c7b7c8990fa6b0512d85a7a8edec97612bd0284ab4e65fa9aefba3a7b122dfbaa09619dcd309ad50f275249b3f5b48db21f9864982a64b93acfbb4f73a8c6c4c35224bb83e0c412a843c8b3decc989ddff746e0c88d4b8d92090607f1ea1448c169cbfb00f08231970b8dd368902afcc743f521493fb619fc716187a5b8622613874f7258dc784652217823bd4ab39466cb2f9fa20a11ea696e33a6fc29d7aaa34fe68d72e44560f1d31bc007180b3a41c9e1a0571d41d90b53149131a6fc7a114653a118c1c6f4292c28852c675936d7f69dd0d3adbb3fb51e1ca4d61a64fa3e6c46344d159df2866e686810fa4c28bc2c849ab39f6e3328fb417c6e5dbc89a02508a6e7d9eb122ec8dcd18bd48d4e75e45c188f5392c11b5779a9283506191fbef7cea20740a3aea3b2eb5056a1450a0497f3b7d190a1d8255a6b1f597fea1cb00d0d1143956226cc5ddcf63ca6a865a8ab0d41ab238b1e10e0c8ecd6e85711f8b1ec240009d9997dac8ea35b8c754cce1ebde31148ca2a103eb5f694aacc0c98d366df0fa205aba79d77c92f08392fc7a66e27522958d11a8ddfdcbd185d31cfcd3df479bbe3851870d45cc270a73e6d64a0d80bb5877de28c4db1c29fb5179fc1a883944593affb93303137427f89db5b192d6e3cd0bd7c053922d4012477310e2df87a679e763e363bdc9e1048885d142ca053232f93a4ab7745440dd0517fdaee178f26846d770e81890c122190ba2c62b4d9347bb28d0d2a9c4fd6420ede9ea1843200179c8b66b82f295debebc777a487d7522e54072ecbc82189387b977d9e811818ef4f070479bf17435cc2be53cf068c1a5e09c38bebac294b6897146fd073461e8160a5dd7d97ab654a83ca7fc097c80c8f2dd787bf05ee982a5c8cc4273dd42ea5b5504f588501d300f17aafb3802b52cbd40203013fdddbad2f45b581b9993fed9d99d8a5206154f1c30646dac414d22e430d692dc0943bf47cb7b2904d711441a739bd5058ad5f22bc57d05f0b6659c151cc6f61dfeb8cdb334f098b0fd374b80e71418641bd01cccb9cac0723dbd917e3fafbf5da5bd2dca23c04da9368ad64c873c2461c9afa572e7446ed15d938571a8d4f86a11427a6f5ea8c4ef4cc2b30eef6490cfad1682bf8432f522530be68e7c16e90743df8467b7a42d698b6512a9cd0be47968f448515fd5f8f93b8307366fdc22530667c1b7a0cdf9ec5175a07689bc147e0f6b26aacf5f78089f8433b912836adc2dfe801cec57c36343fa7e64565ac522c0064b8c22be3d3d4d060359171d21b48f294b8754194cb4c626b5a1866c52064ec9f66597607bbb7b19558835e1475e04a577bf3ef1f039f9bb41d85bb5c6fcfb389013031a5fd110636e6a97141b81368bdbf83a1b707e2bf2de71e56fa2e873ef884f890ec7b2327cc6e6e8fd396517ad2fedc824fb03e31933596a5196e3f5c8e00d1013b47ecb8fbe4ac2e304101e0ddaad79e5728f439a6a6834995164311684492132ee86652523d14b9a43abb80372e304f182adfff3f35cdc4ff1ae3a09f7eb92d2181478b580516ca55b77996244a600cd4d637e7c6e67bfbace5d053af26ccebb2c2d9e091dedf805a4c9175154f7a0677355dbf96db488f0819dd9260077570774ffd266e7ba7197fa26d43cc2eeb85c2922694d8037146946f0b7a35c730c5549533dc41994437e316e4a43faa6ad396395a782e50194cef8e0df51e1b00244cb8094aade877b7d425a98f3cef67a315652d71f34051915c2a22b56fb3000c03701bf093868e19001547490c0b88bccbfe56c3793e140f420a530f2058a84d2ce37cc972e4aca0c49964fd015ac12870c3b97bb89db079603099f114c9c21f3ad027b78992150692be354d7657e6c8477e4dc604cd14450d95b6e6d69d485cb2d7c9c511aae5f033c89b842bcf8b556a87e9ba174b5385fff3bbac5b7c9c03dde59bc226f9a7e25180c0a47a4b7bf72bed6e368fabee163921ad60b712c5d4f08a657fecbe5cc088d25c458b0a5d64eb89a4a40ed10b25a75e283c0f812fbff132eafbdc64592be9f95f5adc4e44115f1a033c3f43a600a4ff8f5610f3d83ba65088a0d251bb6692d2df48f025f56421e4fc07e5551122630d7b44f0f62e829a29bfe3b0c80c177421b1e4a47bddee4f357bcc4c801b472e22f55c2df1cfba2589ca3e2ae52ad62fc8ad7f89716c5e30637afdd5273f05123baf0df7180f778cf3cdfd6a67efeaf8a1607f69d39192dd9e8fbd202be2a30f5d7c16e7aa6715552017667e6024a3b57889a1dfa41d535f6ab9aab8583f7e67dfc9a8b647a59acd024b5a663407b29ab1e2cf0bf17e89b6e1bfc6f617e3579ba277b00dffb298587c61af1655ba0c7aa43215ebbc7cb7fe789b5ea592c48940f654df5274e5712fb2673d644b271800e31d87a7486415194438cf4d6cfb8819c2cda47b36d1a133a9eac8d982e3c7f817f90a2f7cf6af2e92a32519e526bcd42da76f2243ecfaa130d4fe77c97c9ccb447a041b03e45be98d42906db71208812fc407cb0047f7bd84e3873226ec572b7b2123cac576450a34207cbfdf3d5e56bd5e37437a71fc86e0e6b8f0fef01c9d5b1b8871be5f5c0a8a7721b14e3ba86b04cb66e73c3ead20a690c966ab56372fca0f44d481de579783eb828e3eee61413f20d88fa991649220ed75d9b9d9a3f150d1fd2c509c5c92c51f7fd8098675dc62dd6d747ff1b03292973cac0ac83dc3ef6bf3cf6c88024997921ec3562fc5b7909213b2656266c7d4b2d80702b7644078b55d3b1fa75d8b736a7cfa184a3fbebab8f1acdd22621df730d94d4c321da6e32d27650a5c4270988a1db98faf94aef82fbf77ff5c6571dc18abc35d4a248aa54e777e9b8b9c7a1d9bcf5a55e49c0e4b500b68a24abacef46b6825c416f284df82722e6b017449c5f004e90ac81b5dbb1710467dc21e09f8f7296e6d2cbee73eb8cd0934633cc2179466f28b3e48ca6f896bc4a213d90bb459f25cd6a951fcf9d01e9e22b57d4e2b3a0c3a8b8fa95cfaba66066609b7940b6769c7a9997ca5732b81083211954b636808f016697dc72dc4b3f490472cf331a88a17ae02f4ea6c60262f40c83de726d18c6088a9cf6bede7cda6053d48ee891c178a9183685768e2c8d4e974ad155e73c5aa8b971824a25fedb4367c8ac202012b2d39ce63469d061106e6a210da1110c6411900b48249ff49df1f99173cbe899760e324ae3df710317e173416582b77b102c0d4aba27f7a577dd0f31ed59c8f09cc1671e0c2f8343224881e0ca25c6f0ffd12529370c8448d29443d76cad9da4162ab755e61367982fa6bda51a4497e672d07a691497969193604b618295b00085a0482288bc68dd440aacc57c4460d7fcc1d3ef6218afc763f557c25218adaa14f897da22a241d69f14f5d42e84c6371018dde4379bc60330fa7853b438533e4b9885685455d07077ced3a23801dbbc2af4a3ad5b9270639531d85e2221cd71de46432c1fae6cac40a34992608c6175772db678973f7c7d2be0ceaf32bbaeaf2de049c89cd84ed2f7a5a14cceb88dfc84ec8ab4083ad827e897d6e45f080cefa6812523637dc9facd8ba3a5688f5f5bb5a8dc22966aa

private def light (n : ℕ) : Bool :=
  if n≤156 then decide n.Prime else n.gcd 747106292628289444708380937293831544659502112248691679154935029028947927533099589206864815366798234329153235562080607562019236871366935959116501738803666174537810867225241796085310597754619259343815926673638047312709851500780194770609766400000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤24494) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 156 = 747106292628289444708380937293831544659502112248691679154935029028947927533099589206864815366798234329153235562080607562019236871366935959116501738803666174537810867225241796085310597754619259343815926673638047312709851500780194770609766400000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 156 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤24494 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 47 := by unfold smallValid; decide +kernel

private theorem sp47 : smallValid 47 48 := by unfold smallValid; decide +kernel

private theorem sp95 : smallValid 95 48 := by unfold smallValid; decide +kernel

private theorem sp143 : smallValid 143 48 := by unfold smallValid; decide +kernel

private theorem sp191 : smallValid 191 47 := by unfold smallValid; decide +kernel

private theorem sp238 : smallValid 238 48 := by unfold smallValid; decide +kernel

private theorem sp286 : smallValid 286 48 := by unfold smallValid; decide +kernel

private theorem sp334 : smallValid 334 48 := by unfold smallValid; decide +kernel

private theorem sp382 : smallValid 382 47 := by unfold smallValid; decide +kernel

private theorem sp429 : smallValid 429 48 := by unfold smallValid; decide +kernel

private theorem sp477 : smallValid 477 48 := by unfold smallValid; decide +kernel

private theorem sp525 : smallValid 525 48 := by unfold smallValid; decide +kernel

private theorem sp573 : smallValid 573 48 := by unfold smallValid; decide +kernel

private theorem sp621 : smallValid 621 48 := by unfold smallValid; decide +kernel

private theorem sp669 : smallValid 669 48 := by unfold smallValid; decide +kernel

private theorem sp717 : smallValid 717 48 := by unfold smallValid; decide +kernel

private theorem sp765 : smallValid 765 47 := by unfold smallValid; decide +kernel

private theorem sp812 : smallValid 812 48 := by unfold smallValid; decide +kernel

private theorem sp860 : smallValid 860 48 := by unfold smallValid; decide +kernel

private theorem sp908 : smallValid 908 48 := by unfold smallValid; decide +kernel

private theorem sp956 : smallValid 956 47 := by unfold smallValid; decide +kernel

private theorem sp1003 : smallValid 1003 48 := by unfold smallValid; decide +kernel

private theorem sp1051 : smallValid 1051 48 := by unfold smallValid; decide +kernel

private theorem sp1099 : smallValid 1099 48 := by unfold smallValid; decide +kernel

private theorem sp1147 : smallValid 1147 47 := by unfold smallValid; decide +kernel

private theorem sp1194 : smallValid 1194 48 := by unfold smallValid; decide +kernel

private theorem sp1242 : smallValid 1242 48 := by unfold smallValid; decide +kernel

private theorem sp1290 : smallValid 1290 48 := by unfold smallValid; decide +kernel

private theorem sp1338 : smallValid 1338 48 := by unfold smallValid; decide +kernel

private theorem sp1386 : smallValid 1386 48 := by unfold smallValid; decide +kernel

private theorem sp1434 : smallValid 1434 48 := by unfold smallValid; decide +kernel

private theorem sp1482 : smallValid 1482 48 := by unfold smallValid; decide +kernel

private theorem sp1530 : smallValid 1530 47 := by unfold smallValid; decide +kernel

private theorem sp1577 : smallValid 1577 48 := by unfold smallValid; decide +kernel

private theorem sp1625 : smallValid 1625 48 := by unfold smallValid; decide +kernel

private theorem sp1673 : smallValid 1673 48 := by unfold smallValid; decide +kernel

private theorem sp1721 : smallValid 1721 47 := by unfold smallValid; decide +kernel

private theorem sp1768 : smallValid 1768 48 := by unfold smallValid; decide +kernel

private theorem sp1816 : smallValid 1816 48 := by unfold smallValid; decide +kernel

private theorem sp1864 : smallValid 1864 48 := by unfold smallValid; decide +kernel

private theorem sp1912 : smallValid 1912 47 := by unfold smallValid; decide +kernel

private theorem sp1959 : smallValid 1959 48 := by unfold smallValid; decide +kernel

private theorem sp2007 : smallValid 2007 48 := by unfold smallValid; decide +kernel

private theorem sp2055 : smallValid 2055 48 := by unfold smallValid; decide +kernel

private theorem sp2103 : smallValid 2103 48 := by unfold smallValid; decide +kernel

private theorem sp2151 : smallValid 2151 48 := by unfold smallValid; decide +kernel

private theorem sp2199 : smallValid 2199 48 := by unfold smallValid; decide +kernel

private theorem sp2247 : smallValid 2247 48 := by unfold smallValid; decide +kernel

private theorem sp2295 : smallValid 2295 47 := by unfold smallValid; decide +kernel

private theorem sp2342 : smallValid 2342 48 := by unfold smallValid; decide +kernel

private theorem sp2390 : smallValid 2390 48 := by unfold smallValid; decide +kernel

private theorem sp2438 : smallValid 2438 48 := by unfold smallValid; decide +kernel

private theorem sp2486 : smallValid 2486 48 := by unfold smallValid; decide +kernel

private theorem sp2534 : smallValid 2534 48 := by unfold smallValid; decide +kernel

private theorem sp2582 : smallValid 2582 48 := by unfold smallValid; decide +kernel

private theorem sp2630 : smallValid 2630 48 := by unfold smallValid; decide +kernel

private theorem sp2678 : smallValid 2678 47 := by unfold smallValid; decide +kernel

private theorem sp2725 : smallValid 2725 48 := by unfold smallValid; decide +kernel

private theorem sp2773 : smallValid 2773 48 := by unfold smallValid; decide +kernel

private theorem sp2821 : smallValid 2821 48 := by unfold smallValid; decide +kernel

private theorem sp2869 : smallValid 2869 48 := by unfold smallValid; decide +kernel

private theorem sp2917 : smallValid 2917 48 := by unfold smallValid; decide +kernel

private theorem sp2965 : smallValid 2965 48 := by unfold smallValid; decide +kernel

private theorem sp3013 : smallValid 3013 48 := by unfold smallValid; decide +kernel

private theorem sp3061 : smallValid 3061 47 := by unfold smallValid; decide +kernel

private theorem sp3108 : smallValid 3108 48 := by unfold smallValid; decide +kernel

private theorem sp3156 : smallValid 3156 48 := by unfold smallValid; decide +kernel

private theorem sp3204 : smallValid 3204 48 := by unfold smallValid; decide +kernel

private theorem sp3252 : smallValid 3252 47 := by unfold smallValid; decide +kernel

private theorem sp3299 : smallValid 3299 48 := by unfold smallValid; decide +kernel

private theorem sp3347 : smallValid 3347 48 := by unfold smallValid; decide +kernel

private theorem sp3395 : smallValid 3395 48 := by unfold smallValid; decide +kernel

private theorem sp3443 : smallValid 3443 47 := by unfold smallValid; decide +kernel

private theorem sp3490 : smallValid 3490 48 := by unfold smallValid; decide +kernel

private theorem sp3538 : smallValid 3538 48 := by unfold smallValid; decide +kernel

private theorem sp3586 : smallValid 3586 48 := by unfold smallValid; decide +kernel

private theorem sp3634 : smallValid 3634 48 := by unfold smallValid; decide +kernel

private theorem sp3682 : smallValid 3682 48 := by unfold smallValid; decide +kernel

private theorem sp3730 : smallValid 3730 48 := by unfold smallValid; decide +kernel

private theorem sp3778 : smallValid 3778 48 := by unfold smallValid; decide +kernel

private theorem sp3826 : smallValid 3826 47 := by unfold smallValid; decide +kernel

private theorem sp3873 : smallValid 3873 48 := by unfold smallValid; decide +kernel

private theorem sp3921 : smallValid 3921 48 := by unfold smallValid; decide +kernel

private theorem sp3969 : smallValid 3969 48 := by unfold smallValid; decide +kernel

private theorem sp4017 : smallValid 4017 48 := by unfold smallValid; decide +kernel

private theorem sp4065 : smallValid 4065 48 := by unfold smallValid; decide +kernel

private theorem sp4113 : smallValid 4113 48 := by unfold smallValid; decide +kernel

private theorem sp4161 : smallValid 4161 48 := by unfold smallValid; decide +kernel

private theorem sp4209 : smallValid 4209 47 := by unfold smallValid; decide +kernel

private theorem sp4256 : smallValid 4256 48 := by unfold smallValid; decide +kernel

private theorem sp4304 : smallValid 4304 48 := by unfold smallValid; decide +kernel

private theorem sp4352 : smallValid 4352 48 := by unfold smallValid; decide +kernel

private theorem sp4400 : smallValid 4400 48 := by unfold smallValid; decide +kernel

private theorem sp4448 : smallValid 4448 48 := by unfold smallValid; decide +kernel

private theorem sp4496 : smallValid 4496 48 := by unfold smallValid; decide +kernel

private theorem sp4544 : smallValid 4544 48 := by unfold smallValid; decide +kernel

private theorem sp4592 : smallValid 4592 47 := by unfold smallValid; decide +kernel

private theorem sp4639 : smallValid 4639 48 := by unfold smallValid; decide +kernel

private theorem sp4687 : smallValid 4687 48 := by unfold smallValid; decide +kernel

private theorem sp4735 : smallValid 4735 48 := by unfold smallValid; decide +kernel

private theorem sp4783 : smallValid 4783 47 := by unfold smallValid; decide +kernel

private theorem sp4830 : smallValid 4830 48 := by unfold smallValid; decide +kernel

private theorem sp4878 : smallValid 4878 48 := by unfold smallValid; decide +kernel

private theorem sp4926 : smallValid 4926 48 := by unfold smallValid; decide +kernel

private theorem sp4974 : smallValid 4974 47 := by unfold smallValid; decide +kernel

private theorem sp5021 : smallValid 5021 48 := by unfold smallValid; decide +kernel

private theorem sp5069 : smallValid 5069 48 := by unfold smallValid; decide +kernel

private theorem sp5117 : smallValid 5117 48 := by unfold smallValid; decide +kernel

private theorem sp5165 : smallValid 5165 48 := by unfold smallValid; decide +kernel

private theorem sp5213 : smallValid 5213 48 := by unfold smallValid; decide +kernel

private theorem sp5261 : smallValid 5261 48 := by unfold smallValid; decide +kernel

private theorem sp5309 : smallValid 5309 48 := by unfold smallValid; decide +kernel

private theorem sp5357 : smallValid 5357 47 := by unfold smallValid; decide +kernel

private theorem sp5404 : smallValid 5404 48 := by unfold smallValid; decide +kernel

private theorem sp5452 : smallValid 5452 48 := by unfold smallValid; decide +kernel

private theorem sp5500 : smallValid 5500 48 := by unfold smallValid; decide +kernel

private theorem sp5548 : smallValid 5548 48 := by unfold smallValid; decide +kernel

private theorem sp5596 : smallValid 5596 48 := by unfold smallValid; decide +kernel

private theorem sp5644 : smallValid 5644 48 := by unfold smallValid; decide +kernel

private theorem sp5692 : smallValid 5692 48 := by unfold smallValid; decide +kernel

private theorem sp5740 : smallValid 5740 47 := by unfold smallValid; decide +kernel

private theorem sp5787 : smallValid 5787 48 := by unfold smallValid; decide +kernel

private theorem sp5835 : smallValid 5835 48 := by unfold smallValid; decide +kernel

private theorem sp5883 : smallValid 5883 48 := by unfold smallValid; decide +kernel

private theorem sp5931 : smallValid 5931 48 := by unfold smallValid; decide +kernel

private theorem sp5979 : smallValid 5979 48 := by unfold smallValid; decide +kernel

private theorem sp6027 : smallValid 6027 48 := by unfold smallValid; decide +kernel

private theorem sp6075 : smallValid 6075 48 := by unfold smallValid; decide +kernel

private theorem sp6123 : smallValid 6123 47 := by unfold smallValid; decide +kernel

private theorem sp6170 : smallValid 6170 48 := by unfold smallValid; decide +kernel

private theorem sp6218 : smallValid 6218 48 := by unfold smallValid; decide +kernel

private theorem sp6266 : smallValid 6266 48 := by unfold smallValid; decide +kernel

private theorem sp6314 : smallValid 6314 47 := by unfold smallValid; decide +kernel

private theorem sp6361 : smallValid 6361 48 := by unfold smallValid; decide +kernel

private theorem sp6409 : smallValid 6409 48 := by unfold smallValid; decide +kernel

private theorem sp6457 : smallValid 6457 48 := by unfold smallValid; decide +kernel

private theorem sp6505 : smallValid 6505 47 := by unfold smallValid; decide +kernel

private theorem sp6552 : smallValid 6552 48 := by unfold smallValid; decide +kernel

private theorem sp6600 : smallValid 6600 48 := by unfold smallValid; decide +kernel

private theorem sp6648 : smallValid 6648 48 := by unfold smallValid; decide +kernel

private theorem sp6696 : smallValid 6696 48 := by unfold smallValid; decide +kernel

private theorem sp6744 : smallValid 6744 48 := by unfold smallValid; decide +kernel

private theorem sp6792 : smallValid 6792 48 := by unfold smallValid; decide +kernel

private theorem sp6840 : smallValid 6840 48 := by unfold smallValid; decide +kernel

private theorem sp6888 : smallValid 6888 47 := by unfold smallValid; decide +kernel

private theorem sp6935 : smallValid 6935 48 := by unfold smallValid; decide +kernel

private theorem sp6983 : smallValid 6983 48 := by unfold smallValid; decide +kernel

private theorem sp7031 : smallValid 7031 48 := by unfold smallValid; decide +kernel

private theorem sp7079 : smallValid 7079 48 := by unfold smallValid; decide +kernel

private theorem sp7127 : smallValid 7127 48 := by unfold smallValid; decide +kernel

private theorem sp7175 : smallValid 7175 48 := by unfold smallValid; decide +kernel

private theorem sp7223 : smallValid 7223 48 := by unfold smallValid; decide +kernel

private theorem sp7271 : smallValid 7271 47 := by unfold smallValid; decide +kernel

private theorem sp7318 : smallValid 7318 48 := by unfold smallValid; decide +kernel

private theorem sp7366 : smallValid 7366 48 := by unfold smallValid; decide +kernel

private theorem sp7414 : smallValid 7414 48 := by unfold smallValid; decide +kernel

private theorem sp7462 : smallValid 7462 48 := by unfold smallValid; decide +kernel

private theorem sp7510 : smallValid 7510 48 := by unfold smallValid; decide +kernel

private theorem sp7558 : smallValid 7558 48 := by unfold smallValid; decide +kernel

private theorem sp7606 : smallValid 7606 48 := by unfold smallValid; decide +kernel

private theorem sp7654 : smallValid 7654 47 := by unfold smallValid; decide +kernel

private theorem sp7701 : smallValid 7701 48 := by unfold smallValid; decide +kernel

private theorem sp7749 : smallValid 7749 48 := by unfold smallValid; decide +kernel

private theorem sp7797 : smallValid 7797 48 := by unfold smallValid; decide +kernel

private theorem sp7845 : smallValid 7845 47 := by unfold smallValid; decide +kernel

private theorem sp7892 : smallValid 7892 48 := by unfold smallValid; decide +kernel

private theorem sp7940 : smallValid 7940 48 := by unfold smallValid; decide +kernel

private theorem sp7988 : smallValid 7988 48 := by unfold smallValid; decide +kernel

private theorem sp8036 : smallValid 8036 47 := by unfold smallValid; decide +kernel

private theorem sp8083 : smallValid 8083 48 := by unfold smallValid; decide +kernel

private theorem sp8131 : smallValid 8131 48 := by unfold smallValid; decide +kernel

private theorem sp8179 : smallValid 8179 48 := by unfold smallValid; decide +kernel

private theorem sp8227 : smallValid 8227 48 := by unfold smallValid; decide +kernel

private theorem sp8275 : smallValid 8275 48 := by unfold smallValid; decide +kernel

private theorem sp8323 : smallValid 8323 48 := by unfold smallValid; decide +kernel

private theorem sp8371 : smallValid 8371 48 := by unfold smallValid; decide +kernel

private theorem sp8419 : smallValid 8419 47 := by unfold smallValid; decide +kernel

private theorem sp8466 : smallValid 8466 48 := by unfold smallValid; decide +kernel

private theorem sp8514 : smallValid 8514 48 := by unfold smallValid; decide +kernel

private theorem sp8562 : smallValid 8562 48 := by unfold smallValid; decide +kernel

private theorem sp8610 : smallValid 8610 48 := by unfold smallValid; decide +kernel

private theorem sp8658 : smallValid 8658 48 := by unfold smallValid; decide +kernel

private theorem sp8706 : smallValid 8706 48 := by unfold smallValid; decide +kernel

private theorem sp8754 : smallValid 8754 48 := by unfold smallValid; decide +kernel

private theorem sp8802 : smallValid 8802 47 := by unfold smallValid; decide +kernel

private theorem sp8849 : smallValid 8849 48 := by unfold smallValid; decide +kernel

private theorem sp8897 : smallValid 8897 48 := by unfold smallValid; decide +kernel

private theorem sp8945 : smallValid 8945 48 := by unfold smallValid; decide +kernel

private theorem sp8993 : smallValid 8993 48 := by unfold smallValid; decide +kernel

private theorem sp9041 : smallValid 9041 48 := by unfold smallValid; decide +kernel

private theorem sp9089 : smallValid 9089 48 := by unfold smallValid; decide +kernel

private theorem sp9137 : smallValid 9137 48 := by unfold smallValid; decide +kernel

private theorem sp9185 : smallValid 9185 47 := by unfold smallValid; decide +kernel

private theorem sp9232 : smallValid 9232 48 := by unfold smallValid; decide +kernel

private theorem sp9280 : smallValid 9280 48 := by unfold smallValid; decide +kernel

private theorem sp9328 : smallValid 9328 48 := by unfold smallValid; decide +kernel

private theorem sp9376 : smallValid 9376 47 := by unfold smallValid; decide +kernel

private theorem sp9423 : smallValid 9423 48 := by unfold smallValid; decide +kernel

private theorem sp9471 : smallValid 9471 48 := by unfold smallValid; decide +kernel

private theorem sp9519 : smallValid 9519 48 := by unfold smallValid; decide +kernel

private theorem sp9567 : smallValid 9567 47 := by unfold smallValid; decide +kernel

private theorem sp9614 : smallValid 9614 48 := by unfold smallValid; decide +kernel

private theorem sp9662 : smallValid 9662 48 := by unfold smallValid; decide +kernel

private theorem sp9710 : smallValid 9710 48 := by unfold smallValid; decide +kernel

private theorem sp9758 : smallValid 9758 48 := by unfold smallValid; decide +kernel

private theorem sp9806 : smallValid 9806 48 := by unfold smallValid; decide +kernel

private theorem sp9854 : smallValid 9854 48 := by unfold smallValid; decide +kernel

private theorem sp9902 : smallValid 9902 48 := by unfold smallValid; decide +kernel

private theorem sp9950 : smallValid 9950 47 := by unfold smallValid; decide +kernel

private theorem sp9997 : smallValid 9997 48 := by unfold smallValid; decide +kernel

private theorem sp10045 : smallValid 10045 48 := by unfold smallValid; decide +kernel

private theorem sp10093 : smallValid 10093 48 := by unfold smallValid; decide +kernel

private theorem sp10141 : smallValid 10141 48 := by unfold smallValid; decide +kernel

private theorem sp10189 : smallValid 10189 48 := by unfold smallValid; decide +kernel

private theorem sp10237 : smallValid 10237 48 := by unfold smallValid; decide +kernel

private theorem sp10285 : smallValid 10285 48 := by unfold smallValid; decide +kernel

private theorem sp10333 : smallValid 10333 47 := by unfold smallValid; decide +kernel

private theorem sp10380 : smallValid 10380 48 := by unfold smallValid; decide +kernel

private theorem sp10428 : smallValid 10428 48 := by unfold smallValid; decide +kernel

private theorem sp10476 : smallValid 10476 48 := by unfold smallValid; decide +kernel

private theorem sp10524 : smallValid 10524 48 := by unfold smallValid; decide +kernel

private theorem sp10572 : smallValid 10572 48 := by unfold smallValid; decide +kernel

private theorem sp10620 : smallValid 10620 48 := by unfold smallValid; decide +kernel

private theorem sp10668 : smallValid 10668 48 := by unfold smallValid; decide +kernel

private theorem sp10716 : smallValid 10716 47 := by unfold smallValid; decide +kernel

private theorem sp10763 : smallValid 10763 48 := by unfold smallValid; decide +kernel

private theorem sp10811 : smallValid 10811 48 := by unfold smallValid; decide +kernel

private theorem sp10859 : smallValid 10859 48 := by unfold smallValid; decide +kernel

private theorem sp10907 : smallValid 10907 47 := by unfold smallValid; decide +kernel

private theorem sp10954 : smallValid 10954 48 := by unfold smallValid; decide +kernel

private theorem sp11002 : smallValid 11002 48 := by unfold smallValid; decide +kernel

private theorem sp11050 : smallValid 11050 48 := by unfold smallValid; decide +kernel

private theorem sp11098 : smallValid 11098 47 := by unfold smallValid; decide +kernel

private theorem sp11145 : smallValid 11145 48 := by unfold smallValid; decide +kernel

private theorem sp11193 : smallValid 11193 48 := by unfold smallValid; decide +kernel

private theorem sp11241 : smallValid 11241 48 := by unfold smallValid; decide +kernel

private theorem sp11289 : smallValid 11289 48 := by unfold smallValid; decide +kernel

private theorem sp11337 : smallValid 11337 48 := by unfold smallValid; decide +kernel

private theorem sp11385 : smallValid 11385 48 := by unfold smallValid; decide +kernel

private theorem sp11433 : smallValid 11433 48 := by unfold smallValid; decide +kernel

private theorem sp11481 : smallValid 11481 47 := by unfold smallValid; decide +kernel

private theorem sp11528 : smallValid 11528 48 := by unfold smallValid; decide +kernel

private theorem sp11576 : smallValid 11576 48 := by unfold smallValid; decide +kernel

private theorem sp11624 : smallValid 11624 48 := by unfold smallValid; decide +kernel

private theorem sp11672 : smallValid 11672 48 := by unfold smallValid; decide +kernel

private theorem sp11720 : smallValid 11720 48 := by unfold smallValid; decide +kernel

private theorem sp11768 : smallValid 11768 48 := by unfold smallValid; decide +kernel

private theorem sp11816 : smallValid 11816 48 := by unfold smallValid; decide +kernel

private theorem sp11864 : smallValid 11864 47 := by unfold smallValid; decide +kernel

private theorem sp11911 : smallValid 11911 48 := by unfold smallValid; decide +kernel

private theorem sp11959 : smallValid 11959 48 := by unfold smallValid; decide +kernel

private theorem sp12007 : smallValid 12007 48 := by unfold smallValid; decide +kernel

private theorem sp12055 : smallValid 12055 48 := by unfold smallValid; decide +kernel

private theorem sp12103 : smallValid 12103 48 := by unfold smallValid; decide +kernel

private theorem sp12151 : smallValid 12151 48 := by unfold smallValid; decide +kernel

private theorem sp12199 : smallValid 12199 48 := by unfold smallValid; decide +kernel

private theorem sp12247 : smallValid 12247 47 := by unfold smallValid; decide +kernel

private theorem sp12294 : smallValid 12294 48 := by unfold smallValid; decide +kernel

private theorem sp12342 : smallValid 12342 48 := by unfold smallValid; decide +kernel

private theorem sp12390 : smallValid 12390 48 := by unfold smallValid; decide +kernel

private theorem sp12438 : smallValid 12438 47 := by unfold smallValid; decide +kernel

private theorem sp12485 : smallValid 12485 48 := by unfold smallValid; decide +kernel

private theorem sp12533 : smallValid 12533 48 := by unfold smallValid; decide +kernel

private theorem sp12581 : smallValid 12581 48 := by unfold smallValid; decide +kernel

private theorem sp12629 : smallValid 12629 47 := by unfold smallValid; decide +kernel

private theorem sp12676 : smallValid 12676 48 := by unfold smallValid; decide +kernel

private theorem sp12724 : smallValid 12724 48 := by unfold smallValid; decide +kernel

private theorem sp12772 : smallValid 12772 48 := by unfold smallValid; decide +kernel

private theorem sp12820 : smallValid 12820 48 := by unfold smallValid; decide +kernel

private theorem sp12868 : smallValid 12868 48 := by unfold smallValid; decide +kernel

private theorem sp12916 : smallValid 12916 48 := by unfold smallValid; decide +kernel

private theorem sp12964 : smallValid 12964 48 := by unfold smallValid; decide +kernel

private theorem sp13012 : smallValid 13012 47 := by unfold smallValid; decide +kernel

private theorem sp13059 : smallValid 13059 48 := by unfold smallValid; decide +kernel

private theorem sp13107 : smallValid 13107 48 := by unfold smallValid; decide +kernel

private theorem sp13155 : smallValid 13155 48 := by unfold smallValid; decide +kernel

private theorem sp13203 : smallValid 13203 48 := by unfold smallValid; decide +kernel

private theorem sp13251 : smallValid 13251 48 := by unfold smallValid; decide +kernel

private theorem sp13299 : smallValid 13299 48 := by unfold smallValid; decide +kernel

private theorem sp13347 : smallValid 13347 48 := by unfold smallValid; decide +kernel

private theorem sp13395 : smallValid 13395 47 := by unfold smallValid; decide +kernel

private theorem sp13442 : smallValid 13442 48 := by unfold smallValid; decide +kernel

private theorem sp13490 : smallValid 13490 48 := by unfold smallValid; decide +kernel

private theorem sp13538 : smallValid 13538 48 := by unfold smallValid; decide +kernel

private theorem sp13586 : smallValid 13586 48 := by unfold smallValid; decide +kernel

private theorem sp13634 : smallValid 13634 48 := by unfold smallValid; decide +kernel

private theorem sp13682 : smallValid 13682 48 := by unfold smallValid; decide +kernel

private theorem sp13730 : smallValid 13730 48 := by unfold smallValid; decide +kernel

private theorem sp13778 : smallValid 13778 47 := by unfold smallValid; decide +kernel

private theorem sp13825 : smallValid 13825 48 := by unfold smallValid; decide +kernel

private theorem sp13873 : smallValid 13873 48 := by unfold smallValid; decide +kernel

private theorem sp13921 : smallValid 13921 48 := by unfold smallValid; decide +kernel

private theorem sp13969 : smallValid 13969 47 := by unfold smallValid; decide +kernel

private theorem sp14016 : smallValid 14016 48 := by unfold smallValid; decide +kernel

private theorem sp14064 : smallValid 14064 48 := by unfold smallValid; decide +kernel

private theorem sp14112 : smallValid 14112 48 := by unfold smallValid; decide +kernel

private theorem sp14160 : smallValid 14160 47 := by unfold smallValid; decide +kernel

private theorem sp14207 : smallValid 14207 48 := by unfold smallValid; decide +kernel

private theorem sp14255 : smallValid 14255 48 := by unfold smallValid; decide +kernel

private theorem sp14303 : smallValid 14303 48 := by unfold smallValid; decide +kernel

private theorem sp14351 : smallValid 14351 48 := by unfold smallValid; decide +kernel

private theorem sp14399 : smallValid 14399 48 := by unfold smallValid; decide +kernel

private theorem sp14447 : smallValid 14447 48 := by unfold smallValid; decide +kernel

private theorem sp14495 : smallValid 14495 48 := by unfold smallValid; decide +kernel

private theorem sp14543 : smallValid 14543 47 := by unfold smallValid; decide +kernel

private theorem sp14590 : smallValid 14590 48 := by unfold smallValid; decide +kernel

private theorem sp14638 : smallValid 14638 48 := by unfold smallValid; decide +kernel

private theorem sp14686 : smallValid 14686 48 := by unfold smallValid; decide +kernel

private theorem sp14734 : smallValid 14734 48 := by unfold smallValid; decide +kernel

private theorem sp14782 : smallValid 14782 48 := by unfold smallValid; decide +kernel

private theorem sp14830 : smallValid 14830 48 := by unfold smallValid; decide +kernel

private theorem sp14878 : smallValid 14878 48 := by unfold smallValid; decide +kernel

private theorem sp14926 : smallValid 14926 47 := by unfold smallValid; decide +kernel

private theorem sp14973 : smallValid 14973 48 := by unfold smallValid; decide +kernel

private theorem sp15021 : smallValid 15021 48 := by unfold smallValid; decide +kernel

private theorem sp15069 : smallValid 15069 48 := by unfold smallValid; decide +kernel

private theorem sp15117 : smallValid 15117 48 := by unfold smallValid; decide +kernel

private theorem sp15165 : smallValid 15165 48 := by unfold smallValid; decide +kernel

private theorem sp15213 : smallValid 15213 48 := by unfold smallValid; decide +kernel

private theorem sp15261 : smallValid 15261 48 := by unfold smallValid; decide +kernel

private theorem sp15309 : smallValid 15309 47 := by unfold smallValid; decide +kernel

private theorem sp15356 : smallValid 15356 48 := by unfold smallValid; decide +kernel

private theorem sp15404 : smallValid 15404 48 := by unfold smallValid; decide +kernel

private theorem sp15452 : smallValid 15452 48 := by unfold smallValid; decide +kernel

private theorem sp15500 : smallValid 15500 47 := by unfold smallValid; decide +kernel

private theorem sp15547 : smallValid 15547 48 := by unfold smallValid; decide +kernel

private theorem sp15595 : smallValid 15595 48 := by unfold smallValid; decide +kernel

private theorem sp15643 : smallValid 15643 48 := by unfold smallValid; decide +kernel

private theorem sp15691 : smallValid 15691 47 := by unfold smallValid; decide +kernel

private theorem sp15738 : smallValid 15738 48 := by unfold smallValid; decide +kernel

private theorem sp15786 : smallValid 15786 48 := by unfold smallValid; decide +kernel

private theorem sp15834 : smallValid 15834 48 := by unfold smallValid; decide +kernel

private theorem sp15882 : smallValid 15882 48 := by unfold smallValid; decide +kernel

private theorem sp15930 : smallValid 15930 48 := by unfold smallValid; decide +kernel

private theorem sp15978 : smallValid 15978 48 := by unfold smallValid; decide +kernel

private theorem sp16026 : smallValid 16026 48 := by unfold smallValid; decide +kernel

private theorem sp16074 : smallValid 16074 47 := by unfold smallValid; decide +kernel

private theorem sp16121 : smallValid 16121 48 := by unfold smallValid; decide +kernel

private theorem sp16169 : smallValid 16169 48 := by unfold smallValid; decide +kernel

private theorem sp16217 : smallValid 16217 48 := by unfold smallValid; decide +kernel

private theorem sp16265 : smallValid 16265 48 := by unfold smallValid; decide +kernel

private theorem sp16313 : smallValid 16313 48 := by unfold smallValid; decide +kernel

private theorem sp16361 : smallValid 16361 48 := by unfold smallValid; decide +kernel

private theorem sp16409 : smallValid 16409 48 := by unfold smallValid; decide +kernel

private theorem sp16457 : smallValid 16457 47 := by unfold smallValid; decide +kernel

private theorem sp16504 : smallValid 16504 48 := by unfold smallValid; decide +kernel

private theorem sp16552 : smallValid 16552 48 := by unfold smallValid; decide +kernel

private theorem sp16600 : smallValid 16600 48 := by unfold smallValid; decide +kernel

private theorem sp16648 : smallValid 16648 48 := by unfold smallValid; decide +kernel

private theorem sp16696 : smallValid 16696 48 := by unfold smallValid; decide +kernel

private theorem sp16744 : smallValid 16744 48 := by unfold smallValid; decide +kernel

private theorem sp16792 : smallValid 16792 48 := by unfold smallValid; decide +kernel

private theorem sp16840 : smallValid 16840 47 := by unfold smallValid; decide +kernel

private theorem sp16887 : smallValid 16887 48 := by unfold smallValid; decide +kernel

private theorem sp16935 : smallValid 16935 48 := by unfold smallValid; decide +kernel

private theorem sp16983 : smallValid 16983 48 := by unfold smallValid; decide +kernel

private theorem sp17031 : smallValid 17031 47 := by unfold smallValid; decide +kernel

private theorem sp17078 : smallValid 17078 48 := by unfold smallValid; decide +kernel

private theorem sp17126 : smallValid 17126 48 := by unfold smallValid; decide +kernel

private theorem sp17174 : smallValid 17174 48 := by unfold smallValid; decide +kernel

private theorem sp17222 : smallValid 17222 47 := by unfold smallValid; decide +kernel

private theorem sp17269 : smallValid 17269 48 := by unfold smallValid; decide +kernel

private theorem sp17317 : smallValid 17317 48 := by unfold smallValid; decide +kernel

private theorem sp17365 : smallValid 17365 48 := by unfold smallValid; decide +kernel

private theorem sp17413 : smallValid 17413 48 := by unfold smallValid; decide +kernel

private theorem sp17461 : smallValid 17461 48 := by unfold smallValid; decide +kernel

private theorem sp17509 : smallValid 17509 48 := by unfold smallValid; decide +kernel

private theorem sp17557 : smallValid 17557 48 := by unfold smallValid; decide +kernel

private theorem sp17605 : smallValid 17605 47 := by unfold smallValid; decide +kernel

private theorem sp17652 : smallValid 17652 48 := by unfold smallValid; decide +kernel

private theorem sp17700 : smallValid 17700 48 := by unfold smallValid; decide +kernel

private theorem sp17748 : smallValid 17748 48 := by unfold smallValid; decide +kernel

private theorem sp17796 : smallValid 17796 48 := by unfold smallValid; decide +kernel

private theorem sp17844 : smallValid 17844 48 := by unfold smallValid; decide +kernel

private theorem sp17892 : smallValid 17892 48 := by unfold smallValid; decide +kernel

private theorem sp17940 : smallValid 17940 48 := by unfold smallValid; decide +kernel

private theorem sp17988 : smallValid 17988 47 := by unfold smallValid; decide +kernel

private theorem sp18035 : smallValid 18035 48 := by unfold smallValid; decide +kernel

private theorem sp18083 : smallValid 18083 48 := by unfold smallValid; decide +kernel

private theorem sp18131 : smallValid 18131 48 := by unfold smallValid; decide +kernel

private theorem sp18179 : smallValid 18179 48 := by unfold smallValid; decide +kernel

private theorem sp18227 : smallValid 18227 48 := by unfold smallValid; decide +kernel

private theorem sp18275 : smallValid 18275 48 := by unfold smallValid; decide +kernel

private theorem sp18323 : smallValid 18323 48 := by unfold smallValid; decide +kernel

private theorem sp18371 : smallValid 18371 47 := by unfold smallValid; decide +kernel

private theorem sp18418 : smallValid 18418 48 := by unfold smallValid; decide +kernel

private theorem sp18466 : smallValid 18466 48 := by unfold smallValid; decide +kernel

private theorem sp18514 : smallValid 18514 48 := by unfold smallValid; decide +kernel

private theorem sp18562 : smallValid 18562 47 := by unfold smallValid; decide +kernel

private theorem sp18609 : smallValid 18609 48 := by unfold smallValid; decide +kernel

private theorem sp18657 : smallValid 18657 48 := by unfold smallValid; decide +kernel

private theorem sp18705 : smallValid 18705 48 := by unfold smallValid; decide +kernel

private theorem sp18753 : smallValid 18753 47 := by unfold smallValid; decide +kernel

private theorem sp18800 : smallValid 18800 48 := by unfold smallValid; decide +kernel

private theorem sp18848 : smallValid 18848 48 := by unfold smallValid; decide +kernel

private theorem sp18896 : smallValid 18896 48 := by unfold smallValid; decide +kernel

private theorem sp18944 : smallValid 18944 48 := by unfold smallValid; decide +kernel

private theorem sp18992 : smallValid 18992 48 := by unfold smallValid; decide +kernel

private theorem sp19040 : smallValid 19040 48 := by unfold smallValid; decide +kernel

private theorem sp19088 : smallValid 19088 48 := by unfold smallValid; decide +kernel

private theorem sp19136 : smallValid 19136 47 := by unfold smallValid; decide +kernel

private theorem sp19183 : smallValid 19183 48 := by unfold smallValid; decide +kernel

private theorem sp19231 : smallValid 19231 48 := by unfold smallValid; decide +kernel

private theorem sp19279 : smallValid 19279 48 := by unfold smallValid; decide +kernel

private theorem sp19327 : smallValid 19327 48 := by unfold smallValid; decide +kernel

private theorem sp19375 : smallValid 19375 48 := by unfold smallValid; decide +kernel

private theorem sp19423 : smallValid 19423 48 := by unfold smallValid; decide +kernel

private theorem sp19471 : smallValid 19471 48 := by unfold smallValid; decide +kernel

private theorem sp19519 : smallValid 19519 47 := by unfold smallValid; decide +kernel

private theorem sp19566 : smallValid 19566 48 := by unfold smallValid; decide +kernel

private theorem sp19614 : smallValid 19614 48 := by unfold smallValid; decide +kernel

private theorem sp19662 : smallValid 19662 48 := by unfold smallValid; decide +kernel

private theorem sp19710 : smallValid 19710 48 := by unfold smallValid; decide +kernel

private theorem sp19758 : smallValid 19758 48 := by unfold smallValid; decide +kernel

private theorem sp19806 : smallValid 19806 48 := by unfold smallValid; decide +kernel

private theorem sp19854 : smallValid 19854 48 := by unfold smallValid; decide +kernel

private theorem sp19902 : smallValid 19902 47 := by unfold smallValid; decide +kernel

private theorem sp19949 : smallValid 19949 48 := by unfold smallValid; decide +kernel

private theorem sp19997 : smallValid 19997 48 := by unfold smallValid; decide +kernel

private theorem sp20045 : smallValid 20045 48 := by unfold smallValid; decide +kernel

private theorem sp20093 : smallValid 20093 47 := by unfold smallValid; decide +kernel

private theorem sp20140 : smallValid 20140 48 := by unfold smallValid; decide +kernel

private theorem sp20188 : smallValid 20188 48 := by unfold smallValid; decide +kernel

private theorem sp20236 : smallValid 20236 48 := by unfold smallValid; decide +kernel

private theorem sp20284 : smallValid 20284 47 := by unfold smallValid; decide +kernel

private theorem sp20331 : smallValid 20331 48 := by unfold smallValid; decide +kernel

private theorem sp20379 : smallValid 20379 48 := by unfold smallValid; decide +kernel

private theorem sp20427 : smallValid 20427 48 := by unfold smallValid; decide +kernel

private theorem sp20475 : smallValid 20475 48 := by unfold smallValid; decide +kernel

private theorem sp20523 : smallValid 20523 48 := by unfold smallValid; decide +kernel

private theorem sp20571 : smallValid 20571 48 := by unfold smallValid; decide +kernel

private theorem sp20619 : smallValid 20619 48 := by unfold smallValid; decide +kernel

private theorem sp20667 : smallValid 20667 47 := by unfold smallValid; decide +kernel

private theorem sp20714 : smallValid 20714 48 := by unfold smallValid; decide +kernel

private theorem sp20762 : smallValid 20762 48 := by unfold smallValid; decide +kernel

private theorem sp20810 : smallValid 20810 48 := by unfold smallValid; decide +kernel

private theorem sp20858 : smallValid 20858 48 := by unfold smallValid; decide +kernel

private theorem sp20906 : smallValid 20906 48 := by unfold smallValid; decide +kernel

private theorem sp20954 : smallValid 20954 48 := by unfold smallValid; decide +kernel

private theorem sp21002 : smallValid 21002 48 := by unfold smallValid; decide +kernel

private theorem sp21050 : smallValid 21050 47 := by unfold smallValid; decide +kernel

private theorem sp21097 : smallValid 21097 48 := by unfold smallValid; decide +kernel

private theorem sp21145 : smallValid 21145 48 := by unfold smallValid; decide +kernel

private theorem sp21193 : smallValid 21193 48 := by unfold smallValid; decide +kernel

private theorem sp21241 : smallValid 21241 48 := by unfold smallValid; decide +kernel

private theorem sp21289 : smallValid 21289 48 := by unfold smallValid; decide +kernel

private theorem sp21337 : smallValid 21337 48 := by unfold smallValid; decide +kernel

private theorem sp21385 : smallValid 21385 48 := by unfold smallValid; decide +kernel

private theorem sp21433 : smallValid 21433 47 := by unfold smallValid; decide +kernel

private theorem sp21480 : smallValid 21480 48 := by unfold smallValid; decide +kernel

private theorem sp21528 : smallValid 21528 48 := by unfold smallValid; decide +kernel

private theorem sp21576 : smallValid 21576 48 := by unfold smallValid; decide +kernel

private theorem sp21624 : smallValid 21624 47 := by unfold smallValid; decide +kernel

private theorem sp21671 : smallValid 21671 48 := by unfold smallValid; decide +kernel

private theorem sp21719 : smallValid 21719 48 := by unfold smallValid; decide +kernel

private theorem sp21767 : smallValid 21767 48 := by unfold smallValid; decide +kernel

private theorem sp21815 : smallValid 21815 47 := by unfold smallValid; decide +kernel

private theorem sp21862 : smallValid 21862 48 := by unfold smallValid; decide +kernel

private theorem sp21910 : smallValid 21910 48 := by unfold smallValid; decide +kernel

private theorem sp21958 : smallValid 21958 48 := by unfold smallValid; decide +kernel

private theorem sp22006 : smallValid 22006 48 := by unfold smallValid; decide +kernel

private theorem sp22054 : smallValid 22054 48 := by unfold smallValid; decide +kernel

private theorem sp22102 : smallValid 22102 48 := by unfold smallValid; decide +kernel

private theorem sp22150 : smallValid 22150 48 := by unfold smallValid; decide +kernel

private theorem sp22198 : smallValid 22198 47 := by unfold smallValid; decide +kernel

private theorem sp22245 : smallValid 22245 48 := by unfold smallValid; decide +kernel

private theorem sp22293 : smallValid 22293 48 := by unfold smallValid; decide +kernel

private theorem sp22341 : smallValid 22341 48 := by unfold smallValid; decide +kernel

private theorem sp22389 : smallValid 22389 48 := by unfold smallValid; decide +kernel

private theorem sp22437 : smallValid 22437 48 := by unfold smallValid; decide +kernel

private theorem sp22485 : smallValid 22485 48 := by unfold smallValid; decide +kernel

private theorem sp22533 : smallValid 22533 48 := by unfold smallValid; decide +kernel

private theorem sp22581 : smallValid 22581 47 := by unfold smallValid; decide +kernel

private theorem sp22628 : smallValid 22628 48 := by unfold smallValid; decide +kernel

private theorem sp22676 : smallValid 22676 48 := by unfold smallValid; decide +kernel

private theorem sp22724 : smallValid 22724 48 := by unfold smallValid; decide +kernel

private theorem sp22772 : smallValid 22772 48 := by unfold smallValid; decide +kernel

private theorem sp22820 : smallValid 22820 48 := by unfold smallValid; decide +kernel

private theorem sp22868 : smallValid 22868 48 := by unfold smallValid; decide +kernel

private theorem sp22916 : smallValid 22916 48 := by unfold smallValid; decide +kernel

private theorem sp22964 : smallValid 22964 47 := by unfold smallValid; decide +kernel

private theorem sp23011 : smallValid 23011 48 := by unfold smallValid; decide +kernel

private theorem sp23059 : smallValid 23059 48 := by unfold smallValid; decide +kernel

private theorem sp23107 : smallValid 23107 48 := by unfold smallValid; decide +kernel

private theorem sp23155 : smallValid 23155 47 := by unfold smallValid; decide +kernel

private theorem sp23202 : smallValid 23202 48 := by unfold smallValid; decide +kernel

private theorem sp23250 : smallValid 23250 48 := by unfold smallValid; decide +kernel

private theorem sp23298 : smallValid 23298 48 := by unfold smallValid; decide +kernel

private theorem sp23346 : smallValid 23346 47 := by unfold smallValid; decide +kernel

private theorem sp23393 : smallValid 23393 48 := by unfold smallValid; decide +kernel

private theorem sp23441 : smallValid 23441 48 := by unfold smallValid; decide +kernel

private theorem sp23489 : smallValid 23489 48 := by unfold smallValid; decide +kernel

private theorem sp23537 : smallValid 23537 48 := by unfold smallValid; decide +kernel

private theorem sp23585 : smallValid 23585 48 := by unfold smallValid; decide +kernel

private theorem sp23633 : smallValid 23633 48 := by unfold smallValid; decide +kernel

private theorem sp23681 : smallValid 23681 48 := by unfold smallValid; decide +kernel

private theorem sp23729 : smallValid 23729 47 := by unfold smallValid; decide +kernel

private theorem sp23776 : smallValid 23776 48 := by unfold smallValid; decide +kernel

private theorem sp23824 : smallValid 23824 48 := by unfold smallValid; decide +kernel

private theorem sp23872 : smallValid 23872 48 := by unfold smallValid; decide +kernel

private theorem sp23920 : smallValid 23920 48 := by unfold smallValid; decide +kernel

private theorem sp23968 : smallValid 23968 48 := by unfold smallValid; decide +kernel

private theorem sp24016 : smallValid 24016 48 := by unfold smallValid; decide +kernel

private theorem sp24064 : smallValid 24064 48 := by unfold smallValid; decide +kernel

private theorem sp24112 : smallValid 24112 47 := by unfold smallValid; decide +kernel

private theorem sp24159 : smallValid 24159 48 := by unfold smallValid; decide +kernel

private theorem sp24207 : smallValid 24207 48 := by unfold smallValid; decide +kernel

private theorem sp24255 : smallValid 24255 48 := by unfold smallValid; decide +kernel

private theorem sp24303 : smallValid 24303 48 := by unfold smallValid; decide +kernel

private theorem sp24351 : smallValid 24351 48 := by unfold smallValid; decide +kernel

private theorem sp24399 : smallValid 24399 48 := by unfold smallValid; decide +kernel

private theorem sp24447 : smallValid 24447 48 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤24494) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 24495 := (joinSmall (lo:=0) (a:=12247) (b:=12248) (joinSmall (lo:=0) (a:=6123) (b:=6124) (joinSmall (lo:=0) (a:=3061) (b:=3062) (joinSmall (lo:=0) (a:=1530) (b:=1531) (joinSmall (lo:=0) (a:=765) (b:=765) (joinSmall (lo:=0) (a:=382) (b:=383) (joinSmall (lo:=0) (a:=191) (b:=191) (joinSmall (lo:=0) (a:=95) (b:=96) (joinSmall (lo:=0) (a:=47) (b:=48) sp0 sp47) (joinSmall (lo:=95) (a:=48) (b:=48) sp95 sp143)) (joinSmall (lo:=191) (a:=95) (b:=96) (joinSmall (lo:=191) (a:=47) (b:=48) sp191 sp238) (joinSmall (lo:=286) (a:=48) (b:=48) sp286 sp334))) (joinSmall (lo:=382) (a:=191) (b:=192) (joinSmall (lo:=382) (a:=95) (b:=96) (joinSmall (lo:=382) (a:=47) (b:=48) sp382 sp429) (joinSmall (lo:=477) (a:=48) (b:=48) sp477 sp525)) (joinSmall (lo:=573) (a:=96) (b:=96) (joinSmall (lo:=573) (a:=48) (b:=48) sp573 sp621) (joinSmall (lo:=669) (a:=48) (b:=48) sp669 sp717)))) (joinSmall (lo:=765) (a:=382) (b:=383) (joinSmall (lo:=765) (a:=191) (b:=191) (joinSmall (lo:=765) (a:=95) (b:=96) (joinSmall (lo:=765) (a:=47) (b:=48) sp765 sp812) (joinSmall (lo:=860) (a:=48) (b:=48) sp860 sp908)) (joinSmall (lo:=956) (a:=95) (b:=96) (joinSmall (lo:=956) (a:=47) (b:=48) sp956 sp1003) (joinSmall (lo:=1051) (a:=48) (b:=48) sp1051 sp1099))) (joinSmall (lo:=1147) (a:=191) (b:=192) (joinSmall (lo:=1147) (a:=95) (b:=96) (joinSmall (lo:=1147) (a:=47) (b:=48) sp1147 sp1194) (joinSmall (lo:=1242) (a:=48) (b:=48) sp1242 sp1290)) (joinSmall (lo:=1338) (a:=96) (b:=96) (joinSmall (lo:=1338) (a:=48) (b:=48) sp1338 sp1386) (joinSmall (lo:=1434) (a:=48) (b:=48) sp1434 sp1482))))) (joinSmall (lo:=1530) (a:=765) (b:=766) (joinSmall (lo:=1530) (a:=382) (b:=383) (joinSmall (lo:=1530) (a:=191) (b:=191) (joinSmall (lo:=1530) (a:=95) (b:=96) (joinSmall (lo:=1530) (a:=47) (b:=48) sp1530 sp1577) (joinSmall (lo:=1625) (a:=48) (b:=48) sp1625 sp1673)) (joinSmall (lo:=1721) (a:=95) (b:=96) (joinSmall (lo:=1721) (a:=47) (b:=48) sp1721 sp1768) (joinSmall (lo:=1816) (a:=48) (b:=48) sp1816 sp1864))) (joinSmall (lo:=1912) (a:=191) (b:=192) (joinSmall (lo:=1912) (a:=95) (b:=96) (joinSmall (lo:=1912) (a:=47) (b:=48) sp1912 sp1959) (joinSmall (lo:=2007) (a:=48) (b:=48) sp2007 sp2055)) (joinSmall (lo:=2103) (a:=96) (b:=96) (joinSmall (lo:=2103) (a:=48) (b:=48) sp2103 sp2151) (joinSmall (lo:=2199) (a:=48) (b:=48) sp2199 sp2247)))) (joinSmall (lo:=2295) (a:=383) (b:=383) (joinSmall (lo:=2295) (a:=191) (b:=192) (joinSmall (lo:=2295) (a:=95) (b:=96) (joinSmall (lo:=2295) (a:=47) (b:=48) sp2295 sp2342) (joinSmall (lo:=2390) (a:=48) (b:=48) sp2390 sp2438)) (joinSmall (lo:=2486) (a:=96) (b:=96) (joinSmall (lo:=2486) (a:=48) (b:=48) sp2486 sp2534) (joinSmall (lo:=2582) (a:=48) (b:=48) sp2582 sp2630))) (joinSmall (lo:=2678) (a:=191) (b:=192) (joinSmall (lo:=2678) (a:=95) (b:=96) (joinSmall (lo:=2678) (a:=47) (b:=48) sp2678 sp2725) (joinSmall (lo:=2773) (a:=48) (b:=48) sp2773 sp2821)) (joinSmall (lo:=2869) (a:=96) (b:=96) (joinSmall (lo:=2869) (a:=48) (b:=48) sp2869 sp2917) (joinSmall (lo:=2965) (a:=48) (b:=48) sp2965 sp3013)))))) (joinSmall (lo:=3061) (a:=1531) (b:=1531) (joinSmall (lo:=3061) (a:=765) (b:=766) (joinSmall (lo:=3061) (a:=382) (b:=383) (joinSmall (lo:=3061) (a:=191) (b:=191) (joinSmall (lo:=3061) (a:=95) (b:=96) (joinSmall (lo:=3061) (a:=47) (b:=48) sp3061 sp3108) (joinSmall (lo:=3156) (a:=48) (b:=48) sp3156 sp3204)) (joinSmall (lo:=3252) (a:=95) (b:=96) (joinSmall (lo:=3252) (a:=47) (b:=48) sp3252 sp3299) (joinSmall (lo:=3347) (a:=48) (b:=48) sp3347 sp3395))) (joinSmall (lo:=3443) (a:=191) (b:=192) (joinSmall (lo:=3443) (a:=95) (b:=96) (joinSmall (lo:=3443) (a:=47) (b:=48) sp3443 sp3490) (joinSmall (lo:=3538) (a:=48) (b:=48) sp3538 sp3586)) (joinSmall (lo:=3634) (a:=96) (b:=96) (joinSmall (lo:=3634) (a:=48) (b:=48) sp3634 sp3682) (joinSmall (lo:=3730) (a:=48) (b:=48) sp3730 sp3778)))) (joinSmall (lo:=3826) (a:=383) (b:=383) (joinSmall (lo:=3826) (a:=191) (b:=192) (joinSmall (lo:=3826) (a:=95) (b:=96) (joinSmall (lo:=3826) (a:=47) (b:=48) sp3826 sp3873) (joinSmall (lo:=3921) (a:=48) (b:=48) sp3921 sp3969)) (joinSmall (lo:=4017) (a:=96) (b:=96) (joinSmall (lo:=4017) (a:=48) (b:=48) sp4017 sp4065) (joinSmall (lo:=4113) (a:=48) (b:=48) sp4113 sp4161))) (joinSmall (lo:=4209) (a:=191) (b:=192) (joinSmall (lo:=4209) (a:=95) (b:=96) (joinSmall (lo:=4209) (a:=47) (b:=48) sp4209 sp4256) (joinSmall (lo:=4304) (a:=48) (b:=48) sp4304 sp4352)) (joinSmall (lo:=4400) (a:=96) (b:=96) (joinSmall (lo:=4400) (a:=48) (b:=48) sp4400 sp4448) (joinSmall (lo:=4496) (a:=48) (b:=48) sp4496 sp4544))))) (joinSmall (lo:=4592) (a:=765) (b:=766) (joinSmall (lo:=4592) (a:=382) (b:=383) (joinSmall (lo:=4592) (a:=191) (b:=191) (joinSmall (lo:=4592) (a:=95) (b:=96) (joinSmall (lo:=4592) (a:=47) (b:=48) sp4592 sp4639) (joinSmall (lo:=4687) (a:=48) (b:=48) sp4687 sp4735)) (joinSmall (lo:=4783) (a:=95) (b:=96) (joinSmall (lo:=4783) (a:=47) (b:=48) sp4783 sp4830) (joinSmall (lo:=4878) (a:=48) (b:=48) sp4878 sp4926))) (joinSmall (lo:=4974) (a:=191) (b:=192) (joinSmall (lo:=4974) (a:=95) (b:=96) (joinSmall (lo:=4974) (a:=47) (b:=48) sp4974 sp5021) (joinSmall (lo:=5069) (a:=48) (b:=48) sp5069 sp5117)) (joinSmall (lo:=5165) (a:=96) (b:=96) (joinSmall (lo:=5165) (a:=48) (b:=48) sp5165 sp5213) (joinSmall (lo:=5261) (a:=48) (b:=48) sp5261 sp5309)))) (joinSmall (lo:=5357) (a:=383) (b:=383) (joinSmall (lo:=5357) (a:=191) (b:=192) (joinSmall (lo:=5357) (a:=95) (b:=96) (joinSmall (lo:=5357) (a:=47) (b:=48) sp5357 sp5404) (joinSmall (lo:=5452) (a:=48) (b:=48) sp5452 sp5500)) (joinSmall (lo:=5548) (a:=96) (b:=96) (joinSmall (lo:=5548) (a:=48) (b:=48) sp5548 sp5596) (joinSmall (lo:=5644) (a:=48) (b:=48) sp5644 sp5692))) (joinSmall (lo:=5740) (a:=191) (b:=192) (joinSmall (lo:=5740) (a:=95) (b:=96) (joinSmall (lo:=5740) (a:=47) (b:=48) sp5740 sp5787) (joinSmall (lo:=5835) (a:=48) (b:=48) sp5835 sp5883)) (joinSmall (lo:=5931) (a:=96) (b:=96) (joinSmall (lo:=5931) (a:=48) (b:=48) sp5931 sp5979) (joinSmall (lo:=6027) (a:=48) (b:=48) sp6027 sp6075))))))) (joinSmall (lo:=6123) (a:=3062) (b:=3062) (joinSmall (lo:=6123) (a:=1531) (b:=1531) (joinSmall (lo:=6123) (a:=765) (b:=766) (joinSmall (lo:=6123) (a:=382) (b:=383) (joinSmall (lo:=6123) (a:=191) (b:=191) (joinSmall (lo:=6123) (a:=95) (b:=96) (joinSmall (lo:=6123) (a:=47) (b:=48) sp6123 sp6170) (joinSmall (lo:=6218) (a:=48) (b:=48) sp6218 sp6266)) (joinSmall (lo:=6314) (a:=95) (b:=96) (joinSmall (lo:=6314) (a:=47) (b:=48) sp6314 sp6361) (joinSmall (lo:=6409) (a:=48) (b:=48) sp6409 sp6457))) (joinSmall (lo:=6505) (a:=191) (b:=192) (joinSmall (lo:=6505) (a:=95) (b:=96) (joinSmall (lo:=6505) (a:=47) (b:=48) sp6505 sp6552) (joinSmall (lo:=6600) (a:=48) (b:=48) sp6600 sp6648)) (joinSmall (lo:=6696) (a:=96) (b:=96) (joinSmall (lo:=6696) (a:=48) (b:=48) sp6696 sp6744) (joinSmall (lo:=6792) (a:=48) (b:=48) sp6792 sp6840)))) (joinSmall (lo:=6888) (a:=383) (b:=383) (joinSmall (lo:=6888) (a:=191) (b:=192) (joinSmall (lo:=6888) (a:=95) (b:=96) (joinSmall (lo:=6888) (a:=47) (b:=48) sp6888 sp6935) (joinSmall (lo:=6983) (a:=48) (b:=48) sp6983 sp7031)) (joinSmall (lo:=7079) (a:=96) (b:=96) (joinSmall (lo:=7079) (a:=48) (b:=48) sp7079 sp7127) (joinSmall (lo:=7175) (a:=48) (b:=48) sp7175 sp7223))) (joinSmall (lo:=7271) (a:=191) (b:=192) (joinSmall (lo:=7271) (a:=95) (b:=96) (joinSmall (lo:=7271) (a:=47) (b:=48) sp7271 sp7318) (joinSmall (lo:=7366) (a:=48) (b:=48) sp7366 sp7414)) (joinSmall (lo:=7462) (a:=96) (b:=96) (joinSmall (lo:=7462) (a:=48) (b:=48) sp7462 sp7510) (joinSmall (lo:=7558) (a:=48) (b:=48) sp7558 sp7606))))) (joinSmall (lo:=7654) (a:=765) (b:=766) (joinSmall (lo:=7654) (a:=382) (b:=383) (joinSmall (lo:=7654) (a:=191) (b:=191) (joinSmall (lo:=7654) (a:=95) (b:=96) (joinSmall (lo:=7654) (a:=47) (b:=48) sp7654 sp7701) (joinSmall (lo:=7749) (a:=48) (b:=48) sp7749 sp7797)) (joinSmall (lo:=7845) (a:=95) (b:=96) (joinSmall (lo:=7845) (a:=47) (b:=48) sp7845 sp7892) (joinSmall (lo:=7940) (a:=48) (b:=48) sp7940 sp7988))) (joinSmall (lo:=8036) (a:=191) (b:=192) (joinSmall (lo:=8036) (a:=95) (b:=96) (joinSmall (lo:=8036) (a:=47) (b:=48) sp8036 sp8083) (joinSmall (lo:=8131) (a:=48) (b:=48) sp8131 sp8179)) (joinSmall (lo:=8227) (a:=96) (b:=96) (joinSmall (lo:=8227) (a:=48) (b:=48) sp8227 sp8275) (joinSmall (lo:=8323) (a:=48) (b:=48) sp8323 sp8371)))) (joinSmall (lo:=8419) (a:=383) (b:=383) (joinSmall (lo:=8419) (a:=191) (b:=192) (joinSmall (lo:=8419) (a:=95) (b:=96) (joinSmall (lo:=8419) (a:=47) (b:=48) sp8419 sp8466) (joinSmall (lo:=8514) (a:=48) (b:=48) sp8514 sp8562)) (joinSmall (lo:=8610) (a:=96) (b:=96) (joinSmall (lo:=8610) (a:=48) (b:=48) sp8610 sp8658) (joinSmall (lo:=8706) (a:=48) (b:=48) sp8706 sp8754))) (joinSmall (lo:=8802) (a:=191) (b:=192) (joinSmall (lo:=8802) (a:=95) (b:=96) (joinSmall (lo:=8802) (a:=47) (b:=48) sp8802 sp8849) (joinSmall (lo:=8897) (a:=48) (b:=48) sp8897 sp8945)) (joinSmall (lo:=8993) (a:=96) (b:=96) (joinSmall (lo:=8993) (a:=48) (b:=48) sp8993 sp9041) (joinSmall (lo:=9089) (a:=48) (b:=48) sp9089 sp9137)))))) (joinSmall (lo:=9185) (a:=1531) (b:=1531) (joinSmall (lo:=9185) (a:=765) (b:=766) (joinSmall (lo:=9185) (a:=382) (b:=383) (joinSmall (lo:=9185) (a:=191) (b:=191) (joinSmall (lo:=9185) (a:=95) (b:=96) (joinSmall (lo:=9185) (a:=47) (b:=48) sp9185 sp9232) (joinSmall (lo:=9280) (a:=48) (b:=48) sp9280 sp9328)) (joinSmall (lo:=9376) (a:=95) (b:=96) (joinSmall (lo:=9376) (a:=47) (b:=48) sp9376 sp9423) (joinSmall (lo:=9471) (a:=48) (b:=48) sp9471 sp9519))) (joinSmall (lo:=9567) (a:=191) (b:=192) (joinSmall (lo:=9567) (a:=95) (b:=96) (joinSmall (lo:=9567) (a:=47) (b:=48) sp9567 sp9614) (joinSmall (lo:=9662) (a:=48) (b:=48) sp9662 sp9710)) (joinSmall (lo:=9758) (a:=96) (b:=96) (joinSmall (lo:=9758) (a:=48) (b:=48) sp9758 sp9806) (joinSmall (lo:=9854) (a:=48) (b:=48) sp9854 sp9902)))) (joinSmall (lo:=9950) (a:=383) (b:=383) (joinSmall (lo:=9950) (a:=191) (b:=192) (joinSmall (lo:=9950) (a:=95) (b:=96) (joinSmall (lo:=9950) (a:=47) (b:=48) sp9950 sp9997) (joinSmall (lo:=10045) (a:=48) (b:=48) sp10045 sp10093)) (joinSmall (lo:=10141) (a:=96) (b:=96) (joinSmall (lo:=10141) (a:=48) (b:=48) sp10141 sp10189) (joinSmall (lo:=10237) (a:=48) (b:=48) sp10237 sp10285))) (joinSmall (lo:=10333) (a:=191) (b:=192) (joinSmall (lo:=10333) (a:=95) (b:=96) (joinSmall (lo:=10333) (a:=47) (b:=48) sp10333 sp10380) (joinSmall (lo:=10428) (a:=48) (b:=48) sp10428 sp10476)) (joinSmall (lo:=10524) (a:=96) (b:=96) (joinSmall (lo:=10524) (a:=48) (b:=48) sp10524 sp10572) (joinSmall (lo:=10620) (a:=48) (b:=48) sp10620 sp10668))))) (joinSmall (lo:=10716) (a:=765) (b:=766) (joinSmall (lo:=10716) (a:=382) (b:=383) (joinSmall (lo:=10716) (a:=191) (b:=191) (joinSmall (lo:=10716) (a:=95) (b:=96) (joinSmall (lo:=10716) (a:=47) (b:=48) sp10716 sp10763) (joinSmall (lo:=10811) (a:=48) (b:=48) sp10811 sp10859)) (joinSmall (lo:=10907) (a:=95) (b:=96) (joinSmall (lo:=10907) (a:=47) (b:=48) sp10907 sp10954) (joinSmall (lo:=11002) (a:=48) (b:=48) sp11002 sp11050))) (joinSmall (lo:=11098) (a:=191) (b:=192) (joinSmall (lo:=11098) (a:=95) (b:=96) (joinSmall (lo:=11098) (a:=47) (b:=48) sp11098 sp11145) (joinSmall (lo:=11193) (a:=48) (b:=48) sp11193 sp11241)) (joinSmall (lo:=11289) (a:=96) (b:=96) (joinSmall (lo:=11289) (a:=48) (b:=48) sp11289 sp11337) (joinSmall (lo:=11385) (a:=48) (b:=48) sp11385 sp11433)))) (joinSmall (lo:=11481) (a:=383) (b:=383) (joinSmall (lo:=11481) (a:=191) (b:=192) (joinSmall (lo:=11481) (a:=95) (b:=96) (joinSmall (lo:=11481) (a:=47) (b:=48) sp11481 sp11528) (joinSmall (lo:=11576) (a:=48) (b:=48) sp11576 sp11624)) (joinSmall (lo:=11672) (a:=96) (b:=96) (joinSmall (lo:=11672) (a:=48) (b:=48) sp11672 sp11720) (joinSmall (lo:=11768) (a:=48) (b:=48) sp11768 sp11816))) (joinSmall (lo:=11864) (a:=191) (b:=192) (joinSmall (lo:=11864) (a:=95) (b:=96) (joinSmall (lo:=11864) (a:=47) (b:=48) sp11864 sp11911) (joinSmall (lo:=11959) (a:=48) (b:=48) sp11959 sp12007)) (joinSmall (lo:=12055) (a:=96) (b:=96) (joinSmall (lo:=12055) (a:=48) (b:=48) sp12055 sp12103) (joinSmall (lo:=12151) (a:=48) (b:=48) sp12151 sp12199)))))))) (joinSmall (lo:=12247) (a:=6124) (b:=6124) (joinSmall (lo:=12247) (a:=3062) (b:=3062) (joinSmall (lo:=12247) (a:=1531) (b:=1531) (joinSmall (lo:=12247) (a:=765) (b:=766) (joinSmall (lo:=12247) (a:=382) (b:=383) (joinSmall (lo:=12247) (a:=191) (b:=191) (joinSmall (lo:=12247) (a:=95) (b:=96) (joinSmall (lo:=12247) (a:=47) (b:=48) sp12247 sp12294) (joinSmall (lo:=12342) (a:=48) (b:=48) sp12342 sp12390)) (joinSmall (lo:=12438) (a:=95) (b:=96) (joinSmall (lo:=12438) (a:=47) (b:=48) sp12438 sp12485) (joinSmall (lo:=12533) (a:=48) (b:=48) sp12533 sp12581))) (joinSmall (lo:=12629) (a:=191) (b:=192) (joinSmall (lo:=12629) (a:=95) (b:=96) (joinSmall (lo:=12629) (a:=47) (b:=48) sp12629 sp12676) (joinSmall (lo:=12724) (a:=48) (b:=48) sp12724 sp12772)) (joinSmall (lo:=12820) (a:=96) (b:=96) (joinSmall (lo:=12820) (a:=48) (b:=48) sp12820 sp12868) (joinSmall (lo:=12916) (a:=48) (b:=48) sp12916 sp12964)))) (joinSmall (lo:=13012) (a:=383) (b:=383) (joinSmall (lo:=13012) (a:=191) (b:=192) (joinSmall (lo:=13012) (a:=95) (b:=96) (joinSmall (lo:=13012) (a:=47) (b:=48) sp13012 sp13059) (joinSmall (lo:=13107) (a:=48) (b:=48) sp13107 sp13155)) (joinSmall (lo:=13203) (a:=96) (b:=96) (joinSmall (lo:=13203) (a:=48) (b:=48) sp13203 sp13251) (joinSmall (lo:=13299) (a:=48) (b:=48) sp13299 sp13347))) (joinSmall (lo:=13395) (a:=191) (b:=192) (joinSmall (lo:=13395) (a:=95) (b:=96) (joinSmall (lo:=13395) (a:=47) (b:=48) sp13395 sp13442) (joinSmall (lo:=13490) (a:=48) (b:=48) sp13490 sp13538)) (joinSmall (lo:=13586) (a:=96) (b:=96) (joinSmall (lo:=13586) (a:=48) (b:=48) sp13586 sp13634) (joinSmall (lo:=13682) (a:=48) (b:=48) sp13682 sp13730))))) (joinSmall (lo:=13778) (a:=765) (b:=766) (joinSmall (lo:=13778) (a:=382) (b:=383) (joinSmall (lo:=13778) (a:=191) (b:=191) (joinSmall (lo:=13778) (a:=95) (b:=96) (joinSmall (lo:=13778) (a:=47) (b:=48) sp13778 sp13825) (joinSmall (lo:=13873) (a:=48) (b:=48) sp13873 sp13921)) (joinSmall (lo:=13969) (a:=95) (b:=96) (joinSmall (lo:=13969) (a:=47) (b:=48) sp13969 sp14016) (joinSmall (lo:=14064) (a:=48) (b:=48) sp14064 sp14112))) (joinSmall (lo:=14160) (a:=191) (b:=192) (joinSmall (lo:=14160) (a:=95) (b:=96) (joinSmall (lo:=14160) (a:=47) (b:=48) sp14160 sp14207) (joinSmall (lo:=14255) (a:=48) (b:=48) sp14255 sp14303)) (joinSmall (lo:=14351) (a:=96) (b:=96) (joinSmall (lo:=14351) (a:=48) (b:=48) sp14351 sp14399) (joinSmall (lo:=14447) (a:=48) (b:=48) sp14447 sp14495)))) (joinSmall (lo:=14543) (a:=383) (b:=383) (joinSmall (lo:=14543) (a:=191) (b:=192) (joinSmall (lo:=14543) (a:=95) (b:=96) (joinSmall (lo:=14543) (a:=47) (b:=48) sp14543 sp14590) (joinSmall (lo:=14638) (a:=48) (b:=48) sp14638 sp14686)) (joinSmall (lo:=14734) (a:=96) (b:=96) (joinSmall (lo:=14734) (a:=48) (b:=48) sp14734 sp14782) (joinSmall (lo:=14830) (a:=48) (b:=48) sp14830 sp14878))) (joinSmall (lo:=14926) (a:=191) (b:=192) (joinSmall (lo:=14926) (a:=95) (b:=96) (joinSmall (lo:=14926) (a:=47) (b:=48) sp14926 sp14973) (joinSmall (lo:=15021) (a:=48) (b:=48) sp15021 sp15069)) (joinSmall (lo:=15117) (a:=96) (b:=96) (joinSmall (lo:=15117) (a:=48) (b:=48) sp15117 sp15165) (joinSmall (lo:=15213) (a:=48) (b:=48) sp15213 sp15261)))))) (joinSmall (lo:=15309) (a:=1531) (b:=1531) (joinSmall (lo:=15309) (a:=765) (b:=766) (joinSmall (lo:=15309) (a:=382) (b:=383) (joinSmall (lo:=15309) (a:=191) (b:=191) (joinSmall (lo:=15309) (a:=95) (b:=96) (joinSmall (lo:=15309) (a:=47) (b:=48) sp15309 sp15356) (joinSmall (lo:=15404) (a:=48) (b:=48) sp15404 sp15452)) (joinSmall (lo:=15500) (a:=95) (b:=96) (joinSmall (lo:=15500) (a:=47) (b:=48) sp15500 sp15547) (joinSmall (lo:=15595) (a:=48) (b:=48) sp15595 sp15643))) (joinSmall (lo:=15691) (a:=191) (b:=192) (joinSmall (lo:=15691) (a:=95) (b:=96) (joinSmall (lo:=15691) (a:=47) (b:=48) sp15691 sp15738) (joinSmall (lo:=15786) (a:=48) (b:=48) sp15786 sp15834)) (joinSmall (lo:=15882) (a:=96) (b:=96) (joinSmall (lo:=15882) (a:=48) (b:=48) sp15882 sp15930) (joinSmall (lo:=15978) (a:=48) (b:=48) sp15978 sp16026)))) (joinSmall (lo:=16074) (a:=383) (b:=383) (joinSmall (lo:=16074) (a:=191) (b:=192) (joinSmall (lo:=16074) (a:=95) (b:=96) (joinSmall (lo:=16074) (a:=47) (b:=48) sp16074 sp16121) (joinSmall (lo:=16169) (a:=48) (b:=48) sp16169 sp16217)) (joinSmall (lo:=16265) (a:=96) (b:=96) (joinSmall (lo:=16265) (a:=48) (b:=48) sp16265 sp16313) (joinSmall (lo:=16361) (a:=48) (b:=48) sp16361 sp16409))) (joinSmall (lo:=16457) (a:=191) (b:=192) (joinSmall (lo:=16457) (a:=95) (b:=96) (joinSmall (lo:=16457) (a:=47) (b:=48) sp16457 sp16504) (joinSmall (lo:=16552) (a:=48) (b:=48) sp16552 sp16600)) (joinSmall (lo:=16648) (a:=96) (b:=96) (joinSmall (lo:=16648) (a:=48) (b:=48) sp16648 sp16696) (joinSmall (lo:=16744) (a:=48) (b:=48) sp16744 sp16792))))) (joinSmall (lo:=16840) (a:=765) (b:=766) (joinSmall (lo:=16840) (a:=382) (b:=383) (joinSmall (lo:=16840) (a:=191) (b:=191) (joinSmall (lo:=16840) (a:=95) (b:=96) (joinSmall (lo:=16840) (a:=47) (b:=48) sp16840 sp16887) (joinSmall (lo:=16935) (a:=48) (b:=48) sp16935 sp16983)) (joinSmall (lo:=17031) (a:=95) (b:=96) (joinSmall (lo:=17031) (a:=47) (b:=48) sp17031 sp17078) (joinSmall (lo:=17126) (a:=48) (b:=48) sp17126 sp17174))) (joinSmall (lo:=17222) (a:=191) (b:=192) (joinSmall (lo:=17222) (a:=95) (b:=96) (joinSmall (lo:=17222) (a:=47) (b:=48) sp17222 sp17269) (joinSmall (lo:=17317) (a:=48) (b:=48) sp17317 sp17365)) (joinSmall (lo:=17413) (a:=96) (b:=96) (joinSmall (lo:=17413) (a:=48) (b:=48) sp17413 sp17461) (joinSmall (lo:=17509) (a:=48) (b:=48) sp17509 sp17557)))) (joinSmall (lo:=17605) (a:=383) (b:=383) (joinSmall (lo:=17605) (a:=191) (b:=192) (joinSmall (lo:=17605) (a:=95) (b:=96) (joinSmall (lo:=17605) (a:=47) (b:=48) sp17605 sp17652) (joinSmall (lo:=17700) (a:=48) (b:=48) sp17700 sp17748)) (joinSmall (lo:=17796) (a:=96) (b:=96) (joinSmall (lo:=17796) (a:=48) (b:=48) sp17796 sp17844) (joinSmall (lo:=17892) (a:=48) (b:=48) sp17892 sp17940))) (joinSmall (lo:=17988) (a:=191) (b:=192) (joinSmall (lo:=17988) (a:=95) (b:=96) (joinSmall (lo:=17988) (a:=47) (b:=48) sp17988 sp18035) (joinSmall (lo:=18083) (a:=48) (b:=48) sp18083 sp18131)) (joinSmall (lo:=18179) (a:=96) (b:=96) (joinSmall (lo:=18179) (a:=48) (b:=48) sp18179 sp18227) (joinSmall (lo:=18275) (a:=48) (b:=48) sp18275 sp18323))))))) (joinSmall (lo:=18371) (a:=3062) (b:=3062) (joinSmall (lo:=18371) (a:=1531) (b:=1531) (joinSmall (lo:=18371) (a:=765) (b:=766) (joinSmall (lo:=18371) (a:=382) (b:=383) (joinSmall (lo:=18371) (a:=191) (b:=191) (joinSmall (lo:=18371) (a:=95) (b:=96) (joinSmall (lo:=18371) (a:=47) (b:=48) sp18371 sp18418) (joinSmall (lo:=18466) (a:=48) (b:=48) sp18466 sp18514)) (joinSmall (lo:=18562) (a:=95) (b:=96) (joinSmall (lo:=18562) (a:=47) (b:=48) sp18562 sp18609) (joinSmall (lo:=18657) (a:=48) (b:=48) sp18657 sp18705))) (joinSmall (lo:=18753) (a:=191) (b:=192) (joinSmall (lo:=18753) (a:=95) (b:=96) (joinSmall (lo:=18753) (a:=47) (b:=48) sp18753 sp18800) (joinSmall (lo:=18848) (a:=48) (b:=48) sp18848 sp18896)) (joinSmall (lo:=18944) (a:=96) (b:=96) (joinSmall (lo:=18944) (a:=48) (b:=48) sp18944 sp18992) (joinSmall (lo:=19040) (a:=48) (b:=48) sp19040 sp19088)))) (joinSmall (lo:=19136) (a:=383) (b:=383) (joinSmall (lo:=19136) (a:=191) (b:=192) (joinSmall (lo:=19136) (a:=95) (b:=96) (joinSmall (lo:=19136) (a:=47) (b:=48) sp19136 sp19183) (joinSmall (lo:=19231) (a:=48) (b:=48) sp19231 sp19279)) (joinSmall (lo:=19327) (a:=96) (b:=96) (joinSmall (lo:=19327) (a:=48) (b:=48) sp19327 sp19375) (joinSmall (lo:=19423) (a:=48) (b:=48) sp19423 sp19471))) (joinSmall (lo:=19519) (a:=191) (b:=192) (joinSmall (lo:=19519) (a:=95) (b:=96) (joinSmall (lo:=19519) (a:=47) (b:=48) sp19519 sp19566) (joinSmall (lo:=19614) (a:=48) (b:=48) sp19614 sp19662)) (joinSmall (lo:=19710) (a:=96) (b:=96) (joinSmall (lo:=19710) (a:=48) (b:=48) sp19710 sp19758) (joinSmall (lo:=19806) (a:=48) (b:=48) sp19806 sp19854))))) (joinSmall (lo:=19902) (a:=765) (b:=766) (joinSmall (lo:=19902) (a:=382) (b:=383) (joinSmall (lo:=19902) (a:=191) (b:=191) (joinSmall (lo:=19902) (a:=95) (b:=96) (joinSmall (lo:=19902) (a:=47) (b:=48) sp19902 sp19949) (joinSmall (lo:=19997) (a:=48) (b:=48) sp19997 sp20045)) (joinSmall (lo:=20093) (a:=95) (b:=96) (joinSmall (lo:=20093) (a:=47) (b:=48) sp20093 sp20140) (joinSmall (lo:=20188) (a:=48) (b:=48) sp20188 sp20236))) (joinSmall (lo:=20284) (a:=191) (b:=192) (joinSmall (lo:=20284) (a:=95) (b:=96) (joinSmall (lo:=20284) (a:=47) (b:=48) sp20284 sp20331) (joinSmall (lo:=20379) (a:=48) (b:=48) sp20379 sp20427)) (joinSmall (lo:=20475) (a:=96) (b:=96) (joinSmall (lo:=20475) (a:=48) (b:=48) sp20475 sp20523) (joinSmall (lo:=20571) (a:=48) (b:=48) sp20571 sp20619)))) (joinSmall (lo:=20667) (a:=383) (b:=383) (joinSmall (lo:=20667) (a:=191) (b:=192) (joinSmall (lo:=20667) (a:=95) (b:=96) (joinSmall (lo:=20667) (a:=47) (b:=48) sp20667 sp20714) (joinSmall (lo:=20762) (a:=48) (b:=48) sp20762 sp20810)) (joinSmall (lo:=20858) (a:=96) (b:=96) (joinSmall (lo:=20858) (a:=48) (b:=48) sp20858 sp20906) (joinSmall (lo:=20954) (a:=48) (b:=48) sp20954 sp21002))) (joinSmall (lo:=21050) (a:=191) (b:=192) (joinSmall (lo:=21050) (a:=95) (b:=96) (joinSmall (lo:=21050) (a:=47) (b:=48) sp21050 sp21097) (joinSmall (lo:=21145) (a:=48) (b:=48) sp21145 sp21193)) (joinSmall (lo:=21241) (a:=96) (b:=96) (joinSmall (lo:=21241) (a:=48) (b:=48) sp21241 sp21289) (joinSmall (lo:=21337) (a:=48) (b:=48) sp21337 sp21385)))))) (joinSmall (lo:=21433) (a:=1531) (b:=1531) (joinSmall (lo:=21433) (a:=765) (b:=766) (joinSmall (lo:=21433) (a:=382) (b:=383) (joinSmall (lo:=21433) (a:=191) (b:=191) (joinSmall (lo:=21433) (a:=95) (b:=96) (joinSmall (lo:=21433) (a:=47) (b:=48) sp21433 sp21480) (joinSmall (lo:=21528) (a:=48) (b:=48) sp21528 sp21576)) (joinSmall (lo:=21624) (a:=95) (b:=96) (joinSmall (lo:=21624) (a:=47) (b:=48) sp21624 sp21671) (joinSmall (lo:=21719) (a:=48) (b:=48) sp21719 sp21767))) (joinSmall (lo:=21815) (a:=191) (b:=192) (joinSmall (lo:=21815) (a:=95) (b:=96) (joinSmall (lo:=21815) (a:=47) (b:=48) sp21815 sp21862) (joinSmall (lo:=21910) (a:=48) (b:=48) sp21910 sp21958)) (joinSmall (lo:=22006) (a:=96) (b:=96) (joinSmall (lo:=22006) (a:=48) (b:=48) sp22006 sp22054) (joinSmall (lo:=22102) (a:=48) (b:=48) sp22102 sp22150)))) (joinSmall (lo:=22198) (a:=383) (b:=383) (joinSmall (lo:=22198) (a:=191) (b:=192) (joinSmall (lo:=22198) (a:=95) (b:=96) (joinSmall (lo:=22198) (a:=47) (b:=48) sp22198 sp22245) (joinSmall (lo:=22293) (a:=48) (b:=48) sp22293 sp22341)) (joinSmall (lo:=22389) (a:=96) (b:=96) (joinSmall (lo:=22389) (a:=48) (b:=48) sp22389 sp22437) (joinSmall (lo:=22485) (a:=48) (b:=48) sp22485 sp22533))) (joinSmall (lo:=22581) (a:=191) (b:=192) (joinSmall (lo:=22581) (a:=95) (b:=96) (joinSmall (lo:=22581) (a:=47) (b:=48) sp22581 sp22628) (joinSmall (lo:=22676) (a:=48) (b:=48) sp22676 sp22724)) (joinSmall (lo:=22772) (a:=96) (b:=96) (joinSmall (lo:=22772) (a:=48) (b:=48) sp22772 sp22820) (joinSmall (lo:=22868) (a:=48) (b:=48) sp22868 sp22916))))) (joinSmall (lo:=22964) (a:=765) (b:=766) (joinSmall (lo:=22964) (a:=382) (b:=383) (joinSmall (lo:=22964) (a:=191) (b:=191) (joinSmall (lo:=22964) (a:=95) (b:=96) (joinSmall (lo:=22964) (a:=47) (b:=48) sp22964 sp23011) (joinSmall (lo:=23059) (a:=48) (b:=48) sp23059 sp23107)) (joinSmall (lo:=23155) (a:=95) (b:=96) (joinSmall (lo:=23155) (a:=47) (b:=48) sp23155 sp23202) (joinSmall (lo:=23250) (a:=48) (b:=48) sp23250 sp23298))) (joinSmall (lo:=23346) (a:=191) (b:=192) (joinSmall (lo:=23346) (a:=95) (b:=96) (joinSmall (lo:=23346) (a:=47) (b:=48) sp23346 sp23393) (joinSmall (lo:=23441) (a:=48) (b:=48) sp23441 sp23489)) (joinSmall (lo:=23537) (a:=96) (b:=96) (joinSmall (lo:=23537) (a:=48) (b:=48) sp23537 sp23585) (joinSmall (lo:=23633) (a:=48) (b:=48) sp23633 sp23681)))) (joinSmall (lo:=23729) (a:=383) (b:=383) (joinSmall (lo:=23729) (a:=191) (b:=192) (joinSmall (lo:=23729) (a:=95) (b:=96) (joinSmall (lo:=23729) (a:=47) (b:=48) sp23729 sp23776) (joinSmall (lo:=23824) (a:=48) (b:=48) sp23824 sp23872)) (joinSmall (lo:=23920) (a:=96) (b:=96) (joinSmall (lo:=23920) (a:=48) (b:=48) sp23920 sp23968) (joinSmall (lo:=24016) (a:=48) (b:=48) sp24016 sp24064))) (joinSmall (lo:=24112) (a:=191) (b:=192) (joinSmall (lo:=24112) (a:=95) (b:=96) (joinSmall (lo:=24112) (a:=47) (b:=48) sp24112 sp24159) (joinSmall (lo:=24207) (a:=48) (b:=48) sp24207 sp24255)) (joinSmall (lo:=24303) (a:=96) (b:=96) (joinSmall (lo:=24303) (a:=48) (b:=48) sp24303 sp24351) (joinSmall (lo:=24399) (a:=48) (b:=48) sp24399 sp24447)))))))))
  have good : (List.range 24495).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 600000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 24494 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 24494 := by
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


private def packet (i : ℕ) : ℕ := (if i < 153 then (if i < 76 then (if i < 38 then (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else (if i < 8 then 0 else 0)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else (if i < 13 then 0 else 0))) else (if i < 16 then (if i < 15 then 0 else 0) else (if i < 17 then 0 else (if i < 18 then 0 else 0))))) else (if i < 28 then (if i < 23 then (if i < 21 then (if i < 20 then 0 else 0) else (if i < 22 then 0 else 0)) else (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else (if i < 27 then 0 else 0)))) else (if i < 33 then (if i < 30 then (if i < 29 then 0 else 0) else (if i < 31 then 0 else (if i < 32 then 0 else 0))) else (if i < 35 then (if i < 34 then 0 else 0) else (if i < 36 then 0 else (if i < 37 then 0 else 0)))))) else (if i < 57 then (if i < 47 then (if i < 42 then (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0)) else (if i < 44 then (if i < 43 then 0 else 0) else (if i < 45 then 0 else (if i < 46 then 0 else 0)))) else (if i < 52 then (if i < 49 then (if i < 48 then 0 else 0) else (if i < 50 then 0 else (if i < 51 then 0 else 0))) else (if i < 54 then (if i < 53 then 0 else 0) else (if i < 55 then 0 else (if i < 56 then 0 else 0))))) else (if i < 66 then (if i < 61 then (if i < 59 then (if i < 58 then 0 else 0) else (if i < 60 then 0 else 0)) else (if i < 63 then (if i < 62 then 0 else 0) else (if i < 64 then 0 else (if i < 65 then 0 else 0)))) else (if i < 71 then (if i < 68 then (if i < 67 then 0 else 0) else (if i < 69 then 0 else (if i < 70 then 0 else 0))) else (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else (if i < 75 then 0 else 0))))))) else (if i < 114 then (if i < 95 then (if i < 85 then (if i < 80 then (if i < 78 then (if i < 77 then 0 else 0) else (if i < 79 then 0 else 0)) else (if i < 82 then (if i < 81 then 0 else 0) else (if i < 83 then 0 else (if i < 84 then 0 else 0)))) else (if i < 90 then (if i < 87 then (if i < 86 then 0 else 0) else (if i < 88 then 0 else (if i < 89 then 0 else 0))) else (if i < 92 then (if i < 91 then 0 else 0) else (if i < 93 then 0 else (if i < 94 then 0 else 0))))) else (if i < 104 then (if i < 99 then (if i < 97 then (if i < 96 then 0 else 0) else (if i < 98 then 0 else 0)) else (if i < 101 then (if i < 100 then 0 else 0) else (if i < 102 then 0 else (if i < 103 then 0 else 0)))) else (if i < 109 then (if i < 106 then (if i < 105 then 0 else 0) else (if i < 107 then 0 else (if i < 108 then 0 else 0))) else (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else (if i < 113 then 0 else 0)))))) else (if i < 133 then (if i < 123 then (if i < 118 then (if i < 116 then (if i < 115 then 0 else 0) else (if i < 117 then 0 else 0)) else (if i < 120 then (if i < 119 then 0 else 0) else (if i < 121 then 0 else (if i < 122 then 0 else 0)))) else (if i < 128 then (if i < 125 then (if i < 124 then 0 else 0) else (if i < 126 then 0 else (if i < 127 then 0 else 0))) else (if i < 130 then (if i < 129 then 0 else 0) else (if i < 131 then 0 else (if i < 132 then 0 else 0))))) else (if i < 143 then (if i < 138 then (if i < 135 then (if i < 134 then 0 else 0) else (if i < 136 then 0 else (if i < 137 then 0 else 0))) else (if i < 140 then (if i < 139 then 0 else 0) else (if i < 141 then 0 else (if i < 142 then 0 else 0)))) else (if i < 148 then (if i < 145 then (if i < 144 then 0 else 0) else (if i < 146 then 0 else (if i < 147 then 0 else 0))) else (if i < 150 then (if i < 149 then 0 else 0) else (if i < 151 then 0 else (if i < 152 then 0 else 0)))))))) else (if i < 229 then (if i < 191 then (if i < 172 then (if i < 162 then (if i < 157 then (if i < 155 then (if i < 154 then 0 else 0) else (if i < 156 then 0 else 0)) else (if i < 159 then (if i < 158 then 0 else 0) else (if i < 160 then 0 else (if i < 161 then 0 else 0)))) else (if i < 167 then (if i < 164 then (if i < 163 then 0 else 0) else (if i < 165 then 0 else (if i < 166 then 0 else 0))) else (if i < 169 then (if i < 168 then 0 else 0) else (if i < 170 then 0 else (if i < 171 then 0 else 0))))) else (if i < 181 then (if i < 176 then (if i < 174 then (if i < 173 then 0 else 0) else (if i < 175 then 0 else 0)) else (if i < 178 then (if i < 177 then 0 else 0) else (if i < 179 then 0 else (if i < 180 then 0 else 0)))) else (if i < 186 then (if i < 183 then (if i < 182 then 0 else 0) else (if i < 184 then 0 else (if i < 185 then 0 else 0))) else (if i < 188 then (if i < 187 then 0 else 0) else (if i < 189 then 0 else (if i < 190 then 0 else 0)))))) else (if i < 210 then (if i < 200 then (if i < 195 then (if i < 193 then (if i < 192 then 0 else 0) else (if i < 194 then 0 else 0)) else (if i < 197 then (if i < 196 then 0 else 0) else (if i < 198 then 0 else (if i < 199 then 0 else 0)))) else (if i < 205 then (if i < 202 then (if i < 201 then 0 else 0) else (if i < 203 then 0 else (if i < 204 then 0 else 0))) else (if i < 207 then (if i < 206 then 0 else 0) else (if i < 208 then 0 else (if i < 209 then 0 else 0))))) else (if i < 219 then (if i < 214 then (if i < 212 then (if i < 211 then 0 else 0) else (if i < 213 then 0 else 0)) else (if i < 216 then (if i < 215 then 0 else 0) else (if i < 217 then 0 else (if i < 218 then 0 else 0)))) else (if i < 224 then (if i < 221 then (if i < 220 then 0 else 0) else (if i < 222 then 0 else (if i < 223 then 0 else 0))) else (if i < 226 then (if i < 225 then 0 else 0) else (if i < 227 then 0 else (if i < 228 then 0 else 0))))))) else (if i < 267 then (if i < 248 then (if i < 238 then (if i < 233 then (if i < 231 then (if i < 230 then 0 else 0) else (if i < 232 then 0 else 0)) else (if i < 235 then (if i < 234 then 0 else 0) else (if i < 236 then 0 else (if i < 237 then 0 else 0)))) else (if i < 243 then (if i < 240 then (if i < 239 then 0 else 0) else (if i < 241 then 0 else (if i < 242 then 0 else 0))) else (if i < 245 then (if i < 244 then 0 else 0) else (if i < 246 then 0 else (if i < 247 then 0 else 0))))) else (if i < 257 then (if i < 252 then (if i < 250 then (if i < 249 then 0 else 0) else (if i < 251 then 0 else 0)) else (if i < 254 then (if i < 253 then 0 else 0) else (if i < 255 then 0 else (if i < 256 then 0 else 0)))) else (if i < 262 then (if i < 259 then (if i < 258 then 0 else 0) else (if i < 260 then 0 else (if i < 261 then 0 else 0))) else (if i < 264 then (if i < 263 then 0 else 0) else (if i < 265 then 0 else (if i < 266 then 0 else 0)))))) else (if i < 286 then (if i < 276 then (if i < 271 then (if i < 269 then (if i < 268 then 0 else 0) else (if i < 270 then 0 else 0)) else (if i < 273 then (if i < 272 then 0 else 0) else (if i < 274 then 0 else (if i < 275 then 0 else 0)))) else (if i < 281 then (if i < 278 then (if i < 277 then 0 else 0) else (if i < 279 then 0 else (if i < 280 then 0 else 0))) else (if i < 283 then (if i < 282 then 0 else 0) else (if i < 284 then 0 else (if i < 285 then 0 else 0))))) else (if i < 296 then (if i < 291 then (if i < 288 then (if i < 287 then 0 else 0) else (if i < 289 then 0 else (if i < 290 then 0 else 0))) else (if i < 293 then (if i < 292 then 0 else 0x1cbdbee2c594c49944612040ea069e2f715188dc3a017908c82dc0c200001cbd5fc2c894b499e47420b0ed06b22f214a08f83be17e09003140c400001cbd0022ce14f09bc4782118f206dc30e15208d03a417e09182f00c200001cbca1d2c314a09964742108f0c6c82fb14f08e83b618108e82e00ba00001cbc42d2c794a89ac4792098eb868e2f214888fc3a617308b02dc0ae00001cbbe322cc14f49b24812128f146c630815409183d419009802dc0be00001cbb8442c894b49924641fd8e7067e2ee14508c83a016f08c02ec0ac00001cbb2702bc148c9904632000e8867a2de13e88a039a17708c02f00bc00001cbac4f2dd155c9f648b2150f446d630015088e43d818009202e80ac00001cba6662c8949c98e46920a0edc6a02ec14d88f83b617e09283380c400001cba07f2bd94849864631fc0e586742de141089839c17208582bc0c200001cb9a992bd946098c46f2088edc6b62f615089003d419509483200c400001cb94a02c994b89aa47a20a8ef46ca30915889003c617c08f03000c200001cb8ebd2c494c898445c2068ed46b02fc14e08f03a017008e02d00b600001cb88f02bc147897845d2030ea46822d813d087c38216b08802b40a800001cb82e62d214f49c248720d0ecc6aa2fa14b88d83b018809283200c800001cb7cf72c4147c9a647120c0eec6c02ff15008f43aa17e08f03140d200001cb76ef2d795649f04a12270f7c71032515c09743f418c09082e40be00001cb71132c514d09b44742090ed469e2ee14608cc3a417a093831c0d400001cb6b002d695509e04862160f346da30015109203ce18909102e00a000001cb65192c494849704641ff0ea06a22f414d89083c418108e82e80b200001cb5f282c794bc9924682058ec86ac2fe14f09143c617908f02f80ba00001cb59172d615109ce47d2120f086c22ff14d08e03ca17a08d03080c400001cb532f2c014989a246d1ff0e7c6922ea141889c3a617908f83080b000001cb4d412c514a499446f2058ea46ac2f115009283cc17f08f82e00be00001cb47992a593d493643c1ee0df06462be12f87fc36816107e02980ac00001cb41812da95689d248621d0f386d431115389103bc18508c82e00b800001cb3b742d515489ea49921b0f386c030014f88f83b417b094831c0d000001cb35882c2149898e4692070ea468a2e013c887c38216208202900b200001cb2fa02bf147096645c2038e886882e813b085c37015b08702d40ba00001cb29ab2c914f09bc4822168f546de319159894c3ce18109403400c800001cb23a22cd95049c047820e8ef46b02f914b09043bc18209183240ca00001cb1de32b493dc93c4431f58e3c64c2cc13307e834415207d82a80b000001cb17f32c514b09a046c20b8ec46bc2fd15188f83ce18209002fc0bc00001cb11e92d495249ce48e2108f206b630214f88d83c017d08b83100d200001cb0bf52c694bc9a846e2098eb86b82fa14d08f43cc18208e83040c000001cb05fb2cb14cc9b247f20b0ef06aa2f014a08a439c17108602ac0ae00001caffff2d215009d048c2148f146a42fc14c09143dc18608b03040b200001caf9f52d215149bc48220d0ec06aa2f914e09203d218109403100c200001caf4052c7947c97e45b2060ea06aa2f714e08f03ac17908e02ec0ca00001caee0f2cb94e89b248320e8efc6b62ff14d88fc3bc17208782d40b000001cae7f12e295a4a104aa2230f786f831f16009883f219809b83440ce00001cae21c2c314a897a45c2010e5c66a2de14108b038816808b03000ce00001cadbd82f59610a424bb22e0ff472e32e16489843f219f09e03600de00001cad5d72d415189de49521a0f746e0313156893c3ce18008f02f80d200001cacff12c714ec9b64742098ed86b02f714988cc3a817608c82d00ae00001caca0b2c894a099a4752080ef86b62f615088d43a017408d82ec0c000001cac4342bb948096e4531fe8e7066c2e214588a03c418b09383180be00001cabe462c394b89984652068ea86962e214688c03ac17f08b83100d200001cab86f2bf946c97e4652010e906962f414c08d43ae18409603280d600001cab27c2c814e89a44852130f346d82fd14e89083ae17808b02e40a800001caac902c794e09b046e2098ed469e2f014708c83a817f08a02c00bc00001caa6852d8955c9ee4952188f346d430614f09183d618509403440e200001caa0ca2b1940094644c1f98e686882e814908b838e17208b02dc0b800001ca9abd2d595149d048420f0ed06a42ec14888b038c17308c02f80c200001ca94d92c4149098e45f2018eb46a42f114a08f83b417d08d02e80b600001ca8ee82c7949098c4692040ec86aa2f914e08ec3c818609283180be00001ca88f92c694a89804632018e8c6922f114c88ec3ac17808b82f80b400001ca830f2c594889a047720d0ef86b42fd14c88d039a17808c82e80ce00001ca7d282bf949c99446820b8ed46b830c15209183c417d08e82fc0ae00001ca77562b994489684571fa0e5c6642d314408b43a417509083140c600001ca715d2c994d09b047b2118ef46c2302152891c3c818208c02f00cc00001ca6b542d5952c9e249d2220f806ea31715989683f019209983480cc00001ca655f2ce14fc9bc47c20e0efc6ac2fe14688dc3b817e09583180bc000) else (if i < 294 then 0x1cd58bf2ad93f094e4531fe8e8c6962fb14a88f43b817e09003100c400001cd52e92c094a498846d2088edc6ba2f814f08f43bc17f08b82f80b800001cd4d1d2b393e892e4381ec0e046582cb134885036e15907f02a409e00001cd47162d715209d248a20d8f146cc30515309103d619109582f00bc00001cd410a2d3952c9d24912148f306cc303153090c3d618508c02d40b800001cd3aec2e2155c9e64952168f086c42fb14588b43b0187092030c0c600001cd35332ad94189524471f70e6c6722dc13a087038416508d82e40b400001cd2f4a2c294ac99a46f2048eb86ae2fc14d09103dc18609103140c600001cd296a2bd94949a847c20e8ec069a2fb14d88fc3d418709503540c800001cd23312ec15b4a224b02258fbc71231b15a09403d219009803140c200001cd1d5d2bb943896845c1f78e5467a2db13d088839216e08b02f00b200001cd177f2c394949804622038e846a62f314b890c3c6189097030c0cc00001cd11902c994fc9b648620c8ed86b22f814a08d83c0184093032c0c600001cd0b842da954c9e249321a8f806fe31d15c894c3e818e09703040ca00001cd05802d294fc9bc47920f0eec6ae2ed14808e83ac16d08882fc0d000001ccffbe2b294349604581fe8e7067c2d714288a039016e08502d40c000001ccf9c72cd14f49d04842100f146cc31315589243ce18509082f40ba00001ccf3e32c194a099647220b8ed86b030614d88e03d218c09203100b000001ccedda2d314ec9b64812138f286ea31a15709143d418f09a83380be00001cce7fa2c1148897645a2030ec06a02e614408ac38c16d08c02cc0c000001cce21b2c714cc9b247920f0ee06d22ff15008ec3c0187090831c0d800001ccdbe92dc95549d84942198f386ec30c15709483da18a09303340ca00001ccd62a2b2144496e45f2038ea068a2e014108a03b017c08982f40b600001ccd04d2be94949724572008ebc6a02ef147087436c16508102ac09e00001ccca5a2c614d89b047120d0ee46a62f514b88ec3ae17d08a82c40a800001ccc4512d915149dc4882120f206cc2fd14b88d03b218008c02ec0c400001ccbe2d2df157ca1e4a52238f786fc31e15f09203ca18809303080c600001ccb86e2b0140494a4421f28e1c65a2cd137886037416508482b80b600001ccb26c2cf94d49ba4742058e8c6862e914688bc38a16b08902d00ba00001ccac592db154c9d249b2188f346cc30e15289183d618d09403040be00001cca6572ce14f09a046a2078e986962fa14d08e83b217d09103040ca00001cca08e2b994709544571f98e406802e1141089c38416208482c00a400001cc9a9a2c814dc9ba47320b8ee06b82fc14f08e43a417408602b00b200001cc94bc2bb148499c46b2028e986882e114208c83a817809183000ac00001cc8eb22d2150c9cc48320c8ef46b82f614a08e43aa17c09282e80c400001cc88d42c014989684601fc0e646882e114388ac39817208e02e00ba00001cc82f82bc945498c4632038e9069c2ec14888a03a016408502bc0b600001cc7d182bb944497444e1f88e6c6782e114208b839017709083280d200001cc77202ca14c899646f2080ec06a42f615008cc39617408982f40ba00001cc71342cd15149d64832130f0c6b62f714c08dc3b617d08e02f40c400001cc6b3b2d014f09c24802098eec6a22fc15188fc3ba17a08b02d00ae00001cc65282d9153c9ba47b2108ee06ce301150091c3d218809083200cc00001cc5f182d395349d04892118eec6b02f014508cc39e16908202a00a600001cc591e2ca94d89b44822120f286d431415689343da17e08f03140c200001cc533a2c5949498c4611fe8e9868a2eb14708a43a417508902d40cc00001cc4d3b2d395089c447820b8ef86a02f414408983a618008a82dc0b200001cc470d2e695a4a0c4ae2228f806fa32516509883e419509583000d000001cc41212c6149498c4602020ea468c2e514408b039617b08d03040b800001cc3b252cd94fc9c047f20e0efc6ac30115108c03ba17c09183000c800001cc35222cc14cc9c248a2198f1c6d030715489303d818a09503280cc00001cc2f222d415409ce4842140f406e230414c89043c018308c03100c600001cc29182d0950c9c048120b8ee46bc30515089143d618c09403100c400001cc23222cc14f09a046e2060ee06b02f714b08f03c618709383580d400001cc1d332cb14c49c04852118f1c6e430d15c89483da184095031c0ca00001cc174c2c3149c98c45f1fd8e646802e5142088438e16808282b80a800001cc11432d014d098e4602050eb86ae2fa15308f83ba17509282c40bc00001cc0b6d2be145896a45d2038e886882f514c88e83cc18108f02dc0a800001cc05822c794f09ae4792080ed06982e914788ec3ba17808e02f40b400001cbff7b2d1953c9e848e20e8ef86c630c14f88e43ae17208d02e40b400001cbf9642de15649f44992220f886e431615d895c3e219909a83100b800001cbf37c2c2948c99446b2010eb069a2f414f08e83be17f09303040b400001cbeda42be947097a4612030e9c68c2ec146889c39816d08902d40bc00001cbe7b42cd150c9b047220e0f046a42f814a88d43aa17408d83000b600001cbe1df2b9942c95844e1f80e586762dd13f086837a16c08802b409c000 else (if i < 295 then 0x1ced5af2c614b09864712098ee46a430115b89483e018e09b83440c000001cecf8e2e615c8a224b92280fa46fc31f16389943ee194097033c0c800001cec9942cb94dc9ae47e2170f5c6f431615709443f018909582fc0cc00001cec3c52bb94509624491f70e086522d914188a839417108582ec0bc00001cebdae2e0956c9f049d21d0f6c6c82fa14e88ac3b418509503240c800001ceb7cd2c194a49b448220e0f106dc31316109703e418d08c02dc0b000001ceb1d72cf94c09a446e2098eb46b02f714988cc3aa17708e02ec0c600001ceabe62cb14dc9aa47d20b0eb06a42ef14908d83ac17408a82bc09e00001cea6092bd147c9724582090ec46a22eb14908b03b417708a02e40ac00001cea00a2cb150c9be4802130efc6ce30615989683e218709183080c600001ce9a202c814f49a647420b8eb468e2e213f88b83ae17c09183240bc00001ce94562b994309624541ff0e946922f214308bc3b818309303200c400001ce8e6a2c3947c98246a2008e8c68e2dd14488b439817808a02d80b800001ce887d2c794f099c4742080eac6942f714888dc3be18a09402f00b000001ce82a42bd948098c4762078ea46b430014708c83aa18208f83200d200001ce7cc02c794e09ae47b20b8e9c6662d8139084c37415f084829c09c00001ce76d02c5148898847120a0ec86b230315089003d218b095031c0bc00001ce70c52d495209d84922128f186da30515008f43aa17b08d82ec0b800001ce6ae42c594a899a47020a0e946842de13f088c38617008702e80ae00001ce64de2d415149d048020e8ef06aa2f314288ac39416c08802dc0ae00001ce5ec42dc15449d648a2190f586f031315909183d018c09082f00ba00001ce58b62d694f49bc47920d8eec6be30114e89083ac17208c02f80c000001ce52962d715409dc4862190f346da30f15088e03b418108e83100b800001ce4c692e595bca184a22230f486dc315159894c3ec19309383100c400001ce467d2c794a89a446d20c8eec6b82f814d88e43b816f08a82c80ba00001ce40982c714b49884682040eb86aa2fa152092c3d419509383140b800001ce3a7a2dc958ca1a4af2220f88714319158093c3d418309603140c800001ce34a22bb94749884571fd0e9c6a82fd15008ec3be16f08c830c0c000001ce2eb32c294b09a64682030ec468c2fa15409383ca18008d02f00aa00001ce28c02cd14d09aa47a2080ed46b430415109243d618108f83180c400001ce22b02db15609e648f21b0f386dc30f15488f83ba17708e830c0ce00001ce1c9a2d895689fe4a621d8f686dc30b15709103be17c08e02e80a600001ce16e52b113e893a44d1f80e586882ef14808bc3a016b08902ec0c000001ce10fc2c414989784622030e606722e113a887c38616908602a80a800001ce0ae72d715349da49021b0f746f632115f89783f619209a03500da00001ce04e92d315489d848120e8ee46c630d156092c3c217d09383180b200001cdff0e2c014ac98a46a2090ec86962ef14a08e43b817e08a02ec0ba00001cdf9062da15289ba47e2118f0c6ae2fe14e88ec3d618009082ec0bc00001cdf32a2c394d49b44812110f086b42fb14c08d03b618609683200ba00001cded792ab93bc9304381e90dfc64c2c412e884038216608302940a400001cde7692d995489de49221a0f406da30f155892c3d2186090030c0ba00001cde16a2d295089bc47e2148f0c6c02ff14c88e83b418009303380ce00001cddb8e2c0949097645a1ff0e7467a2e314288bc3aa17609102f80a600001cdd5a02c394a89924682038ec46bc2f714f08e03b417208682c80a200001cdcfba2ca14a499e4752060e8868a2e214308a839c17c094031c0c000001cdc9e82be14609704602038ec06b430615589243c618409182f40b000001cdc3f12ce14f09ba4822150f246e4311155892c3e419009903300d400001cdbe042c914cc9aa4742088ed46c430315288f83a017c09203200b800001cdb8322bd145897445e2018e6c6702dc14008b43a416c08a02cc0ae00001cdb23b2c994c499e47920e0f186c62fd14988e03b017808e02e40c800001cdac382d315209de48a2138f246d030215309183de18a093830c0ca00001cda6332d295049c247720b0eec6b22f814b88bc3c4183092032c0ca00001cda0182da95809ec48b2140f346da306151091c3d418b098034c0d400001cd9a462b7942895a4531fd0e3466a2d6140089038e17308a02c00bc00001cd94512c914a899e46a2050eb86a82ef14808b039416708002980a400001cd8e372de15549d848d2160f2c6ca30614f88ec3ae17108a02d00bc00001cd88382cf14d09bc47b2100ee86a82fd14f08f83b417508a82d80a200001cd821f2de955c9f24a22210f906fa31f160893c3e419209a03040ce00001cd7c582b014109564522008e7867a2e014708bc39216808682fc0c600001cd762d2e1957c9e44902168f0c6c22f814b88d03ae180090830c0aa00001cd705d2b2943c9544511fb8e746782e514388bc39e17208e02fc0d600001cd6a4d2d7155c9ea4972178f306cc2f415189203d017d08902f00ac00001cd64662c714ac98e47220a8ea868e2f014a88fc3b616e08c02d80ae00001cd5e7c2bf94809984682020ec06aa2ee14888c839017108982dc0ac000 else 0x1d052022c1947897a4612050eac6902f114888c43a816c08582ac0a000001d04c3d2b9143495444f1f88e546842e614788dc3ac17d09203180aa00001d046602c1949499a4692060e8c67a2e814208bc39416308602c00a800001d0406a2cc15149c04712090ee86b22fb14d89103c817f08d82f80b800001d03a942ba145c96e4542008e7868e2ee14c89003c218009082f40ca00001d0349e2ca14cc9aa47420f8efc6d030415289143ce18508d03000cc00001d02eaa2ca15009ce4872150f006ba2fe14808b83b617c08882dc0ba00001d028a62d194f89ce48d2148f146c82fa14e89043c617c09583440d000001d022e22b0141896645a1fe8e786902e714d08e03d018a09282fc0c600001d01cc62dd95a0a0649921c0f486da31015c89843fe19a09c03340c400001d016cb2ca948898a46d20a0ed86c630214d88d43b417608c030c0cc00001d010b12e01594a0e49b21f8f546e830915409303d418908f83040be00001d00a9b2d7953c9f448d2148f446da30d158893c3ee18b08c82c40ac00001d004bb2c914d899a46e2068ec46b830214c08d039c17908b02c40ae00001cffea02da95449e649621c8f686f632215e09343d218609503080bc00001cff8bd2c0949498646a2060eb06a82f014508c039c16008302980b400001cff2b62cf94fc9be4832140f2c6b22fc14e08fc3c617e09482e80bc00001cfecac2d294f49b847720f8ed46a42ff151894c3d419009903280cc00001cfe6a22cf94f09ca48b2150f086ca30014f89143ce181091833c0d400001cfe0d72b7146c98244b1fa0e306602cf13a086037014707c029009e00001cfdad62cf95009e04882190f306c430315389203d618509803240d000001cfd4fb2bd14989924661fd0e546942ea14788cc3a017608b02d00b600001cfcf152c714ac9a647620e8f0c6d030815288f83c0186091830c0c400001cfc93a2c014b499447120b8ee46a62f814c08fc3ae17308c02d00b200001cfc3422cb94c09a847220e0ef86b830015089083c418409603140d400001cfbd302d995489d248e21a0f4c6f230514f09203d818b09002f40ce00001cfb7412cc14dc9a04712058ec46ac2f014888bc3a217508d02cc0aa00001cfb1422ca94e499846e2038ed46ac2f514988d83bc17e09183140c600001cfab452d015289c248d2138f146cc30315288f43b418208882f00ba00001cfa5982a913e093442d1ef0e006462ca13f08903aa17808982c80be00001cf9fc22b7947897e45f2000e9c6942f714688c43c218b09803300d800001cf99df2cd94f09a64782110f006c0304152891c3ce18909283180c000001cf93e82cb14d09bc47a20d8efc6ac2ec14308a43ae16908902c00b000001cf8dfb2bf144c97c4602038ec86a42f314688b43a617c08d02fc0b400001cf883b2b6944896c4511f98e6065e2d313e08843a616b08f02f40c000001cf824c2cd94dc99446920a8ea46bc2f214a08e03ac17a08c02d00b600001cf7c4b2d395189cc49221a8f346e831515b89343c618709403000c600001cf76292de9570a044a321d0f586f230915088c83d018208d83080d200001cf70602b8944897c4622028e8c6862e514308a839416608682a80c400001cf6a6e2c514a498a47020d0ee06c22fa14708a838e16a08682940ae00001cf645c2d615509e448f2158f1c6d830d15789303d018b09402fc0b600001cf5e5d2d295149ca4862158f346e031015a89383d6194099832c0de00001cf58842c6949c99646c2068eb46a02ee14488b83a216b08702dc0b600001cf527e2d195109d44862158ef86b22f614b88dc3b018409083040c800001cf4c582e315649ea4942198f4c6d031115189103ce17608d82ec0c000001cf46af2a913d892a4321f38e446822e414288a839a16708a02ec0ce00001cf40912e195749fc4a32238f9c71a32415c89383d618609002f00c400001cf3a9d2c894c099846e2120f046a82e914708e83ce18309483240c000001cf34ad2c694c09a04692030ea86942e314088b83b817a09203080c200001cf2eb72c514a899c46d2090ec06a62f914e08e83a417208682c40b400001cf28d92bd946497645e2010ea86902e314708ec3b217208602f40c400001cf22fe2b894509624511fb0e746822e614588b03ae18109303200d200001cf1d222bc147c99246c2010ecc6922e714508a83ac17808b82cc0ac00001cf17192db953c9d44992170f506d031215a09583be17608c02f80b800001cf10eb2e595aca164a32210f6070c32115f899c412196097831c0c200001cf0afc2c594849884672058eb06962e714108c03b418108c03040c600001cf04f82d6151c9c64872118f106e630a15b09443e018309683200cc00001cefeeb2dc95609ec49b2188f846fe315159094c3da18909583480d600001cef8f52cb94bc99046f2098ee46be2ff15509083b818308e82e80c800001cef30e2c394a49864682020e746702cd13b885036e15e08502b009e00001ceed412b3941894c4481fd0e646722d9138088038416308802ec0bc00001cee7672bd948c98245c2008e806902e814108b43a416f08582d40a400001cee1772cb94c499846f2070eb86ae2f614c08e03a417408802cc0b600001cedb992c0149c99447520e8f106c02fd15208ec3b417a091830c0b6000)))) else (if i < 301 then (if i < 298 then (if i < 297 then 0x1d1cf702bc14549624551fb0e346822d413e088c37016908682e80b200001d1c9792c914a89964742080ecc6b22ff15409183ca18509483200c800001d1c3712cc94fc9c447b2120f486e431415989503e419109683040c000001d1bd7c2d214fc9c24842108f286c22fb14908e83be16c08b03040c000001d1b7a32c1949c99647120a8ee46c42fc14c88e83c218409403140c000001d1b1c42bd948c9a446e2030eac6942f114c08f43c2183096030c0c200001d1abd92cb95149da4852148f286d630215609383d618f09503280cc00001d1a5da2d114e89b44732070ec069c2ec14a08e83b017509002f40a800001d19fd52d094e89c047e20d8ee86bc30b158096c3f018d09783300d200001d199fe2bf149499046d2008e7068c2ed14708e83a817308c82e80b600001d1940e2ca14d899a46f2040edc6b62fb14e09143d217f08a82e40be00001d18e302bf948097e45c2000e946942ed14808fc3c619009b83580c800001d188372d014f09c847f2060ec06ac2fe14a88d43ac17108d02e80ae00001d182232d014fc9bc47820f8f046dc31515a892c3f219e09c83540d000001d17c142da953c9d24842110f1c6d430114f08f83be18309282e80aa00001d176012db956c9e249e21d8f6c6ec31015b89343c618409583100c200001d1700a2d215189ce4832138f206e831615509043d218609182fc0bc00001d169f92d915309c44882150f186ea30c15489483e819309603300b800001d1640c2c694b89b24702088ee86d22f714c08fc3b217d08e02fc0b600001d15df22dd15949fc49e21f8f486da2f815189243d018309103080b400001d1581c2c494ac99a4641ff8e946842e914508b83b018109703280d000001d1521c2cf14d49ba4872158f246b230215089083c6183093831c0c800001d14c2c2c594b499446d20c8ee86a02f614e88d83ae17108682f00be00001d146402c3948097e4642020e806922ee14608e43a617c08f02e40c400001d1405f2be947497a4531f60e2066a2e514888e83b618a09202fc0b800001d13a762c0145c97445b2038e946882eb14788e03ae17909182cc0ba00001d1349d2c114c09b647c20e8efc6cc2fa14c89003b6177092831c0c000001d12ea92c514b89a047820d0ef86aa2ee14788e43ba17809183380c600001d128a72ce94fc9ba47b20f8ef06c22fe15609643f018f09303000ba00001d122c42c694ac98e4622038e886942eb14408b43b216808b02e40be00001d11cbd2d215009b847b20e8ef06c030815309203ce17f08d03080c400001d116be2d295009aa47620a0ecc6b42f914a88d83b417608c02fc0c000001d110da2c0946c97a45f2008e706782e614508bc3ba18008e03000a800001d10acb2d215209c247b20a8ed06b22f914c08d43aa17b091832c0ce00001d104bb2d5954c9c048c2160f286c82f914b089439a16b08c82f00b600001d0feca2c994d49b246a2058e9068a2e914908f03bc17608882d40ba00001d0f8bd2d015209d64882148f2c6d430415209203c218109403280d200001d0f2d32c994ac97c4652018e6468e2df13b888c39a17809103300bc00001d0eccc2d014f49a047a20b8ed46bc2f614408ac39a15f07f82ac0a600001d0e6d12cf15109c647e2128f506e830a15789283ca17908c82fc0c200001d0e1062b1143495044a1fe0e806782e714188b83a217108c02e40ae00001d0db392bb944096045f2028e7c6942ea14608d03aa16d08802e00b600001d0d52a2d815309de4812120f146de303153093c3c619109c83440c600001d0cf162dd95709f44a62220f6c6f231415a89503dc18f09183000d200001d0c92b2c694c899c47d2098eb46aa2f714b08e839e17008802b80a600001d0c3302ca14c49a847520e8f206ba2f514b08a43a416e08602dc0b200001d0bd262d495009be47a20c0ef86b82f914c08b438816f08982e40be00001d0b7282d615109c64852140f206d030014c89003ba17a08b02dc0b800001d0b1512c5149099a4652070ea468c2ef14388ac3ae17909002f40aa00001d0ab512cd14d099046f20a8ec469c2fa14b88d03bc17708d02dc0b000001d0a5512ca94e09b047e2100f186c830615308ec3b217608602b80ac00001d09f6a2c0145497645e1ff8eb068a2e914108a83a617108c02d80b000001d099812be14a89844642010e8067c2e714388b439a17208482bc0c600001d093942c714e49a246a2080ee069a2f414b08cc3b417908e83000b200001d08d4e2f41620a484bd22b0fe071832615f89583d218709983300e200001d087362e215709fa4a421d8f4c6ea30d15009203d418c09b03440dc00001d0815d2bf94849924611fd8e5c6682d7138886037c16408102b00b200001d07b702c594d89aa4782048e746882e514488ac39817008702d80b400001d075872c3149499c47820c0ef86b830314f88e83d218108f83000b600001d06f9c2c1948c99445f1ff8ea46902f614d08d43a616f08a02a80b200001d069a32cf95009bc48120b0ee06b030214d88cc3aa17208e02e40be00001d063aa2cb95009c64862138f186ca30e155892c3ce18509102f40bc00001d05dc82c594c49b647a20e0edc6b02e814588d03aa17f09203000b200001d057e42c3949898c4652018e9c6922f214b88ac3b217908d830c0c6000 else 0x1d34afe2d515549e448e21a0f1c6ce30d14f08ec3bc18509802f40ca00001d345452ab140494443e1f58e586922e614508a83b017b09002fc0c000001d33f4f2c814909a64691fd8e7467a2e7143089439017908e02e00b800001d339902af93e494c4501fa0e7868a2e514288a43a016c08502c40b000001d333892d595389d24872120f1c6c830915a89403f81a0099032c0c600001d32dc72ae942095c4511f70e7068a2e714808e43a216b08202a00aa00001d327b92d715049b64842138f0c6ce30114c88f03b017d09083340cc00001d321be2c814e09b447b20e0f0c6bc30515088f03ba18409303100b600001d31bdd2c3148c9904662048ec06982ea13d88903a017408d82e00c400001d315d32d295249c04802118ecc6d030914f08dc39e16f08182bc0a600001d30fcc2d094ec9be4772108ef869c2e714088a438816e08d830c0be00001d309cb2d315109b44732108ee86a22f514508c43a816f08982fc0aa00001d303d82c8947096e45a1ff8e786882ee14c08e43b618809683140b800001d2fdd22d415049c248420a8f006c22fd14f88f43b617b08f02cc0ac00001d2f7af2e515649f449621c0f7c6e031715989483e218908d82dc0b000001d2f1b72cf14f89c047b20d0ed06ae2fc14e88e03a617e08d82dc0c400001d2ebbf2ce94f49ac47920d8eec6c830a15a09483ee19309683300ca00001d2e5ee2b6144c97e4612028e8c68a2e714788fc3b017c090832c0d000001d2e0112be949897a4602018ed469e2f614d89103b017508c82f80c000001d2da4f2b094309664511fc8e746822e514488a437e16208002b80b400001d2d4312de95449d448b2180f4c6ec31115509103ce18909002f80c400001d2ce512c194709824652008eac6942e914908a838e16f08802ec0b000001d2c8482d394f09bc47820b8eb06a02fb14c88cc3a617508d03080c200001d2c24b2ce14e89a84742068eac6962f514d08f83be18408e03040c000001d2bc6c2c3947498046a2090eb069e2f214a88cc3b818308e02cc0b000001d2b6912bf148499847d20e0ed46ba30514e88d03b417b08683040c800001d2b0882da955c9fc4a42218f706da30715289143c218209482fc0b800001d2aa8a2d094fc9d64842120f146d031015a09443bc18309102d80b600001d2a4872d394f49a447a20f8f106ce2fb14988e83b218508e83080c200001d29ea92c294d09a04742030ea86822e0142888c39216e08a02b80b800001d298c62bd148c97c45f1fc0e3c6662df13f087c39e16f08902d80b400001d292cf2cf14f89c848320c8f046c42f714f88dc3b018409102a409c00001d28ce22c614c89b247420a0ed06ac2fd14f88f83be18609103240be00001d2871f2b394589624542018ea068c2db13d885c37616008102a40a000001d281432bf949898e4622080e946a830415008bc38817008882cc0ac00001d27b732bb94789ac47a20c0efc6ce30415388fc3ac18009203300c000001d2754f2e415889e84912170f286d830c15009203be17d08d02f00c600001d26f402dd155c9f448f2150ef86bc2fe155892c3c618409402f00c200001d269662bf14849904642028ec06ba305152091c3bc18009283280c600001d2637d2c614bc99646d20c0edc6ac2fa153890c3ca18809483480cc00001d25d822c794a497e4661fe8e806942f314588bc39417408d82f40b400001d257852cf14e09ac47b20d0f106be2fb15009183d4184098030c0cc00001d251982bf949098645d2018e8867e2e013e88ac3a017308482d40be00001d24b9a2d615009ce4852108ed46b02f314e08d83b417309483200c600001d245be2c214a49844632018e946982ee14c08e83ba18108b82d40c000001d23fc32ce94f09c449921c0f4c6f031b15409003b417a08b82e40be00001d239b12db15389c447a2078ee06c02fe14f88f03b817208b02e40b200001d233c82c494a09ac47a2098eb86882ed14508ec3c017b09102f80c000001d22df12bb947896a45d1ff0e9c6902df14688d439416608882c80c000001d228152c594a89904652028eac6a42fe15309183d218809703180be00001d222062d915449e449321c0f386b62fc14e08fc3ac17408e02f80c000001d21c2f2ba144495e4501fc8e4c6802e914688a038817008b02e40ba00001d216422c394b89904722080ed86c230614e08f43b617a08c83140c600001d210752b3945c9744642018ea467e2d5140885038016408703140d400001d20a792cc94f89bc47b20e0f006c430715288fc3d2192095831c0b200001d2048c2c715009d04842118eec6be2fc14c88cc3bc180092031c0c200001d1fea12c714b098e4662038ea869c2f514e890c3b416c08582b80b400001d1f8b62c514b899646f20b0ef46b02ff14e08cc3b617508a82ec0bc00001d1f2d52c2949c9924732090ea46922f014a08fc3cc18409403000bc00001d1ed252a313dc94644f1fc0e6067e2e113f887038216308682d00a200001d1e7152d395189ca48e2140f086d430d157094c3de17e09303180bc00001d1e1202d215049ca4872178f186e230e158090c3c418508f82ec0b200001d1db392c494b099046920c0ef46ba30615009003c618609483180bc00001d1d53d2ca94ac98646b2010e986a22f1145088038817108f82f40b8000) else (if i < 299 then 0x1d4c72a2ca94d09bc4832128ee86c42fe14808c03a017c08e83000bc00001d4c1412c594e49b847520f0efc6b830314d09083c618709002f80d200001d4bb562c794b099046b20f8f106b82fd15089203d617f09103180be00001d4b5502cb94dc9be4892110f106d430d15489103d418708f03000c200001d4af7c2c094709964672038e8c6882e714588a038c16e08c03000b800001d4a99a2c0148098c4611ff8e7c68e2e414308c43a617b09803400ce00001d4a3a92ce15049ca47b20f8ef86aa2f414c08b03a017908f02f80c200001d49dcb2c2149c9904641fd8e906662dd14308ac39a16c08d83080be00001d497d62cb14f49c848020f0f046da30f15889243c418709903140ca00001d492012bf94909884692048e9c6a62f714f890c3c417c08c82f80c800001d48c0e2ca14a49984692078eb868a2e514508b038416b08682ac0a400001d4860b2cd94dc9a046d2068e946802e113e086c38e16d08e83080c800001d47fe12e9159c9fa49e2178ef46d230d15689243c417b08d83340ca00001d47a0c2bc94849824622030ea069a2f314488a03a416908882cc0b000001d474492b7946096e45e2048ef46ac2f914c08c03ac17908b82c80be00001d46e2f2e115589ea4902160f2c6cc30815489103be18208f83440de00001d468242d815389d248f21c0f686fc322163098440419c09b033c0c000001d462002e015689fe49f21e0f5c6de319159091c3d618609082f40be00001d45c0e2c814b899246b2050ec06a22f014b88f43b017408c02dc0ae00001d456582ad140c94043e1f48e506742e213b086c37816608482a40a400001d4505d2ca94d498446a2070e806842e213f889839417008b02d80b400001d44a5c2cd94f89be47620e8f086ba2fc14d08f03bc17908f03140b600001d444752c3149499447c2108f406c830215089283e418c09203080b600001d43e7e2ca14d099e47120a8eac6942eb14288983a217308d03140c400001d438a22bb148c98c4702088ec06ba30215189043c217d08d82ec0ae00001d4329c2d615449de4842118f286cc30214e89003ce18609203140c600001d42cb72c794e09ae4742088ed46b62f914d88dc3b2186096033c0dc00001d426c22d014d89c047a2110f046b22f914f88f03c417a08f82c00b200001d4210f2aa13b091842d1eb0de063c2cb139086837416308402c80c800001d41b1a2cb94d89a647a2090ec46a82fd14f08fc3c218108a02f80ca00001d415312c594a098a4601ff0e646762d613d087839016508b02e00a400001d40f2f2cd14d49a84662008eac6aa30014e890c3cc190096031c0c800001d409252d515589e448a2170f486ee31215d09543ec18e09103140b600001d403472c214ac9a64702050ed06b02f314908f43ba18209303480da00001d3fd5c2c994f49b247c20f8f006b22f415008e83aa16e08a82e80c000001d3f77f2c1947896e4571ff8e846842da14308a039e16a08902c00b200001d3f1802cc94a898c4641fa0e7067c2e013f087439216608602d80c200001d3eb922ca14c49ae4822100ee06a62ed14908a03a216808602e40b200001d3e5992d194fc9c24882100efc6e230514e88f03b217c09103240d400001d3df8b2d6952c9ce4872140f286ce307156893c3ea18f09383080c400001d3d99b2ce94e89c24832120f2c6da30415309103c217c09183100be00001d3d3992d094f49b247a2128f346d030215409283da184092831c0ca00001d3cd8e2d215189cc47f2140f106c22f414a88e03ae17708f82e40c000001d3c7832d895389c247c20c8ee86da30214908e43c818b09083100d400001d3c1a12c594749704542000e946aa2f514b88d43a417a08d82f80c800001d3bbba2c494989844551f78e5c66a2dd13c08a038815f08602cc0a000001d3b5df2b8942496e4581fc8e7068e2ed14888ac38c16708782f00b200001d3affc2c214a099e47c2118f146cc2f714f89103c017908803040be00001d3aa0d2c314a499446f20a0eb06862e4141087838416308582c00a600001d3a40f2d4153c9dc4812150f406c630a15609583f6198098832c0dc00001d39e162c694bc9a247620c0ecc6a62ff14d89003ba17a08b02d40b400001d3980c2cc94f09b247920a0eec6b830d15508f43d618708f03080b400001d391fd2d895549f248c21d8ef86b230114b88c83b017208302a80aa00001d38be42dd153c9d048a2178f306be2f814e090c3d017e091832c0c400001d386022bf14a89ae47a20a8ec06bc2f614a08e43b417609083240b400001d3800f2ce14ec9aa46f2020eb86ac2e614508b83aa17a08e82d80b600001d37a3d2bd149c9ac48320f0ed06be2ff155090c3b817e09002f40c600001d374432d395149c64902198f486c22fd14908d039816708c83240b800001d36e722bc944097a4622008e946962e614608e43d018d09382e00ae00001d3687f2c814c098a45a1f90e646802de138087439617208c82f00b000001d362b42be948898c47220e8efc6ae2f614b08b839817008a82d80a400001d35cce2cc94dc9b84692000e906922f315008f83ba18309103280dc00001d356d62d394e89c448d2148f406e430715589203da18e09203040b800001d351002ba947499a4722080eec6c430b151092c3ce18709603400d8000 else (if i < 300 then 0x1d643852d615249cc47d2098ea869a2fd14708a43aa17208f83100cc00001d63d802ce94ec9bc4832140f2c6dc30c15989803fe1a109d83380c800001d637752d695289f849a21e0f406ee30815608dc3b817b08e02d40ba00001d631ad2b9148499047120a0ed468c2e714608a839416c08402a40c800001d62bbe2c1949498846b2040e9c6982f014908d83c6192097031c0d000001d625a12da152c9c248b2190f306c830014d08d83b617f095832c0ca00001d61fc52c514a09904722038ea86aa2ff14e88c43ae17e090031c0cc00001d619dc2c314c49a646c2100edc6c2306157891c3f618f09683200c400001d613e12c894e89c647820d0f086d631415689543e218a09303140be00001d60e0d2b9944095c44c1ff8ea06a42f514788c83aa17b08d02f00aa00001d608152c914a498846c2058eb868a2db14188a039a17108b82c80a400001d6022c2c815009aa47120c0ef86aa2f514c88f03ba17c08d82d40b200001d5fc2f2d095109c44792078ee86b22f014408a039e17508a82d80c600001d5f6232d6150c9d649021c8f486e231515789303ca18509583240c000001d5f01b2d395349da48c2110f106ba30c15909483c818d09403300ce00001d5ea582b5944895e44b1f50e0c65a2ce13f889037816208702f40b600001d5e44f2d495289e449b21b0f746f2310159897c40218d09483180de00001d5de6e2bc148899a47120a0ef06c02f715209283ec19609983280bc00001d5d87d2ca94c49a847f2118f086c830915209103d018a09203180b800001d5d2922c314a49964732040eac6902e814a88ec3e218e09082e40bc00001d5cc792dd15309e448a2148f306da313153092c3d818809203280c200001d5c6602e215a4a144a721d8f506e630d15089243d418108e02f40c600001d5c0682d615209cc48d2108ef06c82fe14888d43aa17909102dc0aa00001d5ba7e2c694b899c46e2068ec469e2f314b88c43b017b09202b40ac00001d5b49d2bc147497645c2000e646882e6142089c39a17108a02e00c800001d5aeaa2c394bc99246b2070ec86be30515189203d018209383280be00001d5a8892e315b0a2c4ab2258fa871831f15e09703ea18c08e82e40bc00001d5a27e2d615309c84872130f3c6c62fd15088e03b418309303180b800001d59c7a2d495209c848b2170f2c6de303159093c3de18f09b83480d200001d596842cd94f89b247720e0ee06b430214c89143ce18709503180a600001d590882c614b099a4732070edc6a02f114e09003b018408e82f40b200001d58a772d715249e848d2158f4c6d030a158094c3dc18509583100d000001d584842d114f49d648f2180f486da31315a09503e418a09503240d000001d57e8d2cf150c9b848b2150f106b830514e09083c617d09183080d000001d578a52c694bc9b847d20b8ea06982f014b88e83aa17008982d40bc00001d572bc2c494809864631fe8e846702e3141089c39a16e08e82d40bc00001d56cb32d514f89b847d2100ee46b42f615189043c018b09703440d600001d566dc2be94b499646820a0ea068c2d713d083436416308402d80a800001d5610a2bc14609804692078ecc69a2f014888d03a816b08702d40be00001d55b172c714c89ae47320b8ef06ba2ff15209183c818809082e80b800001d555502b494489604521f78e4466a2dc14088a039617f090831c0c400001d54f832ba144096045f1fb8ea468e2e914788e839416208802b40aa00001d5499a2c914dc99c4652038ea869a2f214708d03ba17908f03140d400001d543c52ba14209524531fd8e746782dc13c086c37216708402d80c200001d53db32db953c9e84972118f306ee31015b093c3d018609203000c200001d537ca2c614e89b447920c0efc6de30b15609403e219009283100ac00001d531da2cc14d099e46f2058ec06b22f614988e83b417308e03040b200001d52bea2c294bc9a44742090ed46a82f714e89103e218508d02b00a600001d525fd2c894dc9a047d2050e906962f214b08e43aa17909102fc0b400001d51ff52d194ec9c847d20d0f306d8303153092c3de18c09a03440c800001d519c72e2958c9f24982190f546ec31515909503f019b09883100c600001d513e02c794a098246a2000e7067c2ed14708a039c16107f82bc0ac00001d50e2e2ad93f494843d1f18e206682e0144089c39416d08802ec0b400001d5083e2c894c89a846a2058e986982f114e88fc3b017b09082fc0b400001d5024d2d295109c447b2120ed46b430414b08c039617108702c40b000001d4fc402db1570a0449c21d8f746fc31615589303d018c09182e40a000001d4f6812b4143c97c46d2080ef46c030214f88f43b017608e03080c000001d4f06f2da15389e448f2170f406f430d15809343dc19409b83640d400001d4eadd298935c90e42f1ed8e346542c7133886037415a08282cc0ac00001d4e4dc2d415389ea48f2140f2c6a82f314b08f43cc185094032c0cc00001d4defb2bf94a498c46620a0ee86a42f515188e03c018a09202f40ba00001d4d9222b7141c94e43d1ee8e046582e114388a438e16f08702b00a200001d4d30a2e095749f049821d8f446d830e15909343e818c09683240c800001d4cd222c514c89ac47620b0ed06b42fc14c88d83ac17b08e02e80c8000 else 0x1d7c1082db15249e849121a0f6c6e430c15b895c3f819109483200d200001d7bb0f2d095009b047420c8eb86ba2f214908d439e16d08682cc0ac00001d7b50a2d595249ca4862148ef86b02f614c88fc3c217908d82d00be00001d7af322bf94ac9924672048ecc6a22de14908f43b617a08982b80a600001d7a9002eb95c4a1e4b22210f986fe31f15d09843fc19609483040ba00001d7a31d2c594a09904672060eb46aa30015288f83b818e09783200d200001d79d422c414a49a44692080ec069a2e814708ac3a016608502d40c000001d7973f2d415409f04972158f3c6cc30215408f03a418009303180d000001d7914c2c794a89984752058ec06942ef14908d03ae17b08f83080e200001d78b5f2c494949944692030e9c6822d9141086838016908803000c000001d785752c194a899e47720f8ec86822e4143089839017108a82f00c400001d77f8e2c514bc99a4742090ec069e2f2145089c39017808d82f80bc00001d7799e2c994f09c648d21f8f9470431b15b89503e818b09503040ce00001d773af2ca94e49b247e2138f286c02ff14e08f43b017909003000be00001d76d952d495009b647d2118ee46bc30f15089203ce18a09483300c800001d767c42b914309664541fc0e4c67a2e014008b43b018209382f00b600001d761d22ca14d09ae4712108f106ca30814d090c3c217e09103280d800001d75be02cd14bc9a247120b8ed069e2f014a88ec3b818509002d80a800001d755db2d1951c9ca4842108ef869e2ec14808a839817608b82cc0c400001d74ff92be147898245c1fe8e686882e9144889c3a217d09283000be00001d74a072c994c09aa47a2108f186d430a15489043be18a09603100c600001d744102c814c89a247b2128f186bc2f214808fc3d618909402fc0c800001d73e1a2c714d09a64682058ed86a82f214c08c83a017208f02e80de00001d738272ca94d09a246d2088eb46802d5139887037c16408a02e40b200001d732382c814e89bc46f2078edc6b62fe14d08e83b017208882e00aa00001d72c382d114e09be4812148f506d430c15209083cc18f094830c0d000001d726372d1150c9c047f2120ee46ac30615709283ca179093833c0c600001d720302d015089ca48a2158f646f431d16089603f419d09d834c0d800001d71a2c2ce95249d848f2160f3c6d02fd15609103c218208e02e40c200001d714262d115049ae46c20a8eb06922e914188943ac16908482f40c000001d70e1b2ce95109d64812098eac68e2f314b08e43ae17e08e82d40ba00001d7080b2d695309cc47d2100f046d830715a09343d218609703180c400001d7023d2b814389504501fa0e6867c2d513d087037816108502d40b200001d6fc722bb145c9684662000e7c6782db14588b83a618009302f00ae00001d6f6642db952c9d848320e0ef86ce30b157894c3dc18609302d00b400001d6f05e2ce15049b047b20e0ef86b42fa14a08f43ae17108402b40a800001d6ea762c194b499c4722038eb86b02f5147088c3a217408c02cc0b000001d6e4a42b8143095644e1fd0eb468a2e614388d839216e08f02f80c200001d6dea42d114ec9b847e20e8ecc69c2f715008f43c218409002dc0b600001d6d8b52c394a89a247420b0f046c230415389043d018508f83080d000001d6d2a22d795509fa49f2190f206d631315689343d618509303100c800001d6cc972d115049be48320e8f106c230615188f83ca18908f82cc0a800001d6c69b2cf151c9c247e20d8ec069a2ed14808d43a817b08b02f80bc00001d6c08d2d114f09a846d2078e9c6862ea14588cc3a817508a83100be00001d6baca2b294109324421f50e3c6502d4139088038c16908a02ec0c000001d6b4e62c394ac9884672070eb869a2e414408a438e16308702e80ba00001d6aef72c8948897a4621fb8e9467c2de140888c3a017808b82ec0a800001d6a92c2b7146898645f1ff0e986982ec14c08fc3ca18809603480c600001d6a31a2dc95649f449621a0f786f431715989443ee19409803280da00001d69cfd2d995449e64842118f2c6c630315389003d018909183180c400001d6972c2ba948098a4682018e986a22f014988c439a17008a82e80ae00001d691232d495289d248f2100f146c830114d08c83a216e08782a80b600001d68b312c914b099c46f2060ec86a82fb15209003b618008e03140ba00001d685322ce14a49ac47320b0eac6aa2fe15189143b6185099033c0c000001d67f5a2bd94649804692088ec06822e2141086c36e15808082a40b000001d679632cd150c9b647e20c0ee46b82fa15108f03b417908c02e80aa00001d673612d395289da48b2150f0c6ba30915089083b818409283040ce00001d66da02b7945094844c1f50e446622d414108ac3a617008a82d00a200001d6677e2dc95409e248c2140f006be308150090c3e618c08e83140d000001d6618d2c6147497246c2050ea06862e514c08e83b617d08a02f00c200001d65b882d2952c9d24882148f0c6cc30515009083b617e08e82d00a400001d6559e2c914cc9a24561f90e5067c2d914008ac3aa17e09003200d000001d64f902d595349d24922230f886ee30f154094c3e019309883140d400001d649962cc15109c04842110f0c6d630714b08d03a216f08d02e40b6000))) else (if i < 303 then (if i < 302 then 0x1d93c892be14889804611fe8e606802dd14188b038c17108a82f00b600001d9369a2cc94d89b648320d0ecc69c2f714c08f43be17c08b02ec0c600001d930952d214f89bc48220f0eec6b62fe14d09103d417d09383440cc00001d92ab52c514709784561f80e546802e714388a83b618209302f40b600001d924db2c594c899e46c2040eb06862eb14708e03a617b09403240c600001d91ef32c714b09b44732070edc6ae2f114809083b818909803280c800001d918e62d915509e849521e0f786f2314158096c3e818c09383340c800001d913062c414c499c46920c0ebc68e2e313f088038416d08982cc0ba00001d90cfe2d215149e04882138edc6b22f414989003d618008e02f00bc00001d9071f2bc149898a46e2068e8c68c2ee14708bc3a417608a82f00c800001d900e92ee15d8a324b92280fbc71c32115e09603e618d092031c0d600001d8fafb2cb14dc9a247520b0ef46c62f814b88dc3a217808c82e40be00001d8f5052ce94e89b64742088ebc6a22f113d887038817108902d40c800001d8ef132cc94d49b847f2100f086c02fb14e08d43b417108c02c80bc00001d8e92a2c4949c98a46a2020e7c6962ee14388a83a416b08903040be00001d8e3292d115189e04992200f286da30415189103c618709303180cc00001d8dd7a2ad93fc9424441f30e4c6622ce13a888839017308d82f00ba00001d8d7912c994b49b44822138f386c42fc14e88cc3be18408f03180c200001d8d1e72a613d093c4451fa0e6867a2da13f087c38416107f828c0a800001d8cbf92c714989b047120b0ed46a82eb14308c43c217f08f02f40ca00001d8c6192c614cc9984642090ea86902e5141089038e16908702c40a000001d8c0412b8946898045f2028ec06a22ed14808bc3ac17708d02fc0c200001d8ba6c2bd146c96c45e1fd8e646802e614689003ac17208902cc0b000001d8b4892bf149097c4672078e946822e514488b83a417c09083300c400001d8ae822d114fc9d047f2130f246e630915008f03c417b08802d80c800001d8a86f2d7952c9d84932138ef06c230515889243da19609903180d600001d8a2962bf94a098e4592018e9c6922e814c88e43bc18d09702e80c000001d89c912cf94ec9b847920e8ee069c300153892c3c218609502f00d000001d896c22b714349764541fb0e7467e2d714308b039c17208982d40aa00001d890ca2d295049ac47d2100ebc69a2f014808c83b617a08982e40be00001d88adb2cf950c9d247a2110efc6b62f314a08d03c218009183140c000001d884fc2bd147c9824672028e886822e014608983a017008a02ec0b200001d87f032c794d89c447c20b0ecc6bc30515489003ca17808802a40b800001d878fe2d4953c9e04922170f186b8302153090c3dc18f09603200ba00001d873172c314b099e47820a8ed06b6301152891c3d218c09483100c800001d86d1b2cb149c98c4632070ea86902eb14708a43a217209483440c000001d8674e2b8946497245d2040e986ac2f914a08d43b617808e83200d800001d861712c714d89b84772090ed069e2e814908d03c218c09302f80b800001d85b972bd945495a45d1f78e6c6842e414408cc3ba17f08f83080d200001d855ac2c314a099a47420e0ee06b02f714588d83a616708582980a000001d84fdb2b994ac9824652050eb869e2f714c08e83b217e09183080c400001d849e52cb14d099a47620b8eec6b430214e88ec3bc17708e82e80c200001d843f72cb94e49ac47820d8efc6ce30315409183d419609483000c800001d83e1d2bd949098a45b2010e906942f314a08ac3aa17d09183200d600001d8380f2d8153c9d04822188f286d030915388f83c217e08f82fc0c200001d8321a2cf15089d44882110ee46aa2f214808b83a617509102e00b200001d82c0c2d695409e84a12180f206c630315509203d8186094032c0be00001d8260e2d095049b84802120f106c630815289083d819909b03140cc00001d820452b614789724622070edc6b62fc14d09103ca18b09b03540cc00001d81aa12a293809044391ec0dd462e2c0139885837a15c07f02a40a200001d8149e2d314e49ae47f2120f0c6b82f214c08d83bc17a09002e80b200001d80e6d2e915c8a2a4bd22c8fd470e32816009783fe19a09603440ca00001d8086e2cf14ec9b648020d0f006dc31315709343c417e092032c0b800001d802662ce94fc9ac47420d0ef86b82f6147890c3be17808a82e00b400001d7fc7f2c114a099246b2038eb06782e814808e43c418208b82f40ae00001d7f6b12b494449464551fb0eb067e2e014388a43a017909283180bc00001d7f0ca2c1948099446f20b0ef06c630c15c89503e019109403100ca00001d7eab12dc15809fc4912188f006c62f914e08d83b417c08b82ec0b400001d7e4d02c5148899246a2058ea46902db13f089c3a217808c82dc0c800001d7df0b2ba94649824621fe8e746942e914308b43b417808a82c40b200001d7d91a2cb14e098e4692048eb469e2f114b88e43ac17108b82e80b400001d7d3222c914b09c24862120f086b630e15589203b417508c03080c800001d7cd402c2148498a46c2068ee06ba307153890c3c818208d02f80b600001d7c7232e015709f04922168f2c6da306157893c3dc181091831c0d2000 else 0x1dab99f2d015149bc47920d0f046d230415809103ce18f09382f80ba00001dab3b52c614dc9ae47920b0ed869e2f414d88fc3c4185090831c0c200001daadb52d095389be47e20f8ef06a82f514888e43c217f094833c0d800001daa7af2cf15409d848e21c0f546e431c15f89683d418e094832c0c400001daa1ba2cf15249be47720a8eb06a02f814a88c43b416e08702d40c800001da9bcb2ca14c49964762098ee06ac2fa14d08e03b617508a82fc0ce00001da95d02d015049c44792098ee46be2fb15009043b017a08e82fc0bc00001da8fc72d395089d64872148f086d42ff15689383d218609402e00c000001da89e32c294d098245c1fd8e9c67e2db13d889038616808982cc0aa00001da84282ae13f895e4541fb8e686822e814388b83a218008f02f80b400001da7e242d295409c848620c0edc6a22f914b08b03ac17d08d02d80a800001da784f2be948498c45c1fe0eb86a42f614c08f43ba17f08e030c0b400001da722c2e2158c9fa4982198f4c6ce308154091c3b217909082f00a800001da6c512be145896c45a1f80e1c6742df141089038417108e030c0c800001da66472dc15849e849521d0f6c6e631015809603f01a6094830c0d200001da60622c1146497244a1f48e5c66a2e014588ac39c17b08f83180cc00001da5a4f2dd95589e24902180f3c6da30515509083ca18208a02f40b400001da54472d315049be47a2108ef86ba2fc15189183c4180091031c0b600001da4e442ce94e09c04822140f106b22fe14c08f83c218308c02d00b000001da48582c6948c9784621fb0e606822e114508ac3a817908882e00be00001da427d2be14a498a4632048e8c6882eb14288bc3a417108702c80b200001da3c792d3152c9b047b2158efc6ce306153094c3ce18609282f80c600001da366c2d49544a0049521c0f8c70431815d09443de18a09803380dc00001da306f2cb15109ce48120b8ebc6be30515409243d819009c03480ea00001da2aa42bb14349684561fe8e7467c2e314308b43a817e08f02fc0c000001da24bd2bb94449784562008eac6942f5146888c3a217608e02fc0c400001da1ee32c0948c99c47520b0efc6ca30715188d43b217b08e83140c600001da18f62c914dc99246f20b0eb469e2e914208b438016a08402ac0b400001da13032c614ac99e46e20b8efc6ba2f614d89003c018409583240bc00001da0d022d115309d64872190f446e430e15488d83c217308c02e80b000001da071a2c914f09cc4842148f406d0309159093c3c217708882c00b600001da01392c294cc9a447320c8ee068e2de14288ac3ac17908a03140c400001d9fb502c294e89b44862158f0c6ca2f9150090c3d218509002e40ac00001d9f5322e215909e64912158f6470032115b095c3e6195098833c0c000001d9ef402c714d499e4712098eb86982ec14888d03a417908f82e80c600001d9e94b2c714d09b84892110f206d430715709583e618b09703100c400001d9e35a2c614b09a247b20f0ed86be303156091c3c218308e82ec0c000001d9dd662d014e89be47b20e0ed46b42f415089483e418d094034c0cc00001d9d7872c0947898a46720b0f306c42f614c88e439c16f08d02cc0b800001d9d19e2c694c09944642020e986a22e114a88c83c418309183080c000001d9cba52c994bc99c46e2090ea86a82f914e88e83bc17a08c82ec0cc00001d9c5bd2c3146495c4541fa8ea06a82fd15109103c617b08602e00be00001d9bfe42ba94509584501f90e786942eb14508a039617208682e00be00001d9b9ea2d0150899e4762100ee06b42f114988ec3c418009082cc0c000001d9b3d72d815509ec4a02228f9c70c32816309743fa19909f033c0de00001d9ade82c5149097c45a1fc8e946982e014008b839c17608c83140cc00001d9a80d2bf147899046b2058e8c6762d814388903ae17508c02e80c200001d9a2282c194b499847420b8ed86a62ed14608ac39817308f82fc0ce00001d99c322ca95149ac47320b8ea06ac304153894c3e818909003180c400001d996722b094009424441f28e0c6582d513a087436e16708483000d000001d990852c794d09ba4822118ef86c02fd15008dc3aa16b08a82fc0b400001d98a7a2d89560a0e49d21d0f446e230b15a09403e618609403080ba00001d9846c2d795209c64802120ee46a22f014c08c83aa17a08c02f00be00001d97e892c494c49ac48020a0ee06ba30315489283be17e09102ec0ce00001d9787c2d5953c9d84892110eec6be2ff14d89083b417208b02f40a400001d972922bc144497044b1fc8e6c6782d913f08b43b816c08202e40a600001d96c692dc95689e449721f0f806f431815b09943f619909783200bc00001d966732c594a899647420e0ecc69e2f614888c43c017508e02f40b400001d960382e995c8a264b12280fa471a31c15789143d418b09583300da00001d95a482c514b098e4622040ecc69e2f114b08d039c17a08f82f00bc00001d954362d815509d048020d8eec6b82fb14b88f03bc18209083080be00001d94e492bf146498245b1ff0e8c6962ee14908c839c17908b02d00b600001d948362d695049cc4852170f246d030014e08e03b616d08c02cc0c200001d9425b2b7146c98446a2070eb06a22ec14d89243d618009303200c0000) else (if i < 304 then 0x1dc364e2c0148c99c46d2090eb06942fa14d88ec3c018008f82fc0cc00001dc304a2d094d09ae47820c8eec6be2fd14f88f03b018008b02c00a400001dc2a3b2ce14d89c64802158f106d630214f890c3bc18809303180b600001dc24532c014789784541fa8e386762d3138086437616e08e82f80ca00001dc1e892b4143896a45c1fc8eac6942f014508d83be17e09403440dc00001dc18be2bb14689584501fd0e746962f114a88d43ac17608a02f00c600001dc12ea2bb146098246b2030eb869c2ed14a08bc3be18c09482e00c000001dc0d052c494d09ae47b2088ed86ac2fa14d08ec3ce18708f03140c200001dc07222c0948498c46220a0ea46822e114208b839617b08f82f80ca00001dc01442c3947c9884612038e8c68a2e514608b03a617908a02e80b600001dbfb572c5949899646e20b8ec06a22ee14988e43c017808d03000c200001dbf57a2bd949898e4642000e8869a2fa14d88e03a417008b02ec0bc00001dbefa02c414909864592028e7c68e2ea14b08d03aa17b09603080c200001dbe9a62ca14c09a647b20d8ec86b42ec14d09043c418509182fc0b600001dbe37e2e495b4a224a72228f906fc31815488ec3cc17908983140ac00001dbdd882d015249c048c2150f386de31715a89243d419209d83440d000001dbd7a12c514a099c46e20a8eac69a2ed147089038a16308402c80ac00001dbd1a92d6951c9b44822110f046cc2ff14f09003b8184091030c0be00001dbcbb42ce94c89aa47c2080ed86b030114e88e03b217809002f00ae00001dbc5ee2b614489644571fc0e646802ea14488b439216c08b82f00a800001dbbfd62dc956ca0849f2208f84706315159095c3f019209483080be00001dbb9e22d195189d649321a0f446fa31715b09383ca18108d03080ae00001dbb4032c214a897c4602050ec46ac30015288f83b417208b02dc0ac00001dbae092c814a099447320f8ef46c230015089003c818309583180c400001dba8182cc94cc9a84752030e6467a2ef14608c83aa178092832c0c400001dba22a2c194bc99c46c2038e9869e2f914a88b43a217209283100c600001db9c1d2d4153c9ce4802128f346da30414988c83ac17408902dc0bc00001db96322c194749804662080ec46a22f314f09083c018808e02e00ce00001db90392cd152c9cc4852150f346c430815188fc3ba17e09503280cc00001db8a3e2d094bc9c247d2120ef86c830315689583e218909883280ce00001db84692ba147097e4692058ed06bc2f914a08ec3b017308802d80a800001db7e882bd94ac9a447c20e8ef46a42f914e08fc3c218109302dc0b000001db78892cb14b098a46e20a8e9c68c2dc140089838617208682c009c00001db72852d615489e449e2228f8871231d15a093c3c817e09103180ca00001db6c982c894c89ac46d2068eac6922ea14488a839017208d032c0b000001db66952d215449d648b2160f346cc30414b88f43aa17c08802c80b000001db60912d5151c9d44982178f186d030d155892c3ea18c08f82f00be00001db5ad92b5142c9684521f88e8069c2fe15009043d618709382e40a400001db54e42cc14c89be4852160f306ee31d15a09143c818009302f80ca00001db4f042bb947c98a4662088edc6b62f414a08e03bc17b08e02f00b800001db48ff2d395049d248e2168f286d630f15808f83c417d09182e00c000001db431c2c514ac99e46e2060ed06902ea14388b439a17308b02bc0b200001db3d3b2c314dc9b247d2108edc6bc2fa14f88e83aa16e08402d00b200001db374c2c194909844672038ea868e2e314208a03a416e08b02f40b800001db31312d995309c64882100eb46a42eb144889439216508c82d80b600001db2b3a2d195389de48d2110f106ae2fd14f08ec3ae17a09383080c400001db25372ce95009b84842118f386f4312158896c3e018e09283240d600001db1f882a913e49384391f08e046502b41328838372166083829c09600001db19722d714fc9d24842108f086ba2f215008f43a016808982b809800001db137e2cc950c9d44922158eec6b230615289383e418209603180c600001db0d752d094e49b24772108f206c630815289383e619109183200b400001db07992c294b09964612000e786902f514a88bc3a017808b83000ce00001db018b2d695149ce48b2130f046bc2ff14b88e03c218308e83180be00001dafb7d2d295089d048b2138efc6ac2fb14b08ac38416a08902d80a000001daf58f2c714a49944672040e886a62f414788e43ac177091832c0cc00001daef9c2c994dc99c46f2050ea06a42e314788d438a16f08c83040cc00001dae9a92cf95209d448220f0ed46ac2f314388b43b617f09303300c800001dae3a92cb14e89ba4762098ee46b42ef14d08e83ac17d08f03100c600001dadd8f2d795249ce4902120f386ea30d15809403e418909702ec0c600001dad7912d215109b44792100ef86c82ff15109043c4187097033c0c600001dad18b2d415489da48e2118ef06b22f5150891c3c819209103180d200001dacbc12b7145c97245f2018ec86ae2f814b88e03b417b09002fc0c600001dac5922e895bca204a821f0f546fe31815989443e419009903180ca00001dabf9f2cb94fc9c84842118f0c6c230015288f03d618708e02fc0c0000 else (if i < 305 then 0x1ddb15f2de95409d24882158f306c82f514c88d43b017908e82f80ae00001ddab932b7145497644b1f50e606802eb13f88a039817908e03180ba00001dda5b22be948498c4652020ea46a22ed14588d43b417b08e82f00b000001dd9f8b2e395b8a1a4a82250f686ea31616009a03f219109383200e400001dd99b22c1949c96c4611ff0e9c6902f614e08e83ca189097830c0c600001dd93d82bf14949a04702050eb869a2ed14908c03a817508b02c00be00001dd8e242aa943495e4662060eb06a62f414f892c3c617c09003100c600001dd88512bd14609824642058ec86a02fd14a09043b018409302fc0c200001dd82522cb95089ce4832128f1c6c230014788cc3a016e08882dc0b800001dd7c632c814e09a046c2068ebc6b630615189103ca17e09102fc0c800001dd76312e795a8a284b12258f9070832215b89343d418609402ec0a400001dd70332d015249ce4872138f2c6e830315489283dc190098833c0e200001dd6a532be145096845c1fb8e746762e2141888037416808b02e40c400001dd64732c2947096a4601fe8e946842e714508ac39217708f831c0c600001dd5ea62bc94589a046e2078ec86ae2fd14d09143c818409403200bc00001dd58cc2bd94649724662050ea86962ec14808d03aa17a09103040b000001dd52eb2c2949c99c4702078ecc6ae2f414688d43a416e08d82e00c400001dd4d192be148c97c45d1fc0e886902e814308b43a817508e83200c600001dd470c2cd952c9e848a2108ef06be2fb14e09043ba18208f83140be00001dd412c2bd149097a4581fd0ea06922ea142889039416308302b80b200001dd3b0c2e51590a084a82208f786e430a15b891c3d418608e02d80c600001dd353a2b3944496e4531fc8e8068c2e2142088c39e17708e02f00c400001dd2f532c394bc9944732078eec6ae30114c88d039e17608c031c0b200001dd29602c894e49be4832158ed06b42f014388c439c16f09103040b600001dd237e2c3149498e46d2040ed06c02fe14e08fc3ba17808c82d00bc00001dd1d8b2c894e49aa47520e0f086d230515188dc3ac17908c02f00d200001dd17b62b814549664521f98e7466e2db145887438217308b82cc0a600001dd119f2d614f49a847f20f0f106c430115008e83c217e09203200c800001dd0bad2ca94c89b04802108efc6a02fb15009283e619309583300d000001dd05ac2d195109d047f20e8ec46b42fb14d88f03b818509383280b800001dcffcb2cc94f89c648c20f0ef469e2f314a88dc3c017609002d00b800001dcf9f02be946096e4581fb8e6c6962e914888c43ac17a08b82cc0b600001dcf4052c414b49984712060e9c68e2ef14b093c3d018c09803200d200001dcedff2d215049cc4952188f4c6dc30a15109183bc17a08d83240ca00001dce7e82da956c9fc4a12210f5c6ec31715889583e818f09283140b200001dce1cf2d7151c9c248120c8f006c02fb14c09143be18408e03000ba00001dcdbde2c614dc9bc48620d8f186c430715609483e018709703380d000001dcd6142b5943c95a4591fb0e6c68c2e214508bc39016d088029809c00001dcd0462be147497c45b2050eb06a02ed14608a439e16508802c80b800001dcca702c214749864652020eb46962f815288fc3c017b08d83100ba00001dcc46f2d2950c9c047a20d0ed06a02e614508c039417a08d02e00b200001dcbe5f2d395289d048f2118f206d62fd15609143dc19509703300c800001dcb85d2d515509e44962190f406dc30814f09103c817d08f03000c200001dcb26e2c914c498e46320a0ebc6802e414e08fc3ba17f09202fc0c200001dcac8f2bc148498446a2078ea469c2f114f88e83b817f09282f80d600001dca6b42b9947c9824622050e9c6842f314708c43ac17609082ec0c800001dca0aa2d8953c9ea48b21c0f606e031015789183c418509103200ce00001dc9ab22cd14f09ac47d2078ec46922e3140089037a17208f83040b600001dc94c92c714d09a248220a8ef06c0304152091c3d418408d03000ca00001dc8f142ac940c95a45b2048ea86a62ff152091c3be18108f82f00ac00001dc89382bd945c99e4722110ee06b82f914c88e03c018209483240c200001dc83442cc94f89b247e20d8ec86a02f914d89103c017908c82dc0c800001dc7d802b7142096c4651fe0eb06ae2f714b88b03a617208402bc0ae00001dc77642d995389d848420d8f006be2fc15208ec3aa17008682e80c200001dc71772cb14a499246f2048ea86a42f114988e03c217e08c82d80a800001dc6ba42b6943c97846c2058e986862e314288a839817608f82e80c800001dc65a92cc94dc9b648620f8f006c22fe15609203d218509403200c400001dc5fc82be14b89a247520b8ecc6ac2f214788b83b017009003140c000001dc59cc2cf14ec9bc47f20f8ecc6922ef14a88c43b817c08d82e40c800001dc53e42c6949899446a2008e9868c2e514788c43a617608c02f40c400001dc4de82ce95349dc48b2110f1c6de30715989343c417808d82bc0b800001dc47e62cd94f89b64822100eec6aa2ec14b08e43ba17c08902bc0ac00001dc420e2bc943c97c45a2000e7c6882ef14808e43bc18208f02f80b400001dc3c222ca14b49a846e20e0f206ee31415709683dc19109302f80c6000 else 0x1ddf89f0000000000000000000000000000000003ac17d08e03200c800001ddf2c92bc942c9624551fa8e386622e214608dc3a217808882d00b200001ddecb52db15549f249921b8f6c6fa31815c09443e419409c83380d000001dde6ba2c994e89ac4782100ef46be2f814f09103c818308e83040c400001dde0b22d91584a0649b2198f386e630b15409083b418509603040be00001dddad32c414a499246d2088eec6d02fd14d88fc3c617c08e02ec0b800001ddd5062b5142494e44c1f68e6c6882e7143889438a17e08f02e00b000001ddcf152ca14d09a447920e0ec86ac2f114608b839417308982e80be00001ddc9252cb94e49b647320d8ebc6902ea14988e43c417d08f83040ca00001ddc3522be948098a45f1fd0e8868e2e214708d43ae17c09283080ce00001ddbd812ba145497a4662020eac6a62fd15189103d218908a82e80b200001ddb77a2d195049e44872170f246d231115189043b418609403180ba000)))))))))

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



private theorem b299453 : covered 299453 299529 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299529 : covered 299529 299605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299605 : covered 299605 299682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299682 : covered 299682 299758 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299758 : covered 299758 299834 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299834 : covered 299834 299910 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299910 : covered 299910 299987 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b299987 : covered 299987 300063 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300063 : covered 300063 300140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300140 : covered 300140 300216 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300216 : covered 300216 300293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300293 : covered 300293 300369 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300369 : covered 300369 300445 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300445 : covered 300445 300521 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300521 : covered 300521 300598 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300598 : covered 300598 300674 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300674 : covered 300674 300750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300750 : covered 300750 300826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300826 : covered 300826 300903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300903 : covered 300903 300979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b300979 : covered 300979 301055 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301055 : covered 301055 301131 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301131 : covered 301131 301208 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301208 : covered 301208 301284 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301284 : covered 301284 301361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301361 : covered 301361 301437 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301437 : covered 301437 301514 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301514 : covered 301514 301590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301590 : covered 301590 301666 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301666 : covered 301666 301742 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301742 : covered 301742 301819 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301819 : covered 301819 301895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301895 : covered 301895 301971 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b301971 : covered 301971 302047 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302047 : covered 302047 302124 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302124 : covered 302124 302200 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302200 : covered 302200 302276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302276 : covered 302276 302352 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302352 : covered 302352 302429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302429 : covered 302429 302505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302505 : covered 302505 302582 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302582 : covered 302582 302658 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302658 : covered 302658 302735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302735 : covered 302735 302811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302811 : covered 302811 302887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302887 : covered 302887 302963 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b302963 : covered 302963 303040 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303040 : covered 303040 303116 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303116 : covered 303116 303192 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303192 : covered 303192 303268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303268 : covered 303268 303345 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303345 : covered 303345 303421 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303421 : covered 303421 303497 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303497 : covered 303497 303573 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303573 : covered 303573 303650 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303650 : covered 303650 303726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303726 : covered 303726 303802 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303802 : covered 303802 303878 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303878 : covered 303878 303955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b303955 : covered 303955 304031 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304031 : covered 304031 304107 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304107 : covered 304107 304183 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304183 : covered 304183 304260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304260 : covered 304260 304336 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304336 : covered 304336 304412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304412 : covered 304412 304488 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304488 : covered 304488 304565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304565 : covered 304565 304641 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304641 : covered 304641 304717 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304717 : covered 304717 304793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304793 : covered 304793 304870 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304870 : covered 304870 304946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b304946 : covered 304946 305023 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305023 : covered 305023 305099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305099 : covered 305099 305176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305176 : covered 305176 305252 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305252 : covered 305252 305328 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305328 : covered 305328 305404 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305404 : covered 305404 305481 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305481 : covered 305481 305557 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305557 : covered 305557 305633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305633 : covered 305633 305709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305709 : covered 305709 305786 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305786 : covered 305786 305862 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305862 : covered 305862 305938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b305938 : covered 305938 306014 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306014 : covered 306014 306091 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306091 : covered 306091 306167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306167 : covered 306167 306244 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306244 : covered 306244 306320 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306320 : covered 306320 306397 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306397 : covered 306397 306473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306473 : covered 306473 306549 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306549 : covered 306549 306625 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306625 : covered 306625 306702 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306702 : covered 306702 306778 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306778 : covered 306778 306854 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306854 : covered 306854 306930 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b306930 : covered 306930 307007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307007 : covered 307007 307083 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307083 : covered 307083 307159 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307159 : covered 307159 307235 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307235 : covered 307235 307312 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307312 : covered 307312 307388 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307388 : covered 307388 307465 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307465 : covered 307465 307541 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307541 : covered 307541 307618 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307618 : covered 307618 307694 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307694 : covered 307694 307770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307770 : covered 307770 307846 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307846 : covered 307846 307923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307923 : covered 307923 307999 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b307999 : covered 307999 308075 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308075 : covered 308075 308151 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308151 : covered 308151 308228 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308228 : covered 308228 308304 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308304 : covered 308304 308380 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308380 : covered 308380 308456 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308456 : covered 308456 308533 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308533 : covered 308533 308609 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308609 : covered 308609 308685 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308685 : covered 308685 308761 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308761 : covered 308761 308838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308838 : covered 308838 308914 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308914 : covered 308914 308990 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b308990 : covered 308990 309066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309066 : covered 309066 309143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309143 : covered 309143 309219 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309219 : covered 309219 309295 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309295 : covered 309295 309371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309371 : covered 309371 309448 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309448 : covered 309448 309524 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309524 : covered 309524 309600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309600 : covered 309600 309676 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309676 : covered 309676 309753 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309753 : covered 309753 309829 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309829 : covered 309829 309906 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309906 : covered 309906 309982 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b309982 : covered 309982 310059 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310059 : covered 310059 310135 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310135 : covered 310135 310211 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310211 : covered 310211 310287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310287 : covered 310287 310364 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310364 : covered 310364 310440 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310440 : covered 310440 310516 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310516 : covered 310516 310592 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310592 : covered 310592 310669 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310669 : covered 310669 310745 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310745 : covered 310745 310821 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310821 : covered 310821 310897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310897 : covered 310897 310974 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b310974 : covered 310974 311050 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311050 : covered 311050 311127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311127 : covered 311127 311203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311203 : covered 311203 311280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311280 : covered 311280 311356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311356 : covered 311356 311432 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311432 : covered 311432 311508 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311508 : covered 311508 311585 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311585 : covered 311585 311661 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311661 : covered 311661 311737 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311737 : covered 311737 311813 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311813 : covered 311813 311890 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311890 : covered 311890 311966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b311966 : covered 311966 312042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312042 : covered 312042 312118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312118 : covered 312118 312195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312195 : covered 312195 312271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312271 : covered 312271 312348 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312348 : covered 312348 312424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b312424 : covered 312424 312501 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 299453 312501 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b299453 b299529) (joinCoverage b299605 (joinCoverage b299682 b299758))) (joinCoverage (joinCoverage b299834 b299910) (joinCoverage b299987 (joinCoverage b300063 b300140)))) (joinCoverage (joinCoverage (joinCoverage b300216 b300293) (joinCoverage b300369 (joinCoverage b300445 b300521))) (joinCoverage (joinCoverage b300598 (joinCoverage b300674 b300750)) (joinCoverage b300826 (joinCoverage b300903 b300979))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b301055 b301131) (joinCoverage b301208 (joinCoverage b301284 b301361))) (joinCoverage (joinCoverage b301437 b301514) (joinCoverage b301590 (joinCoverage b301666 b301742)))) (joinCoverage (joinCoverage (joinCoverage b301819 b301895) (joinCoverage b301971 (joinCoverage b302047 b302124))) (joinCoverage (joinCoverage b302200 (joinCoverage b302276 b302352)) (joinCoverage b302429 (joinCoverage b302505 b302582)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b302658 b302735) (joinCoverage b302811 (joinCoverage b302887 b302963))) (joinCoverage (joinCoverage b303040 b303116) (joinCoverage b303192 (joinCoverage b303268 b303345)))) (joinCoverage (joinCoverage (joinCoverage b303421 b303497) (joinCoverage b303573 (joinCoverage b303650 b303726))) (joinCoverage (joinCoverage b303802 (joinCoverage b303878 b303955)) (joinCoverage b304031 (joinCoverage b304107 b304183))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b304260 b304336) (joinCoverage b304412 (joinCoverage b304488 b304565))) (joinCoverage (joinCoverage b304641 (joinCoverage b304717 b304793)) (joinCoverage b304870 (joinCoverage b304946 b305023)))) (joinCoverage (joinCoverage (joinCoverage b305099 b305176) (joinCoverage b305252 (joinCoverage b305328 b305404))) (joinCoverage (joinCoverage b305481 (joinCoverage b305557 b305633)) (joinCoverage b305709 (joinCoverage b305786 b305862))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b305938 b306014) (joinCoverage b306091 (joinCoverage b306167 b306244))) (joinCoverage (joinCoverage b306320 b306397) (joinCoverage b306473 (joinCoverage b306549 b306625)))) (joinCoverage (joinCoverage (joinCoverage b306702 b306778) (joinCoverage b306854 (joinCoverage b306930 b307007))) (joinCoverage (joinCoverage b307083 (joinCoverage b307159 b307235)) (joinCoverage b307312 (joinCoverage b307388 b307465))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b307541 b307618) (joinCoverage b307694 (joinCoverage b307770 b307846))) (joinCoverage (joinCoverage b307923 (joinCoverage b307999 b308075)) (joinCoverage b308151 (joinCoverage b308228 b308304)))) (joinCoverage (joinCoverage (joinCoverage b308380 b308456) (joinCoverage b308533 (joinCoverage b308609 b308685))) (joinCoverage (joinCoverage b308761 (joinCoverage b308838 b308914)) (joinCoverage b308990 (joinCoverage b309066 b309143)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b309219 b309295) (joinCoverage b309371 (joinCoverage b309448 b309524))) (joinCoverage (joinCoverage b309600 b309676) (joinCoverage b309753 (joinCoverage b309829 b309906)))) (joinCoverage (joinCoverage (joinCoverage b309982 b310059) (joinCoverage b310135 (joinCoverage b310211 b310287))) (joinCoverage (joinCoverage b310364 (joinCoverage b310440 b310516)) (joinCoverage b310592 (joinCoverage b310669 b310745))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b310821 b310897) (joinCoverage b310974 (joinCoverage b311050 b311127))) (joinCoverage (joinCoverage b311203 (joinCoverage b311280 b311356)) (joinCoverage b311432 (joinCoverage b311508 b311585)))) (joinCoverage (joinCoverage (joinCoverage b311661 b311737) (joinCoverage b311813 (joinCoverage b311890 b311966))) (joinCoverage (joinCoverage b312042 (joinCoverage b312118 b312195)) (joinCoverage b312271 (joinCoverage b312348 b312424))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 299453 ≤ index 575000000/512 := by decide +kernel
private theorem starting_value : fast 575000000=30086302 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 575000000=30086302) (n : ℕ) (low : 575000000≤n) (bound : n≤600000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=575000000
    · rw [first,anchor]
      exact starting_value
    · have past : 575000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤600000000 by omega)
        have within : index n / 512 < 312501 := by omega
        have lower : index 575000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤600000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ575000000To600000000
