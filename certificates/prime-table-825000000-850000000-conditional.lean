import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ825000000To850000000

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




private def radical : ℕ := 0xfe9f5d7eca8d151fea5c2ccd9a7bbff3c4f9c52e04f87c9cce15362ffdb377994d5264d8f2015f506199bc9cff233ecbe9cb8e90d9640786041ba37aa49a7c36b66989cdcba4001e3318a18175b5cbb687c8bfc1db369d9a4f0e7b34b415280106d93c0f05034f9fd5d463e97e7110e7183199d833e16cb72755f2126e26858b384ccc16ebf269b65312c11f359ef4fb9b948268a2bfe5b0debddf41c6a76fe84b43380cbbe91c28bc82fa9a877257836ff3ad8eecebbde5dede629accddeef6ac9232136b464863efca0819bea835d8277d0c99e56d2163b445827dad8f64f93d00d6d5eb08134eca783c2f3d945b14b639af0d622bd2e1765b44e96c2e18d6b7aa585b5681c65e570cfb8ef3a23752e90432212c0685e8967897ae8d478b0f5c56b70a753a8566717b54b9b83644e618254bc65f531b802bd68ddcb6636a43c585cb144119da15767668fa7d7dd4567bc22f1def953fe658734a4b4180a6bb042c7061aec920ac8dc479237dd1f3d10fa78ddbc8ed863a96307dda4187023809db88cdc52cb43c2966e4a0d8534c94f57ae62424d5e9375679bc413f00acc022c606f0abe0a5b6dea33f4a2ca13193980e2073249e6960654ce44c13e6f747108e4f2e8178c3516a217c273d80f22307c16f6c0f790b57b993e878a519a27a27c51ac1fb9feceb23572ed20fbcb41a516491e59676fb4347002be75edaeb3b411a4ecf60f0a209181859684c2f8fdf8c82df47fa2bd422b788f86be3886d556edb199df463f4820f0b005471ae3ca6e756cf8087c695a95335af5d7669af611582a6d537cc28dcf50554c47eb35a4ed9c8256e80cd0e7f62ee2f12f42d938733987559300bdedbb326701e76d0be22aefeb3f803586e40b2bf1d689bc9925b23d2a89942a5c937466e4a87d16bdafbcf37e670597e573016c0bce477d23cfd3dc41106ffd38f7b2eecc35729c9d87547b43ba5ce056200a19f0bdeea66cfe8f927d801a24a8dd09cdb0f4fea6aa24004eb57a8d768fe7e5ca43b33a8b7a2c4729a86d0034f57e6d672f14b25abf6c99e2cd3656f1d07c70c7c8e514e3a3902b0fb271ac347b041bf6e0da2df172e8be643805bb832de44ef10757f26daa32e40247a9a1443aef9587d43daeb85d5b80522f0ed755694776aa2629ea27b7fd78f4e57a4912cdb7ad2c00f8a4e148053e99030de5a5a35c77c1b6c7538d21507647c778a4c93e005c7dd67eecf56e4588adc57b359fa3416585c3dcfe7c3ed8dc888b9f68bb2946f703e51a33b648609a1adeb9cd5a79ac3c34d1a00dea0ddf92d2fb202d0038f50a67a1c84dc7de246843e9f35d2293bc08d491d4c864f71250e48fc167580b4d0d9e9481248d7c8ee58acbf94dd51ef29d101b40368d6724a9d6b0c165b01ea2f508d4b7a28526ebece4a4b081b543fe417bab2fac59bbecbf2bd7c78ba0c11195e6c51483516de74eb7e4f206b76167ce6e26c03b2c8ca7c943b0c153bffeb2b1b2a0565892ae4df6ee5a486fdfa76ccebca4f5dae2e3d724ec3211d6c1985a00aace3b43235b69b4d5aebfebe79a56b79ab16293d542937436af95c3406f70ed3a686587d38f266c1bc2fd57189ef8dd36fb49cc7cd8ec3ac087cfaf1614ccf39d8615819da7b3045d5da6707da99e6fb9deb7c334c56cdab417c71a5efa2501bd227f44d9fc6f0f929dc428a0f5750513b89ff498bc372137efe3ac9a8c103c27406f81fc25b54d27b8d21e017fff54ab2b27af3abdb110435633df1e7217a1f06c584bbc12104226e7a04ce927f53e015f919b2c8ec0d9f1b6f783119ea1a0786cfd1009cf15152f995c0d4e95c5c69763e119872daa241cef755a79d633b1ee7d3e8455d40ec094be389c931aaa8244d2d379f63ac2704cfe62861043c5a1623b2fe4b0dcd53840222c2419453045053ee1ab45406f709be1a614c0b3c0e3bcbd490f40a75dbe1c5545b80f5935e0cf49724a8940c5729128665d4fa3017bd29154d4fd3624bce9503b45b98d07c1db7e22c201632d999f5538bcbe836fbc3128fae110a8e2c975b7091a4975545813faa3f763ba67b029808e5e26ca050f199fa8c846ceade57253cbafee27ca1f991e680be68244421608f07ef3bec42bb443b9142991e776d91ea62c56b1b22309c6a0f8c98d8815e1cac0764cdcaa6144087b6a1d95a769c201ddb6802fc2f712419b79295835701a1765e84a1d7984379ef72d0c36885f5e071fbab27ae345d6abfc264f44d5a3642c463db17d262260d68bcdca4d4b62fd19c68743bcc2c5a7071aaab4522f22693560c23d7a8d5843ec0c2e620516f9c199eeb5008ce938912354a0bef228ef1e30ae4a34eca4d0fd3628ea7bb5d39d5b679fc68f908a04e81b4898b6f6d57198467f29e76a23a780379ee8d2ab40142b7690d8d8c99750c67b55f50824c482e8e8307f68af8fc4d2d3202a53c93fe4cab9fa03d1670017e8e615c7e27d875f775ce250033a23bf323c3b3c031210145e86bc480055e1022c5c2790f35cac67f7dbcf96e9723cc48a54855281ae216b0301c9f3edb111a8e66ff8362aabba99fd31f0a8002535c5c2fe5c40d278490ec393f8dc063d3c96b65e1623c7fb910b67838e141f5d8b65a3f726d1d61457e0d90c5744895ed95a8aa29873ba2ff63a76fd673b403982b4f19f0f3668e5993216bfb82bacd036180df4994db58f2c15779a020332c449624850b6023c2cb132699685a50280fefa8b7373671a505a9ba4569cb298deca75ab35557132ff048e5c651991e14f2012ac9a43412d2191ebe44e710e08dfbea5ee0dcda58110e9c41360874fb486426514cc345a1c548522e5a25d922d7942a4f35a517ecf4d1ee6096e32cb6798bace17e3f50dcb0a642be2fd13dd464c40d8e592e1ad3e1706988bd30133a734db6ddb118db5f9104b43455740c1fdeb1a3466bfa1ab02f7afb70a38952c45ed2146bda42812e77f5a4b1bb9481a9217d6a4689218f841a2f24d71d2eef58269a62a0b5753ac816a8849913404afb9b8c747b8cf3f06cb7c3830fe7221e282452af6d449285f4f34d6c0e7595e96551dde827b5f80210bc973659069f83e7e034f4eb2cd3ef5d556ad18addccf9c81043e139b471f31daf57cffe10ae72eba01fc6b6332c14f4dd7d6900d0bfdc6d2de2eadd2c43c8a54442320fa7fc4a7218c86ffffdf1fb716efca5d3f4eec7ab797128d5e5ef4237d89ce299f947dcad18af03bf9411e7e1fe1a5b1a9e1f1414c8f6748b4b930ea67730865d33d245b0a6062a6e32d84f69d39a2b9ededb878d5d3c94e475c8d23565fedc6be3798eaac52d616ac441de6ec37b83ba32e6663a62431d70e32ec84426487b76909d699f8d85ab6f06de0275bebb66121d458d616361d17d27929e9dc8557efcf77e6f6528e6c7454d495daff561849515905a19e9fe91e9020d7a36e9315a779acd1e8bb7f94ffd83412779474297e7201aed74413c034190a1de6d0af10d6ff5c678f156bb6aa3bbdb51114f65be643d1710d7ec79275517f5b742d48392068776cfd8487d1cb0534256829c5db4dc96755c87e673c85b65a39f15152d0a85e4b036f0899a4605706e8c31024e08d7a7a55eb1235a9238e254921e4fd5cb8ed5a07fff75cb3ccea8188911fa6d24a8e19cb5e2b9779953fd881cdcb223dbf3bf2e7e82e0b38c1b95a82a073d2cfb99eac1bcc961494fcf34ed6a800ec83692e64ffafe22899df1d9767d797c5bbb412add871ae7a125a7b1db02d1952de696eb71ea76b2da6f1d7b242fe9dcb68269e6b17eb03ee4b4955131ade3b62f06d9f7fc82e21d511139c6549eef03bc265a3a9957c155b73937628870c93ecac162e5b4e8d3f28bd5ab80f5110833885ae912578f1de97fbd60dab4b2f03cec9abfa311f7d96ae219b01cb3f44d1dca70b5f0e70f6391a40779e4e128bf77e52ba737baac3290c569c1c1310d5c248797481d6eb79f63c8462e5ffc3dc2408e35a35cd69fc60c41d4d51674a0d0ff89cb9e38427c33b3f595cef02a0dd876892724a01c3345d9f73c5ce8f4e88c11710938d78cb6caea48edb64eb834427406873873ba9602b1cd0f455ccaae54ff32848848742aafc1d5d22a3181d634fde354919353b0132abe29d3d05dea5fd4460b1af6a690b21795d1514a66e1ff24a1667a1f026ad97a2dc19c52753536fb9274b011706b9c74a971f44fbc101673376efb721f1a2040b8f540ecdc7900fe7b8c2319e85607e7d037e33037497b03f9e39be699be50a7c90b2186e64da00d214aa778010a67c7cce3ca5848780d778b84b9780a0e1e4c06e3e4c37edfadadb8c187ac93a80112fe9a009c6a0fcba35d96036e0e51789949602065e983282208b77e164574e46e69bc18839b0197f225ee4df029bf182df47519d858695d595b31931e1b4fc047b3443f7f592f441d0ffaf80645666c81d3a554ed17c96928585cb2ad0be7cec943bab11247fd995df9693703c7e0fea16714320a01c5fb27a322a01d7077ece9f6575c07bab2de37751f3b388e7cb2c464183c9ec16f30d2c7c0b9c96d3ceb18e4cfa44c4ecb0c48477457b09fee4231dcf604cba34aec25410bcfdfb39d9cd6704b68bc9fa4f39a5c582a6726f8c4afc503e99944017de1a87405d806d2bd4b731b4531d736a43adbc3dfd3a7baead75766e864575c1c90520bd725e82f290f0ed43f1204f3633161d1d44aa52469f651076bb2f64fb3eb83c8b762e2299e1fcce673cb32e8ffba6f7eee63c011fb59d5e8174b067df96755f07f47d0a86363e15e61fbef16a7d0cc1c2fe095e9459dd6c55eca33122d7e8898bb42dc2fb6bf77ea4f0d3ba0e4b090c79f4e9191150207f3bcb069babe3a10bd42550539ff3cc9bb9fd766f11dc384d11736a882e1d95ccf4fa75d65f13a89852273f32cc02d32ab4502146cd96cd965c8a194d9cda1b050ef37493baf74bc1e86618b226529ed8539bddc4bbdda1a5dd3525f19a20d9c838eaaba9129681da3f9788ed983a2b3617a048dac2a6789fa4569ee25cba3bfc53103aa544c061a588351965dbecc5a5a0a76f6769d683cac3fd0dc696ee21f71d159e15b693f5286538b4d148437557cfa65460477cff23fb1e43cea4f1428a5aa35481848dbd4b5d6cff72c2c31662d1ce925e709416d24aa70df788ed55aae5d68c33e8ba85f852d561d98107ee74e13486a35d199f6857893f7e3dad6479bb9d4223d58b75f4e69334565f90d86d650161ed328f87ed168682560ae143d71ce1bf65ed579eb491161bad385d75005938027570625b63bd542ff5f4dacfcf3ccd645802b65ccb1e8bc727dce3bfaeb31c831bd9064cbf2ac048fea65dc1538f4e159e83bd18835eba8c49114448556cb73afd8852c205675e152ca3a43d585f11d055565e4dfb11f12c0e63a86c1ca899b47ad26ea233d1338ac8b6e8da50ee285446dc59310aa377c0aea76d80953121b95d168aba139a86b229e7af9b1b30ecca5f83552fbe5adbdbeecaa32ddf8d16f03561aa25c48c4ac2c4b46ba84b66337d1da6dbaf182db99dc2c029b0f55c40fd4e909ef8fec561f074c6c395e9fd58dbdff420c0cbf07dca166e51b43ad73d8583fd3fc7e17eaac233c7461c72ebba3269d1841f702c0d138a0a52ce31a89883e1166298acc588f270405dcb6782b4018a20570d375a11e57e44eeca362f34a6bcdaadb3f01e386a53e0c3712e428f09d011ec98a145f749e50bf26c747c08b01eab9cbb6ef939fd37958dce3ced5523a635202378ce621e71ea37489a50aa09e940210715d4974f11e590288a5d253664fc385eb6c5492e9e36c718ac839da34640a499c9cf8b536c644495f3dfc84dedaf0a1ea886fd105400fb6e753b5d741e020b802d293cec9360d2943be4e0091aa94700c693eb558b0e9971d1c4ee130dc6ffef45fccb934c2ab9e92eebdc2740d8fd5026708c4a8ed29ef34e39d3c063be3a22d806cf0de77735b1f0186aaa039ef5d40655a3b2649f0b4ea90e5be2980f5dcd9636a19288ff45b7e45230503b5ce244bcf7a6b0200bb6754be2b9f26f64be10ae5c899a3c9f90c79756154f3780e6ec03697e5def4d79cd0e043752c995ba596c445b50b115326f99bdab67a5788aec2e4692b53dc3320a6bc890d520a4af8b352b137749825e702a0ae24ae85526875f5e724c288b1b66ac70ae15aa253db45c1c93cef5f8206b71f046f72c621ea32fcdc8c9afed26a0568a0b2c5131f49be214277ff8946b3ceb77e63053b50c2f20d895acf434ac7c90a7f99fa862e179ad526973fae2489ce045b930e02cdb46fe335fe634af63b09a51abb33e2d28187e5e4a476744c807204f614e49951beb1187f5ee9967d0efb3e17a12d33e286bc73db095a109798b935d3d6b4ac3a2fd2bb36d2b8f200b9e08275add873afc22d61675651a4b8e5c9a9b2e55805801c97d7a9326729a884c495ac17df385d5dae56ec1f683f7f3c6dc6f20b42b7d75a7f96347878edfcc95168203a3247dcb4ee245e3c8e58560f4d52d8abc32a5ca44e9b85a54415c9ae413fe4ae2a0a28fa7bd44ff8fd9e0e1535983977b7c1c8e3d83f69e613a198d12ed6d62a4c0a92224c1142d1d5da34047c1009d5c81b90485b6003b8c1f9fd4b680eea5eb9ff39157d350fdbfd4efe2141f22259845c333955f9b6acb6beef43dfaf872d3833a05ef06086a82a6ee23da19d1f4c8f7b78355f54e77ccc3041077936b245bd405699e2d7d2e6f567149df93cf680e85b30bb4aa38112ded6083926e5b16fb56258c911782ad827605a0e4002e071f4f42e399c1ac2e1d1d036ca568b3f08f002fb61befee525aa6f5685f589982650c6284e7a10dd69f966f4b7aee06a52e3cadaab38708dd7b4061f0dcec2b83d823799feb59d47f967faaa1539bb61cb2c3a1e340e6abdc23fb8a2161012fe29bcf8dcad891f1cbbedb35d4ffd00c0dc440945fb4420f052ba3343f88da4263a32b8814e5e8ad5ccb3a99ba43b843704e06fe7c08b74e7e4d915ecd62cea371145d3e41e19da140149e54c89b14c86461df619826a58e9312cb85b0125309b28674d2a6741a72c81817f62a6d35df51b0cc86bd9bbdd076f9b1d0df017cb38832c690912f08659459f3909afb3fec93c0d8828b1bb1e939fc32ce275054f1e9480c75965c79b03f82b9a4b8977e1c48c31da950cf2284fe408a358aaafa0fda13d6342b29f11ee74d2beb2d84e7191503cb17713687bf045859a3a68ab5c741e9251d2c159005aea6f44366402dffc36ff8f06a5ba5161af354161a377eacb4874eb8eb244abe225390fee58b782982f4482fe9360f4eece33a69904c0207e935e1bb48ba22706fbefc000c3910e

private def light (n : ℕ) : Bool :=
  if n≤170 then decide n.Prime else n.gcd 7257415615307998967396728211129263114716991681296451376543577798900561843401706157852350749242617459511490991237838520776666022565442753025328900773207510902400430280058295603966612599658257104398558294257568966313439612262571094946806711205568880457193340212661452800000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤29154) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 170 = 7257415615307998967396728211129263114716991681296451376543577798900561843401706157852350749242617459511490991237838520776666022565442753025328900773207510902400430280058295603966612599658257104398558294257568966313439612262571094946806711205568880457193340212661452800000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 170 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤29154 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 56 := by unfold smallValid; decide +kernel

private theorem sp56 : smallValid 56 57 := by unfold smallValid; decide +kernel

private theorem sp113 : smallValid 113 57 := by unfold smallValid; decide +kernel

private theorem sp170 : smallValid 170 57 := by unfold smallValid; decide +kernel

private theorem sp227 : smallValid 227 57 := by unfold smallValid; decide +kernel

private theorem sp284 : smallValid 284 57 := by unfold smallValid; decide +kernel

private theorem sp341 : smallValid 341 57 := by unfold smallValid; decide +kernel

private theorem sp398 : smallValid 398 57 := by unfold smallValid; decide +kernel

private theorem sp455 : smallValid 455 57 := by unfold smallValid; decide +kernel

private theorem sp512 : smallValid 512 57 := by unfold smallValid; decide +kernel

private theorem sp569 : smallValid 569 57 := by unfold smallValid; decide +kernel

private theorem sp626 : smallValid 626 57 := by unfold smallValid; decide +kernel

private theorem sp683 : smallValid 683 57 := by unfold smallValid; decide +kernel

private theorem sp740 : smallValid 740 57 := by unfold smallValid; decide +kernel

private theorem sp797 : smallValid 797 57 := by unfold smallValid; decide +kernel

private theorem sp854 : smallValid 854 57 := by unfold smallValid; decide +kernel

private theorem sp911 : smallValid 911 56 := by unfold smallValid; decide +kernel

private theorem sp967 : smallValid 967 57 := by unfold smallValid; decide +kernel

private theorem sp1024 : smallValid 1024 57 := by unfold smallValid; decide +kernel

private theorem sp1081 : smallValid 1081 57 := by unfold smallValid; decide +kernel

private theorem sp1138 : smallValid 1138 57 := by unfold smallValid; decide +kernel

private theorem sp1195 : smallValid 1195 57 := by unfold smallValid; decide +kernel

private theorem sp1252 : smallValid 1252 57 := by unfold smallValid; decide +kernel

private theorem sp1309 : smallValid 1309 57 := by unfold smallValid; decide +kernel

private theorem sp1366 : smallValid 1366 57 := by unfold smallValid; decide +kernel

private theorem sp1423 : smallValid 1423 57 := by unfold smallValid; decide +kernel

private theorem sp1480 : smallValid 1480 57 := by unfold smallValid; decide +kernel

private theorem sp1537 : smallValid 1537 57 := by unfold smallValid; decide +kernel

private theorem sp1594 : smallValid 1594 57 := by unfold smallValid; decide +kernel

private theorem sp1651 : smallValid 1651 57 := by unfold smallValid; decide +kernel

private theorem sp1708 : smallValid 1708 57 := by unfold smallValid; decide +kernel

private theorem sp1765 : smallValid 1765 57 := by unfold smallValid; decide +kernel

private theorem sp1822 : smallValid 1822 56 := by unfold smallValid; decide +kernel

private theorem sp1878 : smallValid 1878 57 := by unfold smallValid; decide +kernel

private theorem sp1935 : smallValid 1935 57 := by unfold smallValid; decide +kernel

private theorem sp1992 : smallValid 1992 57 := by unfold smallValid; decide +kernel

private theorem sp2049 : smallValid 2049 57 := by unfold smallValid; decide +kernel

private theorem sp2106 : smallValid 2106 57 := by unfold smallValid; decide +kernel

private theorem sp2163 : smallValid 2163 57 := by unfold smallValid; decide +kernel

private theorem sp2220 : smallValid 2220 57 := by unfold smallValid; decide +kernel

private theorem sp2277 : smallValid 2277 57 := by unfold smallValid; decide +kernel

private theorem sp2334 : smallValid 2334 57 := by unfold smallValid; decide +kernel

private theorem sp2391 : smallValid 2391 57 := by unfold smallValid; decide +kernel

private theorem sp2448 : smallValid 2448 57 := by unfold smallValid; decide +kernel

private theorem sp2505 : smallValid 2505 57 := by unfold smallValid; decide +kernel

private theorem sp2562 : smallValid 2562 57 := by unfold smallValid; decide +kernel

private theorem sp2619 : smallValid 2619 57 := by unfold smallValid; decide +kernel

private theorem sp2676 : smallValid 2676 57 := by unfold smallValid; decide +kernel

private theorem sp2733 : smallValid 2733 56 := by unfold smallValid; decide +kernel

private theorem sp2789 : smallValid 2789 57 := by unfold smallValid; decide +kernel

private theorem sp2846 : smallValid 2846 57 := by unfold smallValid; decide +kernel

private theorem sp2903 : smallValid 2903 57 := by unfold smallValid; decide +kernel

private theorem sp2960 : smallValid 2960 57 := by unfold smallValid; decide +kernel

private theorem sp3017 : smallValid 3017 57 := by unfold smallValid; decide +kernel

private theorem sp3074 : smallValid 3074 57 := by unfold smallValid; decide +kernel

private theorem sp3131 : smallValid 3131 57 := by unfold smallValid; decide +kernel

private theorem sp3188 : smallValid 3188 57 := by unfold smallValid; decide +kernel

private theorem sp3245 : smallValid 3245 57 := by unfold smallValid; decide +kernel

private theorem sp3302 : smallValid 3302 57 := by unfold smallValid; decide +kernel

private theorem sp3359 : smallValid 3359 57 := by unfold smallValid; decide +kernel

private theorem sp3416 : smallValid 3416 57 := by unfold smallValid; decide +kernel

private theorem sp3473 : smallValid 3473 57 := by unfold smallValid; decide +kernel

private theorem sp3530 : smallValid 3530 57 := by unfold smallValid; decide +kernel

private theorem sp3587 : smallValid 3587 57 := by unfold smallValid; decide +kernel

private theorem sp3644 : smallValid 3644 56 := by unfold smallValid; decide +kernel

private theorem sp3700 : smallValid 3700 57 := by unfold smallValid; decide +kernel

private theorem sp3757 : smallValid 3757 57 := by unfold smallValid; decide +kernel

private theorem sp3814 : smallValid 3814 57 := by unfold smallValid; decide +kernel

private theorem sp3871 : smallValid 3871 57 := by unfold smallValid; decide +kernel

private theorem sp3928 : smallValid 3928 57 := by unfold smallValid; decide +kernel

private theorem sp3985 : smallValid 3985 57 := by unfold smallValid; decide +kernel

private theorem sp4042 : smallValid 4042 57 := by unfold smallValid; decide +kernel

private theorem sp4099 : smallValid 4099 57 := by unfold smallValid; decide +kernel

private theorem sp4156 : smallValid 4156 57 := by unfold smallValid; decide +kernel

private theorem sp4213 : smallValid 4213 57 := by unfold smallValid; decide +kernel

private theorem sp4270 : smallValid 4270 57 := by unfold smallValid; decide +kernel

private theorem sp4327 : smallValid 4327 57 := by unfold smallValid; decide +kernel

private theorem sp4384 : smallValid 4384 57 := by unfold smallValid; decide +kernel

private theorem sp4441 : smallValid 4441 57 := by unfold smallValid; decide +kernel

private theorem sp4498 : smallValid 4498 57 := by unfold smallValid; decide +kernel

private theorem sp4555 : smallValid 4555 56 := by unfold smallValid; decide +kernel

private theorem sp4611 : smallValid 4611 57 := by unfold smallValid; decide +kernel

private theorem sp4668 : smallValid 4668 57 := by unfold smallValid; decide +kernel

private theorem sp4725 : smallValid 4725 57 := by unfold smallValid; decide +kernel

private theorem sp4782 : smallValid 4782 57 := by unfold smallValid; decide +kernel

private theorem sp4839 : smallValid 4839 57 := by unfold smallValid; decide +kernel

private theorem sp4896 : smallValid 4896 57 := by unfold smallValid; decide +kernel

private theorem sp4953 : smallValid 4953 57 := by unfold smallValid; decide +kernel

private theorem sp5010 : smallValid 5010 57 := by unfold smallValid; decide +kernel

private theorem sp5067 : smallValid 5067 57 := by unfold smallValid; decide +kernel

private theorem sp5124 : smallValid 5124 57 := by unfold smallValid; decide +kernel

private theorem sp5181 : smallValid 5181 57 := by unfold smallValid; decide +kernel

private theorem sp5238 : smallValid 5238 57 := by unfold smallValid; decide +kernel

private theorem sp5295 : smallValid 5295 57 := by unfold smallValid; decide +kernel

private theorem sp5352 : smallValid 5352 57 := by unfold smallValid; decide +kernel

private theorem sp5409 : smallValid 5409 57 := by unfold smallValid; decide +kernel

private theorem sp5466 : smallValid 5466 56 := by unfold smallValid; decide +kernel

private theorem sp5522 : smallValid 5522 57 := by unfold smallValid; decide +kernel

private theorem sp5579 : smallValid 5579 57 := by unfold smallValid; decide +kernel

private theorem sp5636 : smallValid 5636 57 := by unfold smallValid; decide +kernel

private theorem sp5693 : smallValid 5693 57 := by unfold smallValid; decide +kernel

private theorem sp5750 : smallValid 5750 57 := by unfold smallValid; decide +kernel

private theorem sp5807 : smallValid 5807 57 := by unfold smallValid; decide +kernel

private theorem sp5864 : smallValid 5864 57 := by unfold smallValid; decide +kernel

private theorem sp5921 : smallValid 5921 57 := by unfold smallValid; decide +kernel

private theorem sp5978 : smallValid 5978 57 := by unfold smallValid; decide +kernel

private theorem sp6035 : smallValid 6035 57 := by unfold smallValid; decide +kernel

private theorem sp6092 : smallValid 6092 57 := by unfold smallValid; decide +kernel

private theorem sp6149 : smallValid 6149 57 := by unfold smallValid; decide +kernel

private theorem sp6206 : smallValid 6206 57 := by unfold smallValid; decide +kernel

private theorem sp6263 : smallValid 6263 57 := by unfold smallValid; decide +kernel

private theorem sp6320 : smallValid 6320 57 := by unfold smallValid; decide +kernel

private theorem sp6377 : smallValid 6377 56 := by unfold smallValid; decide +kernel

private theorem sp6433 : smallValid 6433 57 := by unfold smallValid; decide +kernel

private theorem sp6490 : smallValid 6490 57 := by unfold smallValid; decide +kernel

private theorem sp6547 : smallValid 6547 57 := by unfold smallValid; decide +kernel

private theorem sp6604 : smallValid 6604 57 := by unfold smallValid; decide +kernel

private theorem sp6661 : smallValid 6661 57 := by unfold smallValid; decide +kernel

private theorem sp6718 : smallValid 6718 57 := by unfold smallValid; decide +kernel

private theorem sp6775 : smallValid 6775 57 := by unfold smallValid; decide +kernel

private theorem sp6832 : smallValid 6832 57 := by unfold smallValid; decide +kernel

private theorem sp6889 : smallValid 6889 57 := by unfold smallValid; decide +kernel

private theorem sp6946 : smallValid 6946 57 := by unfold smallValid; decide +kernel

private theorem sp7003 : smallValid 7003 57 := by unfold smallValid; decide +kernel

private theorem sp7060 : smallValid 7060 57 := by unfold smallValid; decide +kernel

private theorem sp7117 : smallValid 7117 57 := by unfold smallValid; decide +kernel

private theorem sp7174 : smallValid 7174 57 := by unfold smallValid; decide +kernel

private theorem sp7231 : smallValid 7231 57 := by unfold smallValid; decide +kernel

private theorem sp7288 : smallValid 7288 56 := by unfold smallValid; decide +kernel

private theorem sp7344 : smallValid 7344 57 := by unfold smallValid; decide +kernel

private theorem sp7401 : smallValid 7401 57 := by unfold smallValid; decide +kernel

private theorem sp7458 : smallValid 7458 57 := by unfold smallValid; decide +kernel

private theorem sp7515 : smallValid 7515 57 := by unfold smallValid; decide +kernel

private theorem sp7572 : smallValid 7572 57 := by unfold smallValid; decide +kernel

private theorem sp7629 : smallValid 7629 57 := by unfold smallValid; decide +kernel

private theorem sp7686 : smallValid 7686 57 := by unfold smallValid; decide +kernel

private theorem sp7743 : smallValid 7743 57 := by unfold smallValid; decide +kernel

private theorem sp7800 : smallValid 7800 57 := by unfold smallValid; decide +kernel

private theorem sp7857 : smallValid 7857 57 := by unfold smallValid; decide +kernel

private theorem sp7914 : smallValid 7914 57 := by unfold smallValid; decide +kernel

private theorem sp7971 : smallValid 7971 57 := by unfold smallValid; decide +kernel

private theorem sp8028 : smallValid 8028 57 := by unfold smallValid; decide +kernel

private theorem sp8085 : smallValid 8085 57 := by unfold smallValid; decide +kernel

private theorem sp8142 : smallValid 8142 57 := by unfold smallValid; decide +kernel

private theorem sp8199 : smallValid 8199 56 := by unfold smallValid; decide +kernel

private theorem sp8255 : smallValid 8255 57 := by unfold smallValid; decide +kernel

private theorem sp8312 : smallValid 8312 57 := by unfold smallValid; decide +kernel

private theorem sp8369 : smallValid 8369 57 := by unfold smallValid; decide +kernel

private theorem sp8426 : smallValid 8426 57 := by unfold smallValid; decide +kernel

private theorem sp8483 : smallValid 8483 57 := by unfold smallValid; decide +kernel

private theorem sp8540 : smallValid 8540 57 := by unfold smallValid; decide +kernel

private theorem sp8597 : smallValid 8597 57 := by unfold smallValid; decide +kernel

private theorem sp8654 : smallValid 8654 57 := by unfold smallValid; decide +kernel

private theorem sp8711 : smallValid 8711 57 := by unfold smallValid; decide +kernel

private theorem sp8768 : smallValid 8768 57 := by unfold smallValid; decide +kernel

private theorem sp8825 : smallValid 8825 57 := by unfold smallValid; decide +kernel

private theorem sp8882 : smallValid 8882 57 := by unfold smallValid; decide +kernel

private theorem sp8939 : smallValid 8939 57 := by unfold smallValid; decide +kernel

private theorem sp8996 : smallValid 8996 57 := by unfold smallValid; decide +kernel

private theorem sp9053 : smallValid 9053 57 := by unfold smallValid; decide +kernel

private theorem sp9110 : smallValid 9110 56 := by unfold smallValid; decide +kernel

private theorem sp9166 : smallValid 9166 57 := by unfold smallValid; decide +kernel

private theorem sp9223 : smallValid 9223 57 := by unfold smallValid; decide +kernel

private theorem sp9280 : smallValid 9280 57 := by unfold smallValid; decide +kernel

private theorem sp9337 : smallValid 9337 57 := by unfold smallValid; decide +kernel

private theorem sp9394 : smallValid 9394 57 := by unfold smallValid; decide +kernel

private theorem sp9451 : smallValid 9451 57 := by unfold smallValid; decide +kernel

private theorem sp9508 : smallValid 9508 57 := by unfold smallValid; decide +kernel

private theorem sp9565 : smallValid 9565 57 := by unfold smallValid; decide +kernel

private theorem sp9622 : smallValid 9622 57 := by unfold smallValid; decide +kernel

private theorem sp9679 : smallValid 9679 57 := by unfold smallValid; decide +kernel

private theorem sp9736 : smallValid 9736 57 := by unfold smallValid; decide +kernel

private theorem sp9793 : smallValid 9793 57 := by unfold smallValid; decide +kernel

private theorem sp9850 : smallValid 9850 57 := by unfold smallValid; decide +kernel

private theorem sp9907 : smallValid 9907 57 := by unfold smallValid; decide +kernel

private theorem sp9964 : smallValid 9964 57 := by unfold smallValid; decide +kernel

private theorem sp10021 : smallValid 10021 56 := by unfold smallValid; decide +kernel

private theorem sp10077 : smallValid 10077 57 := by unfold smallValid; decide +kernel

private theorem sp10134 : smallValid 10134 57 := by unfold smallValid; decide +kernel

private theorem sp10191 : smallValid 10191 57 := by unfold smallValid; decide +kernel

private theorem sp10248 : smallValid 10248 57 := by unfold smallValid; decide +kernel

private theorem sp10305 : smallValid 10305 57 := by unfold smallValid; decide +kernel

private theorem sp10362 : smallValid 10362 57 := by unfold smallValid; decide +kernel

private theorem sp10419 : smallValid 10419 57 := by unfold smallValid; decide +kernel

private theorem sp10476 : smallValid 10476 57 := by unfold smallValid; decide +kernel

private theorem sp10533 : smallValid 10533 57 := by unfold smallValid; decide +kernel

private theorem sp10590 : smallValid 10590 57 := by unfold smallValid; decide +kernel

private theorem sp10647 : smallValid 10647 57 := by unfold smallValid; decide +kernel

private theorem sp10704 : smallValid 10704 57 := by unfold smallValid; decide +kernel

private theorem sp10761 : smallValid 10761 57 := by unfold smallValid; decide +kernel

private theorem sp10818 : smallValid 10818 57 := by unfold smallValid; decide +kernel

private theorem sp10875 : smallValid 10875 57 := by unfold smallValid; decide +kernel

private theorem sp10932 : smallValid 10932 56 := by unfold smallValid; decide +kernel

private theorem sp10988 : smallValid 10988 57 := by unfold smallValid; decide +kernel

private theorem sp11045 : smallValid 11045 57 := by unfold smallValid; decide +kernel

private theorem sp11102 : smallValid 11102 57 := by unfold smallValid; decide +kernel

private theorem sp11159 : smallValid 11159 57 := by unfold smallValid; decide +kernel

private theorem sp11216 : smallValid 11216 57 := by unfold smallValid; decide +kernel

private theorem sp11273 : smallValid 11273 57 := by unfold smallValid; decide +kernel

private theorem sp11330 : smallValid 11330 57 := by unfold smallValid; decide +kernel

private theorem sp11387 : smallValid 11387 57 := by unfold smallValid; decide +kernel

private theorem sp11444 : smallValid 11444 57 := by unfold smallValid; decide +kernel

private theorem sp11501 : smallValid 11501 57 := by unfold smallValid; decide +kernel

private theorem sp11558 : smallValid 11558 57 := by unfold smallValid; decide +kernel

private theorem sp11615 : smallValid 11615 57 := by unfold smallValid; decide +kernel

private theorem sp11672 : smallValid 11672 57 := by unfold smallValid; decide +kernel

private theorem sp11729 : smallValid 11729 57 := by unfold smallValid; decide +kernel

private theorem sp11786 : smallValid 11786 57 := by unfold smallValid; decide +kernel

private theorem sp11843 : smallValid 11843 56 := by unfold smallValid; decide +kernel

private theorem sp11899 : smallValid 11899 57 := by unfold smallValid; decide +kernel

private theorem sp11956 : smallValid 11956 57 := by unfold smallValid; decide +kernel

private theorem sp12013 : smallValid 12013 57 := by unfold smallValid; decide +kernel

private theorem sp12070 : smallValid 12070 57 := by unfold smallValid; decide +kernel

private theorem sp12127 : smallValid 12127 57 := by unfold smallValid; decide +kernel

private theorem sp12184 : smallValid 12184 57 := by unfold smallValid; decide +kernel

private theorem sp12241 : smallValid 12241 57 := by unfold smallValid; decide +kernel

private theorem sp12298 : smallValid 12298 57 := by unfold smallValid; decide +kernel

private theorem sp12355 : smallValid 12355 57 := by unfold smallValid; decide +kernel

private theorem sp12412 : smallValid 12412 57 := by unfold smallValid; decide +kernel

private theorem sp12469 : smallValid 12469 57 := by unfold smallValid; decide +kernel

private theorem sp12526 : smallValid 12526 57 := by unfold smallValid; decide +kernel

private theorem sp12583 : smallValid 12583 57 := by unfold smallValid; decide +kernel

private theorem sp12640 : smallValid 12640 57 := by unfold smallValid; decide +kernel

private theorem sp12697 : smallValid 12697 57 := by unfold smallValid; decide +kernel

private theorem sp12754 : smallValid 12754 56 := by unfold smallValid; decide +kernel

private theorem sp12810 : smallValid 12810 57 := by unfold smallValid; decide +kernel

private theorem sp12867 : smallValid 12867 57 := by unfold smallValid; decide +kernel

private theorem sp12924 : smallValid 12924 57 := by unfold smallValid; decide +kernel

private theorem sp12981 : smallValid 12981 57 := by unfold smallValid; decide +kernel

private theorem sp13038 : smallValid 13038 57 := by unfold smallValid; decide +kernel

private theorem sp13095 : smallValid 13095 57 := by unfold smallValid; decide +kernel

private theorem sp13152 : smallValid 13152 57 := by unfold smallValid; decide +kernel

private theorem sp13209 : smallValid 13209 57 := by unfold smallValid; decide +kernel

private theorem sp13266 : smallValid 13266 57 := by unfold smallValid; decide +kernel

private theorem sp13323 : smallValid 13323 57 := by unfold smallValid; decide +kernel

private theorem sp13380 : smallValid 13380 57 := by unfold smallValid; decide +kernel

private theorem sp13437 : smallValid 13437 57 := by unfold smallValid; decide +kernel

private theorem sp13494 : smallValid 13494 57 := by unfold smallValid; decide +kernel

private theorem sp13551 : smallValid 13551 57 := by unfold smallValid; decide +kernel

private theorem sp13608 : smallValid 13608 57 := by unfold smallValid; decide +kernel

private theorem sp13665 : smallValid 13665 57 := by unfold smallValid; decide +kernel

private theorem sp13722 : smallValid 13722 57 := by unfold smallValid; decide +kernel

private theorem sp13779 : smallValid 13779 57 := by unfold smallValid; decide +kernel

private theorem sp13836 : smallValid 13836 57 := by unfold smallValid; decide +kernel

private theorem sp13893 : smallValid 13893 57 := by unfold smallValid; decide +kernel

private theorem sp13950 : smallValid 13950 57 := by unfold smallValid; decide +kernel

private theorem sp14007 : smallValid 14007 57 := by unfold smallValid; decide +kernel

private theorem sp14064 : smallValid 14064 57 := by unfold smallValid; decide +kernel

private theorem sp14121 : smallValid 14121 57 := by unfold smallValid; decide +kernel

private theorem sp14178 : smallValid 14178 57 := by unfold smallValid; decide +kernel

private theorem sp14235 : smallValid 14235 57 := by unfold smallValid; decide +kernel

private theorem sp14292 : smallValid 14292 57 := by unfold smallValid; decide +kernel

private theorem sp14349 : smallValid 14349 57 := by unfold smallValid; decide +kernel

private theorem sp14406 : smallValid 14406 57 := by unfold smallValid; decide +kernel

private theorem sp14463 : smallValid 14463 57 := by unfold smallValid; decide +kernel

private theorem sp14520 : smallValid 14520 57 := by unfold smallValid; decide +kernel

private theorem sp14577 : smallValid 14577 56 := by unfold smallValid; decide +kernel

private theorem sp14633 : smallValid 14633 57 := by unfold smallValid; decide +kernel

private theorem sp14690 : smallValid 14690 57 := by unfold smallValid; decide +kernel

private theorem sp14747 : smallValid 14747 57 := by unfold smallValid; decide +kernel

private theorem sp14804 : smallValid 14804 57 := by unfold smallValid; decide +kernel

private theorem sp14861 : smallValid 14861 57 := by unfold smallValid; decide +kernel

private theorem sp14918 : smallValid 14918 57 := by unfold smallValid; decide +kernel

private theorem sp14975 : smallValid 14975 57 := by unfold smallValid; decide +kernel

private theorem sp15032 : smallValid 15032 57 := by unfold smallValid; decide +kernel

private theorem sp15089 : smallValid 15089 57 := by unfold smallValid; decide +kernel

private theorem sp15146 : smallValid 15146 57 := by unfold smallValid; decide +kernel

private theorem sp15203 : smallValid 15203 57 := by unfold smallValid; decide +kernel

private theorem sp15260 : smallValid 15260 57 := by unfold smallValid; decide +kernel

private theorem sp15317 : smallValid 15317 57 := by unfold smallValid; decide +kernel

private theorem sp15374 : smallValid 15374 57 := by unfold smallValid; decide +kernel

private theorem sp15431 : smallValid 15431 57 := by unfold smallValid; decide +kernel

private theorem sp15488 : smallValid 15488 56 := by unfold smallValid; decide +kernel

private theorem sp15544 : smallValid 15544 57 := by unfold smallValid; decide +kernel

private theorem sp15601 : smallValid 15601 57 := by unfold smallValid; decide +kernel

private theorem sp15658 : smallValid 15658 57 := by unfold smallValid; decide +kernel

private theorem sp15715 : smallValid 15715 57 := by unfold smallValid; decide +kernel

private theorem sp15772 : smallValid 15772 57 := by unfold smallValid; decide +kernel

private theorem sp15829 : smallValid 15829 57 := by unfold smallValid; decide +kernel

private theorem sp15886 : smallValid 15886 57 := by unfold smallValid; decide +kernel

private theorem sp15943 : smallValid 15943 57 := by unfold smallValid; decide +kernel

private theorem sp16000 : smallValid 16000 57 := by unfold smallValid; decide +kernel

private theorem sp16057 : smallValid 16057 57 := by unfold smallValid; decide +kernel

private theorem sp16114 : smallValid 16114 57 := by unfold smallValid; decide +kernel

private theorem sp16171 : smallValid 16171 57 := by unfold smallValid; decide +kernel

private theorem sp16228 : smallValid 16228 57 := by unfold smallValid; decide +kernel

private theorem sp16285 : smallValid 16285 57 := by unfold smallValid; decide +kernel

private theorem sp16342 : smallValid 16342 57 := by unfold smallValid; decide +kernel

private theorem sp16399 : smallValid 16399 56 := by unfold smallValid; decide +kernel

private theorem sp16455 : smallValid 16455 57 := by unfold smallValid; decide +kernel

private theorem sp16512 : smallValid 16512 57 := by unfold smallValid; decide +kernel

private theorem sp16569 : smallValid 16569 57 := by unfold smallValid; decide +kernel

private theorem sp16626 : smallValid 16626 57 := by unfold smallValid; decide +kernel

private theorem sp16683 : smallValid 16683 57 := by unfold smallValid; decide +kernel

private theorem sp16740 : smallValid 16740 57 := by unfold smallValid; decide +kernel

private theorem sp16797 : smallValid 16797 57 := by unfold smallValid; decide +kernel

private theorem sp16854 : smallValid 16854 57 := by unfold smallValid; decide +kernel

private theorem sp16911 : smallValid 16911 57 := by unfold smallValid; decide +kernel

private theorem sp16968 : smallValid 16968 57 := by unfold smallValid; decide +kernel

private theorem sp17025 : smallValid 17025 57 := by unfold smallValid; decide +kernel

private theorem sp17082 : smallValid 17082 57 := by unfold smallValid; decide +kernel

private theorem sp17139 : smallValid 17139 57 := by unfold smallValid; decide +kernel

private theorem sp17196 : smallValid 17196 57 := by unfold smallValid; decide +kernel

private theorem sp17253 : smallValid 17253 57 := by unfold smallValid; decide +kernel

private theorem sp17310 : smallValid 17310 56 := by unfold smallValid; decide +kernel

private theorem sp17366 : smallValid 17366 57 := by unfold smallValid; decide +kernel

private theorem sp17423 : smallValid 17423 57 := by unfold smallValid; decide +kernel

private theorem sp17480 : smallValid 17480 57 := by unfold smallValid; decide +kernel

private theorem sp17537 : smallValid 17537 57 := by unfold smallValid; decide +kernel

private theorem sp17594 : smallValid 17594 57 := by unfold smallValid; decide +kernel

private theorem sp17651 : smallValid 17651 57 := by unfold smallValid; decide +kernel

private theorem sp17708 : smallValid 17708 57 := by unfold smallValid; decide +kernel

private theorem sp17765 : smallValid 17765 57 := by unfold smallValid; decide +kernel

private theorem sp17822 : smallValid 17822 57 := by unfold smallValid; decide +kernel

private theorem sp17879 : smallValid 17879 57 := by unfold smallValid; decide +kernel

private theorem sp17936 : smallValid 17936 57 := by unfold smallValid; decide +kernel

private theorem sp17993 : smallValid 17993 57 := by unfold smallValid; decide +kernel

private theorem sp18050 : smallValid 18050 57 := by unfold smallValid; decide +kernel

private theorem sp18107 : smallValid 18107 57 := by unfold smallValid; decide +kernel

private theorem sp18164 : smallValid 18164 57 := by unfold smallValid; decide +kernel

private theorem sp18221 : smallValid 18221 56 := by unfold smallValid; decide +kernel

private theorem sp18277 : smallValid 18277 57 := by unfold smallValid; decide +kernel

private theorem sp18334 : smallValid 18334 57 := by unfold smallValid; decide +kernel

private theorem sp18391 : smallValid 18391 57 := by unfold smallValid; decide +kernel

private theorem sp18448 : smallValid 18448 57 := by unfold smallValid; decide +kernel

private theorem sp18505 : smallValid 18505 57 := by unfold smallValid; decide +kernel

private theorem sp18562 : smallValid 18562 57 := by unfold smallValid; decide +kernel

private theorem sp18619 : smallValid 18619 57 := by unfold smallValid; decide +kernel

private theorem sp18676 : smallValid 18676 57 := by unfold smallValid; decide +kernel

private theorem sp18733 : smallValid 18733 57 := by unfold smallValid; decide +kernel

private theorem sp18790 : smallValid 18790 57 := by unfold smallValid; decide +kernel

private theorem sp18847 : smallValid 18847 57 := by unfold smallValid; decide +kernel

private theorem sp18904 : smallValid 18904 57 := by unfold smallValid; decide +kernel

private theorem sp18961 : smallValid 18961 57 := by unfold smallValid; decide +kernel

private theorem sp19018 : smallValid 19018 57 := by unfold smallValid; decide +kernel

private theorem sp19075 : smallValid 19075 57 := by unfold smallValid; decide +kernel

private theorem sp19132 : smallValid 19132 56 := by unfold smallValid; decide +kernel

private theorem sp19188 : smallValid 19188 57 := by unfold smallValid; decide +kernel

private theorem sp19245 : smallValid 19245 57 := by unfold smallValid; decide +kernel

private theorem sp19302 : smallValid 19302 57 := by unfold smallValid; decide +kernel

private theorem sp19359 : smallValid 19359 57 := by unfold smallValid; decide +kernel

private theorem sp19416 : smallValid 19416 57 := by unfold smallValid; decide +kernel

private theorem sp19473 : smallValid 19473 57 := by unfold smallValid; decide +kernel

private theorem sp19530 : smallValid 19530 57 := by unfold smallValid; decide +kernel

private theorem sp19587 : smallValid 19587 57 := by unfold smallValid; decide +kernel

private theorem sp19644 : smallValid 19644 57 := by unfold smallValid; decide +kernel

private theorem sp19701 : smallValid 19701 57 := by unfold smallValid; decide +kernel

private theorem sp19758 : smallValid 19758 57 := by unfold smallValid; decide +kernel

private theorem sp19815 : smallValid 19815 57 := by unfold smallValid; decide +kernel

private theorem sp19872 : smallValid 19872 57 := by unfold smallValid; decide +kernel

private theorem sp19929 : smallValid 19929 57 := by unfold smallValid; decide +kernel

private theorem sp19986 : smallValid 19986 57 := by unfold smallValid; decide +kernel

private theorem sp20043 : smallValid 20043 56 := by unfold smallValid; decide +kernel

private theorem sp20099 : smallValid 20099 57 := by unfold smallValid; decide +kernel

private theorem sp20156 : smallValid 20156 57 := by unfold smallValid; decide +kernel

private theorem sp20213 : smallValid 20213 57 := by unfold smallValid; decide +kernel

private theorem sp20270 : smallValid 20270 57 := by unfold smallValid; decide +kernel

private theorem sp20327 : smallValid 20327 57 := by unfold smallValid; decide +kernel

private theorem sp20384 : smallValid 20384 57 := by unfold smallValid; decide +kernel

private theorem sp20441 : smallValid 20441 57 := by unfold smallValid; decide +kernel

private theorem sp20498 : smallValid 20498 57 := by unfold smallValid; decide +kernel

private theorem sp20555 : smallValid 20555 57 := by unfold smallValid; decide +kernel

private theorem sp20612 : smallValid 20612 57 := by unfold smallValid; decide +kernel

private theorem sp20669 : smallValid 20669 57 := by unfold smallValid; decide +kernel

private theorem sp20726 : smallValid 20726 57 := by unfold smallValid; decide +kernel

private theorem sp20783 : smallValid 20783 57 := by unfold smallValid; decide +kernel

private theorem sp20840 : smallValid 20840 57 := by unfold smallValid; decide +kernel

private theorem sp20897 : smallValid 20897 57 := by unfold smallValid; decide +kernel

private theorem sp20954 : smallValid 20954 57 := by unfold smallValid; decide +kernel

private theorem sp21011 : smallValid 21011 57 := by unfold smallValid; decide +kernel

private theorem sp21068 : smallValid 21068 57 := by unfold smallValid; decide +kernel

private theorem sp21125 : smallValid 21125 57 := by unfold smallValid; decide +kernel

private theorem sp21182 : smallValid 21182 57 := by unfold smallValid; decide +kernel

private theorem sp21239 : smallValid 21239 57 := by unfold smallValid; decide +kernel

private theorem sp21296 : smallValid 21296 57 := by unfold smallValid; decide +kernel

private theorem sp21353 : smallValid 21353 57 := by unfold smallValid; decide +kernel

private theorem sp21410 : smallValid 21410 57 := by unfold smallValid; decide +kernel

private theorem sp21467 : smallValid 21467 57 := by unfold smallValid; decide +kernel

private theorem sp21524 : smallValid 21524 57 := by unfold smallValid; decide +kernel

private theorem sp21581 : smallValid 21581 57 := by unfold smallValid; decide +kernel

private theorem sp21638 : smallValid 21638 57 := by unfold smallValid; decide +kernel

private theorem sp21695 : smallValid 21695 57 := by unfold smallValid; decide +kernel

private theorem sp21752 : smallValid 21752 57 := by unfold smallValid; decide +kernel

private theorem sp21809 : smallValid 21809 57 := by unfold smallValid; decide +kernel

private theorem sp21866 : smallValid 21866 56 := by unfold smallValid; decide +kernel

private theorem sp21922 : smallValid 21922 57 := by unfold smallValid; decide +kernel

private theorem sp21979 : smallValid 21979 57 := by unfold smallValid; decide +kernel

private theorem sp22036 : smallValid 22036 57 := by unfold smallValid; decide +kernel

private theorem sp22093 : smallValid 22093 57 := by unfold smallValid; decide +kernel

private theorem sp22150 : smallValid 22150 57 := by unfold smallValid; decide +kernel

private theorem sp22207 : smallValid 22207 57 := by unfold smallValid; decide +kernel

private theorem sp22264 : smallValid 22264 57 := by unfold smallValid; decide +kernel

private theorem sp22321 : smallValid 22321 57 := by unfold smallValid; decide +kernel

private theorem sp22378 : smallValid 22378 57 := by unfold smallValid; decide +kernel

private theorem sp22435 : smallValid 22435 57 := by unfold smallValid; decide +kernel

private theorem sp22492 : smallValid 22492 57 := by unfold smallValid; decide +kernel

private theorem sp22549 : smallValid 22549 57 := by unfold smallValid; decide +kernel

private theorem sp22606 : smallValid 22606 57 := by unfold smallValid; decide +kernel

private theorem sp22663 : smallValid 22663 57 := by unfold smallValid; decide +kernel

private theorem sp22720 : smallValid 22720 57 := by unfold smallValid; decide +kernel

private theorem sp22777 : smallValid 22777 56 := by unfold smallValid; decide +kernel

private theorem sp22833 : smallValid 22833 57 := by unfold smallValid; decide +kernel

private theorem sp22890 : smallValid 22890 57 := by unfold smallValid; decide +kernel

private theorem sp22947 : smallValid 22947 57 := by unfold smallValid; decide +kernel

private theorem sp23004 : smallValid 23004 57 := by unfold smallValid; decide +kernel

private theorem sp23061 : smallValid 23061 57 := by unfold smallValid; decide +kernel

private theorem sp23118 : smallValid 23118 57 := by unfold smallValid; decide +kernel

private theorem sp23175 : smallValid 23175 57 := by unfold smallValid; decide +kernel

private theorem sp23232 : smallValid 23232 57 := by unfold smallValid; decide +kernel

private theorem sp23289 : smallValid 23289 57 := by unfold smallValid; decide +kernel

private theorem sp23346 : smallValid 23346 57 := by unfold smallValid; decide +kernel

private theorem sp23403 : smallValid 23403 57 := by unfold smallValid; decide +kernel

private theorem sp23460 : smallValid 23460 57 := by unfold smallValid; decide +kernel

private theorem sp23517 : smallValid 23517 57 := by unfold smallValid; decide +kernel

private theorem sp23574 : smallValid 23574 57 := by unfold smallValid; decide +kernel

private theorem sp23631 : smallValid 23631 57 := by unfold smallValid; decide +kernel

private theorem sp23688 : smallValid 23688 56 := by unfold smallValid; decide +kernel

private theorem sp23744 : smallValid 23744 57 := by unfold smallValid; decide +kernel

private theorem sp23801 : smallValid 23801 57 := by unfold smallValid; decide +kernel

private theorem sp23858 : smallValid 23858 57 := by unfold smallValid; decide +kernel

private theorem sp23915 : smallValid 23915 57 := by unfold smallValid; decide +kernel

private theorem sp23972 : smallValid 23972 57 := by unfold smallValid; decide +kernel

private theorem sp24029 : smallValid 24029 57 := by unfold smallValid; decide +kernel

private theorem sp24086 : smallValid 24086 57 := by unfold smallValid; decide +kernel

private theorem sp24143 : smallValid 24143 57 := by unfold smallValid; decide +kernel

private theorem sp24200 : smallValid 24200 57 := by unfold smallValid; decide +kernel

private theorem sp24257 : smallValid 24257 57 := by unfold smallValid; decide +kernel

private theorem sp24314 : smallValid 24314 57 := by unfold smallValid; decide +kernel

private theorem sp24371 : smallValid 24371 57 := by unfold smallValid; decide +kernel

private theorem sp24428 : smallValid 24428 57 := by unfold smallValid; decide +kernel

private theorem sp24485 : smallValid 24485 57 := by unfold smallValid; decide +kernel

private theorem sp24542 : smallValid 24542 57 := by unfold smallValid; decide +kernel

private theorem sp24599 : smallValid 24599 56 := by unfold smallValid; decide +kernel

private theorem sp24655 : smallValid 24655 57 := by unfold smallValid; decide +kernel

private theorem sp24712 : smallValid 24712 57 := by unfold smallValid; decide +kernel

private theorem sp24769 : smallValid 24769 57 := by unfold smallValid; decide +kernel

private theorem sp24826 : smallValid 24826 57 := by unfold smallValid; decide +kernel

private theorem sp24883 : smallValid 24883 57 := by unfold smallValid; decide +kernel

private theorem sp24940 : smallValid 24940 57 := by unfold smallValid; decide +kernel

private theorem sp24997 : smallValid 24997 57 := by unfold smallValid; decide +kernel

private theorem sp25054 : smallValid 25054 57 := by unfold smallValid; decide +kernel

private theorem sp25111 : smallValid 25111 57 := by unfold smallValid; decide +kernel

private theorem sp25168 : smallValid 25168 57 := by unfold smallValid; decide +kernel

private theorem sp25225 : smallValid 25225 57 := by unfold smallValid; decide +kernel

private theorem sp25282 : smallValid 25282 57 := by unfold smallValid; decide +kernel

private theorem sp25339 : smallValid 25339 57 := by unfold smallValid; decide +kernel

private theorem sp25396 : smallValid 25396 57 := by unfold smallValid; decide +kernel

private theorem sp25453 : smallValid 25453 57 := by unfold smallValid; decide +kernel

private theorem sp25510 : smallValid 25510 56 := by unfold smallValid; decide +kernel

private theorem sp25566 : smallValid 25566 57 := by unfold smallValid; decide +kernel

private theorem sp25623 : smallValid 25623 57 := by unfold smallValid; decide +kernel

private theorem sp25680 : smallValid 25680 57 := by unfold smallValid; decide +kernel

private theorem sp25737 : smallValid 25737 57 := by unfold smallValid; decide +kernel

private theorem sp25794 : smallValid 25794 57 := by unfold smallValid; decide +kernel

private theorem sp25851 : smallValid 25851 57 := by unfold smallValid; decide +kernel

private theorem sp25908 : smallValid 25908 57 := by unfold smallValid; decide +kernel

private theorem sp25965 : smallValid 25965 57 := by unfold smallValid; decide +kernel

private theorem sp26022 : smallValid 26022 57 := by unfold smallValid; decide +kernel

private theorem sp26079 : smallValid 26079 57 := by unfold smallValid; decide +kernel

private theorem sp26136 : smallValid 26136 57 := by unfold smallValid; decide +kernel

private theorem sp26193 : smallValid 26193 57 := by unfold smallValid; decide +kernel

private theorem sp26250 : smallValid 26250 57 := by unfold smallValid; decide +kernel

private theorem sp26307 : smallValid 26307 57 := by unfold smallValid; decide +kernel

private theorem sp26364 : smallValid 26364 57 := by unfold smallValid; decide +kernel

private theorem sp26421 : smallValid 26421 56 := by unfold smallValid; decide +kernel

private theorem sp26477 : smallValid 26477 57 := by unfold smallValid; decide +kernel

private theorem sp26534 : smallValid 26534 57 := by unfold smallValid; decide +kernel

private theorem sp26591 : smallValid 26591 57 := by unfold smallValid; decide +kernel

private theorem sp26648 : smallValid 26648 57 := by unfold smallValid; decide +kernel

private theorem sp26705 : smallValid 26705 57 := by unfold smallValid; decide +kernel

private theorem sp26762 : smallValid 26762 57 := by unfold smallValid; decide +kernel

private theorem sp26819 : smallValid 26819 57 := by unfold smallValid; decide +kernel

private theorem sp26876 : smallValid 26876 57 := by unfold smallValid; decide +kernel

private theorem sp26933 : smallValid 26933 57 := by unfold smallValid; decide +kernel

private theorem sp26990 : smallValid 26990 57 := by unfold smallValid; decide +kernel

private theorem sp27047 : smallValid 27047 57 := by unfold smallValid; decide +kernel

private theorem sp27104 : smallValid 27104 57 := by unfold smallValid; decide +kernel

private theorem sp27161 : smallValid 27161 57 := by unfold smallValid; decide +kernel

private theorem sp27218 : smallValid 27218 57 := by unfold smallValid; decide +kernel

private theorem sp27275 : smallValid 27275 57 := by unfold smallValid; decide +kernel

private theorem sp27332 : smallValid 27332 56 := by unfold smallValid; decide +kernel

private theorem sp27388 : smallValid 27388 57 := by unfold smallValid; decide +kernel

private theorem sp27445 : smallValid 27445 57 := by unfold smallValid; decide +kernel

private theorem sp27502 : smallValid 27502 57 := by unfold smallValid; decide +kernel

private theorem sp27559 : smallValid 27559 57 := by unfold smallValid; decide +kernel

private theorem sp27616 : smallValid 27616 57 := by unfold smallValid; decide +kernel

private theorem sp27673 : smallValid 27673 57 := by unfold smallValid; decide +kernel

private theorem sp27730 : smallValid 27730 57 := by unfold smallValid; decide +kernel

private theorem sp27787 : smallValid 27787 57 := by unfold smallValid; decide +kernel

private theorem sp27844 : smallValid 27844 57 := by unfold smallValid; decide +kernel

private theorem sp27901 : smallValid 27901 57 := by unfold smallValid; decide +kernel

private theorem sp27958 : smallValid 27958 57 := by unfold smallValid; decide +kernel

private theorem sp28015 : smallValid 28015 57 := by unfold smallValid; decide +kernel

private theorem sp28072 : smallValid 28072 57 := by unfold smallValid; decide +kernel

private theorem sp28129 : smallValid 28129 57 := by unfold smallValid; decide +kernel

private theorem sp28186 : smallValid 28186 57 := by unfold smallValid; decide +kernel

private theorem sp28243 : smallValid 28243 57 := by unfold smallValid; decide +kernel

private theorem sp28300 : smallValid 28300 57 := by unfold smallValid; decide +kernel

private theorem sp28357 : smallValid 28357 57 := by unfold smallValid; decide +kernel

private theorem sp28414 : smallValid 28414 57 := by unfold smallValid; decide +kernel

private theorem sp28471 : smallValid 28471 57 := by unfold smallValid; decide +kernel

private theorem sp28528 : smallValid 28528 57 := by unfold smallValid; decide +kernel

private theorem sp28585 : smallValid 28585 57 := by unfold smallValid; decide +kernel

private theorem sp28642 : smallValid 28642 57 := by unfold smallValid; decide +kernel

private theorem sp28699 : smallValid 28699 57 := by unfold smallValid; decide +kernel

private theorem sp28756 : smallValid 28756 57 := by unfold smallValid; decide +kernel

private theorem sp28813 : smallValid 28813 57 := by unfold smallValid; decide +kernel

private theorem sp28870 : smallValid 28870 57 := by unfold smallValid; decide +kernel

private theorem sp28927 : smallValid 28927 57 := by unfold smallValid; decide +kernel

private theorem sp28984 : smallValid 28984 57 := by unfold smallValid; decide +kernel

private theorem sp29041 : smallValid 29041 57 := by unfold smallValid; decide +kernel

private theorem sp29098 : smallValid 29098 57 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤29154) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 29155 := (joinSmall (lo:=0) (a:=14577) (b:=14578) (joinSmall (lo:=0) (a:=7288) (b:=7289) (joinSmall (lo:=0) (a:=3644) (b:=3644) (joinSmall (lo:=0) (a:=1822) (b:=1822) (joinSmall (lo:=0) (a:=911) (b:=911) (joinSmall (lo:=0) (a:=455) (b:=456) (joinSmall (lo:=0) (a:=227) (b:=228) (joinSmall (lo:=0) (a:=113) (b:=114) (joinSmall (lo:=0) (a:=56) (b:=57) sp0 sp56) (joinSmall (lo:=113) (a:=57) (b:=57) sp113 sp170)) (joinSmall (lo:=227) (a:=114) (b:=114) (joinSmall (lo:=227) (a:=57) (b:=57) sp227 sp284) (joinSmall (lo:=341) (a:=57) (b:=57) sp341 sp398))) (joinSmall (lo:=455) (a:=228) (b:=228) (joinSmall (lo:=455) (a:=114) (b:=114) (joinSmall (lo:=455) (a:=57) (b:=57) sp455 sp512) (joinSmall (lo:=569) (a:=57) (b:=57) sp569 sp626)) (joinSmall (lo:=683) (a:=114) (b:=114) (joinSmall (lo:=683) (a:=57) (b:=57) sp683 sp740) (joinSmall (lo:=797) (a:=57) (b:=57) sp797 sp854)))) (joinSmall (lo:=911) (a:=455) (b:=456) (joinSmall (lo:=911) (a:=227) (b:=228) (joinSmall (lo:=911) (a:=113) (b:=114) (joinSmall (lo:=911) (a:=56) (b:=57) sp911 sp967) (joinSmall (lo:=1024) (a:=57) (b:=57) sp1024 sp1081)) (joinSmall (lo:=1138) (a:=114) (b:=114) (joinSmall (lo:=1138) (a:=57) (b:=57) sp1138 sp1195) (joinSmall (lo:=1252) (a:=57) (b:=57) sp1252 sp1309))) (joinSmall (lo:=1366) (a:=228) (b:=228) (joinSmall (lo:=1366) (a:=114) (b:=114) (joinSmall (lo:=1366) (a:=57) (b:=57) sp1366 sp1423) (joinSmall (lo:=1480) (a:=57) (b:=57) sp1480 sp1537)) (joinSmall (lo:=1594) (a:=114) (b:=114) (joinSmall (lo:=1594) (a:=57) (b:=57) sp1594 sp1651) (joinSmall (lo:=1708) (a:=57) (b:=57) sp1708 sp1765))))) (joinSmall (lo:=1822) (a:=911) (b:=911) (joinSmall (lo:=1822) (a:=455) (b:=456) (joinSmall (lo:=1822) (a:=227) (b:=228) (joinSmall (lo:=1822) (a:=113) (b:=114) (joinSmall (lo:=1822) (a:=56) (b:=57) sp1822 sp1878) (joinSmall (lo:=1935) (a:=57) (b:=57) sp1935 sp1992)) (joinSmall (lo:=2049) (a:=114) (b:=114) (joinSmall (lo:=2049) (a:=57) (b:=57) sp2049 sp2106) (joinSmall (lo:=2163) (a:=57) (b:=57) sp2163 sp2220))) (joinSmall (lo:=2277) (a:=228) (b:=228) (joinSmall (lo:=2277) (a:=114) (b:=114) (joinSmall (lo:=2277) (a:=57) (b:=57) sp2277 sp2334) (joinSmall (lo:=2391) (a:=57) (b:=57) sp2391 sp2448)) (joinSmall (lo:=2505) (a:=114) (b:=114) (joinSmall (lo:=2505) (a:=57) (b:=57) sp2505 sp2562) (joinSmall (lo:=2619) (a:=57) (b:=57) sp2619 sp2676)))) (joinSmall (lo:=2733) (a:=455) (b:=456) (joinSmall (lo:=2733) (a:=227) (b:=228) (joinSmall (lo:=2733) (a:=113) (b:=114) (joinSmall (lo:=2733) (a:=56) (b:=57) sp2733 sp2789) (joinSmall (lo:=2846) (a:=57) (b:=57) sp2846 sp2903)) (joinSmall (lo:=2960) (a:=114) (b:=114) (joinSmall (lo:=2960) (a:=57) (b:=57) sp2960 sp3017) (joinSmall (lo:=3074) (a:=57) (b:=57) sp3074 sp3131))) (joinSmall (lo:=3188) (a:=228) (b:=228) (joinSmall (lo:=3188) (a:=114) (b:=114) (joinSmall (lo:=3188) (a:=57) (b:=57) sp3188 sp3245) (joinSmall (lo:=3302) (a:=57) (b:=57) sp3302 sp3359)) (joinSmall (lo:=3416) (a:=114) (b:=114) (joinSmall (lo:=3416) (a:=57) (b:=57) sp3416 sp3473) (joinSmall (lo:=3530) (a:=57) (b:=57) sp3530 sp3587)))))) (joinSmall (lo:=3644) (a:=1822) (b:=1822) (joinSmall (lo:=3644) (a:=911) (b:=911) (joinSmall (lo:=3644) (a:=455) (b:=456) (joinSmall (lo:=3644) (a:=227) (b:=228) (joinSmall (lo:=3644) (a:=113) (b:=114) (joinSmall (lo:=3644) (a:=56) (b:=57) sp3644 sp3700) (joinSmall (lo:=3757) (a:=57) (b:=57) sp3757 sp3814)) (joinSmall (lo:=3871) (a:=114) (b:=114) (joinSmall (lo:=3871) (a:=57) (b:=57) sp3871 sp3928) (joinSmall (lo:=3985) (a:=57) (b:=57) sp3985 sp4042))) (joinSmall (lo:=4099) (a:=228) (b:=228) (joinSmall (lo:=4099) (a:=114) (b:=114) (joinSmall (lo:=4099) (a:=57) (b:=57) sp4099 sp4156) (joinSmall (lo:=4213) (a:=57) (b:=57) sp4213 sp4270)) (joinSmall (lo:=4327) (a:=114) (b:=114) (joinSmall (lo:=4327) (a:=57) (b:=57) sp4327 sp4384) (joinSmall (lo:=4441) (a:=57) (b:=57) sp4441 sp4498)))) (joinSmall (lo:=4555) (a:=455) (b:=456) (joinSmall (lo:=4555) (a:=227) (b:=228) (joinSmall (lo:=4555) (a:=113) (b:=114) (joinSmall (lo:=4555) (a:=56) (b:=57) sp4555 sp4611) (joinSmall (lo:=4668) (a:=57) (b:=57) sp4668 sp4725)) (joinSmall (lo:=4782) (a:=114) (b:=114) (joinSmall (lo:=4782) (a:=57) (b:=57) sp4782 sp4839) (joinSmall (lo:=4896) (a:=57) (b:=57) sp4896 sp4953))) (joinSmall (lo:=5010) (a:=228) (b:=228) (joinSmall (lo:=5010) (a:=114) (b:=114) (joinSmall (lo:=5010) (a:=57) (b:=57) sp5010 sp5067) (joinSmall (lo:=5124) (a:=57) (b:=57) sp5124 sp5181)) (joinSmall (lo:=5238) (a:=114) (b:=114) (joinSmall (lo:=5238) (a:=57) (b:=57) sp5238 sp5295) (joinSmall (lo:=5352) (a:=57) (b:=57) sp5352 sp5409))))) (joinSmall (lo:=5466) (a:=911) (b:=911) (joinSmall (lo:=5466) (a:=455) (b:=456) (joinSmall (lo:=5466) (a:=227) (b:=228) (joinSmall (lo:=5466) (a:=113) (b:=114) (joinSmall (lo:=5466) (a:=56) (b:=57) sp5466 sp5522) (joinSmall (lo:=5579) (a:=57) (b:=57) sp5579 sp5636)) (joinSmall (lo:=5693) (a:=114) (b:=114) (joinSmall (lo:=5693) (a:=57) (b:=57) sp5693 sp5750) (joinSmall (lo:=5807) (a:=57) (b:=57) sp5807 sp5864))) (joinSmall (lo:=5921) (a:=228) (b:=228) (joinSmall (lo:=5921) (a:=114) (b:=114) (joinSmall (lo:=5921) (a:=57) (b:=57) sp5921 sp5978) (joinSmall (lo:=6035) (a:=57) (b:=57) sp6035 sp6092)) (joinSmall (lo:=6149) (a:=114) (b:=114) (joinSmall (lo:=6149) (a:=57) (b:=57) sp6149 sp6206) (joinSmall (lo:=6263) (a:=57) (b:=57) sp6263 sp6320)))) (joinSmall (lo:=6377) (a:=455) (b:=456) (joinSmall (lo:=6377) (a:=227) (b:=228) (joinSmall (lo:=6377) (a:=113) (b:=114) (joinSmall (lo:=6377) (a:=56) (b:=57) sp6377 sp6433) (joinSmall (lo:=6490) (a:=57) (b:=57) sp6490 sp6547)) (joinSmall (lo:=6604) (a:=114) (b:=114) (joinSmall (lo:=6604) (a:=57) (b:=57) sp6604 sp6661) (joinSmall (lo:=6718) (a:=57) (b:=57) sp6718 sp6775))) (joinSmall (lo:=6832) (a:=228) (b:=228) (joinSmall (lo:=6832) (a:=114) (b:=114) (joinSmall (lo:=6832) (a:=57) (b:=57) sp6832 sp6889) (joinSmall (lo:=6946) (a:=57) (b:=57) sp6946 sp7003)) (joinSmall (lo:=7060) (a:=114) (b:=114) (joinSmall (lo:=7060) (a:=57) (b:=57) sp7060 sp7117) (joinSmall (lo:=7174) (a:=57) (b:=57) sp7174 sp7231))))))) (joinSmall (lo:=7288) (a:=3644) (b:=3645) (joinSmall (lo:=7288) (a:=1822) (b:=1822) (joinSmall (lo:=7288) (a:=911) (b:=911) (joinSmall (lo:=7288) (a:=455) (b:=456) (joinSmall (lo:=7288) (a:=227) (b:=228) (joinSmall (lo:=7288) (a:=113) (b:=114) (joinSmall (lo:=7288) (a:=56) (b:=57) sp7288 sp7344) (joinSmall (lo:=7401) (a:=57) (b:=57) sp7401 sp7458)) (joinSmall (lo:=7515) (a:=114) (b:=114) (joinSmall (lo:=7515) (a:=57) (b:=57) sp7515 sp7572) (joinSmall (lo:=7629) (a:=57) (b:=57) sp7629 sp7686))) (joinSmall (lo:=7743) (a:=228) (b:=228) (joinSmall (lo:=7743) (a:=114) (b:=114) (joinSmall (lo:=7743) (a:=57) (b:=57) sp7743 sp7800) (joinSmall (lo:=7857) (a:=57) (b:=57) sp7857 sp7914)) (joinSmall (lo:=7971) (a:=114) (b:=114) (joinSmall (lo:=7971) (a:=57) (b:=57) sp7971 sp8028) (joinSmall (lo:=8085) (a:=57) (b:=57) sp8085 sp8142)))) (joinSmall (lo:=8199) (a:=455) (b:=456) (joinSmall (lo:=8199) (a:=227) (b:=228) (joinSmall (lo:=8199) (a:=113) (b:=114) (joinSmall (lo:=8199) (a:=56) (b:=57) sp8199 sp8255) (joinSmall (lo:=8312) (a:=57) (b:=57) sp8312 sp8369)) (joinSmall (lo:=8426) (a:=114) (b:=114) (joinSmall (lo:=8426) (a:=57) (b:=57) sp8426 sp8483) (joinSmall (lo:=8540) (a:=57) (b:=57) sp8540 sp8597))) (joinSmall (lo:=8654) (a:=228) (b:=228) (joinSmall (lo:=8654) (a:=114) (b:=114) (joinSmall (lo:=8654) (a:=57) (b:=57) sp8654 sp8711) (joinSmall (lo:=8768) (a:=57) (b:=57) sp8768 sp8825)) (joinSmall (lo:=8882) (a:=114) (b:=114) (joinSmall (lo:=8882) (a:=57) (b:=57) sp8882 sp8939) (joinSmall (lo:=8996) (a:=57) (b:=57) sp8996 sp9053))))) (joinSmall (lo:=9110) (a:=911) (b:=911) (joinSmall (lo:=9110) (a:=455) (b:=456) (joinSmall (lo:=9110) (a:=227) (b:=228) (joinSmall (lo:=9110) (a:=113) (b:=114) (joinSmall (lo:=9110) (a:=56) (b:=57) sp9110 sp9166) (joinSmall (lo:=9223) (a:=57) (b:=57) sp9223 sp9280)) (joinSmall (lo:=9337) (a:=114) (b:=114) (joinSmall (lo:=9337) (a:=57) (b:=57) sp9337 sp9394) (joinSmall (lo:=9451) (a:=57) (b:=57) sp9451 sp9508))) (joinSmall (lo:=9565) (a:=228) (b:=228) (joinSmall (lo:=9565) (a:=114) (b:=114) (joinSmall (lo:=9565) (a:=57) (b:=57) sp9565 sp9622) (joinSmall (lo:=9679) (a:=57) (b:=57) sp9679 sp9736)) (joinSmall (lo:=9793) (a:=114) (b:=114) (joinSmall (lo:=9793) (a:=57) (b:=57) sp9793 sp9850) (joinSmall (lo:=9907) (a:=57) (b:=57) sp9907 sp9964)))) (joinSmall (lo:=10021) (a:=455) (b:=456) (joinSmall (lo:=10021) (a:=227) (b:=228) (joinSmall (lo:=10021) (a:=113) (b:=114) (joinSmall (lo:=10021) (a:=56) (b:=57) sp10021 sp10077) (joinSmall (lo:=10134) (a:=57) (b:=57) sp10134 sp10191)) (joinSmall (lo:=10248) (a:=114) (b:=114) (joinSmall (lo:=10248) (a:=57) (b:=57) sp10248 sp10305) (joinSmall (lo:=10362) (a:=57) (b:=57) sp10362 sp10419))) (joinSmall (lo:=10476) (a:=228) (b:=228) (joinSmall (lo:=10476) (a:=114) (b:=114) (joinSmall (lo:=10476) (a:=57) (b:=57) sp10476 sp10533) (joinSmall (lo:=10590) (a:=57) (b:=57) sp10590 sp10647)) (joinSmall (lo:=10704) (a:=114) (b:=114) (joinSmall (lo:=10704) (a:=57) (b:=57) sp10704 sp10761) (joinSmall (lo:=10818) (a:=57) (b:=57) sp10818 sp10875)))))) (joinSmall (lo:=10932) (a:=1822) (b:=1823) (joinSmall (lo:=10932) (a:=911) (b:=911) (joinSmall (lo:=10932) (a:=455) (b:=456) (joinSmall (lo:=10932) (a:=227) (b:=228) (joinSmall (lo:=10932) (a:=113) (b:=114) (joinSmall (lo:=10932) (a:=56) (b:=57) sp10932 sp10988) (joinSmall (lo:=11045) (a:=57) (b:=57) sp11045 sp11102)) (joinSmall (lo:=11159) (a:=114) (b:=114) (joinSmall (lo:=11159) (a:=57) (b:=57) sp11159 sp11216) (joinSmall (lo:=11273) (a:=57) (b:=57) sp11273 sp11330))) (joinSmall (lo:=11387) (a:=228) (b:=228) (joinSmall (lo:=11387) (a:=114) (b:=114) (joinSmall (lo:=11387) (a:=57) (b:=57) sp11387 sp11444) (joinSmall (lo:=11501) (a:=57) (b:=57) sp11501 sp11558)) (joinSmall (lo:=11615) (a:=114) (b:=114) (joinSmall (lo:=11615) (a:=57) (b:=57) sp11615 sp11672) (joinSmall (lo:=11729) (a:=57) (b:=57) sp11729 sp11786)))) (joinSmall (lo:=11843) (a:=455) (b:=456) (joinSmall (lo:=11843) (a:=227) (b:=228) (joinSmall (lo:=11843) (a:=113) (b:=114) (joinSmall (lo:=11843) (a:=56) (b:=57) sp11843 sp11899) (joinSmall (lo:=11956) (a:=57) (b:=57) sp11956 sp12013)) (joinSmall (lo:=12070) (a:=114) (b:=114) (joinSmall (lo:=12070) (a:=57) (b:=57) sp12070 sp12127) (joinSmall (lo:=12184) (a:=57) (b:=57) sp12184 sp12241))) (joinSmall (lo:=12298) (a:=228) (b:=228) (joinSmall (lo:=12298) (a:=114) (b:=114) (joinSmall (lo:=12298) (a:=57) (b:=57) sp12298 sp12355) (joinSmall (lo:=12412) (a:=57) (b:=57) sp12412 sp12469)) (joinSmall (lo:=12526) (a:=114) (b:=114) (joinSmall (lo:=12526) (a:=57) (b:=57) sp12526 sp12583) (joinSmall (lo:=12640) (a:=57) (b:=57) sp12640 sp12697))))) (joinSmall (lo:=12754) (a:=911) (b:=912) (joinSmall (lo:=12754) (a:=455) (b:=456) (joinSmall (lo:=12754) (a:=227) (b:=228) (joinSmall (lo:=12754) (a:=113) (b:=114) (joinSmall (lo:=12754) (a:=56) (b:=57) sp12754 sp12810) (joinSmall (lo:=12867) (a:=57) (b:=57) sp12867 sp12924)) (joinSmall (lo:=12981) (a:=114) (b:=114) (joinSmall (lo:=12981) (a:=57) (b:=57) sp12981 sp13038) (joinSmall (lo:=13095) (a:=57) (b:=57) sp13095 sp13152))) (joinSmall (lo:=13209) (a:=228) (b:=228) (joinSmall (lo:=13209) (a:=114) (b:=114) (joinSmall (lo:=13209) (a:=57) (b:=57) sp13209 sp13266) (joinSmall (lo:=13323) (a:=57) (b:=57) sp13323 sp13380)) (joinSmall (lo:=13437) (a:=114) (b:=114) (joinSmall (lo:=13437) (a:=57) (b:=57) sp13437 sp13494) (joinSmall (lo:=13551) (a:=57) (b:=57) sp13551 sp13608)))) (joinSmall (lo:=13665) (a:=456) (b:=456) (joinSmall (lo:=13665) (a:=228) (b:=228) (joinSmall (lo:=13665) (a:=114) (b:=114) (joinSmall (lo:=13665) (a:=57) (b:=57) sp13665 sp13722) (joinSmall (lo:=13779) (a:=57) (b:=57) sp13779 sp13836)) (joinSmall (lo:=13893) (a:=114) (b:=114) (joinSmall (lo:=13893) (a:=57) (b:=57) sp13893 sp13950) (joinSmall (lo:=14007) (a:=57) (b:=57) sp14007 sp14064))) (joinSmall (lo:=14121) (a:=228) (b:=228) (joinSmall (lo:=14121) (a:=114) (b:=114) (joinSmall (lo:=14121) (a:=57) (b:=57) sp14121 sp14178) (joinSmall (lo:=14235) (a:=57) (b:=57) sp14235 sp14292)) (joinSmall (lo:=14349) (a:=114) (b:=114) (joinSmall (lo:=14349) (a:=57) (b:=57) sp14349 sp14406) (joinSmall (lo:=14463) (a:=57) (b:=57) sp14463 sp14520)))))))) (joinSmall (lo:=14577) (a:=7289) (b:=7289) (joinSmall (lo:=14577) (a:=3644) (b:=3645) (joinSmall (lo:=14577) (a:=1822) (b:=1822) (joinSmall (lo:=14577) (a:=911) (b:=911) (joinSmall (lo:=14577) (a:=455) (b:=456) (joinSmall (lo:=14577) (a:=227) (b:=228) (joinSmall (lo:=14577) (a:=113) (b:=114) (joinSmall (lo:=14577) (a:=56) (b:=57) sp14577 sp14633) (joinSmall (lo:=14690) (a:=57) (b:=57) sp14690 sp14747)) (joinSmall (lo:=14804) (a:=114) (b:=114) (joinSmall (lo:=14804) (a:=57) (b:=57) sp14804 sp14861) (joinSmall (lo:=14918) (a:=57) (b:=57) sp14918 sp14975))) (joinSmall (lo:=15032) (a:=228) (b:=228) (joinSmall (lo:=15032) (a:=114) (b:=114) (joinSmall (lo:=15032) (a:=57) (b:=57) sp15032 sp15089) (joinSmall (lo:=15146) (a:=57) (b:=57) sp15146 sp15203)) (joinSmall (lo:=15260) (a:=114) (b:=114) (joinSmall (lo:=15260) (a:=57) (b:=57) sp15260 sp15317) (joinSmall (lo:=15374) (a:=57) (b:=57) sp15374 sp15431)))) (joinSmall (lo:=15488) (a:=455) (b:=456) (joinSmall (lo:=15488) (a:=227) (b:=228) (joinSmall (lo:=15488) (a:=113) (b:=114) (joinSmall (lo:=15488) (a:=56) (b:=57) sp15488 sp15544) (joinSmall (lo:=15601) (a:=57) (b:=57) sp15601 sp15658)) (joinSmall (lo:=15715) (a:=114) (b:=114) (joinSmall (lo:=15715) (a:=57) (b:=57) sp15715 sp15772) (joinSmall (lo:=15829) (a:=57) (b:=57) sp15829 sp15886))) (joinSmall (lo:=15943) (a:=228) (b:=228) (joinSmall (lo:=15943) (a:=114) (b:=114) (joinSmall (lo:=15943) (a:=57) (b:=57) sp15943 sp16000) (joinSmall (lo:=16057) (a:=57) (b:=57) sp16057 sp16114)) (joinSmall (lo:=16171) (a:=114) (b:=114) (joinSmall (lo:=16171) (a:=57) (b:=57) sp16171 sp16228) (joinSmall (lo:=16285) (a:=57) (b:=57) sp16285 sp16342))))) (joinSmall (lo:=16399) (a:=911) (b:=911) (joinSmall (lo:=16399) (a:=455) (b:=456) (joinSmall (lo:=16399) (a:=227) (b:=228) (joinSmall (lo:=16399) (a:=113) (b:=114) (joinSmall (lo:=16399) (a:=56) (b:=57) sp16399 sp16455) (joinSmall (lo:=16512) (a:=57) (b:=57) sp16512 sp16569)) (joinSmall (lo:=16626) (a:=114) (b:=114) (joinSmall (lo:=16626) (a:=57) (b:=57) sp16626 sp16683) (joinSmall (lo:=16740) (a:=57) (b:=57) sp16740 sp16797))) (joinSmall (lo:=16854) (a:=228) (b:=228) (joinSmall (lo:=16854) (a:=114) (b:=114) (joinSmall (lo:=16854) (a:=57) (b:=57) sp16854 sp16911) (joinSmall (lo:=16968) (a:=57) (b:=57) sp16968 sp17025)) (joinSmall (lo:=17082) (a:=114) (b:=114) (joinSmall (lo:=17082) (a:=57) (b:=57) sp17082 sp17139) (joinSmall (lo:=17196) (a:=57) (b:=57) sp17196 sp17253)))) (joinSmall (lo:=17310) (a:=455) (b:=456) (joinSmall (lo:=17310) (a:=227) (b:=228) (joinSmall (lo:=17310) (a:=113) (b:=114) (joinSmall (lo:=17310) (a:=56) (b:=57) sp17310 sp17366) (joinSmall (lo:=17423) (a:=57) (b:=57) sp17423 sp17480)) (joinSmall (lo:=17537) (a:=114) (b:=114) (joinSmall (lo:=17537) (a:=57) (b:=57) sp17537 sp17594) (joinSmall (lo:=17651) (a:=57) (b:=57) sp17651 sp17708))) (joinSmall (lo:=17765) (a:=228) (b:=228) (joinSmall (lo:=17765) (a:=114) (b:=114) (joinSmall (lo:=17765) (a:=57) (b:=57) sp17765 sp17822) (joinSmall (lo:=17879) (a:=57) (b:=57) sp17879 sp17936)) (joinSmall (lo:=17993) (a:=114) (b:=114) (joinSmall (lo:=17993) (a:=57) (b:=57) sp17993 sp18050) (joinSmall (lo:=18107) (a:=57) (b:=57) sp18107 sp18164)))))) (joinSmall (lo:=18221) (a:=1822) (b:=1823) (joinSmall (lo:=18221) (a:=911) (b:=911) (joinSmall (lo:=18221) (a:=455) (b:=456) (joinSmall (lo:=18221) (a:=227) (b:=228) (joinSmall (lo:=18221) (a:=113) (b:=114) (joinSmall (lo:=18221) (a:=56) (b:=57) sp18221 sp18277) (joinSmall (lo:=18334) (a:=57) (b:=57) sp18334 sp18391)) (joinSmall (lo:=18448) (a:=114) (b:=114) (joinSmall (lo:=18448) (a:=57) (b:=57) sp18448 sp18505) (joinSmall (lo:=18562) (a:=57) (b:=57) sp18562 sp18619))) (joinSmall (lo:=18676) (a:=228) (b:=228) (joinSmall (lo:=18676) (a:=114) (b:=114) (joinSmall (lo:=18676) (a:=57) (b:=57) sp18676 sp18733) (joinSmall (lo:=18790) (a:=57) (b:=57) sp18790 sp18847)) (joinSmall (lo:=18904) (a:=114) (b:=114) (joinSmall (lo:=18904) (a:=57) (b:=57) sp18904 sp18961) (joinSmall (lo:=19018) (a:=57) (b:=57) sp19018 sp19075)))) (joinSmall (lo:=19132) (a:=455) (b:=456) (joinSmall (lo:=19132) (a:=227) (b:=228) (joinSmall (lo:=19132) (a:=113) (b:=114) (joinSmall (lo:=19132) (a:=56) (b:=57) sp19132 sp19188) (joinSmall (lo:=19245) (a:=57) (b:=57) sp19245 sp19302)) (joinSmall (lo:=19359) (a:=114) (b:=114) (joinSmall (lo:=19359) (a:=57) (b:=57) sp19359 sp19416) (joinSmall (lo:=19473) (a:=57) (b:=57) sp19473 sp19530))) (joinSmall (lo:=19587) (a:=228) (b:=228) (joinSmall (lo:=19587) (a:=114) (b:=114) (joinSmall (lo:=19587) (a:=57) (b:=57) sp19587 sp19644) (joinSmall (lo:=19701) (a:=57) (b:=57) sp19701 sp19758)) (joinSmall (lo:=19815) (a:=114) (b:=114) (joinSmall (lo:=19815) (a:=57) (b:=57) sp19815 sp19872) (joinSmall (lo:=19929) (a:=57) (b:=57) sp19929 sp19986))))) (joinSmall (lo:=20043) (a:=911) (b:=912) (joinSmall (lo:=20043) (a:=455) (b:=456) (joinSmall (lo:=20043) (a:=227) (b:=228) (joinSmall (lo:=20043) (a:=113) (b:=114) (joinSmall (lo:=20043) (a:=56) (b:=57) sp20043 sp20099) (joinSmall (lo:=20156) (a:=57) (b:=57) sp20156 sp20213)) (joinSmall (lo:=20270) (a:=114) (b:=114) (joinSmall (lo:=20270) (a:=57) (b:=57) sp20270 sp20327) (joinSmall (lo:=20384) (a:=57) (b:=57) sp20384 sp20441))) (joinSmall (lo:=20498) (a:=228) (b:=228) (joinSmall (lo:=20498) (a:=114) (b:=114) (joinSmall (lo:=20498) (a:=57) (b:=57) sp20498 sp20555) (joinSmall (lo:=20612) (a:=57) (b:=57) sp20612 sp20669)) (joinSmall (lo:=20726) (a:=114) (b:=114) (joinSmall (lo:=20726) (a:=57) (b:=57) sp20726 sp20783) (joinSmall (lo:=20840) (a:=57) (b:=57) sp20840 sp20897)))) (joinSmall (lo:=20954) (a:=456) (b:=456) (joinSmall (lo:=20954) (a:=228) (b:=228) (joinSmall (lo:=20954) (a:=114) (b:=114) (joinSmall (lo:=20954) (a:=57) (b:=57) sp20954 sp21011) (joinSmall (lo:=21068) (a:=57) (b:=57) sp21068 sp21125)) (joinSmall (lo:=21182) (a:=114) (b:=114) (joinSmall (lo:=21182) (a:=57) (b:=57) sp21182 sp21239) (joinSmall (lo:=21296) (a:=57) (b:=57) sp21296 sp21353))) (joinSmall (lo:=21410) (a:=228) (b:=228) (joinSmall (lo:=21410) (a:=114) (b:=114) (joinSmall (lo:=21410) (a:=57) (b:=57) sp21410 sp21467) (joinSmall (lo:=21524) (a:=57) (b:=57) sp21524 sp21581)) (joinSmall (lo:=21638) (a:=114) (b:=114) (joinSmall (lo:=21638) (a:=57) (b:=57) sp21638 sp21695) (joinSmall (lo:=21752) (a:=57) (b:=57) sp21752 sp21809))))))) (joinSmall (lo:=21866) (a:=3644) (b:=3645) (joinSmall (lo:=21866) (a:=1822) (b:=1822) (joinSmall (lo:=21866) (a:=911) (b:=911) (joinSmall (lo:=21866) (a:=455) (b:=456) (joinSmall (lo:=21866) (a:=227) (b:=228) (joinSmall (lo:=21866) (a:=113) (b:=114) (joinSmall (lo:=21866) (a:=56) (b:=57) sp21866 sp21922) (joinSmall (lo:=21979) (a:=57) (b:=57) sp21979 sp22036)) (joinSmall (lo:=22093) (a:=114) (b:=114) (joinSmall (lo:=22093) (a:=57) (b:=57) sp22093 sp22150) (joinSmall (lo:=22207) (a:=57) (b:=57) sp22207 sp22264))) (joinSmall (lo:=22321) (a:=228) (b:=228) (joinSmall (lo:=22321) (a:=114) (b:=114) (joinSmall (lo:=22321) (a:=57) (b:=57) sp22321 sp22378) (joinSmall (lo:=22435) (a:=57) (b:=57) sp22435 sp22492)) (joinSmall (lo:=22549) (a:=114) (b:=114) (joinSmall (lo:=22549) (a:=57) (b:=57) sp22549 sp22606) (joinSmall (lo:=22663) (a:=57) (b:=57) sp22663 sp22720)))) (joinSmall (lo:=22777) (a:=455) (b:=456) (joinSmall (lo:=22777) (a:=227) (b:=228) (joinSmall (lo:=22777) (a:=113) (b:=114) (joinSmall (lo:=22777) (a:=56) (b:=57) sp22777 sp22833) (joinSmall (lo:=22890) (a:=57) (b:=57) sp22890 sp22947)) (joinSmall (lo:=23004) (a:=114) (b:=114) (joinSmall (lo:=23004) (a:=57) (b:=57) sp23004 sp23061) (joinSmall (lo:=23118) (a:=57) (b:=57) sp23118 sp23175))) (joinSmall (lo:=23232) (a:=228) (b:=228) (joinSmall (lo:=23232) (a:=114) (b:=114) (joinSmall (lo:=23232) (a:=57) (b:=57) sp23232 sp23289) (joinSmall (lo:=23346) (a:=57) (b:=57) sp23346 sp23403)) (joinSmall (lo:=23460) (a:=114) (b:=114) (joinSmall (lo:=23460) (a:=57) (b:=57) sp23460 sp23517) (joinSmall (lo:=23574) (a:=57) (b:=57) sp23574 sp23631))))) (joinSmall (lo:=23688) (a:=911) (b:=911) (joinSmall (lo:=23688) (a:=455) (b:=456) (joinSmall (lo:=23688) (a:=227) (b:=228) (joinSmall (lo:=23688) (a:=113) (b:=114) (joinSmall (lo:=23688) (a:=56) (b:=57) sp23688 sp23744) (joinSmall (lo:=23801) (a:=57) (b:=57) sp23801 sp23858)) (joinSmall (lo:=23915) (a:=114) (b:=114) (joinSmall (lo:=23915) (a:=57) (b:=57) sp23915 sp23972) (joinSmall (lo:=24029) (a:=57) (b:=57) sp24029 sp24086))) (joinSmall (lo:=24143) (a:=228) (b:=228) (joinSmall (lo:=24143) (a:=114) (b:=114) (joinSmall (lo:=24143) (a:=57) (b:=57) sp24143 sp24200) (joinSmall (lo:=24257) (a:=57) (b:=57) sp24257 sp24314)) (joinSmall (lo:=24371) (a:=114) (b:=114) (joinSmall (lo:=24371) (a:=57) (b:=57) sp24371 sp24428) (joinSmall (lo:=24485) (a:=57) (b:=57) sp24485 sp24542)))) (joinSmall (lo:=24599) (a:=455) (b:=456) (joinSmall (lo:=24599) (a:=227) (b:=228) (joinSmall (lo:=24599) (a:=113) (b:=114) (joinSmall (lo:=24599) (a:=56) (b:=57) sp24599 sp24655) (joinSmall (lo:=24712) (a:=57) (b:=57) sp24712 sp24769)) (joinSmall (lo:=24826) (a:=114) (b:=114) (joinSmall (lo:=24826) (a:=57) (b:=57) sp24826 sp24883) (joinSmall (lo:=24940) (a:=57) (b:=57) sp24940 sp24997))) (joinSmall (lo:=25054) (a:=228) (b:=228) (joinSmall (lo:=25054) (a:=114) (b:=114) (joinSmall (lo:=25054) (a:=57) (b:=57) sp25054 sp25111) (joinSmall (lo:=25168) (a:=57) (b:=57) sp25168 sp25225)) (joinSmall (lo:=25282) (a:=114) (b:=114) (joinSmall (lo:=25282) (a:=57) (b:=57) sp25282 sp25339) (joinSmall (lo:=25396) (a:=57) (b:=57) sp25396 sp25453)))))) (joinSmall (lo:=25510) (a:=1822) (b:=1823) (joinSmall (lo:=25510) (a:=911) (b:=911) (joinSmall (lo:=25510) (a:=455) (b:=456) (joinSmall (lo:=25510) (a:=227) (b:=228) (joinSmall (lo:=25510) (a:=113) (b:=114) (joinSmall (lo:=25510) (a:=56) (b:=57) sp25510 sp25566) (joinSmall (lo:=25623) (a:=57) (b:=57) sp25623 sp25680)) (joinSmall (lo:=25737) (a:=114) (b:=114) (joinSmall (lo:=25737) (a:=57) (b:=57) sp25737 sp25794) (joinSmall (lo:=25851) (a:=57) (b:=57) sp25851 sp25908))) (joinSmall (lo:=25965) (a:=228) (b:=228) (joinSmall (lo:=25965) (a:=114) (b:=114) (joinSmall (lo:=25965) (a:=57) (b:=57) sp25965 sp26022) (joinSmall (lo:=26079) (a:=57) (b:=57) sp26079 sp26136)) (joinSmall (lo:=26193) (a:=114) (b:=114) (joinSmall (lo:=26193) (a:=57) (b:=57) sp26193 sp26250) (joinSmall (lo:=26307) (a:=57) (b:=57) sp26307 sp26364)))) (joinSmall (lo:=26421) (a:=455) (b:=456) (joinSmall (lo:=26421) (a:=227) (b:=228) (joinSmall (lo:=26421) (a:=113) (b:=114) (joinSmall (lo:=26421) (a:=56) (b:=57) sp26421 sp26477) (joinSmall (lo:=26534) (a:=57) (b:=57) sp26534 sp26591)) (joinSmall (lo:=26648) (a:=114) (b:=114) (joinSmall (lo:=26648) (a:=57) (b:=57) sp26648 sp26705) (joinSmall (lo:=26762) (a:=57) (b:=57) sp26762 sp26819))) (joinSmall (lo:=26876) (a:=228) (b:=228) (joinSmall (lo:=26876) (a:=114) (b:=114) (joinSmall (lo:=26876) (a:=57) (b:=57) sp26876 sp26933) (joinSmall (lo:=26990) (a:=57) (b:=57) sp26990 sp27047)) (joinSmall (lo:=27104) (a:=114) (b:=114) (joinSmall (lo:=27104) (a:=57) (b:=57) sp27104 sp27161) (joinSmall (lo:=27218) (a:=57) (b:=57) sp27218 sp27275))))) (joinSmall (lo:=27332) (a:=911) (b:=912) (joinSmall (lo:=27332) (a:=455) (b:=456) (joinSmall (lo:=27332) (a:=227) (b:=228) (joinSmall (lo:=27332) (a:=113) (b:=114) (joinSmall (lo:=27332) (a:=56) (b:=57) sp27332 sp27388) (joinSmall (lo:=27445) (a:=57) (b:=57) sp27445 sp27502)) (joinSmall (lo:=27559) (a:=114) (b:=114) (joinSmall (lo:=27559) (a:=57) (b:=57) sp27559 sp27616) (joinSmall (lo:=27673) (a:=57) (b:=57) sp27673 sp27730))) (joinSmall (lo:=27787) (a:=228) (b:=228) (joinSmall (lo:=27787) (a:=114) (b:=114) (joinSmall (lo:=27787) (a:=57) (b:=57) sp27787 sp27844) (joinSmall (lo:=27901) (a:=57) (b:=57) sp27901 sp27958)) (joinSmall (lo:=28015) (a:=114) (b:=114) (joinSmall (lo:=28015) (a:=57) (b:=57) sp28015 sp28072) (joinSmall (lo:=28129) (a:=57) (b:=57) sp28129 sp28186)))) (joinSmall (lo:=28243) (a:=456) (b:=456) (joinSmall (lo:=28243) (a:=228) (b:=228) (joinSmall (lo:=28243) (a:=114) (b:=114) (joinSmall (lo:=28243) (a:=57) (b:=57) sp28243 sp28300) (joinSmall (lo:=28357) (a:=57) (b:=57) sp28357 sp28414)) (joinSmall (lo:=28471) (a:=114) (b:=114) (joinSmall (lo:=28471) (a:=57) (b:=57) sp28471 sp28528) (joinSmall (lo:=28585) (a:=57) (b:=57) sp28585 sp28642))) (joinSmall (lo:=28699) (a:=228) (b:=228) (joinSmall (lo:=28699) (a:=114) (b:=114) (joinSmall (lo:=28699) (a:=57) (b:=57) sp28699 sp28756) (joinSmall (lo:=28813) (a:=57) (b:=57) sp28813 sp28870)) (joinSmall (lo:=28927) (a:=114) (b:=114) (joinSmall (lo:=28927) (a:=57) (b:=57) sp28927 sp28984) (joinSmall (lo:=29041) (a:=57) (b:=57) sp29041 sp29098)))))))))
  have good : (List.range 29155).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 850000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 29154 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 29154 := by
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


private def packet (i : ℕ) : ℕ := (if i < 216 then (if i < 108 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else 0)))) else (if i < 20 then (if i < 16 then (if i < 14 then 0 else (if i < 15 then 0 else 0)) else (if i < 18 then (if i < 17 then 0 else 0) else (if i < 19 then 0 else 0))) else (if i < 23 then (if i < 21 then 0 else (if i < 22 then 0 else 0)) else (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else 0))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then 0 else (if i < 29 then 0 else 0)) else (if i < 31 then 0 else (if i < 32 then 0 else 0))) else (if i < 36 then (if i < 34 then 0 else (if i < 35 then 0 else 0)) else (if i < 38 then (if i < 37 then 0 else 0) else (if i < 39 then 0 else 0)))) else (if i < 47 then (if i < 43 then (if i < 41 then 0 else (if i < 42 then 0 else 0)) else (if i < 45 then (if i < 44 then 0 else 0) else (if i < 46 then 0 else 0))) else (if i < 50 then (if i < 48 then 0 else (if i < 49 then 0 else 0)) else (if i < 52 then (if i < 51 then 0 else 0) else (if i < 53 then 0 else 0)))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then 0 else (if i < 56 then 0 else 0)) else (if i < 58 then 0 else (if i < 59 then 0 else 0))) else (if i < 63 then (if i < 61 then 0 else (if i < 62 then 0 else 0)) else (if i < 65 then (if i < 64 then 0 else 0) else (if i < 66 then 0 else 0)))) else (if i < 74 then (if i < 70 then (if i < 68 then 0 else (if i < 69 then 0 else 0)) else (if i < 72 then (if i < 71 then 0 else 0) else (if i < 73 then 0 else 0))) else (if i < 77 then (if i < 75 then 0 else (if i < 76 then 0 else 0)) else (if i < 79 then (if i < 78 then 0 else 0) else (if i < 80 then 0 else 0))))) else (if i < 94 then (if i < 87 then (if i < 84 then (if i < 82 then 0 else (if i < 83 then 0 else 0)) else (if i < 85 then 0 else (if i < 86 then 0 else 0))) else (if i < 90 then (if i < 88 then 0 else (if i < 89 then 0 else 0)) else (if i < 92 then (if i < 91 then 0 else 0) else (if i < 93 then 0 else 0)))) else (if i < 101 then (if i < 97 then (if i < 95 then 0 else (if i < 96 then 0 else 0)) else (if i < 99 then (if i < 98 then 0 else 0) else (if i < 100 then 0 else 0))) else (if i < 104 then (if i < 102 then 0 else (if i < 103 then 0 else 0)) else (if i < 106 then (if i < 105 then 0 else 0) else (if i < 107 then 0 else 0))))))) else (if i < 162 then (if i < 135 then (if i < 121 then (if i < 114 then (if i < 111 then (if i < 109 then 0 else (if i < 110 then 0 else 0)) else (if i < 112 then 0 else (if i < 113 then 0 else 0))) else (if i < 117 then (if i < 115 then 0 else (if i < 116 then 0 else 0)) else (if i < 119 then (if i < 118 then 0 else 0) else (if i < 120 then 0 else 0)))) else (if i < 128 then (if i < 124 then (if i < 122 then 0 else (if i < 123 then 0 else 0)) else (if i < 126 then (if i < 125 then 0 else 0) else (if i < 127 then 0 else 0))) else (if i < 131 then (if i < 129 then 0 else (if i < 130 then 0 else 0)) else (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else 0))))) else (if i < 148 then (if i < 141 then (if i < 138 then (if i < 136 then 0 else (if i < 137 then 0 else 0)) else (if i < 139 then 0 else (if i < 140 then 0 else 0))) else (if i < 144 then (if i < 142 then 0 else (if i < 143 then 0 else 0)) else (if i < 146 then (if i < 145 then 0 else 0) else (if i < 147 then 0 else 0)))) else (if i < 155 then (if i < 151 then (if i < 149 then 0 else (if i < 150 then 0 else 0)) else (if i < 153 then (if i < 152 then 0 else 0) else (if i < 154 then 0 else 0))) else (if i < 158 then (if i < 156 then 0 else (if i < 157 then 0 else 0)) else (if i < 160 then (if i < 159 then 0 else 0) else (if i < 161 then 0 else 0)))))) else (if i < 189 then (if i < 175 then (if i < 168 then (if i < 165 then (if i < 163 then 0 else (if i < 164 then 0 else 0)) else (if i < 166 then 0 else (if i < 167 then 0 else 0))) else (if i < 171 then (if i < 169 then 0 else (if i < 170 then 0 else 0)) else (if i < 173 then (if i < 172 then 0 else 0) else (if i < 174 then 0 else 0)))) else (if i < 182 then (if i < 178 then (if i < 176 then 0 else (if i < 177 then 0 else 0)) else (if i < 180 then (if i < 179 then 0 else 0) else (if i < 181 then 0 else 0))) else (if i < 185 then (if i < 183 then 0 else (if i < 184 then 0 else 0)) else (if i < 187 then (if i < 186 then 0 else 0) else (if i < 188 then 0 else 0))))) else (if i < 202 then (if i < 195 then (if i < 192 then (if i < 190 then 0 else (if i < 191 then 0 else 0)) else (if i < 193 then 0 else (if i < 194 then 0 else 0))) else (if i < 198 then (if i < 196 then 0 else (if i < 197 then 0 else 0)) else (if i < 200 then (if i < 199 then 0 else 0) else (if i < 201 then 0 else 0)))) else (if i < 209 then (if i < 205 then (if i < 203 then 0 else (if i < 204 then 0 else 0)) else (if i < 207 then (if i < 206 then 0 else 0) else (if i < 208 then 0 else 0))) else (if i < 212 then (if i < 210 then 0 else (if i < 211 then 0 else 0)) else (if i < 214 then (if i < 213 then 0 else 0) else (if i < 215 then 0 else 0)))))))) else (if i < 324 then (if i < 270 then (if i < 243 then (if i < 229 then (if i < 222 then (if i < 219 then (if i < 217 then 0 else (if i < 218 then 0 else 0)) else (if i < 220 then 0 else (if i < 221 then 0 else 0))) else (if i < 225 then (if i < 223 then 0 else (if i < 224 then 0 else 0)) else (if i < 227 then (if i < 226 then 0 else 0) else (if i < 228 then 0 else 0)))) else (if i < 236 then (if i < 232 then (if i < 230 then 0 else (if i < 231 then 0 else 0)) else (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else 0))) else (if i < 239 then (if i < 237 then 0 else (if i < 238 then 0 else 0)) else (if i < 241 then (if i < 240 then 0 else 0) else (if i < 242 then 0 else 0))))) else (if i < 256 then (if i < 249 then (if i < 246 then (if i < 244 then 0 else (if i < 245 then 0 else 0)) else (if i < 247 then 0 else (if i < 248 then 0 else 0))) else (if i < 252 then (if i < 250 then 0 else (if i < 251 then 0 else 0)) else (if i < 254 then (if i < 253 then 0 else 0) else (if i < 255 then 0 else 0)))) else (if i < 263 then (if i < 259 then (if i < 257 then 0 else (if i < 258 then 0 else 0)) else (if i < 261 then (if i < 260 then 0 else 0) else (if i < 262 then 0 else 0))) else (if i < 266 then (if i < 264 then 0 else (if i < 265 then 0 else 0)) else (if i < 268 then (if i < 267 then 0 else 0) else (if i < 269 then 0 else 0)))))) else (if i < 297 then (if i < 283 then (if i < 276 then (if i < 273 then (if i < 271 then 0 else (if i < 272 then 0 else 0)) else (if i < 274 then 0 else (if i < 275 then 0 else 0))) else (if i < 279 then (if i < 277 then 0 else (if i < 278 then 0 else 0)) else (if i < 281 then (if i < 280 then 0 else 0) else (if i < 282 then 0 else 0)))) else (if i < 290 then (if i < 286 then (if i < 284 then 0 else (if i < 285 then 0 else 0)) else (if i < 288 then (if i < 287 then 0 else 0) else (if i < 289 then 0 else 0))) else (if i < 293 then (if i < 291 then 0 else (if i < 292 then 0 else 0)) else (if i < 295 then (if i < 294 then 0 else 0) else (if i < 296 then 0 else 0))))) else (if i < 310 then (if i < 303 then (if i < 300 then (if i < 298 then 0 else (if i < 299 then 0 else 0)) else (if i < 301 then 0 else (if i < 302 then 0 else 0))) else (if i < 306 then (if i < 304 then 0 else (if i < 305 then 0 else 0)) else (if i < 308 then (if i < 307 then 0 else 0) else (if i < 309 then 0 else 0)))) else (if i < 317 then (if i < 313 then (if i < 311 then 0 else (if i < 312 then 0 else 0)) else (if i < 315 then (if i < 314 then 0 else 0) else (if i < 316 then 0 else 0))) else (if i < 320 then (if i < 318 then 0 else (if i < 319 then 0 else 0)) else (if i < 322 then (if i < 321 then 0 else 0) else (if i < 323 then 0 else 0))))))) else (if i < 378 then (if i < 351 then (if i < 337 then (if i < 330 then (if i < 327 then (if i < 325 then 0 else (if i < 326 then 0 else 0)) else (if i < 328 then 0 else (if i < 329 then 0 else 0))) else (if i < 333 then (if i < 331 then 0 else (if i < 332 then 0 else 0)) else (if i < 335 then (if i < 334 then 0 else 0) else (if i < 336 then 0 else 0)))) else (if i < 344 then (if i < 340 then (if i < 338 then 0 else (if i < 339 then 0 else 0)) else (if i < 342 then (if i < 341 then 0 else 0) else (if i < 343 then 0 else 0))) else (if i < 347 then (if i < 345 then 0 else (if i < 346 then 0 else 0)) else (if i < 349 then (if i < 348 then 0 else 0) else (if i < 350 then 0 else 0))))) else (if i < 364 then (if i < 357 then (if i < 354 then (if i < 352 then 0 else (if i < 353 then 0 else 0)) else (if i < 355 then 0 else (if i < 356 then 0 else 0))) else (if i < 360 then (if i < 358 then 0 else (if i < 359 then 0 else 0)) else (if i < 362 then (if i < 361 then 0 else 0) else (if i < 363 then 0 else 0)))) else (if i < 371 then (if i < 367 then (if i < 365 then 0 else (if i < 366 then 0 else 0)) else (if i < 369 then (if i < 368 then 0 else 0) else (if i < 370 then 0 else 0))) else (if i < 374 then (if i < 372 then 0 else (if i < 373 then 0 else 0)) else (if i < 376 then (if i < 375 then 0 else 0) else (if i < 377 then 0 else 0)))))) else (if i < 405 then (if i < 391 then (if i < 384 then (if i < 381 then (if i < 379 then 0 else (if i < 380 then 0 else 0)) else (if i < 382 then 0 else (if i < 383 then 0 else 0))) else (if i < 387 then (if i < 385 then 0 else (if i < 386 then 0 else 0)) else (if i < 389 then (if i < 388 then 0 else 0) else (if i < 390 then 0 else 0)))) else (if i < 398 then (if i < 394 then (if i < 392 then 0 else (if i < 393 then 0 else 0)) else (if i < 396 then (if i < 395 then 0 else 0) else (if i < 397 then 0 else 0))) else (if i < 401 then (if i < 399 then 0 else (if i < 400 then 0 else 0)) else (if i < 403 then (if i < 402 then 0 else 0) else (if i < 404 then 0 else 0))))) else (if i < 419 then (if i < 412 then (if i < 408 then (if i < 406 then 0 else (if i < 407 then 0 else 0)) else (if i < 410 then (if i < 409 then 0 else 0) else (if i < 411 then 0 else 0))) else (if i < 415 then (if i < 413 then 0 else (if i < 414 then 0 else 0)) else (if i < 417 then (if i < 416 then 0 else 0) else (if i < 418 then 0 else 0)))) else (if i < 426 then (if i < 422 then (if i < 420 then 0x286f9a82bb946497a4521f98e6c66c2de142088c39216708082b00ac0000286f3b32ca94e09a446f2078eb46a42fc14b08b43a617508c82f80ba0000286edde2bd145897445e1fb0e506642de13f88ac38e16e08c82dc0b20000286e7f72cc14c09aa4752048e906902e914888bc39617108f03000b60000286e2352b1140094444d1f80e646602d213c889439416408802e40ba0000286dc802ae13f895444d1f88e306702da140888437815d08402bc0b60000286d6842ce14e89b44702028ea468e2eb14908b03b218108e82d00b60000286d0b42bb14889964692078ec46aa2f914c08d83b017408c02cc0ac0000286cae22b994489684511f60e146522d813f086c38016908a82fc0b20000286c53c2a793708ea4191e18db46322c213a084c36e16508682e40b20000286bf402cd15049ac4762048ea86a42f814708bc3a816b08c82e40a40000286b93d2d595189d24932158f3c6d22fe15108d43b217608582dc0a80000286b34c2c894dc99a4792148f3c6f031115609403de18909402f00be0000286ada32aa13f49544511f90e806862e614308ac38617108682b80aa0000286a7bd2bc148098846b2048ea469e2ee14508bc39c16f08a83040c40000286a1f32b0940c94e43c1ef8df464c2d5140089c37c16808d02f80c800002869bec2cf95289e048f2168f106c22f914a89003bc17d08d82ec0aa000028695fa2c994cc9a848020d0ee06ba2f414b89043b617d09383180cc0000286901c2bd94889a046e2088eb46982f914908ec3b018509203240c600002868a292c494ac99e45d1ff0e886922ed14d09003ba17308882cc0b2000028684542ba14489724702100f286dc30b15489483dc18c09103200ba00002867e7f2b9144497e45c1fc0e5c6682d113c089838617108402c80a8000028678c62b513f493a44c1f78e546742d5138884437616108182d00b6000028672fd2b614109524481f20e346742da13a887037015d082828c0b000002866d2e2be14809924632040ea06922dd13b886837e16508002a80a00000286670a2de15949e649821c0f546de30714d88f03b817808e03040be000028661362b4940c9664602070ec469c2f314c88e83c218209103100d200002865b722b6946897646d2028e9067e2dc13b886838416808502d409e0000286559d2c114889a24732050ea06942e714688cc3c218508f02e40c600002864fcd2b9945c98a45c2000eac69e2f314988cc3be18309182ec09a000028649e42c514c898e4712098ed86b02f214808e03ac17908d02ec0ae000028644232ad943096844a1f98e346602da13d887837a16308302a40b400002863e712ad93f09424431ee8e3c6682da140887038017008d83180c2000028638b02b313f895044e1f68e446582bc13a088c3a017108b82e40b40000286331029e938091642e1ec8dcc6302c4132884836a14e07c02a40a200002862d362b914349604451f50e2c65e2d5144888837816408402b00a8000028627662bb949499a4722070edc6a430014d08f83b217e08c82e00a4000028621802c514b499246d20a8edc69a2f014d88f43d017c08e83100da00002861ba42c394a898845d2090eb46aa2fb15408f83aa17408a82c80a4000028615d82b013bc94c4471f28e386622da140089c39616d08882d00ba00002860fe72c914a09ae47720f8eec6b82fc14908ec3a417408c02dc0b400002860a172bd94a09904661fe8e7c6962e9140089439016b08a82e00ba000028604442bd94b099c46a1fc0e846982f814e89303ce18709202e40aa0000285fe612bc94509744601fc0e6c6722e114608bc3b017a08b02f80d20000285f8772c894bc9b84862170f446f431b15b09603dc18909503280ce0000285f2bd2ab13f09444401f58e6c6802db142888c3b418308e83000c00000285ecfa2af94149404401f28e606702df145089c3a017208c82fc0b60000285e7332b3942c94c44d1f38e5866c2dc13f08ac38e16408702bc0aa0000285e15d2b8141c96e4501fb0e786922f414a88f43b817f08b82fc0bc0000285db9d2ae140c93c43d1e90df46422cd135886838816908b02c00aa0000285d5e22af94089504451f40e506622e014588b43a617509003280d20000285cffd2c494b899e4742098efc6c430715088fc3c218809703000ba0000285ca382b094049544481fe8e6c6902e114308b83b418609103140bc0000285c4732ad13ec94c44a1f80e486602e013e088c39816c08502d80ac0000285bec42a913e09384421f80e1465c2d713a08ac3b617008b82ec0ce0000285b8c82cb94e49b047120a0f206d630415109003ca192094830c0ca0000285b2fc2b3947498a46b2068eb86a62fd14d08b83a417708b830c0ca0000285acee2ce94fc9ba4822138f186d230214f88f83b617c09002dc0b60000285a7292b6941c9564511fc8e6c6642e214808bc39e17d08c82f40b60000285a1512c4147898c46c1ff0ec06a02e014308a039c17708b82dc0aa00002859b9c2a9940893643f1f38e306682d5142888c38816408882f40c0000028595912d115189c248b20d8edc6b82f714c09183d218509683140c400002858fee2a593b893844a1f58e3c66e2e614788cc39e16408902ec0ba000028589f12ce95009c647920f0f006b82fe14f88f03c417708982ec0b8000 else (if i < 421 then 0x2886faf2b814589704551fa8e6067c2df13a888c37416c08f03180bc000028869b32cd94cc9844652040ecc6822df14708d43a817308902d80c6000028863db2c214b499847520a8ebc6ae2ef14788d039816c07f82a80ae00002885e102bc945c9744622068e8069a2eb14088ac39816a08d82f80ce0000288582c2c2149498c4651fe0e986a02f714c88e83ae17e09082f40c80000288526f2ac13f89644581fb8e6067c2dc142889c39417108e82f00b600002884cb92b113e494e4411f40e106682dc14388c03a617408e82f40ba000028846d52c714f89ba48220e8ee06982e4141089439817008802cc0b4000028840f82c1948c9924632008e5c6722e1138889c39a16708782f00aa00002883b322b5145096845a1fc8e886862e514408ac3a417809083240c00000288356e2b3141093c4461f10df46322bf138088439417809183240d600002882f6f2ca95109e04882140f1c6d830115288fc3ca17c090831c0c60000288297a2cb14ec9c248320d0ec46982ed14e89083c818109683200c40000288237e2ca94e89b847e2150f046be30d15109103ae17608c02f00c200002881d9a2c0946098445c2010e786762db14088c03ae17808c83180c6000028817e32ac14189484601fe8e4c6602d314088b439617609082ec0be0000288120c2bf148498e4621fe0e7c6762d813f087837a16708902d40b000002880c0b2cc95049c647620e0ed86ae2f814a88b039616f08b02f00b80000288064d2b2941894844b1f18e146762d513f889c3a617809303080c4000028800912b2140c95a4561fd8e9867a2e514208ac3a817608e02e80c20000287fad92af14089444441f40df46482c4136884836e16108302b009a0000287f4e22cc14b89ae47a2118f146e431515e09483ec19409703340ca0000287ef182b7946097c45e1ff8eb06a22f414e88ec3bc180091033c0c40000287e9392c494a898a45d2038ea46902e914588783a017808e02d40b80000287e3652be146097e4651fc0e8468c2f614888c839017608e02f40d20000287dd7b2c694a898e4662060eac68e2ec14708d83b418008d03100ca0000287d79c2c214a098c4632018e986902f314888b03a417208c82dc0c80000287d1d02b3944895444d1fa0e3c65e2d4140887439017608e02e00c60000287cbf12be148c9804611fe0e8467e2e314a08d03b217808882dc0c00000287c6492a913b093243d1f80e5c65e2d3139884438216e08982d80ca0000287c0832b6943897445e1ff0e7c6762df13f88ac39e16508702e00bc0000287ba9e2c914d49a646c20b0eb46b22fb14a08ec3b417208c83380c20000287b4a92cb94c899647220d8f046a62ec14808bc39217408e82f00b80000287aee72b1142895e4511f98e346602cf135889039016a08a82f00b60000287a8fd2c314a09a246c20d0ec06ba30215709003c417d08b02f40cc0000287a33f2ae93f093243d1ed0df86402d114008a83aa17f08d02f40aa00002879d7c2b013fc9524541fa8e5c6842e414908d03a817e08902c80ac0000287977b2d095209d84862188f486e431815509183c617808d83180ca000028791b42b2942096445f2010e786942e213f887837c16308b83080c600002878bd42c2948499247920a8ec06a62ea14988c039a17108c82c00a2000028785e72c914cc99a4702078e986802e714708c839c16c08b82f00d000002877ff12c994f09ac47220e0ef46be30215109183d218b09603000c200002877a302af940c94e4491f88e7c66c2e514708ac39e16908b83000a80000287745c2b894709a246f2090edc6c02f715088fc3c017c09302d40cc00002876e662ce94fc99a47220b0ec06a62fe14e88d039e17a09283100ce0000287688a2bd947898245b2020e906962ed14788b43b617808b02d40aa000028762b72b694589684531f70e346582d5137885838a16008682d00a600002875cc62cb14ac98e4672020ea46942ed14d08e03b817609103000d2000028756fa2be946898046b2038eb06bc2fc15088e43b417008a82e40ae000028751382b0942494c43e1f30e546782e114108943a017709082e80be00002874b532c894ac99c4692038ea468e2f415188e039617308902ec0c6000028745922b193f894e4461f28e246522df142088439617808f82fc0b800002873fb92bd146897a45c1fc0e906942f014909043b418408d03180be000028739cc2c494d49a04772068ec46982f014688c03a017208d82f00b2000028733f92be145c97045e1fe0e786722e113e889c3a417a08b02cc0b000002872e402af13f892c4491f58e4066a2d714088c83b017908f030c0b20000287284a2cc15149ce47f2110f106ba2f714888f03c217d090030408e0000287227c2b9941c96645b1fd0e646702e714b08e43b617508902cc0c200002871c9a2c614dc9b24752058eac6842dd14508a039617a08d82e00a4000028716ce2b814789744551fd0e946962e314588b43a817208d02d00c0000028711132ac13f893443d1ec0df063c2ca138887038e16f08602c80ac00002870b642a493bc9364501fd8e7867a2e2141889838a16908702c40c6000028705632d294ec9b847c20c0eb06a22f214b88c039a17d08e83100c60000286ff812c3945096a4591fd0e7c6762da14308a039016f08402c00b8000 else 0x289e5b32af943494e4431f18e006422cd13988a439417408b82f40b80000289dfeb2b2144496c4531f98e606702d7140087c38616c08882f80c80000289da072c094a099047520b0ed86b22fa15188e83b817508d02f40c60000289d43b2b3942c9564431f68e246702df143086038217008282c00b20000289ce872a813ec93e43e1f08e546662db141886438216d08782e00a60000289c8bb2ba14709744551fc0e886802e2144088c39016408582a008e0000289c2f32b5945c9884652048eb06a62f314508f03ac17808a02bc0ba0000289bd132c614dc9ae47520b8ee86ac2fa14b08e83a816f08702cc09c0000289b72e2c394a498c46a2010e906962ee14808ac3aa17508b02e80ae0000289b1452c614b49984702038e8869c2f514f09143d618a09302f80c80000289ab502ca949c9aa4712070ea06a02fe14a08e83b018009283400d80000289a58a2b5943895a44d1fa8e606722d5138083837215a07e02b40ba00002899fc12b714449744561fd0e706802d213f884c36c15e07f8278096000028999e92bd14989904652030eb469c2f114d88dc3bc184092030c0d4000028993f92c994d89c248720d0ec068c2e914708e43c417b08b02bc0ac00002898e2e2b6144095a44b1f80e3c6822eb14308a039217308782b40ac000028988502bf148098c4732090eb46a42f114c08f83a817508a82f00b0000028982662c394b09804652050e946902ef14b08c039a17108682dc0b000002897c682c2949c99c4692038e8c6862ea14a890c3bc17408d02fc0bc000028976a42b5144897645e1fe8ea46982ec14808c83aa18008f03040c00000289709f2d395049c847b20c0ee46a82fa14f89343de19609582f80d000002896acc2b9946098e4652088ec86c22fb152090c3d017f08b02dc0ba000028965092b4141896445d2018e7c6842e714308bc39e17208a83000c000002895f202bf148c99c4722060e986aa30015109283e018909402f80c4000028959312c494909824651fa8e5067c2e6140889c39e17508a02cc0b4000028953622b694549824672080e986922ed14708cc3a417108a02e40c400002894da62ab93dc94844d1f78e4467c2e514888a03a817a08c03100d2000028947dc2b914549804602028e986a62f415108fc3bc17f09003000c2000028941ef2c494a899a4752080ecc6b430514d88dc3ac17508c02d40ba00002893c062c614ac9a64681fb0e8068a2e314288c83b417608a02c80bc0000289362b2bc143096a4612058eec6ae2ee143888838817b08a02c80b0000028930832a6940c94a44b1fb0e546762e614088c039217c08f83140c000002892ab82b3143c9684501f60e5c6742dc14388a039c17508d83080cc0000289250f2ac13d49384461f78e446602c8137884837416008102bc0aa00002891f272c914b89b24782100ed86ae30015109003c017e08e02d80aa0000289194a2c0948898a46920a0edc6a82ed14c08f83b617608f82f00bc000028913602c594a498c4792058eac6b42fc15108e43c218008e83000d200002890d932b794549604541f78e3c64c2ca137086436215308102940a0000028907ad2be14749884601fb0e6c66a2d413c886837616d08282940ba000028901ae2d115149ce4912158f006be30315309343ca18909603200e20000288fbd82be146897245f2028e9c6802e214388cc3a017508682e00ba0000288f5f02c914dc9ae47d20f0ecc6be30215409443de18b09283000c40000288f0252b9943896e4582008e6c66c2d613b888c37e15c08402bc0a60000288ea452c2146497a46520b8edc6ac2f315009083c019009783180c00000288e48f2a693e094043b1f28e1c64c2c7134082037415a08002980980000288debb2b8943c95444a1fa8e406762d9141089439a17509483040cc0000288d8c52c4149498646b2050ea46822eb14688a438c16608902b40b40000288d2a42db95589e048d2180f306e031315689243ba17808a82e80c60000288ccc92bb146897e46920a0ec46962ea140086838a17008782e40b60000288c6e92ba147c9984682030ea069e2fc15008e43b4187096031c0ba0000288c11d2c0949097c46d2068ec86ae2ff14f89083d018909583140c00000288bb6d2aa13ec9424501f60e606662e413e089439c16c089030c0c80000288b58a2bd144897045d1fb8e6466a2d3138083c37e16308382b80b20000288afaa2c1148098446e2030eac6a62f914908c839816c08382a80a80000288a9a82d095449ec49421a8f686f831915789203c617e09203080c40000288a3ce2be948c98846e2058ea86a42f914f89003c617b08e03000d600002889df62c2148c9a647920c8ee46a62f114508bc3aa16e08882d40d20000288980b2c614b49a046b2030e9c6962f414308a038c16808b02dc0ac000028892512ae93e893a4371ef8e1865a2d513a886836c15408382cc0ae00002888cb129f139c9204331e88dd463c2c9139084c37216408402b80bc000028886d62b9146098447320d0ee06b830215189043b417b09203140bc000028881312a813bc92c4371ed0e246622d913f88ac37015808282ec0ae00002887b6f2b6143c95e45e1ff8e946a42ee14b09043c617c08602f40ce0000288757b2cd950c9b447820c0f006ce30a15489203ce18108f03100b4000)) else (if i < 424 then (if i < 423 then 0x28b5b7a2b414249544531f98e3867e2e2143889837e16608802ec0c2000028b55a72b9948497e46c1ff8ea868c2ee14908d03b617508c02e00b0000028b4fa32d494ec9b64752130f006be30015109183c218308f03100c2000028b49ee2ac140495e4541fe8e406722e014688cc3a617508a02bc0b0000028b44182bb94849844632068e9c68c2e814388b83b418409403080c0000028b3e532b714289664561fb8e946802db141089039417708882d00bc000028b388e2b194149504461f80e606782dc144089038817308882f00c2000028b32c72af943895c45b1fe8eb06b22f614688a839c16808a82bc0ba000028b2d052b0141c9444521f90e446702d313b086c38615707f02a009e000028b273c2b714489724521f58e4c6602d3138887437817108b82d40a8000028b216d2bf147897c46a2060e986782d814008ac38c16f08b82e40c6000028b1b7e2ca94e49d249521a0f786f831e16189b44161a509e033c0d8000028b157d2d015109bc48b2160f206c22fc15088ec3a6180092832c0ca000028b0fa32b994709724661fe0e606662db14108d83a0184094830c0bc000028b09a92cd94e89a447120b8ec06ae2f714a88c43ac18809683240d0000028b03ad2d3951c9c648720c8ebc6aa2f914b88b839617008b02f40ba000028afdce2c194949a447c2060ec86a82f014788c03ac17a08f82f80b2000028af80b2b5147097c4632050ec869c2ee14e08d43c418b09903400d6000028af2322be14a49a64772088ed86a02ec14608bc3c618909383180be000028aec412c9949498e46d2060e8068c2e314688c03ac17608c02cc0c0000028ae6892b114149684582038ed06bc2f214908fc3be17e08f02f40ba000028ae0cc2b7945c97a45c1f50e4c6522cc138885c36815907d02ac0b0000028adaf82bc946897e4541fd0e886902f114488a438a16a08882f80d6000028ad5112c594a499e46d2088ed46ae2f414608c43a017b09603140c6000028acf652a693d09224301e88df863c2c8135084437015f07d827c0a2000028ac9b32ae94149504541fa0e546942f714b08c03b418a092030c0d4000028ac3df2bb947c9924772060ebc69e2f014b88fc3ca17408802c80be000028abe022bc947c99a4702048ea46862e9145088837416008202a00b0000028ab83a2b614589704592018e806a62f314d08e03a217808e82f40be000028ab2882ac13e49404471ec8de06682ec14788b43a417b09082e40c2000028aac972c214b49904622030e706922e514a88c439e16708482dc0b2000028aa6cc2b2144497a4632018ec46a42fa14b88cc39c16908202f80b8000028aa0cd2d014ec9b847720f8eec6be30a15389403e018a08f82d80ac000028a9af82bd944096a4471f70e4867e2e314108a03a617808c02cc0b4000028a950f2c794d499a46b20a8f046ba2f714908ec3c817a08b82dc0c2000028a8f442b714449884672098eb868c2df14508e43a817108a02c80a8000028a89552c694bc99c46f2098ecc6a02de141887438617308a02f40c2000028a837b2be144c97245e2068eb46902f014708cc3ae17e09082f80c2000028a7d8e2c514809684581fc8e7467a2ea14308983a816908682a80b0000028a77b82c094b09b047920f8eec6c6307157892c3dc18509383240c2000028a71ca2c9149c9b64852168f046c030214f890c3de19409783400ca000028a6bce2c894d09b848220b0eec6d430215009043ba18909183080e0000028a66072b8145c95e4511fd8e786602e1141889839a17608b02f40bc000028a5ff92db95609ec49f21c0f506d230115409083bc17a08e02c40b2000028a5a282b794409824682068ec06a02f814b88f03ba18508d02fc0b0000028a54632b694409864632010e8c68c2ef14608a839616d088828c09a000028a4eaa2b4945096e45c2038e8467e2e8141889438216208002a00a2000028a48ce2c014a89a046b2090ef869e2f014b89003ca18309203400c8000028a42eb2bf948498a46f2040ea46922e614b08c43a417608702f40b2000028a3d082c294b89a84802148f046c030c150891c3de18a08e83100c4000028a37582ab93e093c44a1f38e2864c2cf13c885836a14b08002ac0ac000028a31712cb95009b04822138ef86b82f614b08fc3c417e08c830c0c6000028a2b8e2c2148c9a047520d0ed06982f214789083d0187091030c0ca000028a25aa2c294bc9b44852138f1c6e231015589283e218808e02fc0bc000028a1fe42b6946c9764551ff0e646642e614708bc3ac17609002f00c4000028a1a152b6142095c4511fb0e386722d913e888c39617108802e00bc000028a14502b3144897445a1fc8e906942f314788d83b018208982c40a2000028a0e5b2cb95049b447d2100eec6b22fe14e08e43a817e093830c0b6000028a086c2c914ac9a847420b8eac6922ea14588b83ac17108702e80b6000028a02af2b3145496c4642010ea06882e8146889c39a17609403140ba0000289fcec2b3940c9304491f70e686802e714388b43aa17709082d409a0000289f71f2ba944498046b2020e7468e2eb14608a039817108d831c0b80000289f1302d014fc9b64722090ef06b030414d08f03c818609083140c20000289eb6f2b6943c96c45e2030eb46962f414788ac3a217c093030c0d0000 else 0x28cd1b02c5148c98c4642080eb06a42f714f08fc3d018608e031c0b6000028ccbab2d495209d24872158f5c6dc31315a094c3d418709402e40b2000028cc5bc2c814bc9aa4822118ef06d631515409443e819209803100c4000028cbff12b3144c97245e2028ebc68c2ed14688dc3b217e090030c0c4000028cba0c2c314b49b047920f8f046bc306150890c3b8185096831c0c0000028cb4102d415249d04852108ef46c030315109103c418408e83080ba000028cae1c2cb14d899e47820b0ed46b82f814988e039017008c83180c8000028ca8612b5141894644c1f58e306602c3137888c38416e08702fc0c6000028ca2682cc14f49b647620c0f006b230214f08f43c217b08f03000be000028c9c9c2b7942893e44d1f28e346642d5136084437e15e08582cc0ac000028c96af2c494c09a247a20d0f086a82fa158893c3e219209282fc0b0000028c90de2b594409504541fa8e446742db13d886838216c084829c0aa000028c8b1b2b3143c96045e1f98e6867e2ed14a08b839416608402c00aa000028c858529e937492c43b1eb0e0c6582d113c087838816a08502c40b0000028c7fbd2b6944c9704591fe8e686602e013e888039017308682c80ae000028c79cb2cb14e49b247520b8ecc6982f814b88c43c418609183000bc000028c73da2cb14ec99e47a2090ed869e2f614d88dc3bc17c08b82e00be000028c6e132b6145096e4642070eb06822ee14388b83aa16f08602f00c0000028c68412ba947098e4612008eb46962f014888d03c017a08902ec0c4000028c62662bc944c96c45a1fa0e806922e714588a03a418008f02d80b2000028c5c912bb146096e4521fe8e9c68e2ea14708dc3aa17108b83100ae000028c569e2ce94e89aa47220d8ee06a22f014408b43ba17c08c02c40ac000028c50b02c2148c99e4722088ed86a42ef14a88f03ac17108b82e80b2000028c4af52b314149524511f88e4067a2e113e088c38416d08282840a6000028c45352af141095844e1f90e406682dd14408bc3b617808d82e40b4000028c3f3e2cf95109ce4892170f246d230c152890c3c218509702d40c0000028c39512ce14c49a247120c8ef46d230815489083ce18909803380d6000028c335d2cb94c89a247520b8ee468e2ee14c08e039a17508e83140ba000028c2d572d014d49b847b2078ec46c2306150093c3c819109803400e0000028c279f2b694309644531fa8e546702da14188a43a417208802ac0a8000028c21d12b694589704561f78e5867e2d913f888c37816308502a80a4000028c1c132b494449704511f98e806722d5139086836815c08002840a0000028c16392b9945497e46720a0ebc6922f314d08e03c017a09082e00c2000028c10692b194209624511fe0e786742de137886837e17408882c00b2000028c0a822c6147897c45c2028ed06b02ef14988bc3a016d08982c00b6000028c04b62ba14489704571ff8e8869a2e814208a839817208882c80a0000028bfec92ce14e89a647d2088ed86b6301155093c3f819409683200cc000028bf8eb2ba14609684641ff8e986a82f614989083ca18108d83140c0000028bf3202bd94909824622050e606622d2135086438016908802d80be000028bed3e2c194d09aa47420d0ef86bc30415509283cc183096834c0c2000028be7662bd945897a45f1ff8e6869e2ea14888d03ae18709002fc0c4000028be1bd2a593f094044f1f68e4065a2c9138087036a15308302dc0b2000028bdbe72be148098645b1fc8e906822f114989003ba18708d830c0ba000028bd62b2b1943095444c1f50e206442cd13187f436a15e08302c40bc000028bd04c2c1949098845c2010e9469e2f114a08e03c017208902b80b2000028bca5f2c414b49924652038ea868a2e614388b439a17908c83180c0000028bc4742c814bc9a84772068e946902ef14608b83a018608e02e40b4000028bbec92a993e493e4491f88e5866a2dc14308d83c817908902a4092000028bb8d02c4947898e4632070eb06982f014988f83b018209083140b4000028bb3082b5146097c4642058eac69a2f014408b03a016f08a82f80c6000028bad1c2c214589744542000e906aa2fe14408d83ac17e08d82f40d8000028ba72b2cf95309e44932158f406d630c15488f03c018c09203100c8000028ba1492bb14589604562008e6c67c2e514488a038e17808b02f80d8000028b9b8e2b1140894e44c1fc0e5868a2e714b88e43b218509402ec0ba000028b959a2ca14cc9a447120c8ef86ae2f214408a83ac16e08a02c40ba000028b8fcc2b8145096e4571f60e2c6702df14308983a416f08b02dc0b0000028b89fc2bc947c97245f2048e9068a2e2139884c37015907e82b40ac000028b84102cf15089c64812128ee06b42f614888e43c418609583100be000028b7e4f2ac14109624511fc0e646682ce137085839216a08402b00ae000028b787b2ba143096645d2040e886822dc13e889439c16e08882e40be000028b72912c0944c9644541fc0e8c66e2e314d08bc3a216708302c40ac000028b6cd62b1941c9544521fb0e7068c2f214688c43b21750858288092000028b66ff2ba145c97445d1fc8e786882df141087c38016108882d80b2000028b613a2b714409644571ff8e986a42fa14b89003bc17b08d82f80c6000) else (if i < 425 then 0x28e47bc2b894649844622030e686842e614388c039e16f08482b40a4000028e41ef2b2940c9544511fb8e6867e2eb14708b03a017108b02f40b6000028e3c072c114809824601fe8e986742e1140888038616e08c02d40be000028e36552ae94049564421ee0e106442bd135887837c15608002b00b6000028e30672cc14ec9be48020c8ee86be30514f89043cc18709283080b6000028e2abc2a513f89464391f20e506762e614508c43b217e09403380d4000028e24b92d094f49aa4702078ed06a42f814b08cc3be17908e02f80c6000028e1ed02c394c098c4642010e8c6802e014a08b83be17909003300b2000028e19132b294309644592020e9867c2e914508a43b217208b82d80b4000028e13382c2948c9944642020ea068c2df13f88a439817909282fc0c8000028e0d5a2c2949499647020e0ed469c2f514808d43a816a08582c80a4000028e07382e315509f04962198f3c6d831915d09683f819909f83600e8000028e015f2be149898c4692010e886822df14388d43c618209082e80ba000028dfb8d2b9945c96e45c2040e986842e113c087c38416e08b02e40b0000028df5cd2b194249744531f58e606642d513d885438016a08602c40b4000028deff52c094989944631ff0ea46922df13c087c38416c08202b80ae000028dea2c2b814289644581ff8e906902df144089039617108b82f00ca000028de45d2b7944c97c45e2010e706662e014108bc39c16a08182ac0bc000028dde972b6146c99c4692038ea46ac2ee14788d83a416c08b82c40a0000028dd8b32c414c49c24912130f5c70431d159094c3e619509283100b8000028dd2fe2a693f493a4401f08de46482c7135885c36a15f08482bc0c4000028dcd2a2c1948898046a2048ed46c62f514588c039417008f02e00b4000028dc7572c0947c97845c1fe8ea06982f114988b439616b08302a8098000028dc1902b3942c95644f1f90e986822dc13e089038e17708d02fc0c6000028dbba02d414d89a047320c0ed46ae2e814708b439e17a08f03000c4000028db5e42b313ec9424471f30e0065a2d913d885c37416008202c80b0000028db0042bd94a89b44862118f206cc30214c08d039e17a08a82d80ba000028daa252be94849944631fc8e586742d613c889439817008b02e00be000028da4402c794e09ae47820f8f0c6a42ee14788e03ae17808982c00ba000028d9e5e2c214a49a846620a8e986922ec14808a439e16508602b40b4000028d986e2c914ac9744481f80e5465e2d4143088839816d08902d00c4000028d92992b9142c9664471f78e1c65e2d614488d83b417f08d02f40bc000028d8cbd2c414b49a647f2128f146c430615189003da18809403080d2000028d86ba2d115249e649a21d8f5c6de31815b89283de18b09283140d6000028d80fd2ae941c94a4551fe8e7867c2dc141086038a17708c83040b2000028d7b202c794e49a84792090f006e431915809303d217f08c82ec0bc000028d75432bc144c9704551f98e5066c2df13f087837a16608482a80aa000028d6f4f2ca14bc9944722058e686722ee14908f03c617f08b82e80ce000028d698f2ab13d893843d1f68e246682d214088d43b818008e03040ae000028d639d2ca14ac9944712090eb86aa2e6143088438417108802f00c4000028d5db82c4148c97245e1ff0e786922f114988c439816608482c80b4000028d57be2cc14c09ae47120a0ec069e2f214d88cc3b018009283080c2000028d51ca2ce14fc9be4792078eb46902e7142089c37e16908582dc0a8000028d4bfd2bd948c99a47420b8ee86b42fc15208f83c218309103240ca000028d46432a913f49424461f50e2c67e2e414388bc3a817c08f03240c2000028d40962a913a89164371ea8df86422cc13a085c38016908b82ec0b2000028d3ad62b514309724632040eb46962ec14388b83c218609383480d4000028d34f02bf146497e45d1ff0e646802df139887439a17108602cc0b6000028d2f132c2948898a46c2038e806862e9141888c38016808582ac0a8000028d29392bf949c99e47b20b0ee46a02f014908dc3ac17808d02f80ce000028d238d2a813d493c4481f48e2c6642d113d884c36e15a082829c0a2000028d1d842d214fc9cc48c2138f106be2fe14d09103c818809683340dc000028d17b02b914749864672068ecc6962e414708b43a416f08f02e80b6000028d11c62c314909844652070e986962ed14588a839617008982f00cc000028d0c082b1940c94a4411f70e346662d913e088439617808d831c0d6000028d063c2ba94709824662058ecc6b22ee14b88e43d418909183380d0000028d00942af14189564451f50e4066e2d313b085036c16808802d80bc000028cfabd2bf949499446f20f8f186b830415509203c017a08a82d80ba000028cf4d72bc149097a4621ff8e9c6882e3142886c37416508302d00c8000028cef192b294109464511ff0e5065e2d814288a03a017b09483100b8000028ce93c2c2148497645a1ff0e8468c2ef141889838a16d08e02e40ac000028ce38c2a993d89404471fc0e7468c2df140089839a17508a82e80b6000028cdd8c2d094e49ac48220d0ee46a830015689543e018d09983280ce000028cd79b2c894ec9b24802100f106e230415208e83bc18509183240bc000 else 0x28fbd0e2c494a899c45e1f90e5866e2e4141887438215e08082b00b4000028fb7352c014b49a24682090ee46b42ed14988ec3aa16d08d83000b4000028fb14f2c814d09a04762070ed86c6302153091c3d618509003140c2000028fab8c2b4144096645f1ff0e646862e414908bc3a017108a02f00b6000028fa5a32cb94e49c04822118f0469a2ef14a88f03c818b09183000ba000028f9fcf2b5942896c45c1fa0e6465a2cf13a087838a16408682c40a6000028f99f22bb947897e45e2068eb86962eb14c08e83b017708d02f80c0000028f94342ab13f893e4461f28dfc6522c4133082435015607d82900a0000028f8e652b5945097e45a2010ea86802f214f09103c818809583240ca000028f88732bf948096c45d1fe8e8467c2e814108c437c16c089830c0ce000028f82c02ab93b892243b1ee8e446662d8139889838a16908802cc0a6000028f7cd72c894b898e46620a0eb06982f214c89183c418409302f00ba000028f77082b6942495645d1fc0e746862de14488c43a817308a02fc0be000028f71372bd14749844692058ecc6962f314c08d83b017208e82e80d4000028f6b5c2c414ac9a446f20b0f006b62fe15389243ca18108e830c0c4000028f65882bd147c97c45d1fe8e5c67c2de14008ac38216a08582bc0be000028f5fbe2b3942c9684622020eb469c2ee14b08f43b017708d02f00ce000028f59d12c5949c97c4651fe8e906882e9142889c39a17708d02d00ba000028f540f2b9946c99446b20f0f046ba2f114f09583ce19109103180c6000028f4e562ac940495a44b1ef8e246522d713b887836c15f08202bc0ae000028f488d2b5943895c4571f90e406542d413c887039215f08502940a6000028f42a02c894d098e4651fe0e8c6882de14308ac38c16d08c82f40cc000028f3cca2ba144095e4571fc0e706742ec14588c43ae17909183140bc000028f37242a994049444501f80e346642cd132081c35c15707e02c00ae000028f313b2cb14dc9c04842170f2c6d630c15c09583ea19309d83880e0000028f2ba22a293bc9344411ef8e146642db13f087c38015508002c00b4000028f25c42c1946897c4541fa8e7c69c2f614c08c03a217c08802cc0aa000028f1fe92c394a09864601fb0e5067e2eb14a08c83ae17708883140ca000028f19ec2ca14f09c24872138f2c6e630715289003a817008c02f40ba000028f14182b3144498c4691ff8e706722dd14408bc39616c08b02d00b0000028f0e012d895189a647720d8f286d031615889643f0196096833c0e0000028f08212c614d89b847c2108efc6be2fe14f092c3de18608f03180be000028f025b2b0941c9484421f68e646822e714908e83c017408a82c40be000028efc7b2c1947c98e46c1fe8e846902fc14e08fc3b617f08f82e00c2000028ef6862c814b49a646f2048ebc6962f714908d43b218309403200cc000028ef09f2c294a098e4682050eb86a62f614708c43a417008302b40a2000028eeadd2b4946497c45a1fc8ea069c2fb14f88d83b017908b82fc0c4000028ee4f92c0148898846e2058eb46982f314808ec3b017508f82d80b8000028edf312b194289724572008e846782e6144889c39e17c09083000c4000028ed97f2af93f89464421ea0e046502d713c888837615c08502d40b2000028ed3dd2a993cc92c43f1f78e1c6582cf138084837a16508102c40a6000028ecde82cc14fc9bc48420e8ec06b62fa14f092c3d017a08883080d0000028ec80d2c0947096e45c2010e886702db14608bc3ac17608b02cc0ba000028ec2602a913c49384451f40e4866e2d613e088438416108302b00ac000028ebc792c995089ac4782090ea069e30315189403da19009182e80a2000028eb6912c714cc9b247920d8f086e230e15c89583da17c08f02ec0c0000028eb0ac2c814d49a647620e8efc6d630014788d43a017308702b80b6000028eaacd2bd146098a46c2058e9c68e2d713e888437616808782dc0a6000028ea4d12c894c09a247a2118f086b42fe14e08f03bc18808f02f40cc000028e9eec2c594dc9a246e2050eb46a82f514988f43c417e08b82d40ac000028e993d2a893e09324421f78e3c6642d8140887837c15c08502cc0b4000028e93762b4144495e4531f70e5c67a2d914008b438a16f08d02e00ba000028e8db72b3942494a4511f70e546682e214008b43aa17f08b82d40ba000028e87df2ba14989aa47d20c0ee86aa2fb14908b83a217308902e80ba000028e82112b614249504531fa8e386802dc140088838616a08382c00be000028e7c472ba945c97a4671ff0e946962eb14808b839416f08b02cc0a0000028e766a2be148c98e46c2060e8467c2e014188ac38e17008c831c0ca000028e709c2b914849824652058eb468e2e714c08c43a218408f02e00a8000028e6abd2be94349504501f98e786902e614188a83b217a09082d80b8000028e64e12be145c9784612028eb46982ed14488a839017008802e80c2000028e5ee42d014ec9c447b20e8ed46a22f714808c83ac17508b02d809e000028e59152ba147497a4672048ea06922e814908cc3a817109203180c8000028e53742a793b892043e1ee8e0c65c2cf13b088c37816108802fc0b0000028e4d8b2c794d099a47a20a0ec86a02f814d09103cc17e09282e80b6000))) else (if i < 429 then (if i < 427 then 0x29133442bc945c97245d2020e946822de142087839617b08f03100b400002912d652c6949498c45c1ff8e9469e2e714508c03b216f08882d80ba000029127662ce94f49bc48620b8ef06b630014988bc3a817608c03040b6000029121a12b5145c97645d2008e8066c2cf13d889438616708402cc0c800002911bb52bd145895644d1f60e3c6802df14288cc3bc18008f02fc0c8000029115e52b8942495e4481f20e1864e2c6133081437c15f08482f80b8000029110112b7944c9604521f70e5865a2d013d887838816c08582b40b000002910a322c2148096245b2030e9c6962e714508a038a16d08982e40b2000029104802b1142495c4501f58e106542d313e089438816f08b02c80be0000290fe922c794b899a47a20f0ee86be30415309283b217c08b02f40c60000290f8b22c694a099c4682030ed86bc2f014808a03a8179091031c0c00000290f2ef2b4144c95a44a1fa0e5c6702df14688dc3bc18609002f80c60000290ecef2d015149ba4882178f2c6c630615589083ca18809403480e00000290e7342ae940894044b1f40e646782ea14708a83aa17208b03000b20000290e1752a993f093e4361f08e1c6482d6135885037816308482b40aa0000290db9d2b7141894e44e1fd0e6c66a2e213c887839417208902e40a60000290d5d02b7943897045d2040eb86862ea144887c39216808c02ec0ae0000290d0172b1940c93e4461f48e4c66c2dc13e886439217508e03040ce0000290ca422bb946898a46b2088ebc6822e914608e83a217008b82f00ae0000290c45d2c2947898c4672050ebc68e2f014c08c83b617c09183240c20000290beaa2ab143495044c1f78e6c6742dd13d887c39016708a02dc0d00000290b9082a593b493243c1f00de064c2d313b885837a16508602cc0bc0000290b3342b814309564511fb0e786982e7144887837e16108502c40a20000290ad4f2c294b49a04722080eb06842de141086437215a07c02a40b60000290a77a2b7143896a44e1f48e286662d413d88b43c018109783280d80000290a1c02ae14289604561fc0e646922e9142087438e16b08702b80b600002909bf42b514189484521f98e6c6822e914488a03a618309002f40ba0000290960f2c494b49a046c2070ee46c22fb14e08e83ac17908d03040c60000290903d2bc145c9724671ff8eb06b22ec14888a83a217608f82d40c800002908a912a493ac9264391f00e386642ce138084037a17008702d80be000029084b72bd14449704622018e786582d013c08a839216c08682d40d000002907f0c2a593e890c42d1e90db861e2b0124080034e15607e02840aa000029079372bb94449684521fe8e846942ef14c88d03b217c08f82e40a4000029073352cd94e89c247f20b0eb869a2ef14908bc3ba17c08d82e00a400002906d142db9554a084962140f246ce30714b08dc3c618509203080d2000029067272ca14d09c848d2148f406ca30a15589483e619009603380da0000290617b2a693b492843d1f10e086622d613e887039216908782cc0a600002905bae2b4942495444f1f80e446622cd13b085c38216308802d80b4000029055de2be14389724651fe0e646742eb14788e03c217408b82f00c2000029050142bd945496445d1fe8e946982f914809003c417a09303140c800002904a462ba147496c4642028ebc6962f314b08e03ac17b09002e80be000029044332d915189d64902140f6471032b160897c41219d09e035c0d200002903e5b2ba94589884672018e9869a2ec14388ac39e16708602e00ca0000290386b2ca94cc9b44772098ed06a82f714808b439a17108b82fc0b4000029032712cc94e89be47f2108f206d831c15f895c3e619109283200c000002902cb02b2942496644e1fc0e6068a2f714d89203c618a097032c0d40000290268c2db15609f249f21f8f5c6dc306151893c3d618909603180ca000029020bb2ba148097e4571fb8e5866e2dc141889439017008882dc0b200002901ae02bd14749744681fd0e7c6762d4138888838a16708b02ac0ae000029015082bc947898a4641f90e706842ee14a08a838e16c08c02fc0ca00002900f032d715409dc4822108f146ec31815c09403da18f09002f40c00000290091a2c514b49b84722020eac6a230414d89043c0179093830c0ce000029003472bd947897e46a2040e8c6822e314308a439417308f82f40bc000028ffd5f2c314dc9b24832128f346ea31015689303d618009182f00b4000028ff7a92b3142896845a1ff8e986922f514b88d03b617809103240c4000028ff1dd2bc149c9a247920a8ec469a2fb15309303ce17c09083000be000028fec042bd14a498c46e2078eb86942f214a88d03b017608d82fc0c2000028fe6222c514cc9b446f2058ed06a62fa14e89003bc17208d83140b6000028fe02d2c994d49c04812108f206b62fb15909383c418409183180c6000028fda4e2bb947898a45e2050ec46a62f014a08ec3bc185096037c0de000028fd4632c994c49aa47420d0ef46c82f915288f83d618809503040b4000028fceb72ad93f09504511f80e4867c2e6146889439217308c82d00b2000028fc8d72ca14c49b448820f8ed86be2f514b88fc3be18508f03200d0000028fc2f12c394bc99c4682080ed46aa30514e091c3be18a09203180ce000 else (if i < 428 then 0x292a8932b3942897244f1f58e306542ce137082436e16008182a40a40000292a2be2bb948099a4642060ecc6b62f214488ac3ae17908d83400cc00002929ce62c794a49904672000e906942f314588cc39617308d02f40aa000029297352a913d894244b1f40e146402bd132082837216808b02c80b40000292915f2bf14709904692088ee06c230415609043bc18409102e80be00002928bac2ab93e893843d1f50e746a22ee145889c37c17508d03040b4000029286232a0137c9004291e38dc863a2ce13e889839e16908882c40ba000029280572ba94949984662070ec069c2fb14b08e83c818209503480d200002927a8a2b8944496044f1f60e946942f3145089439a16908182d40a4000029274c52b0942c9684531fd0e8468a2de143888038c15f08582f40c000002926eee2be145c97a4521f90e546822e913e885837216008202940ac0000292691c2b714489644581fd0e886822d813c887c39c16e08982e40b80000292633a2be14709844672088ea06802eb14888d83c017f08d82d40aa00002925d852b1943895a44e1f80e3465a2d2138886438616d08d03000cc000029257942cc14f89a64752100f0c6d62fe15108f03a817c09082f00c4000029251bc2c514b49ae47620a0f086b62fd15309243c017908a02c80a400002924bff2b4943896c45e1fd8ea86b22fb14d08d03b017008b02cc0ac0000292460d2c894e49c649221b8f546ca31215989203d418b09083100c4000029240492ac93fc9484431f60e4066c2cf13e088c38616308302c40c200002923a722bb94649664662040e6867c2e3140088839a16c08782f00b8000029234772c694ec9b64892138f2c6c62f814a08d43a617808902dc0b400002922e992c0149c99e46a2078ec86b82fd14d090c3c417508e02e40c4000029228b22be146c97c47220e0ec86b030c15509083d818609303340de000029222ec2bb94489684561f90e5466c2e2143889838a16a08982ac0a800002921d242b213e89364441f80e706982fc15509183c8188093031c0c80000292175d2b694449584431f18dfc6522ca13e086c38416b08782c80ba000029211a22ad941095a44c1f30e146442c6136086438416b08882c00a800002920bc32c1145c9744622020ea469a2dd14188b83c618209203000b6000029205eb2bd946497a46a2068e8c69c2ee14a08c43b618909483380d8000029200132bc148097645d1ff0e6867c2df141887c39616f08902ec0ae0000291fa572ae140093c4441f50e7066e2db141089c3a617b09083000b80000291f4892b6147498a4692098f086cc30715589103cc17e08d02f80b80000291ee7a2d395389d648921a0f286d430515009203d418008e03080b60000291e89d2c014a09824591ff0eac69a2ef14788dc3ae17b08f03080c40000291e2cd2b7943894e4562018e986842ee14908f83bc18508d83040b40000291dcdc2c794d89b047e2170f3c6ba308155093c3de17e08f02c40b80000291d6f72c914c09a44702068eac68c2eb14988c03aa17f08c02f40d60000291d13e2b013fc9524481f88e606522cf13c885837416508782f80b60000291cb522c695209d24812110f046de314162098840019b09b03200c00000291c56d2be948498a45c2018e7c6a42f8150091c3c218209402f00c00000291bfac2b1143496044a1fa0e446642d313a087c38616e08702ac0a00000291b9e92b6143c97645e1ff8e606782f014809103d018809683100be0000291b4212bd944c98245f1fe8e6c67e2de13c88a83ae17d09002d80ae0000291ae2c2ca14d09ac47420c0ecc6922e4141087838816808983080c00000291a8712b494389664552010e7c66e2db13d087838416308802d80c80000291a2822c714e89b847520d0f006aa2fa14d09003b018208b02c80b000002919ccb2af93c891a4351f68e5c65c2db136882c35c15908482b80ae000029196ea2c214949924692060ef46c4306152091c3b617b09002f00ca000029190f22cc94ec9ba47d20b8ed86b02fe14e08f43bc183093832c0be00002918b102c1948897a4642000e8867c2e3146089c39417008782d00b40000291851f2c814ac9a046e2010e7868a2e414488b439817308582d809800002917f432bc946c98846e2088eb86982ed14d88f43c218008c83040d0000029179812ac943495644a1f78e446682d914208a439a17108902b80b0000029173ce2ad93d09404421f10e246562c5136080c35814207a027009200002916dec2bf146498c4622078ec06982f214688c83a617809303080b80000291682e2b2141894e4491ff0eb46a82f415008f83b217a08802d00b60000291625c2b9146097845d2018eac6a02f014c08dc3a217908c02e80b200002915c822c314c49b44671ff0e946802e614808bc38e17908a82c80a00000291566e2d214f89c047a20a8edc6a82f014a88ac3a417b09103080c0000029150672d495009b447e20e0f186dc30d15609703ec19509503200c200002914a912ba146c97e4561fa0e886962f414808a039817208c02e80c4000029144c02bb948498646b2050eb86b42f815208e83ac17708a82d009c00002913f072ab940494a4431f90e546702e6141887439416e08983040c40000291391b2c594b899a46e2098ecc6922f0146888439817a08c82ec0b8000 else 0x2941fec2b214409784591fa8e5c6822e0136888037216008182bc0b6000029419ed2cf150c9d04802168f0069e2fe15309003ea18c09503140b8000029413f02cd15049b447d2100f2c6c830015288e83b217e08f83140c200002940e192ba944497e45d1fe8ebc6a82f314688b43a617008b82ec0bc000029408472c214a09904792108f186a82f514b88cc3b417609103100be000029402412d4152c9e049621d0f746f031015689183d818409182ec0b60000293fc782b8144c96244c1fb0e706722e314888b038216908682f40be0000293f6822ce94f49b447920d0ee06a42fc15309203d819309503180ce0000293f0ca2ad93f49464461f70e546642d514788c03a017008a82d80be0000293eae02cd151c9c84772098eb069a2f414a88d03c418709a834c0e60000293e5052bc145c96044d1f80e406742e1140888039017308302c409c0000293df222c114909a447920f8f146cc30115008c839a16308882c00be0000293d91f2ce15189c44922148f246d22fd14f09043d619609403280ca0000293d3722b094009584431f28e3c6662d513f888438416407d82ac0ae0000293cda02bc947498e4612040eb86922f714b88f03b417409403200c20000293c7d22b4144896c45b2008e9869a2f214c08f43c016e08702dc0b40000293c21e2ad93e09364471f50e5c67a2e4146889439416a08282bc0b60000293bc3b2c2148497e4642010e706842e714988dc3bc18909583140be0000293b6442cd94fc9b047620c0efc6d430314d88ec3b817f08b82f00b60000293b0592c994c098e47320e0f086ca2f714a88c03c217e08e82e40b40000293aa5c2ca14e09bc47f2128eec6ac2f014d090c3c017e08682ac09a0000293a46c2c514a899246320b8ef86c22fd14a88f43c418509202fc0be00002939e892c214909904722048eb86aa2f414c88dc3ac17408e82f40cc000029398d12ab13e892442f1ee0de86422c3138087838415d08482b00a8000029392b12e1157c9f64a321d0f586ee31b15e891c3c017a08782d00b400002938ce02bd149c9844622008e4465c2d514408d83b217008d82f00a8000029387062c3149c9944662050ec86962f414c08c039617608d03040aa000029381252be94689704682050ea86a02f314608c039a16e08982e80bc00002937b322cc94c09b447f20c0ef86c8309154090c3b017208282c40ae000029375622b6147096c45b1ff8e606802dd141887439016308802b00a800002936f9d2b714449644511fe8e9068e2f414e08f03b217c08d02d8098000029369d62b294209504481f28e2866c2e8140889c39c17108c02dc0cc000029364042b814589904641fe8e9868e2e314608f03c617a09182ec0b200002935e2b2bc945c97a45e2040e806862ea14988e43c818609283240e00000293586c2b914549684662000ea46942e714908cc3ac17f08b82b80b0000029352bc2a693dc9344401f40e246602d414508d43b417208b82c00b200002934cbf2cc94c899e46e2058e9467a2e514588cc3ba17608402a00b00000293470d2a813d493e4511fa0e4c6862e614388c83aa17908c82ec0b2000029341442ae941496a4602018e7068a2ed140086c37a16008282c80b600002933b702ba147498245f1ff8e806802e414588d03a618108e03140c80000293357f2c494b09964632008e8c6882f314608c03a417c08982fc0b200002932fb82b3142c94e4501f40e206622dc14108a039c17709002e80c4000029329b32da152c9d248220e0efc6b42fa14b88fc3c418209683380d2000029323e32ba144896e4542030ec86a22f314b88f03b617608982ec0b200002931dfc2c594c89ac47120e0ef06c42fd14e88f43b017708c02f40b0000029318132c414c09be47d20f0f0c6ac2f914d88ec3b617208382b80a6000029312292c514b89a447220b0edc6b22fc14b08f83b018809503080d000002930c632b2943c9604531fb8e686722dd14208b038817008482f80b2000029306bb2a593d091643f1f90e4c6842de141889c38e17208c82f00c6000029300f62b3143496e4551fc8e9066e2d913d088839216608782b00b40000292fafa2cc94e09a04782188f346e830f154894c3e018f09483080cc0000292f5132c594949a44722118f186c22fb14a08f83c217b08e82e40be0000292ef242ca95049d84872148f446d0307150891c3de19509503000be0000292e9432c0147c9864682040eb068c2f314b08e43c817708d82e40c60000292e34b2cd14f09ba47d2098ed869e2f214488843a216e08c02d40c00000292dd8c2b6942c9624592020ea06922fc14d88f03c617d09082fc0bc0000292d7a32cd94ec9ae47a20b0edc6b42f314608b439617a08903040bc0000292d1b52c894b89984752118f106c430215409243e018509503200d00000292cbd92c414a499c46b20b0eb868c2e514208b03a617808802a80a60000292c5f42c494bc99446c2098ed46a62eb14688e83a217b093831c0ca0000292c01b2b8944896e4601fd8eb46aa2fa14f88e03ac17a09003040bc0000292ba3c2c294b09a646f2048ec06702da13e088439a16f08a82d40aa0000292b43b2cf95189cc47320c0ed069e2f214a08e43b618409103180ca0000292ae602bf94649824561fb0e906902e914608a83be17c09283100cc000)) else (if i < 431 then (if i < 430 then 0x29594c12a213b491a4331f38e286562ce137085038216608982e00a600002958ef02b7145c9664581fd0e886922fb14b88f43ac17408b82fc0c0000029589052c4146496e45d2038eac6ac30215188f03c618208b83040b6000029583592a713c492043a1ec0dd462a2c1131083c36615d08402ac0b000002957da82ad94309664581fa0e346522ca132882436415608102b40aa000029577cb2bc146496844f1fd0e746662d513b88b839816c08702b80aa000029571e22c194889924661fd8e8069e2f214a88e03a016808c02e40b200002956c102b6942494a4471f28e1864c2cf134083835a15507d829809a0000295663d2b9945897645d2010e746822e514688c039a16c08802a40ac0000295606d2b9942895044d1fd8e506622d613f88a838e16e08802d80b600002955a7f2c794b49aa46f2068ea46a02eb14b08f43be18509003080bc0000295549c2c3149499847220f0f2c6cc31b158893c3b417909103340ca00002954ed02b9144497645d1fe8e986982ef14108b03a216f08a02f80c6000029548d52cd94e499e4672058ec069c2f414c88ec3b618109082f00c8000029543112ab94109544471f48e086482c9136085438616108882dc0ba00002953d412b5143096a4571fa0e4c6562da13d88a43a017208802cc0ba000029537652bd14809724521f80e486742e4143089c38a16a08882d40aa0000295317f2c414989a44692038ebc6be307157094c3f019109703340d400002952b892c394b09984672080ec46c830015489303da18c09783280c0000029525cd2b2940894e44c1f38e386682e614888c83aa17208f02e40bc00002951fe22c3948498c46e2068ec86b22f314a88b039416d08582c80a600002951a012bd947498c4692088eb469a2e814708bc3c217608c82e40c80000295143d2b2141896644b1fd8e646862eb14688e03a817408f02f00bc00002950e632ba946896e4601fd8e5066a2dc13d887437215808602bc0a0000029508a12b0140c94243f1ed8de46382b512c882435614f07e02c80c6000029502d72ba947c97245c2030ecc6be2f314808b03a016708782d40b00000294fcfe2b794449764612028e7867c2e214288a83b418808b82e40ba0000294f7262be14a49a24662010e786822d813e889038616508a03040c20000294f16c2b094249644521fd0e446662d313f887c38016508882a40b20000294eb9d2b7943093e4411f20e1c6582d813d888037c16208702f40d60000294e5e52b314309684581fd0ea86902f614888bc3a617808882c40ae0000294e0062bd945c96644c1f68e406682e2147888437e16508482a40b00000294da0d2c714d49b047920c0ee06a62f114808f03c418909583180d60000294d4522b2944495c4632068e8c6782e013f089839016608982f80be0000294ce752b994409564581ff8e4c6822df14308c43b017c08b02f00b60000294c8cc2aa93d493c4411f30e406822e013f888037417208682dc0ce0000294c2e42bf94bc9964702058eb46a42f114908d83d818409082f00be0000294bd022c414ac9a647a20e0ed86a42f014c890c3ba18909403280c40000294b7372b314149524481f78e406722e8141888437c15d07f02b00b00000294b15e2be14589844622038eb06b630415209003c217408c82d80bc0000294aba42b1940893a4481fb0e6066c2da14288b839417208f83140ca0000294a5c52bc147898a45e2040ec06bc2f815288dc3aa17008682c40a200002949ff42b9144096845b2008e686942e8146889c38416b08702cc0c000002949a1a2bd946096c4541fc8e586722de14408d43b417f09583000b8000029494552b494549744591fc8e6c6742e914809043aa17908c82f80ba00002948e852b7144c97445e1fd0e3c6682d713e88a838816908703080b2000029488c92b213ec93c44a1f30e186582cd13d888037615408182d00b6000029482fc2b614689724662070e9868c2e814888bc3ae17d08d02dc0b200002947d142c414a09884642030e9068c2f214788b03ac17508902d80b00000294774d2b2942896644c1f40e4c6602d9144087c39416008a02e80be0000294717b2bd948097245a1fe0e886802ee14b09083ce18909483140c200002946bc72af144095644e1f58e686862e614008bc3b218209582f80b4000029465e62c0148c98c4622040ea869e2f014c88b43a417408c02e00ae000029460032be94709744541f40e246602d513e08943a017608c83040d000002945a412b3941895e4541f80e906862ec14408a839a17408c02e40c00000294544b2cc94e09984762100f286d8311157894c3ca18609603100c000002944e932b113f89444461f78e6c6842ef14d89103c618909783380d0000029448c62b594409744602018e886742e213a087438a16408202a80b2000029442ef2b994489444451f30e4866a2cf13f088c3ac17508d831c0ba00002943cff2c294909a046e2028ec069c2e6140889839617b09383280bc0000294372d2bc947097645d2018eac6a42f314b08e43c417408b02e00c20000294314a2bd947c9724622028e9c68a2eb140086439016c08882c00ba00002942b902ad93f49464441f48e1c6662d613e88983b2185098032c0ca000029425b12be147c9724581fd8e8c6902e9144888c39017608b02e00ba000 else 0x29709ab2b094189624551f98e3866a2da14208bc38c16d08b03000b8000029703bc2c394949964642040ed86b62f114908c43ac17508c02f00b40000296fe1b2a413cc9504481f28e2866e2e214188ac3b217b08d03040bc0000296f8472bb14309744592038ec86b630015289103d4191094030c0c40000296f27a2b894449624501f50e406822ea14688d439817508d82f00be0000296ec982c394ac9704571ff8e906822ee14c88d83a617808b83100cc0000296e6ae2c514cc99c47520d0ee86d230315209583e418d09702e80c40000296e0e22b994609824571fd0e706722de144089838a16708282c00be0000296db1b2b3143497e45f2008e7467c2e014508d03b217608a82f40c20000296d5512b7943c96a45b1fb0e706882ea14608dc3b617708982d00a80000296cf972ae941496445a1fa8e946942e914b88dc3b4185096831c0ba0000296c9ae2c294a498a46b2098ee06982f314b08e43ca18509103140c80000296c3e82b3140094844b1f58e706922dd140886c37a16108a82e00b80000296be142b8143c9664561fb8e6c6622cf133883836216408602f40b80000296b8152cf14ec9ae47b20c0efc6c830215408f83cc17c09182f80c00000296b2652a713f094c4591f78e5067c2de14408ac3b017508b02c00aa0000296ac802c594dc9a646f20b8ed06a02e214408b43aa17409183000cc0000296a6b12bb14749844661ff8eb46922e414308bc3ae17008b02d80b00000296a0d42bb94b09a847d2110eec6b42ff15108e03a417d093030c0ca00002969b122b1143494c44e1f90e746802de142889c38e16508982d00aa000029695572b2144097244e1f48e346622e014788d03bc17609083000ba00002968f732c3949899a47620c0ec86ae2f514c090c3b617008c03100ba000029689ad2b8143c97245a1ff8e9069e2e714608d43b818108f02fc0b2000029683ed2b493f893043c1f68e4866a2d913d088837a16e08e02e40c600002967e512a013b090c42c1eb8e086522d414008883a017408b03040c00000296788a2b8942896a45a1fb0e646782eb13d887438a16108502c40b2000029672a02c314ac9a04762110f2c6e830f156890c3c817c08c02dc0b800002966cb52cb15089be48320d8ef06b82fb15089143c418909283000c6000029666d02c094949924642020eb06962e4144889c38a16508602f80cc000029661002b6146497245d2018e906962e214408c43c818b09683380dc00002965b1a2c1148c99047720b0f006c22f514d88e83b217a09182e40ae000029655662a793a49204331ec8df06502ce138085837c16208582d40ba00002964f952bb14609604541fb8e1865c2d314008a83a817208c02e40ae000029649b42c314a49764642010e9c6882f614b08ec3b817509082f80c4000029643ea2b4942c9544521fe0e5c6702e614008b439a17308782b80a600002963ddd2d495109d449a21d8f686dc317158092c3e818d09383100ba000029638072bf149c9844672050ec06ac30014c88d43ae17508b02d40ac000029632512b1941c95a4411f18e086422c5136884837416208602bc0a000002962c982b114149584531fb0e846822e7140087838817108a830c0c4000029626aa2c594749664561fa8e846802f114a88e43b017b08a82fc0ca000029620dc2b814709764622020e986902ef14c88dc3ac17909203300e000002961af52c314949744632078f106d830515589043b818409083200be000029615332b014189664501f60e3c66a2da14088b43b217809183040c200002960f5d2bb14709624611fe0e6c6842ec14e09003a217308c82d80ba000029609a32aa93cc9484561fe0e7c69e2ec14608e039c17508e83000ba000029603a42cf94f49ae4832150f006ce30715108f43bc17a08d03000bc0000295fdc32c0146496e45d1fe0e5c6842e5140088c39c17508d02c80b40000295f8062b193f893043c1eb0e186362c8134883836615408382d80a60000295f2232bc146c9784632030e906982ec14888dc39616e08b02d80ac0000295ec432c294d09ac47820c0ee46a42f914c88ec3c018008d82e40ca0000295e6742bd94749a24872138f3c6d430915689383e419109b02f80cc0000295e0ab2b5142493c4471f90e6867c2e814a08fc3c2182092830c0be0000295daa02d295309ee4932188f586fa31f158893c3d417f09082ec0d00000295d4c72bc147c9704551f98e706822e914588c83a818008f02dc0b40000295cf0b2b1944496a4632030e7c6942f414f08dc3a817008a83080c40000295c90d2cf14fc9ba47320a0ef86ba2f814e08f03bc17d09203280c40000295c3562b0942096245d2020e9469e2eb14a08b039817008f83340c20000295bd882b7143494c4491f98e806902ee14a08f43c018709403100d60000295b78b2cf950c9ca47720b8eac6b430315409303c817c09003100c00000295b1a12c914f09a84762098eb46882eb14588d83a217a08c82f40c80000295abc62bd148899046b2038ea869a2e114588e83be18c09483200ca0000295a5e82c614d09bc4802120ee46b42f314908d43ae18308d82fc0c20000295a0362ab93e494643e1f70e2465a2d814288a839617d09283180d400002959a5e2bc945497c4591fe0e2466a2e114208a039a17509083140da000) else (if i < 432 then 0x2987fbe2ac140894a4501fb8e746722e114608983a217308702d0092000029879e22c314989904622008e9c6862e614788ec3ca18709503040bc000029874202b5141c9504511f78e5c6782d213a883836215c08582c40aa00002986e6f2ac13f095844f1fa8e786782d813c886438416208802d80ae0000298689f2b4944494844b1fa0e4c67c2e7142887c37615a07f02a40b2000029862cc2b9145898045c1fe8ea86aa2ed14688d83b217c08f02f40b800002985cfd2be947c99246a2088f046cc31415709283bc184091832c0c40000298572d2bc947c9864642088eb46a62fe14f08c438e17a08902d40a8000029851512b8146c97c45c2000e8c6902e6140089439a16608882d80b400002984b6b2c614a899847220b0ef46d230d156093c3e21950a003600da0000298459b2b6145097e4621ff0e9c6942ef14a08e83a416b08902e80b800002983fab2cd94c89a846b2068e9c6802e414308a83a617608c02fc0a4000029839c92c614c89a44762070eac6a22fa14c88e03ba180090830c0c4000029834012b113e89524521fb8e6466a2e814788dc3bc17d09003040b800002982e252bd146c99846e1fe0e5066e2e513e88c03ac17308b82f40be000029828532bc945c9824642020eb068c2df13a087437c16408782d80b20000298227d2b814589764601fc0e586722d813f889039a17308d82e00b600002981ca82ba146c9804672030eb06942fe15609183d818809583300c2000029816bc2c094789984642070ed06b02fc15809403d818809102fc0b0000029810dd2c0147c98846a2068ecc69a2f814a88d439c17308882d40b000002980ab12e49594a0e4a521d0f206f6315156093c3c817e08e82e80ac000029804dd2b694549664561f88e5c66e2d213b088838216908302c40a60000297ff232b3142894e44e1fa0e3467e2dd14308b03b217509102fc0ce0000297f91b2d494f89c648c21a0f5c6d830914b88c438e17108a02e80c00000297f3212c814789824622058ea06902dd14188a83a817908b82c00be0000297ed2b2c814c89a44722080ef46a82f614508b03ac18008f03280ca0000297e7562bf145c9864641fd0e746922e414508ec3a216e08782f40be0000297e1762c394ac9a446c2060ed06b42fb14a08f03ba17808d82dc0c40000297db822c894d89ac47b20b8efc6ba2f214808c83cc17f08f82ec0c80000297d5a82c3948c99c46b2048ec86c831115809503f0194096030c0ae0000297cfc02c194709684541fb8e7067a2d913d08803a617409203100cc0000297c9da2c994d89b647720b8ed86c630214e08c439c17508d82d80a80000297c3fb2bf948498e46a20a8ecc6b42ff14c08d83a017808f82f00ba0000297be182c0946097645d1fe8eb467e2e113d887c37e16408982e00ac0000297b8572ae93ec95844d1fc0e646682dc13e08983a416f08b02e00c20000297b2a22ac14009504471f10e4865e2d013e887838617308a82e40b40000297acd62b7143096845b2008e9067a2dd14308ac39c17308982c40a80000297a6e32d115289e64942160f206e830f158095c3e618c09203040b20000297a10c2c3949c9904682030ec46a22e814488a43aa17e08f02e00b400002979b512b014209644602008e6c6722e0143089039416e08c02b80ba0000297956e2c294949984602000ea868a2df14608dc3aa17408802f00bc00002978fa42b6141c95644e1f40e2466e2de13e88a439c17508702d80c8000029789da2ba947497445e2018ea069a2eb14b08f83bc18308882d40be0000297840d2b914789644602058e986922f314688ac39a17a08d830c0ca00002977e302bf948898e4612018e906a230014d88d439a17108b02c80a8000029778562c714d09b046d2070ed86aa2eb14308943a017508982dc0b4000029772992a693d09264441f80e746602c413a088037415607a827408600002976cdb2b2942895044e1fb8e646722de13e088038616c081029c09a000029766eb2c5147098a46e2050ed06a42f014a08dc3b017808f82e40b2000029761142be149c97c4632038eb869e2f314b88ec3ca18809303080c600002975b4a2b7147497c45c2008ea868c2df14108bc39e17108902c80bc000029755932ad13e894a44d1fa8e8466e2df14508a43a217008b02b40bc00002974fba2bd948c98c46f2088ee46b42f614588c439416908182b00ae000029749ea2bc145897e4662028e6c6922e913f888c39e17308c830c0d4000029744212b514289604582040ebc6a02fc14f88f03b817c08d82d40a200002973e4c2bc14809864601fc0e8067e2dc13d886838a17008a02e40be0000297386b2bd94809724541fd0e686822e3147887838216408102c40aa000029732862c214b09ae4702050ea86882e214488b03b217308a82b40a400002972c862cf14f499a47920b8f046c230515509283e418909082d80b6000029726cc2b5943c9604511fa8e7c67c2e713f08b039816c08902c00b4000029720f02bd949899046d20c0f0c6ce30c155090c3c818009483080ca00002971b342ac13b49164341f10e2065e2d5141088839a17108d82d80c6000029715402cd94f49ba47f2120f086e430614c89083a017308a82fc0bc00002970f672bb146897445d1fb8e806842d814288d03ae17708b82e40ba000 else 0x299007e00000000000000000000000000000000039617509102f80ba0000298faa12c1149c9904672008e6c6742e5141888438616108782a00b60000298f4d12bd949c98e45b2020e9468c2df14908a839416e08a82d40aa0000298ef132b214389704581fe0ea06a82ec14688c03a217508982d40ac0000298e9342c3949498e46920d8f0c6da30a156893c3e418e09483000ca0000298e3432c514cc99446d2088ecc6a42f614a08b03b417c08e82e40a20000298dd622be146c98a4611ff8e7867c2e414408cc3ba17f09483080c60000298d7832bd145897645f1ff0e846782d913b886035e15808082a80b00000298d1562e21588a084a321d8f986f631315a89483d418809803180c80000298cb572d515309d048c2128efc6ca30015309243ce18209282c80ae0000298c58d2ba14489664641fe0e6c66a2da141087c39a17608d82f00c20000298bfc92b094189564602010e9068c2e214388a43a417508d02f40ae0000298ba052b3944c9564522030e7c69a2f114988c43aa17d08c83080c20000298b4192c3949499047420d0ec468c2ef144089c39216d08782d40c40000298ae482bd14449984612030ee46ae2f914908d03a817809183180bc0000298a8792bb948498245f1fc8e8069a2f214b08e03c218309203280c20000298a2752d294fc9bc47620e8f086cc30615089203c018109103000c800002989ca12bb94b89944692088ee86c6308154892c3d618a09603140c80000298970e299135c8fe42f1ee0e286682dc140088c39a16908882c80b6000029891332be94889884622058eb46c830e157893c3e018909603240bc00002988b3a2cd14f89bc4862110ee46ae30315108e03b617c08c02ec0c40000298857f2aa93e49464471fb8e7c6882e514708dc3ac17c08b83140c4000)))))))))

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



private theorem b429630 : covered 429630 429738 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429738 : covered 429738 429846 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429846 : covered 429846 429954 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b429954 : covered 429954 430062 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430062 : covered 430062 430170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430170 : covered 430170 430278 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430278 : covered 430278 430386 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430386 : covered 430386 430494 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430494 : covered 430494 430603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430603 : covered 430603 430711 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430711 : covered 430711 430819 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430819 : covered 430819 430927 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b430927 : covered 430927 431035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431035 : covered 431035 431143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431143 : covered 431143 431251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431251 : covered 431251 431359 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431359 : covered 431359 431467 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431467 : covered 431467 431575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431575 : covered 431575 431683 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431683 : covered 431683 431791 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431791 : covered 431791 431899 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b431899 : covered 431899 432007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432007 : covered 432007 432115 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432115 : covered 432115 432223 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432223 : covered 432223 432332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432332 : covered 432332 432440 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432440 : covered 432440 432548 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432548 : covered 432548 432656 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432656 : covered 432656 432764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432764 : covered 432764 432872 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432872 : covered 432872 432980 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b432980 : covered 432980 433088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433088 : covered 433088 433196 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433196 : covered 433196 433304 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433304 : covered 433304 433412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433412 : covered 433412 433520 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433520 : covered 433520 433628 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433628 : covered 433628 433736 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433736 : covered 433736 433844 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433844 : covered 433844 433952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b433952 : covered 433952 434061 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434061 : covered 434061 434169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434169 : covered 434169 434277 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434277 : covered 434277 434385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434385 : covered 434385 434493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434493 : covered 434493 434601 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434601 : covered 434601 434709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434709 : covered 434709 434817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434817 : covered 434817 434926 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b434926 : covered 434926 435034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435034 : covered 435034 435142 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435142 : covered 435142 435250 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435250 : covered 435250 435358 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435358 : covered 435358 435466 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435466 : covered 435466 435574 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435574 : covered 435574 435682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435682 : covered 435682 435791 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435791 : covered 435791 435899 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b435899 : covered 435899 436007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436007 : covered 436007 436115 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436115 : covered 436115 436223 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436223 : covered 436223 436331 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436331 : covered 436331 436439 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436439 : covered 436439 436547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436547 : covered 436547 436655 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436655 : covered 436655 436763 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436763 : covered 436763 436871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436871 : covered 436871 436979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b436979 : covered 436979 437087 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437087 : covered 437087 437195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437195 : covered 437195 437303 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437303 : covered 437303 437411 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437411 : covered 437411 437520 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437520 : covered 437520 437628 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437628 : covered 437628 437736 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437736 : covered 437736 437844 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437844 : covered 437844 437952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b437952 : covered 437952 438060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438060 : covered 438060 438168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438168 : covered 438168 438276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438276 : covered 438276 438385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438385 : covered 438385 438493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438493 : covered 438493 438601 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438601 : covered 438601 438709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438709 : covered 438709 438817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438817 : covered 438817 438925 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b438925 : covered 438925 439033 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439033 : covered 439033 439141 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439141 : covered 439141 439250 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439250 : covered 439250 439358 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439358 : covered 439358 439466 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439466 : covered 439466 439574 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439574 : covered 439574 439682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439682 : covered 439682 439790 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439790 : covered 439790 439898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b439898 : covered 439898 440006 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440006 : covered 440006 440114 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440114 : covered 440114 440222 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440222 : covered 440222 440330 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440330 : covered 440330 440438 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440438 : covered 440438 440546 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440546 : covered 440546 440654 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440654 : covered 440654 440762 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440762 : covered 440762 440870 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440870 : covered 440870 440979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b440979 : covered 440979 441087 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441087 : covered 441087 441195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441195 : covered 441195 441303 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441303 : covered 441303 441411 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441411 : covered 441411 441519 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441519 : covered 441519 441627 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441627 : covered 441627 441735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441735 : covered 441735 441844 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441844 : covered 441844 441952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b441952 : covered 441952 442060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442060 : covered 442060 442168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442168 : covered 442168 442276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442276 : covered 442276 442384 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442384 : covered 442384 442492 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442492 : covered 442492 442600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b442600 : covered 442600 442709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 429630 442709 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b429630 (joinCoverage b429738 b429846)) (joinCoverage (joinCoverage b429954 b430062) (joinCoverage b430170 b430278))) (joinCoverage (joinCoverage (joinCoverage b430386 b430494) (joinCoverage b430603 b430711)) (joinCoverage (joinCoverage b430819 b430927) (joinCoverage b431035 b431143)))) (joinCoverage (joinCoverage (joinCoverage b431251 (joinCoverage b431359 b431467)) (joinCoverage (joinCoverage b431575 b431683) (joinCoverage b431791 b431899))) (joinCoverage (joinCoverage (joinCoverage b432007 b432115) (joinCoverage b432223 b432332)) (joinCoverage (joinCoverage b432440 b432548) (joinCoverage b432656 b432764))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b432872 (joinCoverage b432980 b433088)) (joinCoverage (joinCoverage b433196 b433304) (joinCoverage b433412 b433520))) (joinCoverage (joinCoverage (joinCoverage b433628 b433736) (joinCoverage b433844 b433952)) (joinCoverage (joinCoverage b434061 b434169) (joinCoverage b434277 b434385)))) (joinCoverage (joinCoverage (joinCoverage b434493 (joinCoverage b434601 b434709)) (joinCoverage (joinCoverage b434817 b434926) (joinCoverage b435034 b435142))) (joinCoverage (joinCoverage (joinCoverage b435250 b435358) (joinCoverage b435466 b435574)) (joinCoverage (joinCoverage b435682 b435791) (joinCoverage b435899 b436007)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b436115 (joinCoverage b436223 b436331)) (joinCoverage (joinCoverage b436439 b436547) (joinCoverage b436655 b436763))) (joinCoverage (joinCoverage (joinCoverage b436871 b436979) (joinCoverage b437087 b437195)) (joinCoverage (joinCoverage b437303 b437411) (joinCoverage b437520 b437628)))) (joinCoverage (joinCoverage (joinCoverage b437736 (joinCoverage b437844 b437952)) (joinCoverage (joinCoverage b438060 b438168) (joinCoverage b438276 b438385))) (joinCoverage (joinCoverage (joinCoverage b438493 b438601) (joinCoverage b438709 b438817)) (joinCoverage (joinCoverage b438925 b439033) (joinCoverage b439141 b439250))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b439358 (joinCoverage b439466 b439574)) (joinCoverage (joinCoverage b439682 b439790) (joinCoverage b439898 b440006))) (joinCoverage (joinCoverage (joinCoverage b440114 b440222) (joinCoverage b440330 b440438)) (joinCoverage (joinCoverage b440546 b440654) (joinCoverage b440762 b440870)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b440979 b441087) (joinCoverage b441195 b441303)) (joinCoverage (joinCoverage b441411 b441519) (joinCoverage b441627 b441735))) (joinCoverage (joinCoverage (joinCoverage b441844 b441952) (joinCoverage b442060 b442168)) (joinCoverage (joinCoverage b442276 b442384) (joinCoverage b442492 b442600)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 429630 ≤ index 825000000/512 := by decide +kernel
private theorem starting_value : fast 825000000=42364890 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 825000000=42364890) (n : ℕ) (low : 825000000≤n) (bound : n≤850000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=825000000
    · rw [first,anchor]
      exact starting_value
    · have past : 825000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤850000000 by omega)
        have within : index n / 512 < 442709 := by omega
        have lower : index 825000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤850000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ825000000To850000000
