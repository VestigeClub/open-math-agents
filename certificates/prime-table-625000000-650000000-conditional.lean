import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ625000000To650000000

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




private def radical : ℕ := 0x28ed95baab9314bc851c33ec7f2c42e6c91dccb4f1379b0b62886bcaadc91dea1514e53048b5cdbc444f0cd6152a37aa5b90b180afca9d1cad24e9224c81b150cd483b71dc98f756353ece064786dad7cebe80434f2a4b87463a8f08855d200877ad0796ea4726cf1ccf751241f7dd32a514cecbe3999b3aa66acbfef5fe72c1023fdd99cb670bb99ec2dd9f03f8ceee35a483dec4cb5cd67302eb6b6346a9dafefb5ce1843f946ddce92d0bdfa7ee8275afcc92a4ef6ffdffa653b6e6336f8a7a5ddb07ed6af364e8690a74e96120a82fd50b874d5fcbc8301b9178cedc390f5adb963c48bf16935e9467d6f797a20a1669d9f922f9b4f35a4b89a98e02ac75c5d6053b522def0cd3343dd71d732ade19f3f625e7f593eea69b301a3c25353bdde9e12f32fd8f287940bc2a2ea088133e9554a51ba81296e1054cf21d178d482030308b5a0fe57ecd73f9bffc13ca892a897d0e9375d3b22026ecb798f74f3bdccff68076f9e378a3b6f23ab3f210be0c794cc83f2b440fc632f47f05e3288d70306a28790e5d7dac4824a559f87a4052d0419b13461b9671ba7393910d29a912a60e37601a6ec271bebc2fd6e6a8bacda1692bfdae865c4c56d75ae61760b9201796d71e35ff238427ca48dfc68c6c396de2c57180765a7d16d88b4e8afd59d23205580a00c93f4395e15c1120caa2b9fe56d352b6d0fd2d9a16d369c3da57a8bcdb3a61b54ae38ab03874591690a1524b52783d1ae82e2dddeda67955645c751cffca6f6a814123c2cd03fca223d64c1972bd5357abef7d45023463f076b16440288905191ab318aecef5481c56a18c844b8779f25db059be47339478d0d045b67bc15ccce9686edde2af76dc0e79daffc1cc8825271b5a9b65f393148b64e840672f9b3cd2c9e912c9767173e838ea5458495f5204f9cf5b73e51dc9e288e227884f1d3d0893ff20269c897820a55fd84a033c626b6235aa6b6e94e254d089342176e67b2963d1d6e45d216574fe59d5e0444481b35801b47771351f879e8b545c89c0c4baf2947b7a522c28f4c1a2e56f77bcdd4788597fe492fed8a0bb37f7116c19f5e1cbcfdb3364ea9f46d9ff43bb7f0aeae638de8cedffbda2bafc648db77b3f0e238fce3140b692f572a817634484a8f826fb7dccc86484bcf16600cf54a4c10265d2bd6c93d8acc2101b0ab5c1fa75ca452d6b076304ad521a6606e3e51b37cc4608bc3411bbdf229f335590669886f9a1df715e1695ea2a3ee94f1a6609ed5b3758d2f4b26a84291cdff3e82de39c77be174db9a1a542a970bd38c0a88ad6b4bda887c3535162b70c92a7057b2908dd5c0c1946d5ab5596ad02da8602ae2a73d2f7123c31b26f3122a887d4f23c2acd0677a0107790c0d3de8d6e92846ba1246eb8162c47a70f5457de8442807ced09ab07cd6f854cded928cacfe48cfdceb4f1a3ed92e471656f49bf67378b77fe39338810a7ad3605146f2db31f5cbe26eb306fb0d5c9ac5c8ff28684c8fe9b6ebee9ca71b9d173ed5aa370c6fe51a710d02b4d92774a6297a3af652727df9f4e728d9b11c22acd6e6b99be4bf2d319afba3e74458daf9f8eaad6bf2e9405c06f1ac7bd1f3871e7a1e7db33c9aeba09e7dd2742ce6d748006ff5cdeb23574a316191a48718f07134fac80545d8368e042b167757200fa58c1733d098f24777bbc105c7ce5e02c1641acf3292933facf27db4fd3d3a3eb623041693e41d5083269a97ecee106e5e084280ceddbc099a8fb6bec7e7aad97943430458df8f8d436061276aec24473668a1246d5a748e9b91ecb82db1eed50ce187675b8a092934f82b2b6631ed8926cbf53d01ffed258e5e7f49d203e66573fd7393621b4e54b287b19eb778b1833297a308ddd558f765f046dc76d4c0d3d6b680b5ec330bb903618f69218e00842f854c8445620797f955024d902266bcecd5ec9c37f8d02a713705ca26f841000135ab9d79dcbf98ceb9525ff18295aa0bf4754a3dfceda24a5ba00e1837dade53576e88a2689a0baecdaaa1d992e3ac99b5e487c7ab45767cd6f0334809dd0d910d71b22d64c6df36b2a87e713a5cf73e4f2c7902955e2c381bca9a6001802a031d162ca37f044714981ca76f4bf948697ff9eaa6cf33b84ee9b5247420b01d7910ebb13e7a205fe25eb94e61bcecb14cfe1345e3a87c8417d560733587c15245c82696328edd560497270179df64828182bc2b5166248da528eba13cb47bf099ef08a5c2d05d5bb55d4e95654ab34334d9c7bbcf9cf80b3ba9116b2e00630ea3a8015f7e27c0f704231191db9777cbcc01d79cd358866f6a197c920541a5817521d614441bbb74a5525441c7dbab35cd47fb3e9095a4a98075e4e490f35ac540dd550b1ea61b48d1d7937d09663c98033a40a6bcc6c4099c51f449a8add939c55442e288f83fbc0e1ea1d7da8092d457e3944a8e5102a187b66fae278a40f084bbed7b91c58dd4ab281e2441d97eed95afe5e4dd6e7aab9e1ed7b6feb01d9f656a59eb2c843fba0967cc1ff2e39ee0ff968acae0b98ac189dd492a97e98beaae539644bd1aaa11847088ff1f2b728482733339c33b5c0eec0291f0e66edf58069365614d1fc3f40e58e7870cd6d1c774af65edf176f226f3e8f89c47c52176616633b9a340e588135045d9934dddd4706b6174a2fe019f2433717b15892eaf833aa35affc8317079968fb7d6b5a7ef9681358e861cd39c16785a538b0cc478669caebd8f43990bc64f86752be04b99dd212629b16c3c90b2953cf81471c465098fe305c4e62fd7152ad926bfdb72576e73fec0bf1d4e22344987889be240e81a39b3c1183a2a570d7f425b9f606262aa4ae0ad74adea80f358bb6cbc203ee514090be2ec43d7411e098d66c84fc757b00d6efa120bc7cf6c517f62fc30ab5c9c1c9083b781cf797673682c751c5e7973415a747c783b26f5a4d1d122fc5d1951b86a7de877888ceaf20e90488e1da7f9caf68625054da199c12553c92dd1fd2bf3f8f5b52b83c55f09d25f9d1ddd53ad3399b3e74b540a08368071be4c490f92c68c277eeb6bf2efad179d3e5b4141e7ef0ae2c34bd96a6ef6dbe1fb4e1a50db770c0dfbdea7079eeadd7141d4351c19de130fb52d2ea255069b258e7390a8f5a4a74af8862392b7fe7a1fd12c78392a253c934bb177b9206863c6485369510f8483ddd611e3a5e79fca110942d9baa9983bdc02a34dfdf58dda8f457f441f47d64ee0ac9e7379057e70566802939930929f3e213086f0e3ec882a434bb31cbe80004ea52301ab54ca24c4e38ee34e0e2938c6a372e547952c7fb8411e2ab7896aff8d3f4eec2f7839be3a6dd0aa653e0b6c5538b2c581fe978b520f9aed37f8f4baf0bb07ace508e31f0562221434a4d9826c646b1257edc1be82041156bf65bd3b5b3f84f19f7f939a73e5b8601659e359d1ba1b132535903c5e0e9159507dd65b000799cb9238896d9ad72c11a10addd8b19bf895d056f316a2e0ed939c60ec641e37f88d305fe563d7c4f64aa4f126af4785f8b588c0849811fa58bb2438ab40bae0d7093b8ce0d87e687382610c288c14cef980671a735d7a65e12dd0e8b518786daf8b33683ccf89961379bb59da2f3d47b673212119de3e1332671aa7bdbebfaa7d80a433a42124246804344925efdc1ebba65c59095eaec0e7cedce8d52a56db0b2206d32c70ee8750a38f545ad57ee19886c5619c259174018d2a07e25dd8b66fc9c512fd15d1762b3ff7e15bc26612354a113b5cc64c5e7f5cca80b65569da010c020709f5e850633e1bbf4e45d6cc2163064e85fd5ad696d5636e274a2dcff520cfd3c55420277b10d76d0339a4148a66060ffe93e2b6bc4e5f1dd7d19272cd942f2c5d5acec85770fa7a83a5fb2994e5cc322966d676aecedda3011509035b5cad7472c41a444bffe4958c5719f9438094698a1422d87cd6d4ba0de20f3f7abdf7c0138b8147cfaaeab54f2a81838d6f2ee6a6adeee3b3a1361ebc87e5371a007cc186ee90d6ee97ab465c122bb064ee3f4ae0a15aa1becc9111585269d2cebd69dc37c7e8d4b86180b6be939ab148efae2c9c897aa6f852b9031266edd26b77344b01290d45150ba71ae5d7a2103bc19594dfb2c73bee49314da9a7949fa61e892c64cf6336dde9059b078dd0b4cb46d2444b3487eb3f6a891193d52b8154bf6609c3ecb4c412f2537a5d5b95f9eda4a129f2e78cd667d05836793a98a02978f228fcef00058e8d4019a1b71f5c1a479808e4db8f0b5b6bf0d626b1fb58ad1f15876021ed2cb85812fce5ad5288289567203cf0f1c76c311d314d78e170ef14db02d34de28f030d1fd956c4c7fe9076908e752b562625017b4df437b464f004887f262399d7628621cffdfb3bffc47bd97fc59d1281210fb8ea8de034e1f99c8530dc1210cdaa8ce705c0ac5835db648358d537b37e763a4867edd7a2760cc440f6662fd2838f79bb92152a2d2d3419dad7f73ac43a19605701dfd07e0502cde48510f698b2b3b9730e5b0bd5873a264a06035cc4696a9bc1cbc6c16d76fd12fe5a8c683adce94a9f6487791f83a4afd0d57a475cf779ae727029abe39b5a6bb5a9c35a9e5114dda22379baeeccfe5e8e7930219907b0979fe4a69d8b5b5a13ebc22aca2e652637e98c55c43a7eeedc1aa2c8c1e1d6c328a5f2ad4372f81abac0a9cc30baeeb4673654db96449d15024695fe9a21da45b5e0aa9b84aa745a94922e6bcae57d5907d5a7f1688c3137a3573ddbc1f1353f177c1b77e3617dda39204339b7bc39544aa648b3788ac0a78b0709c636a1f0973ce97c7d801b37700fd3a472958ca1af18a89c7a9370a0d6d4e050f0ddad59b9d8eaf68931c48b564180d8be856b387d52e5d8f8ec4e4f82847d9712fd942efbb234c90f532f431075bbbb1fb1a5df1fe2f3448440a731739bc37bfdc7e1fd927fdc855ae23060c3a8a08b22b9480eecc8c057b4b894687e323410b5d53d5e722289dd44a0fd6f4f30d451ef68d9d280418a8590aaa0848a01e4f41224fcd29de6fc40f0829d650000c4970ed76f895b5b595f60b38ae1ed6a32b16fccfe674ab50d5fb1af3697df7c608c78bd3b7ea63d443965c7517b114ca9dfa75c26070eaa7bcde83d4b0c8563032c19b22ea2269c82950f3aacb55a037741839d22e69eeb14d8b40cef1205d48919be06543aa7e50191b557c7a476187c60e753b838fca824e41ed6532c531c18029b0b7d843dcb8a31cd6c1e6fdc4d5b7e71cf37f56095f1f357381968c75076de83b474a7866def472809e51feec3f58d491e36c649b29f42e094db8f6c246b84e2a3579239c74a65bf4fa4a609200363f576657b157b83bb2f05af819751999d43ae1c4059419855a461651d783ffe7c19d6a7659c09ac3a8f87137067f432dfb766df3ac09c0199c1660c8cbbd2036c58ca9e70617be1742b5d471ae6c689714b585725125d4af13793e37030efddf5eb341d368270bfb0e48f364e9b0c40b508e9af4af1b1cd80f4b4d37cfe40648bb83ed7933c0739536676e4894e09b111c74fed4a523a803f14e3d6492e00ea4dbf934cfed70a8cf95c9101cd668acfbc53c122ec02c59ded26ca722fa6989f8b78540b6b3b3bab0d4a445a608c159104b1b5caa4be420ad655eae18ad60af8d00b46e3bd62d22658f618034c7ec01e519c3e60ebbfdf23417336f05dead2991d05f53575fc12e902d794f3457bd95c01fec760170b5744449fa2b05856df6a106461f9d5973e0c61483bc1f3abb3c1f9a06fb878633b7b25801298f70b9d555d0c7e04194b1321b8900a6dee8b25f6d3bac3d70d36ffb576119413f0f49b23c10d67737a31c4f9cce144536246307070dc6c96b60b00c9e98cd245c00582e729d5a3a93105edbb2cbf2238b693dd5387e8b7586fcd9b5f30ee522b312ab34854b2757e8c7d48b6cf451e8fe08912c53e0eda399223c2e65ddfb4a07d74687977c3f0e7e9fd7fb4b232a18fa2bc8d6d30ac7d6aef648e75fe06abb3c7bb06957677de513c46d9ee200dba157ede16467614f27a26bfc90fc74892954547417cf53d98cc0c059c0826c8cbe01ec3e8cdc77c0414ffed9091f0294958300224f44e5492d4434f63cec6b4e13c6d007d5f83a8c050cae9b78afda630ad7b34201732c8a269b2605a88682fb5f2729b70c4d46b68b8cc5081f0a0ca5dbdb94b7b237bb21216419f81294bc141011202ebb84961a810b2016f5d80557afb29eed70a217ed584624d600e02e03db17c44cc4ab38f51fb6ead7c6db71b2a915b858eac05fa328d874100d25454455516a42791521a20c98f7dd989111579c2c53676d26e90997e0219abb38e9ce57494ddf7f84429f32ba13d3f8b004ec1ace10922e839358ecb0bc3200b9d33e7d505c0ab32f4e472dbd9c2994de965eb3a1f5c09342

private def light (n : ℕ) : Bool :=
  if n≤159 then decide n.Prime else n.gcd 2946702272495038326504339507351214862194953894034126281105653614484641084171384877168612688988218723122267050655122476638168421183149385930893186799109435156968004883209906330997062135376272570217948962453536198860613811636208208325279592585625600000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤25495) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 159 = 2946702272495038326504339507351214862194953894034126281105653614484641084171384877168612688988218723122267050655122476638168421183149385930893186799109435156968004883209906330997062135376272570217948962453536198860613811636208208325279592585625600000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 159 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤25495 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 49 := by unfold smallValid; decide +kernel

private theorem sp49 : smallValid 49 50 := by unfold smallValid; decide +kernel

private theorem sp99 : smallValid 99 50 := by unfold smallValid; decide +kernel

private theorem sp149 : smallValid 149 50 := by unfold smallValid; decide +kernel

private theorem sp199 : smallValid 199 49 := by unfold smallValid; decide +kernel

private theorem sp248 : smallValid 248 50 := by unfold smallValid; decide +kernel

private theorem sp298 : smallValid 298 50 := by unfold smallValid; decide +kernel

private theorem sp348 : smallValid 348 50 := by unfold smallValid; decide +kernel

private theorem sp398 : smallValid 398 49 := by unfold smallValid; decide +kernel

private theorem sp447 : smallValid 447 50 := by unfold smallValid; decide +kernel

private theorem sp497 : smallValid 497 50 := by unfold smallValid; decide +kernel

private theorem sp547 : smallValid 547 50 := by unfold smallValid; decide +kernel

private theorem sp597 : smallValid 597 49 := by unfold smallValid; decide +kernel

private theorem sp646 : smallValid 646 50 := by unfold smallValid; decide +kernel

private theorem sp696 : smallValid 696 50 := by unfold smallValid; decide +kernel

private theorem sp746 : smallValid 746 50 := by unfold smallValid; decide +kernel

private theorem sp796 : smallValid 796 49 := by unfold smallValid; decide +kernel

private theorem sp845 : smallValid 845 50 := by unfold smallValid; decide +kernel

private theorem sp895 : smallValid 895 50 := by unfold smallValid; decide +kernel

private theorem sp945 : smallValid 945 50 := by unfold smallValid; decide +kernel

private theorem sp995 : smallValid 995 49 := by unfold smallValid; decide +kernel

private theorem sp1044 : smallValid 1044 50 := by unfold smallValid; decide +kernel

private theorem sp1094 : smallValid 1094 50 := by unfold smallValid; decide +kernel

private theorem sp1144 : smallValid 1144 50 := by unfold smallValid; decide +kernel

private theorem sp1194 : smallValid 1194 49 := by unfold smallValid; decide +kernel

private theorem sp1243 : smallValid 1243 50 := by unfold smallValid; decide +kernel

private theorem sp1293 : smallValid 1293 50 := by unfold smallValid; decide +kernel

private theorem sp1343 : smallValid 1343 50 := by unfold smallValid; decide +kernel

private theorem sp1393 : smallValid 1393 50 := by unfold smallValid; decide +kernel

private theorem sp1443 : smallValid 1443 50 := by unfold smallValid; decide +kernel

private theorem sp1493 : smallValid 1493 50 := by unfold smallValid; decide +kernel

private theorem sp1543 : smallValid 1543 50 := by unfold smallValid; decide +kernel

private theorem sp1593 : smallValid 1593 49 := by unfold smallValid; decide +kernel

private theorem sp1642 : smallValid 1642 50 := by unfold smallValid; decide +kernel

private theorem sp1692 : smallValid 1692 50 := by unfold smallValid; decide +kernel

private theorem sp1742 : smallValid 1742 50 := by unfold smallValid; decide +kernel

private theorem sp1792 : smallValid 1792 49 := by unfold smallValid; decide +kernel

private theorem sp1841 : smallValid 1841 50 := by unfold smallValid; decide +kernel

private theorem sp1891 : smallValid 1891 50 := by unfold smallValid; decide +kernel

private theorem sp1941 : smallValid 1941 50 := by unfold smallValid; decide +kernel

private theorem sp1991 : smallValid 1991 49 := by unfold smallValid; decide +kernel

private theorem sp2040 : smallValid 2040 50 := by unfold smallValid; decide +kernel

private theorem sp2090 : smallValid 2090 50 := by unfold smallValid; decide +kernel

private theorem sp2140 : smallValid 2140 50 := by unfold smallValid; decide +kernel

private theorem sp2190 : smallValid 2190 50 := by unfold smallValid; decide +kernel

private theorem sp2240 : smallValid 2240 50 := by unfold smallValid; decide +kernel

private theorem sp2290 : smallValid 2290 50 := by unfold smallValid; decide +kernel

private theorem sp2340 : smallValid 2340 50 := by unfold smallValid; decide +kernel

private theorem sp2390 : smallValid 2390 49 := by unfold smallValid; decide +kernel

private theorem sp2439 : smallValid 2439 50 := by unfold smallValid; decide +kernel

private theorem sp2489 : smallValid 2489 50 := by unfold smallValid; decide +kernel

private theorem sp2539 : smallValid 2539 50 := by unfold smallValid; decide +kernel

private theorem sp2589 : smallValid 2589 49 := by unfold smallValid; decide +kernel

private theorem sp2638 : smallValid 2638 50 := by unfold smallValid; decide +kernel

private theorem sp2688 : smallValid 2688 50 := by unfold smallValid; decide +kernel

private theorem sp2738 : smallValid 2738 50 := by unfold smallValid; decide +kernel

private theorem sp2788 : smallValid 2788 49 := by unfold smallValid; decide +kernel

private theorem sp2837 : smallValid 2837 50 := by unfold smallValid; decide +kernel

private theorem sp2887 : smallValid 2887 50 := by unfold smallValid; decide +kernel

private theorem sp2937 : smallValid 2937 50 := by unfold smallValid; decide +kernel

private theorem sp2987 : smallValid 2987 50 := by unfold smallValid; decide +kernel

private theorem sp3037 : smallValid 3037 50 := by unfold smallValid; decide +kernel

private theorem sp3087 : smallValid 3087 50 := by unfold smallValid; decide +kernel

private theorem sp3137 : smallValid 3137 50 := by unfold smallValid; decide +kernel

private theorem sp3187 : smallValid 3187 49 := by unfold smallValid; decide +kernel

private theorem sp3236 : smallValid 3236 50 := by unfold smallValid; decide +kernel

private theorem sp3286 : smallValid 3286 50 := by unfold smallValid; decide +kernel

private theorem sp3336 : smallValid 3336 50 := by unfold smallValid; decide +kernel

private theorem sp3386 : smallValid 3386 49 := by unfold smallValid; decide +kernel

private theorem sp3435 : smallValid 3435 50 := by unfold smallValid; decide +kernel

private theorem sp3485 : smallValid 3485 50 := by unfold smallValid; decide +kernel

private theorem sp3535 : smallValid 3535 50 := by unfold smallValid; decide +kernel

private theorem sp3585 : smallValid 3585 49 := by unfold smallValid; decide +kernel

private theorem sp3634 : smallValid 3634 50 := by unfold smallValid; decide +kernel

private theorem sp3684 : smallValid 3684 50 := by unfold smallValid; decide +kernel

private theorem sp3734 : smallValid 3734 50 := by unfold smallValid; decide +kernel

private theorem sp3784 : smallValid 3784 49 := by unfold smallValid; decide +kernel

private theorem sp3833 : smallValid 3833 50 := by unfold smallValid; decide +kernel

private theorem sp3883 : smallValid 3883 50 := by unfold smallValid; decide +kernel

private theorem sp3933 : smallValid 3933 50 := by unfold smallValid; decide +kernel

private theorem sp3983 : smallValid 3983 49 := by unfold smallValid; decide +kernel

private theorem sp4032 : smallValid 4032 50 := by unfold smallValid; decide +kernel

private theorem sp4082 : smallValid 4082 50 := by unfold smallValid; decide +kernel

private theorem sp4132 : smallValid 4132 50 := by unfold smallValid; decide +kernel

private theorem sp4182 : smallValid 4182 49 := by unfold smallValid; decide +kernel

private theorem sp4231 : smallValid 4231 50 := by unfold smallValid; decide +kernel

private theorem sp4281 : smallValid 4281 50 := by unfold smallValid; decide +kernel

private theorem sp4331 : smallValid 4331 50 := by unfold smallValid; decide +kernel

private theorem sp4381 : smallValid 4381 49 := by unfold smallValid; decide +kernel

private theorem sp4430 : smallValid 4430 50 := by unfold smallValid; decide +kernel

private theorem sp4480 : smallValid 4480 50 := by unfold smallValid; decide +kernel

private theorem sp4530 : smallValid 4530 50 := by unfold smallValid; decide +kernel

private theorem sp4580 : smallValid 4580 50 := by unfold smallValid; decide +kernel

private theorem sp4630 : smallValid 4630 50 := by unfold smallValid; decide +kernel

private theorem sp4680 : smallValid 4680 50 := by unfold smallValid; decide +kernel

private theorem sp4730 : smallValid 4730 50 := by unfold smallValid; decide +kernel

private theorem sp4780 : smallValid 4780 49 := by unfold smallValid; decide +kernel

private theorem sp4829 : smallValid 4829 50 := by unfold smallValid; decide +kernel

private theorem sp4879 : smallValid 4879 50 := by unfold smallValid; decide +kernel

private theorem sp4929 : smallValid 4929 50 := by unfold smallValid; decide +kernel

private theorem sp4979 : smallValid 4979 49 := by unfold smallValid; decide +kernel

private theorem sp5028 : smallValid 5028 50 := by unfold smallValid; decide +kernel

private theorem sp5078 : smallValid 5078 50 := by unfold smallValid; decide +kernel

private theorem sp5128 : smallValid 5128 50 := by unfold smallValid; decide +kernel

private theorem sp5178 : smallValid 5178 49 := by unfold smallValid; decide +kernel

private theorem sp5227 : smallValid 5227 50 := by unfold smallValid; decide +kernel

private theorem sp5277 : smallValid 5277 50 := by unfold smallValid; decide +kernel

private theorem sp5327 : smallValid 5327 50 := by unfold smallValid; decide +kernel

private theorem sp5377 : smallValid 5377 50 := by unfold smallValid; decide +kernel

private theorem sp5427 : smallValid 5427 50 := by unfold smallValid; decide +kernel

private theorem sp5477 : smallValid 5477 50 := by unfold smallValid; decide +kernel

private theorem sp5527 : smallValid 5527 50 := by unfold smallValid; decide +kernel

private theorem sp5577 : smallValid 5577 49 := by unfold smallValid; decide +kernel

private theorem sp5626 : smallValid 5626 50 := by unfold smallValid; decide +kernel

private theorem sp5676 : smallValid 5676 50 := by unfold smallValid; decide +kernel

private theorem sp5726 : smallValid 5726 50 := by unfold smallValid; decide +kernel

private theorem sp5776 : smallValid 5776 49 := by unfold smallValid; decide +kernel

private theorem sp5825 : smallValid 5825 50 := by unfold smallValid; decide +kernel

private theorem sp5875 : smallValid 5875 50 := by unfold smallValid; decide +kernel

private theorem sp5925 : smallValid 5925 50 := by unfold smallValid; decide +kernel

private theorem sp5975 : smallValid 5975 49 := by unfold smallValid; decide +kernel

private theorem sp6024 : smallValid 6024 50 := by unfold smallValid; decide +kernel

private theorem sp6074 : smallValid 6074 50 := by unfold smallValid; decide +kernel

private theorem sp6124 : smallValid 6124 50 := by unfold smallValid; decide +kernel

private theorem sp6174 : smallValid 6174 50 := by unfold smallValid; decide +kernel

private theorem sp6224 : smallValid 6224 50 := by unfold smallValid; decide +kernel

private theorem sp6274 : smallValid 6274 50 := by unfold smallValid; decide +kernel

private theorem sp6324 : smallValid 6324 50 := by unfold smallValid; decide +kernel

private theorem sp6374 : smallValid 6374 49 := by unfold smallValid; decide +kernel

private theorem sp6423 : smallValid 6423 50 := by unfold smallValid; decide +kernel

private theorem sp6473 : smallValid 6473 50 := by unfold smallValid; decide +kernel

private theorem sp6523 : smallValid 6523 50 := by unfold smallValid; decide +kernel

private theorem sp6573 : smallValid 6573 49 := by unfold smallValid; decide +kernel

private theorem sp6622 : smallValid 6622 50 := by unfold smallValid; decide +kernel

private theorem sp6672 : smallValid 6672 50 := by unfold smallValid; decide +kernel

private theorem sp6722 : smallValid 6722 50 := by unfold smallValid; decide +kernel

private theorem sp6772 : smallValid 6772 49 := by unfold smallValid; decide +kernel

private theorem sp6821 : smallValid 6821 50 := by unfold smallValid; decide +kernel

private theorem sp6871 : smallValid 6871 50 := by unfold smallValid; decide +kernel

private theorem sp6921 : smallValid 6921 50 := by unfold smallValid; decide +kernel

private theorem sp6971 : smallValid 6971 49 := by unfold smallValid; decide +kernel

private theorem sp7020 : smallValid 7020 50 := by unfold smallValid; decide +kernel

private theorem sp7070 : smallValid 7070 50 := by unfold smallValid; decide +kernel

private theorem sp7120 : smallValid 7120 50 := by unfold smallValid; decide +kernel

private theorem sp7170 : smallValid 7170 49 := by unfold smallValid; decide +kernel

private theorem sp7219 : smallValid 7219 50 := by unfold smallValid; decide +kernel

private theorem sp7269 : smallValid 7269 50 := by unfold smallValid; decide +kernel

private theorem sp7319 : smallValid 7319 50 := by unfold smallValid; decide +kernel

private theorem sp7369 : smallValid 7369 49 := by unfold smallValid; decide +kernel

private theorem sp7418 : smallValid 7418 50 := by unfold smallValid; decide +kernel

private theorem sp7468 : smallValid 7468 50 := by unfold smallValid; decide +kernel

private theorem sp7518 : smallValid 7518 50 := by unfold smallValid; decide +kernel

private theorem sp7568 : smallValid 7568 49 := by unfold smallValid; decide +kernel

private theorem sp7617 : smallValid 7617 50 := by unfold smallValid; decide +kernel

private theorem sp7667 : smallValid 7667 50 := by unfold smallValid; decide +kernel

private theorem sp7717 : smallValid 7717 50 := by unfold smallValid; decide +kernel

private theorem sp7767 : smallValid 7767 50 := by unfold smallValid; decide +kernel

private theorem sp7817 : smallValid 7817 50 := by unfold smallValid; decide +kernel

private theorem sp7867 : smallValid 7867 50 := by unfold smallValid; decide +kernel

private theorem sp7917 : smallValid 7917 50 := by unfold smallValid; decide +kernel

private theorem sp7967 : smallValid 7967 49 := by unfold smallValid; decide +kernel

private theorem sp8016 : smallValid 8016 50 := by unfold smallValid; decide +kernel

private theorem sp8066 : smallValid 8066 50 := by unfold smallValid; decide +kernel

private theorem sp8116 : smallValid 8116 50 := by unfold smallValid; decide +kernel

private theorem sp8166 : smallValid 8166 49 := by unfold smallValid; decide +kernel

private theorem sp8215 : smallValid 8215 50 := by unfold smallValid; decide +kernel

private theorem sp8265 : smallValid 8265 50 := by unfold smallValid; decide +kernel

private theorem sp8315 : smallValid 8315 50 := by unfold smallValid; decide +kernel

private theorem sp8365 : smallValid 8365 49 := by unfold smallValid; decide +kernel

private theorem sp8414 : smallValid 8414 50 := by unfold smallValid; decide +kernel

private theorem sp8464 : smallValid 8464 50 := by unfold smallValid; decide +kernel

private theorem sp8514 : smallValid 8514 50 := by unfold smallValid; decide +kernel

private theorem sp8564 : smallValid 8564 50 := by unfold smallValid; decide +kernel

private theorem sp8614 : smallValid 8614 50 := by unfold smallValid; decide +kernel

private theorem sp8664 : smallValid 8664 50 := by unfold smallValid; decide +kernel

private theorem sp8714 : smallValid 8714 50 := by unfold smallValid; decide +kernel

private theorem sp8764 : smallValid 8764 49 := by unfold smallValid; decide +kernel

private theorem sp8813 : smallValid 8813 50 := by unfold smallValid; decide +kernel

private theorem sp8863 : smallValid 8863 50 := by unfold smallValid; decide +kernel

private theorem sp8913 : smallValid 8913 50 := by unfold smallValid; decide +kernel

private theorem sp8963 : smallValid 8963 49 := by unfold smallValid; decide +kernel

private theorem sp9012 : smallValid 9012 50 := by unfold smallValid; decide +kernel

private theorem sp9062 : smallValid 9062 50 := by unfold smallValid; decide +kernel

private theorem sp9112 : smallValid 9112 50 := by unfold smallValid; decide +kernel

private theorem sp9162 : smallValid 9162 49 := by unfold smallValid; decide +kernel

private theorem sp9211 : smallValid 9211 50 := by unfold smallValid; decide +kernel

private theorem sp9261 : smallValid 9261 50 := by unfold smallValid; decide +kernel

private theorem sp9311 : smallValid 9311 50 := by unfold smallValid; decide +kernel

private theorem sp9361 : smallValid 9361 50 := by unfold smallValid; decide +kernel

private theorem sp9411 : smallValid 9411 50 := by unfold smallValid; decide +kernel

private theorem sp9461 : smallValid 9461 50 := by unfold smallValid; decide +kernel

private theorem sp9511 : smallValid 9511 50 := by unfold smallValid; decide +kernel

private theorem sp9561 : smallValid 9561 49 := by unfold smallValid; decide +kernel

private theorem sp9610 : smallValid 9610 50 := by unfold smallValid; decide +kernel

private theorem sp9660 : smallValid 9660 50 := by unfold smallValid; decide +kernel

private theorem sp9710 : smallValid 9710 50 := by unfold smallValid; decide +kernel

private theorem sp9760 : smallValid 9760 49 := by unfold smallValid; decide +kernel

private theorem sp9809 : smallValid 9809 50 := by unfold smallValid; decide +kernel

private theorem sp9859 : smallValid 9859 50 := by unfold smallValid; decide +kernel

private theorem sp9909 : smallValid 9909 50 := by unfold smallValid; decide +kernel

private theorem sp9959 : smallValid 9959 49 := by unfold smallValid; decide +kernel

private theorem sp10008 : smallValid 10008 50 := by unfold smallValid; decide +kernel

private theorem sp10058 : smallValid 10058 50 := by unfold smallValid; decide +kernel

private theorem sp10108 : smallValid 10108 50 := by unfold smallValid; decide +kernel

private theorem sp10158 : smallValid 10158 49 := by unfold smallValid; decide +kernel

private theorem sp10207 : smallValid 10207 50 := by unfold smallValid; decide +kernel

private theorem sp10257 : smallValid 10257 50 := by unfold smallValid; decide +kernel

private theorem sp10307 : smallValid 10307 50 := by unfold smallValid; decide +kernel

private theorem sp10357 : smallValid 10357 49 := by unfold smallValid; decide +kernel

private theorem sp10406 : smallValid 10406 50 := by unfold smallValid; decide +kernel

private theorem sp10456 : smallValid 10456 50 := by unfold smallValid; decide +kernel

private theorem sp10506 : smallValid 10506 50 := by unfold smallValid; decide +kernel

private theorem sp10556 : smallValid 10556 49 := by unfold smallValid; decide +kernel

private theorem sp10605 : smallValid 10605 50 := by unfold smallValid; decide +kernel

private theorem sp10655 : smallValid 10655 50 := by unfold smallValid; decide +kernel

private theorem sp10705 : smallValid 10705 50 := by unfold smallValid; decide +kernel

private theorem sp10755 : smallValid 10755 49 := by unfold smallValid; decide +kernel

private theorem sp10804 : smallValid 10804 50 := by unfold smallValid; decide +kernel

private theorem sp10854 : smallValid 10854 50 := by unfold smallValid; decide +kernel

private theorem sp10904 : smallValid 10904 50 := by unfold smallValid; decide +kernel

private theorem sp10954 : smallValid 10954 50 := by unfold smallValid; decide +kernel

private theorem sp11004 : smallValid 11004 50 := by unfold smallValid; decide +kernel

private theorem sp11054 : smallValid 11054 50 := by unfold smallValid; decide +kernel

private theorem sp11104 : smallValid 11104 50 := by unfold smallValid; decide +kernel

private theorem sp11154 : smallValid 11154 49 := by unfold smallValid; decide +kernel

private theorem sp11203 : smallValid 11203 50 := by unfold smallValid; decide +kernel

private theorem sp11253 : smallValid 11253 50 := by unfold smallValid; decide +kernel

private theorem sp11303 : smallValid 11303 50 := by unfold smallValid; decide +kernel

private theorem sp11353 : smallValid 11353 49 := by unfold smallValid; decide +kernel

private theorem sp11402 : smallValid 11402 50 := by unfold smallValid; decide +kernel

private theorem sp11452 : smallValid 11452 50 := by unfold smallValid; decide +kernel

private theorem sp11502 : smallValid 11502 50 := by unfold smallValid; decide +kernel

private theorem sp11552 : smallValid 11552 49 := by unfold smallValid; decide +kernel

private theorem sp11601 : smallValid 11601 50 := by unfold smallValid; decide +kernel

private theorem sp11651 : smallValid 11651 50 := by unfold smallValid; decide +kernel

private theorem sp11701 : smallValid 11701 50 := by unfold smallValid; decide +kernel

private theorem sp11751 : smallValid 11751 50 := by unfold smallValid; decide +kernel

private theorem sp11801 : smallValid 11801 50 := by unfold smallValid; decide +kernel

private theorem sp11851 : smallValid 11851 50 := by unfold smallValid; decide +kernel

private theorem sp11901 : smallValid 11901 50 := by unfold smallValid; decide +kernel

private theorem sp11951 : smallValid 11951 49 := by unfold smallValid; decide +kernel

private theorem sp12000 : smallValid 12000 50 := by unfold smallValid; decide +kernel

private theorem sp12050 : smallValid 12050 50 := by unfold smallValid; decide +kernel

private theorem sp12100 : smallValid 12100 50 := by unfold smallValid; decide +kernel

private theorem sp12150 : smallValid 12150 49 := by unfold smallValid; decide +kernel

private theorem sp12199 : smallValid 12199 50 := by unfold smallValid; decide +kernel

private theorem sp12249 : smallValid 12249 50 := by unfold smallValid; decide +kernel

private theorem sp12299 : smallValid 12299 50 := by unfold smallValid; decide +kernel

private theorem sp12349 : smallValid 12349 49 := by unfold smallValid; decide +kernel

private theorem sp12398 : smallValid 12398 50 := by unfold smallValid; decide +kernel

private theorem sp12448 : smallValid 12448 50 := by unfold smallValid; decide +kernel

private theorem sp12498 : smallValid 12498 50 := by unfold smallValid; decide +kernel

private theorem sp12548 : smallValid 12548 50 := by unfold smallValid; decide +kernel

private theorem sp12598 : smallValid 12598 50 := by unfold smallValid; decide +kernel

private theorem sp12648 : smallValid 12648 50 := by unfold smallValid; decide +kernel

private theorem sp12698 : smallValid 12698 50 := by unfold smallValid; decide +kernel

private theorem sp12748 : smallValid 12748 49 := by unfold smallValid; decide +kernel

private theorem sp12797 : smallValid 12797 50 := by unfold smallValid; decide +kernel

private theorem sp12847 : smallValid 12847 50 := by unfold smallValid; decide +kernel

private theorem sp12897 : smallValid 12897 50 := by unfold smallValid; decide +kernel

private theorem sp12947 : smallValid 12947 49 := by unfold smallValid; decide +kernel

private theorem sp12996 : smallValid 12996 50 := by unfold smallValid; decide +kernel

private theorem sp13046 : smallValid 13046 50 := by unfold smallValid; decide +kernel

private theorem sp13096 : smallValid 13096 50 := by unfold smallValid; decide +kernel

private theorem sp13146 : smallValid 13146 49 := by unfold smallValid; decide +kernel

private theorem sp13195 : smallValid 13195 50 := by unfold smallValid; decide +kernel

private theorem sp13245 : smallValid 13245 50 := by unfold smallValid; decide +kernel

private theorem sp13295 : smallValid 13295 50 := by unfold smallValid; decide +kernel

private theorem sp13345 : smallValid 13345 49 := by unfold smallValid; decide +kernel

private theorem sp13394 : smallValid 13394 50 := by unfold smallValid; decide +kernel

private theorem sp13444 : smallValid 13444 50 := by unfold smallValid; decide +kernel

private theorem sp13494 : smallValid 13494 50 := by unfold smallValid; decide +kernel

private theorem sp13544 : smallValid 13544 49 := by unfold smallValid; decide +kernel

private theorem sp13593 : smallValid 13593 50 := by unfold smallValid; decide +kernel

private theorem sp13643 : smallValid 13643 50 := by unfold smallValid; decide +kernel

private theorem sp13693 : smallValid 13693 50 := by unfold smallValid; decide +kernel

private theorem sp13743 : smallValid 13743 49 := by unfold smallValid; decide +kernel

private theorem sp13792 : smallValid 13792 50 := by unfold smallValid; decide +kernel

private theorem sp13842 : smallValid 13842 50 := by unfold smallValid; decide +kernel

private theorem sp13892 : smallValid 13892 50 := by unfold smallValid; decide +kernel

private theorem sp13942 : smallValid 13942 49 := by unfold smallValid; decide +kernel

private theorem sp13991 : smallValid 13991 50 := by unfold smallValid; decide +kernel

private theorem sp14041 : smallValid 14041 50 := by unfold smallValid; decide +kernel

private theorem sp14091 : smallValid 14091 50 := by unfold smallValid; decide +kernel

private theorem sp14141 : smallValid 14141 50 := by unfold smallValid; decide +kernel

private theorem sp14191 : smallValid 14191 50 := by unfold smallValid; decide +kernel

private theorem sp14241 : smallValid 14241 50 := by unfold smallValid; decide +kernel

private theorem sp14291 : smallValid 14291 50 := by unfold smallValid; decide +kernel

private theorem sp14341 : smallValid 14341 49 := by unfold smallValid; decide +kernel

private theorem sp14390 : smallValid 14390 50 := by unfold smallValid; decide +kernel

private theorem sp14440 : smallValid 14440 50 := by unfold smallValid; decide +kernel

private theorem sp14490 : smallValid 14490 50 := by unfold smallValid; decide +kernel

private theorem sp14540 : smallValid 14540 49 := by unfold smallValid; decide +kernel

private theorem sp14589 : smallValid 14589 50 := by unfold smallValid; decide +kernel

private theorem sp14639 : smallValid 14639 50 := by unfold smallValid; decide +kernel

private theorem sp14689 : smallValid 14689 50 := by unfold smallValid; decide +kernel

private theorem sp14739 : smallValid 14739 49 := by unfold smallValid; decide +kernel

private theorem sp14788 : smallValid 14788 50 := by unfold smallValid; decide +kernel

private theorem sp14838 : smallValid 14838 50 := by unfold smallValid; decide +kernel

private theorem sp14888 : smallValid 14888 50 := by unfold smallValid; decide +kernel

private theorem sp14938 : smallValid 14938 50 := by unfold smallValid; decide +kernel

private theorem sp14988 : smallValid 14988 50 := by unfold smallValid; decide +kernel

private theorem sp15038 : smallValid 15038 50 := by unfold smallValid; decide +kernel

private theorem sp15088 : smallValid 15088 50 := by unfold smallValid; decide +kernel

private theorem sp15138 : smallValid 15138 49 := by unfold smallValid; decide +kernel

private theorem sp15187 : smallValid 15187 50 := by unfold smallValid; decide +kernel

private theorem sp15237 : smallValid 15237 50 := by unfold smallValid; decide +kernel

private theorem sp15287 : smallValid 15287 50 := by unfold smallValid; decide +kernel

private theorem sp15337 : smallValid 15337 49 := by unfold smallValid; decide +kernel

private theorem sp15386 : smallValid 15386 50 := by unfold smallValid; decide +kernel

private theorem sp15436 : smallValid 15436 50 := by unfold smallValid; decide +kernel

private theorem sp15486 : smallValid 15486 50 := by unfold smallValid; decide +kernel

private theorem sp15536 : smallValid 15536 49 := by unfold smallValid; decide +kernel

private theorem sp15585 : smallValid 15585 50 := by unfold smallValid; decide +kernel

private theorem sp15635 : smallValid 15635 50 := by unfold smallValid; decide +kernel

private theorem sp15685 : smallValid 15685 50 := by unfold smallValid; decide +kernel

private theorem sp15735 : smallValid 15735 50 := by unfold smallValid; decide +kernel

private theorem sp15785 : smallValid 15785 50 := by unfold smallValid; decide +kernel

private theorem sp15835 : smallValid 15835 50 := by unfold smallValid; decide +kernel

private theorem sp15885 : smallValid 15885 50 := by unfold smallValid; decide +kernel

private theorem sp15935 : smallValid 15935 49 := by unfold smallValid; decide +kernel

private theorem sp15984 : smallValid 15984 50 := by unfold smallValid; decide +kernel

private theorem sp16034 : smallValid 16034 50 := by unfold smallValid; decide +kernel

private theorem sp16084 : smallValid 16084 50 := by unfold smallValid; decide +kernel

private theorem sp16134 : smallValid 16134 49 := by unfold smallValid; decide +kernel

private theorem sp16183 : smallValid 16183 50 := by unfold smallValid; decide +kernel

private theorem sp16233 : smallValid 16233 50 := by unfold smallValid; decide +kernel

private theorem sp16283 : smallValid 16283 50 := by unfold smallValid; decide +kernel

private theorem sp16333 : smallValid 16333 49 := by unfold smallValid; decide +kernel

private theorem sp16382 : smallValid 16382 50 := by unfold smallValid; decide +kernel

private theorem sp16432 : smallValid 16432 50 := by unfold smallValid; decide +kernel

private theorem sp16482 : smallValid 16482 50 := by unfold smallValid; decide +kernel

private theorem sp16532 : smallValid 16532 49 := by unfold smallValid; decide +kernel

private theorem sp16581 : smallValid 16581 50 := by unfold smallValid; decide +kernel

private theorem sp16631 : smallValid 16631 50 := by unfold smallValid; decide +kernel

private theorem sp16681 : smallValid 16681 50 := by unfold smallValid; decide +kernel

private theorem sp16731 : smallValid 16731 49 := by unfold smallValid; decide +kernel

private theorem sp16780 : smallValid 16780 50 := by unfold smallValid; decide +kernel

private theorem sp16830 : smallValid 16830 50 := by unfold smallValid; decide +kernel

private theorem sp16880 : smallValid 16880 50 := by unfold smallValid; decide +kernel

private theorem sp16930 : smallValid 16930 49 := by unfold smallValid; decide +kernel

private theorem sp16979 : smallValid 16979 50 := by unfold smallValid; decide +kernel

private theorem sp17029 : smallValid 17029 50 := by unfold smallValid; decide +kernel

private theorem sp17079 : smallValid 17079 50 := by unfold smallValid; decide +kernel

private theorem sp17129 : smallValid 17129 49 := by unfold smallValid; decide +kernel

private theorem sp17178 : smallValid 17178 50 := by unfold smallValid; decide +kernel

private theorem sp17228 : smallValid 17228 50 := by unfold smallValid; decide +kernel

private theorem sp17278 : smallValid 17278 50 := by unfold smallValid; decide +kernel

private theorem sp17328 : smallValid 17328 50 := by unfold smallValid; decide +kernel

private theorem sp17378 : smallValid 17378 50 := by unfold smallValid; decide +kernel

private theorem sp17428 : smallValid 17428 50 := by unfold smallValid; decide +kernel

private theorem sp17478 : smallValid 17478 50 := by unfold smallValid; decide +kernel

private theorem sp17528 : smallValid 17528 49 := by unfold smallValid; decide +kernel

private theorem sp17577 : smallValid 17577 50 := by unfold smallValid; decide +kernel

private theorem sp17627 : smallValid 17627 50 := by unfold smallValid; decide +kernel

private theorem sp17677 : smallValid 17677 50 := by unfold smallValid; decide +kernel

private theorem sp17727 : smallValid 17727 49 := by unfold smallValid; decide +kernel

private theorem sp17776 : smallValid 17776 50 := by unfold smallValid; decide +kernel

private theorem sp17826 : smallValid 17826 50 := by unfold smallValid; decide +kernel

private theorem sp17876 : smallValid 17876 50 := by unfold smallValid; decide +kernel

private theorem sp17926 : smallValid 17926 49 := by unfold smallValid; decide +kernel

private theorem sp17975 : smallValid 17975 50 := by unfold smallValid; decide +kernel

private theorem sp18025 : smallValid 18025 50 := by unfold smallValid; decide +kernel

private theorem sp18075 : smallValid 18075 50 := by unfold smallValid; decide +kernel

private theorem sp18125 : smallValid 18125 50 := by unfold smallValid; decide +kernel

private theorem sp18175 : smallValid 18175 50 := by unfold smallValid; decide +kernel

private theorem sp18225 : smallValid 18225 50 := by unfold smallValid; decide +kernel

private theorem sp18275 : smallValid 18275 50 := by unfold smallValid; decide +kernel

private theorem sp18325 : smallValid 18325 49 := by unfold smallValid; decide +kernel

private theorem sp18374 : smallValid 18374 50 := by unfold smallValid; decide +kernel

private theorem sp18424 : smallValid 18424 50 := by unfold smallValid; decide +kernel

private theorem sp18474 : smallValid 18474 50 := by unfold smallValid; decide +kernel

private theorem sp18524 : smallValid 18524 49 := by unfold smallValid; decide +kernel

private theorem sp18573 : smallValid 18573 50 := by unfold smallValid; decide +kernel

private theorem sp18623 : smallValid 18623 50 := by unfold smallValid; decide +kernel

private theorem sp18673 : smallValid 18673 50 := by unfold smallValid; decide +kernel

private theorem sp18723 : smallValid 18723 49 := by unfold smallValid; decide +kernel

private theorem sp18772 : smallValid 18772 50 := by unfold smallValid; decide +kernel

private theorem sp18822 : smallValid 18822 50 := by unfold smallValid; decide +kernel

private theorem sp18872 : smallValid 18872 50 := by unfold smallValid; decide +kernel

private theorem sp18922 : smallValid 18922 50 := by unfold smallValid; decide +kernel

private theorem sp18972 : smallValid 18972 50 := by unfold smallValid; decide +kernel

private theorem sp19022 : smallValid 19022 50 := by unfold smallValid; decide +kernel

private theorem sp19072 : smallValid 19072 50 := by unfold smallValid; decide +kernel

private theorem sp19122 : smallValid 19122 49 := by unfold smallValid; decide +kernel

private theorem sp19171 : smallValid 19171 50 := by unfold smallValid; decide +kernel

private theorem sp19221 : smallValid 19221 50 := by unfold smallValid; decide +kernel

private theorem sp19271 : smallValid 19271 50 := by unfold smallValid; decide +kernel

private theorem sp19321 : smallValid 19321 49 := by unfold smallValid; decide +kernel

private theorem sp19370 : smallValid 19370 50 := by unfold smallValid; decide +kernel

private theorem sp19420 : smallValid 19420 50 := by unfold smallValid; decide +kernel

private theorem sp19470 : smallValid 19470 50 := by unfold smallValid; decide +kernel

private theorem sp19520 : smallValid 19520 49 := by unfold smallValid; decide +kernel

private theorem sp19569 : smallValid 19569 50 := by unfold smallValid; decide +kernel

private theorem sp19619 : smallValid 19619 50 := by unfold smallValid; decide +kernel

private theorem sp19669 : smallValid 19669 50 := by unfold smallValid; decide +kernel

private theorem sp19719 : smallValid 19719 49 := by unfold smallValid; decide +kernel

private theorem sp19768 : smallValid 19768 50 := by unfold smallValid; decide +kernel

private theorem sp19818 : smallValid 19818 50 := by unfold smallValid; decide +kernel

private theorem sp19868 : smallValid 19868 50 := by unfold smallValid; decide +kernel

private theorem sp19918 : smallValid 19918 49 := by unfold smallValid; decide +kernel

private theorem sp19967 : smallValid 19967 50 := by unfold smallValid; decide +kernel

private theorem sp20017 : smallValid 20017 50 := by unfold smallValid; decide +kernel

private theorem sp20067 : smallValid 20067 50 := by unfold smallValid; decide +kernel

private theorem sp20117 : smallValid 20117 49 := by unfold smallValid; decide +kernel

private theorem sp20166 : smallValid 20166 50 := by unfold smallValid; decide +kernel

private theorem sp20216 : smallValid 20216 50 := by unfold smallValid; decide +kernel

private theorem sp20266 : smallValid 20266 50 := by unfold smallValid; decide +kernel

private theorem sp20316 : smallValid 20316 49 := by unfold smallValid; decide +kernel

private theorem sp20365 : smallValid 20365 50 := by unfold smallValid; decide +kernel

private theorem sp20415 : smallValid 20415 50 := by unfold smallValid; decide +kernel

private theorem sp20465 : smallValid 20465 50 := by unfold smallValid; decide +kernel

private theorem sp20515 : smallValid 20515 50 := by unfold smallValid; decide +kernel

private theorem sp20565 : smallValid 20565 50 := by unfold smallValid; decide +kernel

private theorem sp20615 : smallValid 20615 50 := by unfold smallValid; decide +kernel

private theorem sp20665 : smallValid 20665 50 := by unfold smallValid; decide +kernel

private theorem sp20715 : smallValid 20715 49 := by unfold smallValid; decide +kernel

private theorem sp20764 : smallValid 20764 50 := by unfold smallValid; decide +kernel

private theorem sp20814 : smallValid 20814 50 := by unfold smallValid; decide +kernel

private theorem sp20864 : smallValid 20864 50 := by unfold smallValid; decide +kernel

private theorem sp20914 : smallValid 20914 49 := by unfold smallValid; decide +kernel

private theorem sp20963 : smallValid 20963 50 := by unfold smallValid; decide +kernel

private theorem sp21013 : smallValid 21013 50 := by unfold smallValid; decide +kernel

private theorem sp21063 : smallValid 21063 50 := by unfold smallValid; decide +kernel

private theorem sp21113 : smallValid 21113 49 := by unfold smallValid; decide +kernel

private theorem sp21162 : smallValid 21162 50 := by unfold smallValid; decide +kernel

private theorem sp21212 : smallValid 21212 50 := by unfold smallValid; decide +kernel

private theorem sp21262 : smallValid 21262 50 := by unfold smallValid; decide +kernel

private theorem sp21312 : smallValid 21312 50 := by unfold smallValid; decide +kernel

private theorem sp21362 : smallValid 21362 50 := by unfold smallValid; decide +kernel

private theorem sp21412 : smallValid 21412 50 := by unfold smallValid; decide +kernel

private theorem sp21462 : smallValid 21462 50 := by unfold smallValid; decide +kernel

private theorem sp21512 : smallValid 21512 49 := by unfold smallValid; decide +kernel

private theorem sp21561 : smallValid 21561 50 := by unfold smallValid; decide +kernel

private theorem sp21611 : smallValid 21611 50 := by unfold smallValid; decide +kernel

private theorem sp21661 : smallValid 21661 50 := by unfold smallValid; decide +kernel

private theorem sp21711 : smallValid 21711 49 := by unfold smallValid; decide +kernel

private theorem sp21760 : smallValid 21760 50 := by unfold smallValid; decide +kernel

private theorem sp21810 : smallValid 21810 50 := by unfold smallValid; decide +kernel

private theorem sp21860 : smallValid 21860 50 := by unfold smallValid; decide +kernel

private theorem sp21910 : smallValid 21910 49 := by unfold smallValid; decide +kernel

private theorem sp21959 : smallValid 21959 50 := by unfold smallValid; decide +kernel

private theorem sp22009 : smallValid 22009 50 := by unfold smallValid; decide +kernel

private theorem sp22059 : smallValid 22059 50 := by unfold smallValid; decide +kernel

private theorem sp22109 : smallValid 22109 50 := by unfold smallValid; decide +kernel

private theorem sp22159 : smallValid 22159 50 := by unfold smallValid; decide +kernel

private theorem sp22209 : smallValid 22209 50 := by unfold smallValid; decide +kernel

private theorem sp22259 : smallValid 22259 50 := by unfold smallValid; decide +kernel

private theorem sp22309 : smallValid 22309 49 := by unfold smallValid; decide +kernel

private theorem sp22358 : smallValid 22358 50 := by unfold smallValid; decide +kernel

private theorem sp22408 : smallValid 22408 50 := by unfold smallValid; decide +kernel

private theorem sp22458 : smallValid 22458 50 := by unfold smallValid; decide +kernel

private theorem sp22508 : smallValid 22508 49 := by unfold smallValid; decide +kernel

private theorem sp22557 : smallValid 22557 50 := by unfold smallValid; decide +kernel

private theorem sp22607 : smallValid 22607 50 := by unfold smallValid; decide +kernel

private theorem sp22657 : smallValid 22657 50 := by unfold smallValid; decide +kernel

private theorem sp22707 : smallValid 22707 49 := by unfold smallValid; decide +kernel

private theorem sp22756 : smallValid 22756 50 := by unfold smallValid; decide +kernel

private theorem sp22806 : smallValid 22806 50 := by unfold smallValid; decide +kernel

private theorem sp22856 : smallValid 22856 50 := by unfold smallValid; decide +kernel

private theorem sp22906 : smallValid 22906 49 := by unfold smallValid; decide +kernel

private theorem sp22955 : smallValid 22955 50 := by unfold smallValid; decide +kernel

private theorem sp23005 : smallValid 23005 50 := by unfold smallValid; decide +kernel

private theorem sp23055 : smallValid 23055 50 := by unfold smallValid; decide +kernel

private theorem sp23105 : smallValid 23105 49 := by unfold smallValid; decide +kernel

private theorem sp23154 : smallValid 23154 50 := by unfold smallValid; decide +kernel

private theorem sp23204 : smallValid 23204 50 := by unfold smallValid; decide +kernel

private theorem sp23254 : smallValid 23254 50 := by unfold smallValid; decide +kernel

private theorem sp23304 : smallValid 23304 49 := by unfold smallValid; decide +kernel

private theorem sp23353 : smallValid 23353 50 := by unfold smallValid; decide +kernel

private theorem sp23403 : smallValid 23403 50 := by unfold smallValid; decide +kernel

private theorem sp23453 : smallValid 23453 50 := by unfold smallValid; decide +kernel

private theorem sp23503 : smallValid 23503 49 := by unfold smallValid; decide +kernel

private theorem sp23552 : smallValid 23552 50 := by unfold smallValid; decide +kernel

private theorem sp23602 : smallValid 23602 50 := by unfold smallValid; decide +kernel

private theorem sp23652 : smallValid 23652 50 := by unfold smallValid; decide +kernel

private theorem sp23702 : smallValid 23702 50 := by unfold smallValid; decide +kernel

private theorem sp23752 : smallValid 23752 50 := by unfold smallValid; decide +kernel

private theorem sp23802 : smallValid 23802 50 := by unfold smallValid; decide +kernel

private theorem sp23852 : smallValid 23852 50 := by unfold smallValid; decide +kernel

private theorem sp23902 : smallValid 23902 49 := by unfold smallValid; decide +kernel

private theorem sp23951 : smallValid 23951 50 := by unfold smallValid; decide +kernel

private theorem sp24001 : smallValid 24001 50 := by unfold smallValid; decide +kernel

private theorem sp24051 : smallValid 24051 50 := by unfold smallValid; decide +kernel

private theorem sp24101 : smallValid 24101 49 := by unfold smallValid; decide +kernel

private theorem sp24150 : smallValid 24150 50 := by unfold smallValid; decide +kernel

private theorem sp24200 : smallValid 24200 50 := by unfold smallValid; decide +kernel

private theorem sp24250 : smallValid 24250 50 := by unfold smallValid; decide +kernel

private theorem sp24300 : smallValid 24300 49 := by unfold smallValid; decide +kernel

private theorem sp24349 : smallValid 24349 50 := by unfold smallValid; decide +kernel

private theorem sp24399 : smallValid 24399 50 := by unfold smallValid; decide +kernel

private theorem sp24449 : smallValid 24449 50 := by unfold smallValid; decide +kernel

private theorem sp24499 : smallValid 24499 50 := by unfold smallValid; decide +kernel

private theorem sp24549 : smallValid 24549 50 := by unfold smallValid; decide +kernel

private theorem sp24599 : smallValid 24599 50 := by unfold smallValid; decide +kernel

private theorem sp24649 : smallValid 24649 50 := by unfold smallValid; decide +kernel

private theorem sp24699 : smallValid 24699 49 := by unfold smallValid; decide +kernel

private theorem sp24748 : smallValid 24748 50 := by unfold smallValid; decide +kernel

private theorem sp24798 : smallValid 24798 50 := by unfold smallValid; decide +kernel

private theorem sp24848 : smallValid 24848 50 := by unfold smallValid; decide +kernel

private theorem sp24898 : smallValid 24898 49 := by unfold smallValid; decide +kernel

private theorem sp24947 : smallValid 24947 50 := by unfold smallValid; decide +kernel

private theorem sp24997 : smallValid 24997 50 := by unfold smallValid; decide +kernel

private theorem sp25047 : smallValid 25047 50 := by unfold smallValid; decide +kernel

private theorem sp25097 : smallValid 25097 49 := by unfold smallValid; decide +kernel

private theorem sp25146 : smallValid 25146 50 := by unfold smallValid; decide +kernel

private theorem sp25196 : smallValid 25196 50 := by unfold smallValid; decide +kernel

private theorem sp25246 : smallValid 25246 50 := by unfold smallValid; decide +kernel

private theorem sp25296 : smallValid 25296 50 := by unfold smallValid; decide +kernel

private theorem sp25346 : smallValid 25346 50 := by unfold smallValid; decide +kernel

private theorem sp25396 : smallValid 25396 50 := by unfold smallValid; decide +kernel

private theorem sp25446 : smallValid 25446 50 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤25495) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 25496 := (joinSmall (lo:=0) (a:=12748) (b:=12748) (joinSmall (lo:=0) (a:=6374) (b:=6374) (joinSmall (lo:=0) (a:=3187) (b:=3187) (joinSmall (lo:=0) (a:=1593) (b:=1594) (joinSmall (lo:=0) (a:=796) (b:=797) (joinSmall (lo:=0) (a:=398) (b:=398) (joinSmall (lo:=0) (a:=199) (b:=199) (joinSmall (lo:=0) (a:=99) (b:=100) (joinSmall (lo:=0) (a:=49) (b:=50) sp0 sp49) (joinSmall (lo:=99) (a:=50) (b:=50) sp99 sp149)) (joinSmall (lo:=199) (a:=99) (b:=100) (joinSmall (lo:=199) (a:=49) (b:=50) sp199 sp248) (joinSmall (lo:=298) (a:=50) (b:=50) sp298 sp348))) (joinSmall (lo:=398) (a:=199) (b:=199) (joinSmall (lo:=398) (a:=99) (b:=100) (joinSmall (lo:=398) (a:=49) (b:=50) sp398 sp447) (joinSmall (lo:=497) (a:=50) (b:=50) sp497 sp547)) (joinSmall (lo:=597) (a:=99) (b:=100) (joinSmall (lo:=597) (a:=49) (b:=50) sp597 sp646) (joinSmall (lo:=696) (a:=50) (b:=50) sp696 sp746)))) (joinSmall (lo:=796) (a:=398) (b:=399) (joinSmall (lo:=796) (a:=199) (b:=199) (joinSmall (lo:=796) (a:=99) (b:=100) (joinSmall (lo:=796) (a:=49) (b:=50) sp796 sp845) (joinSmall (lo:=895) (a:=50) (b:=50) sp895 sp945)) (joinSmall (lo:=995) (a:=99) (b:=100) (joinSmall (lo:=995) (a:=49) (b:=50) sp995 sp1044) (joinSmall (lo:=1094) (a:=50) (b:=50) sp1094 sp1144))) (joinSmall (lo:=1194) (a:=199) (b:=200) (joinSmall (lo:=1194) (a:=99) (b:=100) (joinSmall (lo:=1194) (a:=49) (b:=50) sp1194 sp1243) (joinSmall (lo:=1293) (a:=50) (b:=50) sp1293 sp1343)) (joinSmall (lo:=1393) (a:=100) (b:=100) (joinSmall (lo:=1393) (a:=50) (b:=50) sp1393 sp1443) (joinSmall (lo:=1493) (a:=50) (b:=50) sp1493 sp1543))))) (joinSmall (lo:=1593) (a:=797) (b:=797) (joinSmall (lo:=1593) (a:=398) (b:=399) (joinSmall (lo:=1593) (a:=199) (b:=199) (joinSmall (lo:=1593) (a:=99) (b:=100) (joinSmall (lo:=1593) (a:=49) (b:=50) sp1593 sp1642) (joinSmall (lo:=1692) (a:=50) (b:=50) sp1692 sp1742)) (joinSmall (lo:=1792) (a:=99) (b:=100) (joinSmall (lo:=1792) (a:=49) (b:=50) sp1792 sp1841) (joinSmall (lo:=1891) (a:=50) (b:=50) sp1891 sp1941))) (joinSmall (lo:=1991) (a:=199) (b:=200) (joinSmall (lo:=1991) (a:=99) (b:=100) (joinSmall (lo:=1991) (a:=49) (b:=50) sp1991 sp2040) (joinSmall (lo:=2090) (a:=50) (b:=50) sp2090 sp2140)) (joinSmall (lo:=2190) (a:=100) (b:=100) (joinSmall (lo:=2190) (a:=50) (b:=50) sp2190 sp2240) (joinSmall (lo:=2290) (a:=50) (b:=50) sp2290 sp2340)))) (joinSmall (lo:=2390) (a:=398) (b:=399) (joinSmall (lo:=2390) (a:=199) (b:=199) (joinSmall (lo:=2390) (a:=99) (b:=100) (joinSmall (lo:=2390) (a:=49) (b:=50) sp2390 sp2439) (joinSmall (lo:=2489) (a:=50) (b:=50) sp2489 sp2539)) (joinSmall (lo:=2589) (a:=99) (b:=100) (joinSmall (lo:=2589) (a:=49) (b:=50) sp2589 sp2638) (joinSmall (lo:=2688) (a:=50) (b:=50) sp2688 sp2738))) (joinSmall (lo:=2788) (a:=199) (b:=200) (joinSmall (lo:=2788) (a:=99) (b:=100) (joinSmall (lo:=2788) (a:=49) (b:=50) sp2788 sp2837) (joinSmall (lo:=2887) (a:=50) (b:=50) sp2887 sp2937)) (joinSmall (lo:=2987) (a:=100) (b:=100) (joinSmall (lo:=2987) (a:=50) (b:=50) sp2987 sp3037) (joinSmall (lo:=3087) (a:=50) (b:=50) sp3087 sp3137)))))) (joinSmall (lo:=3187) (a:=1593) (b:=1594) (joinSmall (lo:=3187) (a:=796) (b:=797) (joinSmall (lo:=3187) (a:=398) (b:=398) (joinSmall (lo:=3187) (a:=199) (b:=199) (joinSmall (lo:=3187) (a:=99) (b:=100) (joinSmall (lo:=3187) (a:=49) (b:=50) sp3187 sp3236) (joinSmall (lo:=3286) (a:=50) (b:=50) sp3286 sp3336)) (joinSmall (lo:=3386) (a:=99) (b:=100) (joinSmall (lo:=3386) (a:=49) (b:=50) sp3386 sp3435) (joinSmall (lo:=3485) (a:=50) (b:=50) sp3485 sp3535))) (joinSmall (lo:=3585) (a:=199) (b:=199) (joinSmall (lo:=3585) (a:=99) (b:=100) (joinSmall (lo:=3585) (a:=49) (b:=50) sp3585 sp3634) (joinSmall (lo:=3684) (a:=50) (b:=50) sp3684 sp3734)) (joinSmall (lo:=3784) (a:=99) (b:=100) (joinSmall (lo:=3784) (a:=49) (b:=50) sp3784 sp3833) (joinSmall (lo:=3883) (a:=50) (b:=50) sp3883 sp3933)))) (joinSmall (lo:=3983) (a:=398) (b:=399) (joinSmall (lo:=3983) (a:=199) (b:=199) (joinSmall (lo:=3983) (a:=99) (b:=100) (joinSmall (lo:=3983) (a:=49) (b:=50) sp3983 sp4032) (joinSmall (lo:=4082) (a:=50) (b:=50) sp4082 sp4132)) (joinSmall (lo:=4182) (a:=99) (b:=100) (joinSmall (lo:=4182) (a:=49) (b:=50) sp4182 sp4231) (joinSmall (lo:=4281) (a:=50) (b:=50) sp4281 sp4331))) (joinSmall (lo:=4381) (a:=199) (b:=200) (joinSmall (lo:=4381) (a:=99) (b:=100) (joinSmall (lo:=4381) (a:=49) (b:=50) sp4381 sp4430) (joinSmall (lo:=4480) (a:=50) (b:=50) sp4480 sp4530)) (joinSmall (lo:=4580) (a:=100) (b:=100) (joinSmall (lo:=4580) (a:=50) (b:=50) sp4580 sp4630) (joinSmall (lo:=4680) (a:=50) (b:=50) sp4680 sp4730))))) (joinSmall (lo:=4780) (a:=797) (b:=797) (joinSmall (lo:=4780) (a:=398) (b:=399) (joinSmall (lo:=4780) (a:=199) (b:=199) (joinSmall (lo:=4780) (a:=99) (b:=100) (joinSmall (lo:=4780) (a:=49) (b:=50) sp4780 sp4829) (joinSmall (lo:=4879) (a:=50) (b:=50) sp4879 sp4929)) (joinSmall (lo:=4979) (a:=99) (b:=100) (joinSmall (lo:=4979) (a:=49) (b:=50) sp4979 sp5028) (joinSmall (lo:=5078) (a:=50) (b:=50) sp5078 sp5128))) (joinSmall (lo:=5178) (a:=199) (b:=200) (joinSmall (lo:=5178) (a:=99) (b:=100) (joinSmall (lo:=5178) (a:=49) (b:=50) sp5178 sp5227) (joinSmall (lo:=5277) (a:=50) (b:=50) sp5277 sp5327)) (joinSmall (lo:=5377) (a:=100) (b:=100) (joinSmall (lo:=5377) (a:=50) (b:=50) sp5377 sp5427) (joinSmall (lo:=5477) (a:=50) (b:=50) sp5477 sp5527)))) (joinSmall (lo:=5577) (a:=398) (b:=399) (joinSmall (lo:=5577) (a:=199) (b:=199) (joinSmall (lo:=5577) (a:=99) (b:=100) (joinSmall (lo:=5577) (a:=49) (b:=50) sp5577 sp5626) (joinSmall (lo:=5676) (a:=50) (b:=50) sp5676 sp5726)) (joinSmall (lo:=5776) (a:=99) (b:=100) (joinSmall (lo:=5776) (a:=49) (b:=50) sp5776 sp5825) (joinSmall (lo:=5875) (a:=50) (b:=50) sp5875 sp5925))) (joinSmall (lo:=5975) (a:=199) (b:=200) (joinSmall (lo:=5975) (a:=99) (b:=100) (joinSmall (lo:=5975) (a:=49) (b:=50) sp5975 sp6024) (joinSmall (lo:=6074) (a:=50) (b:=50) sp6074 sp6124)) (joinSmall (lo:=6174) (a:=100) (b:=100) (joinSmall (lo:=6174) (a:=50) (b:=50) sp6174 sp6224) (joinSmall (lo:=6274) (a:=50) (b:=50) sp6274 sp6324))))))) (joinSmall (lo:=6374) (a:=3187) (b:=3187) (joinSmall (lo:=6374) (a:=1593) (b:=1594) (joinSmall (lo:=6374) (a:=796) (b:=797) (joinSmall (lo:=6374) (a:=398) (b:=398) (joinSmall (lo:=6374) (a:=199) (b:=199) (joinSmall (lo:=6374) (a:=99) (b:=100) (joinSmall (lo:=6374) (a:=49) (b:=50) sp6374 sp6423) (joinSmall (lo:=6473) (a:=50) (b:=50) sp6473 sp6523)) (joinSmall (lo:=6573) (a:=99) (b:=100) (joinSmall (lo:=6573) (a:=49) (b:=50) sp6573 sp6622) (joinSmall (lo:=6672) (a:=50) (b:=50) sp6672 sp6722))) (joinSmall (lo:=6772) (a:=199) (b:=199) (joinSmall (lo:=6772) (a:=99) (b:=100) (joinSmall (lo:=6772) (a:=49) (b:=50) sp6772 sp6821) (joinSmall (lo:=6871) (a:=50) (b:=50) sp6871 sp6921)) (joinSmall (lo:=6971) (a:=99) (b:=100) (joinSmall (lo:=6971) (a:=49) (b:=50) sp6971 sp7020) (joinSmall (lo:=7070) (a:=50) (b:=50) sp7070 sp7120)))) (joinSmall (lo:=7170) (a:=398) (b:=399) (joinSmall (lo:=7170) (a:=199) (b:=199) (joinSmall (lo:=7170) (a:=99) (b:=100) (joinSmall (lo:=7170) (a:=49) (b:=50) sp7170 sp7219) (joinSmall (lo:=7269) (a:=50) (b:=50) sp7269 sp7319)) (joinSmall (lo:=7369) (a:=99) (b:=100) (joinSmall (lo:=7369) (a:=49) (b:=50) sp7369 sp7418) (joinSmall (lo:=7468) (a:=50) (b:=50) sp7468 sp7518))) (joinSmall (lo:=7568) (a:=199) (b:=200) (joinSmall (lo:=7568) (a:=99) (b:=100) (joinSmall (lo:=7568) (a:=49) (b:=50) sp7568 sp7617) (joinSmall (lo:=7667) (a:=50) (b:=50) sp7667 sp7717)) (joinSmall (lo:=7767) (a:=100) (b:=100) (joinSmall (lo:=7767) (a:=50) (b:=50) sp7767 sp7817) (joinSmall (lo:=7867) (a:=50) (b:=50) sp7867 sp7917))))) (joinSmall (lo:=7967) (a:=797) (b:=797) (joinSmall (lo:=7967) (a:=398) (b:=399) (joinSmall (lo:=7967) (a:=199) (b:=199) (joinSmall (lo:=7967) (a:=99) (b:=100) (joinSmall (lo:=7967) (a:=49) (b:=50) sp7967 sp8016) (joinSmall (lo:=8066) (a:=50) (b:=50) sp8066 sp8116)) (joinSmall (lo:=8166) (a:=99) (b:=100) (joinSmall (lo:=8166) (a:=49) (b:=50) sp8166 sp8215) (joinSmall (lo:=8265) (a:=50) (b:=50) sp8265 sp8315))) (joinSmall (lo:=8365) (a:=199) (b:=200) (joinSmall (lo:=8365) (a:=99) (b:=100) (joinSmall (lo:=8365) (a:=49) (b:=50) sp8365 sp8414) (joinSmall (lo:=8464) (a:=50) (b:=50) sp8464 sp8514)) (joinSmall (lo:=8564) (a:=100) (b:=100) (joinSmall (lo:=8564) (a:=50) (b:=50) sp8564 sp8614) (joinSmall (lo:=8664) (a:=50) (b:=50) sp8664 sp8714)))) (joinSmall (lo:=8764) (a:=398) (b:=399) (joinSmall (lo:=8764) (a:=199) (b:=199) (joinSmall (lo:=8764) (a:=99) (b:=100) (joinSmall (lo:=8764) (a:=49) (b:=50) sp8764 sp8813) (joinSmall (lo:=8863) (a:=50) (b:=50) sp8863 sp8913)) (joinSmall (lo:=8963) (a:=99) (b:=100) (joinSmall (lo:=8963) (a:=49) (b:=50) sp8963 sp9012) (joinSmall (lo:=9062) (a:=50) (b:=50) sp9062 sp9112))) (joinSmall (lo:=9162) (a:=199) (b:=200) (joinSmall (lo:=9162) (a:=99) (b:=100) (joinSmall (lo:=9162) (a:=49) (b:=50) sp9162 sp9211) (joinSmall (lo:=9261) (a:=50) (b:=50) sp9261 sp9311)) (joinSmall (lo:=9361) (a:=100) (b:=100) (joinSmall (lo:=9361) (a:=50) (b:=50) sp9361 sp9411) (joinSmall (lo:=9461) (a:=50) (b:=50) sp9461 sp9511)))))) (joinSmall (lo:=9561) (a:=1593) (b:=1594) (joinSmall (lo:=9561) (a:=796) (b:=797) (joinSmall (lo:=9561) (a:=398) (b:=398) (joinSmall (lo:=9561) (a:=199) (b:=199) (joinSmall (lo:=9561) (a:=99) (b:=100) (joinSmall (lo:=9561) (a:=49) (b:=50) sp9561 sp9610) (joinSmall (lo:=9660) (a:=50) (b:=50) sp9660 sp9710)) (joinSmall (lo:=9760) (a:=99) (b:=100) (joinSmall (lo:=9760) (a:=49) (b:=50) sp9760 sp9809) (joinSmall (lo:=9859) (a:=50) (b:=50) sp9859 sp9909))) (joinSmall (lo:=9959) (a:=199) (b:=199) (joinSmall (lo:=9959) (a:=99) (b:=100) (joinSmall (lo:=9959) (a:=49) (b:=50) sp9959 sp10008) (joinSmall (lo:=10058) (a:=50) (b:=50) sp10058 sp10108)) (joinSmall (lo:=10158) (a:=99) (b:=100) (joinSmall (lo:=10158) (a:=49) (b:=50) sp10158 sp10207) (joinSmall (lo:=10257) (a:=50) (b:=50) sp10257 sp10307)))) (joinSmall (lo:=10357) (a:=398) (b:=399) (joinSmall (lo:=10357) (a:=199) (b:=199) (joinSmall (lo:=10357) (a:=99) (b:=100) (joinSmall (lo:=10357) (a:=49) (b:=50) sp10357 sp10406) (joinSmall (lo:=10456) (a:=50) (b:=50) sp10456 sp10506)) (joinSmall (lo:=10556) (a:=99) (b:=100) (joinSmall (lo:=10556) (a:=49) (b:=50) sp10556 sp10605) (joinSmall (lo:=10655) (a:=50) (b:=50) sp10655 sp10705))) (joinSmall (lo:=10755) (a:=199) (b:=200) (joinSmall (lo:=10755) (a:=99) (b:=100) (joinSmall (lo:=10755) (a:=49) (b:=50) sp10755 sp10804) (joinSmall (lo:=10854) (a:=50) (b:=50) sp10854 sp10904)) (joinSmall (lo:=10954) (a:=100) (b:=100) (joinSmall (lo:=10954) (a:=50) (b:=50) sp10954 sp11004) (joinSmall (lo:=11054) (a:=50) (b:=50) sp11054 sp11104))))) (joinSmall (lo:=11154) (a:=797) (b:=797) (joinSmall (lo:=11154) (a:=398) (b:=399) (joinSmall (lo:=11154) (a:=199) (b:=199) (joinSmall (lo:=11154) (a:=99) (b:=100) (joinSmall (lo:=11154) (a:=49) (b:=50) sp11154 sp11203) (joinSmall (lo:=11253) (a:=50) (b:=50) sp11253 sp11303)) (joinSmall (lo:=11353) (a:=99) (b:=100) (joinSmall (lo:=11353) (a:=49) (b:=50) sp11353 sp11402) (joinSmall (lo:=11452) (a:=50) (b:=50) sp11452 sp11502))) (joinSmall (lo:=11552) (a:=199) (b:=200) (joinSmall (lo:=11552) (a:=99) (b:=100) (joinSmall (lo:=11552) (a:=49) (b:=50) sp11552 sp11601) (joinSmall (lo:=11651) (a:=50) (b:=50) sp11651 sp11701)) (joinSmall (lo:=11751) (a:=100) (b:=100) (joinSmall (lo:=11751) (a:=50) (b:=50) sp11751 sp11801) (joinSmall (lo:=11851) (a:=50) (b:=50) sp11851 sp11901)))) (joinSmall (lo:=11951) (a:=398) (b:=399) (joinSmall (lo:=11951) (a:=199) (b:=199) (joinSmall (lo:=11951) (a:=99) (b:=100) (joinSmall (lo:=11951) (a:=49) (b:=50) sp11951 sp12000) (joinSmall (lo:=12050) (a:=50) (b:=50) sp12050 sp12100)) (joinSmall (lo:=12150) (a:=99) (b:=100) (joinSmall (lo:=12150) (a:=49) (b:=50) sp12150 sp12199) (joinSmall (lo:=12249) (a:=50) (b:=50) sp12249 sp12299))) (joinSmall (lo:=12349) (a:=199) (b:=200) (joinSmall (lo:=12349) (a:=99) (b:=100) (joinSmall (lo:=12349) (a:=49) (b:=50) sp12349 sp12398) (joinSmall (lo:=12448) (a:=50) (b:=50) sp12448 sp12498)) (joinSmall (lo:=12548) (a:=100) (b:=100) (joinSmall (lo:=12548) (a:=50) (b:=50) sp12548 sp12598) (joinSmall (lo:=12648) (a:=50) (b:=50) sp12648 sp12698)))))))) (joinSmall (lo:=12748) (a:=6374) (b:=6374) (joinSmall (lo:=12748) (a:=3187) (b:=3187) (joinSmall (lo:=12748) (a:=1593) (b:=1594) (joinSmall (lo:=12748) (a:=796) (b:=797) (joinSmall (lo:=12748) (a:=398) (b:=398) (joinSmall (lo:=12748) (a:=199) (b:=199) (joinSmall (lo:=12748) (a:=99) (b:=100) (joinSmall (lo:=12748) (a:=49) (b:=50) sp12748 sp12797) (joinSmall (lo:=12847) (a:=50) (b:=50) sp12847 sp12897)) (joinSmall (lo:=12947) (a:=99) (b:=100) (joinSmall (lo:=12947) (a:=49) (b:=50) sp12947 sp12996) (joinSmall (lo:=13046) (a:=50) (b:=50) sp13046 sp13096))) (joinSmall (lo:=13146) (a:=199) (b:=199) (joinSmall (lo:=13146) (a:=99) (b:=100) (joinSmall (lo:=13146) (a:=49) (b:=50) sp13146 sp13195) (joinSmall (lo:=13245) (a:=50) (b:=50) sp13245 sp13295)) (joinSmall (lo:=13345) (a:=99) (b:=100) (joinSmall (lo:=13345) (a:=49) (b:=50) sp13345 sp13394) (joinSmall (lo:=13444) (a:=50) (b:=50) sp13444 sp13494)))) (joinSmall (lo:=13544) (a:=398) (b:=399) (joinSmall (lo:=13544) (a:=199) (b:=199) (joinSmall (lo:=13544) (a:=99) (b:=100) (joinSmall (lo:=13544) (a:=49) (b:=50) sp13544 sp13593) (joinSmall (lo:=13643) (a:=50) (b:=50) sp13643 sp13693)) (joinSmall (lo:=13743) (a:=99) (b:=100) (joinSmall (lo:=13743) (a:=49) (b:=50) sp13743 sp13792) (joinSmall (lo:=13842) (a:=50) (b:=50) sp13842 sp13892))) (joinSmall (lo:=13942) (a:=199) (b:=200) (joinSmall (lo:=13942) (a:=99) (b:=100) (joinSmall (lo:=13942) (a:=49) (b:=50) sp13942 sp13991) (joinSmall (lo:=14041) (a:=50) (b:=50) sp14041 sp14091)) (joinSmall (lo:=14141) (a:=100) (b:=100) (joinSmall (lo:=14141) (a:=50) (b:=50) sp14141 sp14191) (joinSmall (lo:=14241) (a:=50) (b:=50) sp14241 sp14291))))) (joinSmall (lo:=14341) (a:=797) (b:=797) (joinSmall (lo:=14341) (a:=398) (b:=399) (joinSmall (lo:=14341) (a:=199) (b:=199) (joinSmall (lo:=14341) (a:=99) (b:=100) (joinSmall (lo:=14341) (a:=49) (b:=50) sp14341 sp14390) (joinSmall (lo:=14440) (a:=50) (b:=50) sp14440 sp14490)) (joinSmall (lo:=14540) (a:=99) (b:=100) (joinSmall (lo:=14540) (a:=49) (b:=50) sp14540 sp14589) (joinSmall (lo:=14639) (a:=50) (b:=50) sp14639 sp14689))) (joinSmall (lo:=14739) (a:=199) (b:=200) (joinSmall (lo:=14739) (a:=99) (b:=100) (joinSmall (lo:=14739) (a:=49) (b:=50) sp14739 sp14788) (joinSmall (lo:=14838) (a:=50) (b:=50) sp14838 sp14888)) (joinSmall (lo:=14938) (a:=100) (b:=100) (joinSmall (lo:=14938) (a:=50) (b:=50) sp14938 sp14988) (joinSmall (lo:=15038) (a:=50) (b:=50) sp15038 sp15088)))) (joinSmall (lo:=15138) (a:=398) (b:=399) (joinSmall (lo:=15138) (a:=199) (b:=199) (joinSmall (lo:=15138) (a:=99) (b:=100) (joinSmall (lo:=15138) (a:=49) (b:=50) sp15138 sp15187) (joinSmall (lo:=15237) (a:=50) (b:=50) sp15237 sp15287)) (joinSmall (lo:=15337) (a:=99) (b:=100) (joinSmall (lo:=15337) (a:=49) (b:=50) sp15337 sp15386) (joinSmall (lo:=15436) (a:=50) (b:=50) sp15436 sp15486))) (joinSmall (lo:=15536) (a:=199) (b:=200) (joinSmall (lo:=15536) (a:=99) (b:=100) (joinSmall (lo:=15536) (a:=49) (b:=50) sp15536 sp15585) (joinSmall (lo:=15635) (a:=50) (b:=50) sp15635 sp15685)) (joinSmall (lo:=15735) (a:=100) (b:=100) (joinSmall (lo:=15735) (a:=50) (b:=50) sp15735 sp15785) (joinSmall (lo:=15835) (a:=50) (b:=50) sp15835 sp15885)))))) (joinSmall (lo:=15935) (a:=1593) (b:=1594) (joinSmall (lo:=15935) (a:=796) (b:=797) (joinSmall (lo:=15935) (a:=398) (b:=398) (joinSmall (lo:=15935) (a:=199) (b:=199) (joinSmall (lo:=15935) (a:=99) (b:=100) (joinSmall (lo:=15935) (a:=49) (b:=50) sp15935 sp15984) (joinSmall (lo:=16034) (a:=50) (b:=50) sp16034 sp16084)) (joinSmall (lo:=16134) (a:=99) (b:=100) (joinSmall (lo:=16134) (a:=49) (b:=50) sp16134 sp16183) (joinSmall (lo:=16233) (a:=50) (b:=50) sp16233 sp16283))) (joinSmall (lo:=16333) (a:=199) (b:=199) (joinSmall (lo:=16333) (a:=99) (b:=100) (joinSmall (lo:=16333) (a:=49) (b:=50) sp16333 sp16382) (joinSmall (lo:=16432) (a:=50) (b:=50) sp16432 sp16482)) (joinSmall (lo:=16532) (a:=99) (b:=100) (joinSmall (lo:=16532) (a:=49) (b:=50) sp16532 sp16581) (joinSmall (lo:=16631) (a:=50) (b:=50) sp16631 sp16681)))) (joinSmall (lo:=16731) (a:=398) (b:=399) (joinSmall (lo:=16731) (a:=199) (b:=199) (joinSmall (lo:=16731) (a:=99) (b:=100) (joinSmall (lo:=16731) (a:=49) (b:=50) sp16731 sp16780) (joinSmall (lo:=16830) (a:=50) (b:=50) sp16830 sp16880)) (joinSmall (lo:=16930) (a:=99) (b:=100) (joinSmall (lo:=16930) (a:=49) (b:=50) sp16930 sp16979) (joinSmall (lo:=17029) (a:=50) (b:=50) sp17029 sp17079))) (joinSmall (lo:=17129) (a:=199) (b:=200) (joinSmall (lo:=17129) (a:=99) (b:=100) (joinSmall (lo:=17129) (a:=49) (b:=50) sp17129 sp17178) (joinSmall (lo:=17228) (a:=50) (b:=50) sp17228 sp17278)) (joinSmall (lo:=17328) (a:=100) (b:=100) (joinSmall (lo:=17328) (a:=50) (b:=50) sp17328 sp17378) (joinSmall (lo:=17428) (a:=50) (b:=50) sp17428 sp17478))))) (joinSmall (lo:=17528) (a:=797) (b:=797) (joinSmall (lo:=17528) (a:=398) (b:=399) (joinSmall (lo:=17528) (a:=199) (b:=199) (joinSmall (lo:=17528) (a:=99) (b:=100) (joinSmall (lo:=17528) (a:=49) (b:=50) sp17528 sp17577) (joinSmall (lo:=17627) (a:=50) (b:=50) sp17627 sp17677)) (joinSmall (lo:=17727) (a:=99) (b:=100) (joinSmall (lo:=17727) (a:=49) (b:=50) sp17727 sp17776) (joinSmall (lo:=17826) (a:=50) (b:=50) sp17826 sp17876))) (joinSmall (lo:=17926) (a:=199) (b:=200) (joinSmall (lo:=17926) (a:=99) (b:=100) (joinSmall (lo:=17926) (a:=49) (b:=50) sp17926 sp17975) (joinSmall (lo:=18025) (a:=50) (b:=50) sp18025 sp18075)) (joinSmall (lo:=18125) (a:=100) (b:=100) (joinSmall (lo:=18125) (a:=50) (b:=50) sp18125 sp18175) (joinSmall (lo:=18225) (a:=50) (b:=50) sp18225 sp18275)))) (joinSmall (lo:=18325) (a:=398) (b:=399) (joinSmall (lo:=18325) (a:=199) (b:=199) (joinSmall (lo:=18325) (a:=99) (b:=100) (joinSmall (lo:=18325) (a:=49) (b:=50) sp18325 sp18374) (joinSmall (lo:=18424) (a:=50) (b:=50) sp18424 sp18474)) (joinSmall (lo:=18524) (a:=99) (b:=100) (joinSmall (lo:=18524) (a:=49) (b:=50) sp18524 sp18573) (joinSmall (lo:=18623) (a:=50) (b:=50) sp18623 sp18673))) (joinSmall (lo:=18723) (a:=199) (b:=200) (joinSmall (lo:=18723) (a:=99) (b:=100) (joinSmall (lo:=18723) (a:=49) (b:=50) sp18723 sp18772) (joinSmall (lo:=18822) (a:=50) (b:=50) sp18822 sp18872)) (joinSmall (lo:=18922) (a:=100) (b:=100) (joinSmall (lo:=18922) (a:=50) (b:=50) sp18922 sp18972) (joinSmall (lo:=19022) (a:=50) (b:=50) sp19022 sp19072))))))) (joinSmall (lo:=19122) (a:=3187) (b:=3187) (joinSmall (lo:=19122) (a:=1593) (b:=1594) (joinSmall (lo:=19122) (a:=796) (b:=797) (joinSmall (lo:=19122) (a:=398) (b:=398) (joinSmall (lo:=19122) (a:=199) (b:=199) (joinSmall (lo:=19122) (a:=99) (b:=100) (joinSmall (lo:=19122) (a:=49) (b:=50) sp19122 sp19171) (joinSmall (lo:=19221) (a:=50) (b:=50) sp19221 sp19271)) (joinSmall (lo:=19321) (a:=99) (b:=100) (joinSmall (lo:=19321) (a:=49) (b:=50) sp19321 sp19370) (joinSmall (lo:=19420) (a:=50) (b:=50) sp19420 sp19470))) (joinSmall (lo:=19520) (a:=199) (b:=199) (joinSmall (lo:=19520) (a:=99) (b:=100) (joinSmall (lo:=19520) (a:=49) (b:=50) sp19520 sp19569) (joinSmall (lo:=19619) (a:=50) (b:=50) sp19619 sp19669)) (joinSmall (lo:=19719) (a:=99) (b:=100) (joinSmall (lo:=19719) (a:=49) (b:=50) sp19719 sp19768) (joinSmall (lo:=19818) (a:=50) (b:=50) sp19818 sp19868)))) (joinSmall (lo:=19918) (a:=398) (b:=399) (joinSmall (lo:=19918) (a:=199) (b:=199) (joinSmall (lo:=19918) (a:=99) (b:=100) (joinSmall (lo:=19918) (a:=49) (b:=50) sp19918 sp19967) (joinSmall (lo:=20017) (a:=50) (b:=50) sp20017 sp20067)) (joinSmall (lo:=20117) (a:=99) (b:=100) (joinSmall (lo:=20117) (a:=49) (b:=50) sp20117 sp20166) (joinSmall (lo:=20216) (a:=50) (b:=50) sp20216 sp20266))) (joinSmall (lo:=20316) (a:=199) (b:=200) (joinSmall (lo:=20316) (a:=99) (b:=100) (joinSmall (lo:=20316) (a:=49) (b:=50) sp20316 sp20365) (joinSmall (lo:=20415) (a:=50) (b:=50) sp20415 sp20465)) (joinSmall (lo:=20515) (a:=100) (b:=100) (joinSmall (lo:=20515) (a:=50) (b:=50) sp20515 sp20565) (joinSmall (lo:=20615) (a:=50) (b:=50) sp20615 sp20665))))) (joinSmall (lo:=20715) (a:=797) (b:=797) (joinSmall (lo:=20715) (a:=398) (b:=399) (joinSmall (lo:=20715) (a:=199) (b:=199) (joinSmall (lo:=20715) (a:=99) (b:=100) (joinSmall (lo:=20715) (a:=49) (b:=50) sp20715 sp20764) (joinSmall (lo:=20814) (a:=50) (b:=50) sp20814 sp20864)) (joinSmall (lo:=20914) (a:=99) (b:=100) (joinSmall (lo:=20914) (a:=49) (b:=50) sp20914 sp20963) (joinSmall (lo:=21013) (a:=50) (b:=50) sp21013 sp21063))) (joinSmall (lo:=21113) (a:=199) (b:=200) (joinSmall (lo:=21113) (a:=99) (b:=100) (joinSmall (lo:=21113) (a:=49) (b:=50) sp21113 sp21162) (joinSmall (lo:=21212) (a:=50) (b:=50) sp21212 sp21262)) (joinSmall (lo:=21312) (a:=100) (b:=100) (joinSmall (lo:=21312) (a:=50) (b:=50) sp21312 sp21362) (joinSmall (lo:=21412) (a:=50) (b:=50) sp21412 sp21462)))) (joinSmall (lo:=21512) (a:=398) (b:=399) (joinSmall (lo:=21512) (a:=199) (b:=199) (joinSmall (lo:=21512) (a:=99) (b:=100) (joinSmall (lo:=21512) (a:=49) (b:=50) sp21512 sp21561) (joinSmall (lo:=21611) (a:=50) (b:=50) sp21611 sp21661)) (joinSmall (lo:=21711) (a:=99) (b:=100) (joinSmall (lo:=21711) (a:=49) (b:=50) sp21711 sp21760) (joinSmall (lo:=21810) (a:=50) (b:=50) sp21810 sp21860))) (joinSmall (lo:=21910) (a:=199) (b:=200) (joinSmall (lo:=21910) (a:=99) (b:=100) (joinSmall (lo:=21910) (a:=49) (b:=50) sp21910 sp21959) (joinSmall (lo:=22009) (a:=50) (b:=50) sp22009 sp22059)) (joinSmall (lo:=22109) (a:=100) (b:=100) (joinSmall (lo:=22109) (a:=50) (b:=50) sp22109 sp22159) (joinSmall (lo:=22209) (a:=50) (b:=50) sp22209 sp22259)))))) (joinSmall (lo:=22309) (a:=1593) (b:=1594) (joinSmall (lo:=22309) (a:=796) (b:=797) (joinSmall (lo:=22309) (a:=398) (b:=398) (joinSmall (lo:=22309) (a:=199) (b:=199) (joinSmall (lo:=22309) (a:=99) (b:=100) (joinSmall (lo:=22309) (a:=49) (b:=50) sp22309 sp22358) (joinSmall (lo:=22408) (a:=50) (b:=50) sp22408 sp22458)) (joinSmall (lo:=22508) (a:=99) (b:=100) (joinSmall (lo:=22508) (a:=49) (b:=50) sp22508 sp22557) (joinSmall (lo:=22607) (a:=50) (b:=50) sp22607 sp22657))) (joinSmall (lo:=22707) (a:=199) (b:=199) (joinSmall (lo:=22707) (a:=99) (b:=100) (joinSmall (lo:=22707) (a:=49) (b:=50) sp22707 sp22756) (joinSmall (lo:=22806) (a:=50) (b:=50) sp22806 sp22856)) (joinSmall (lo:=22906) (a:=99) (b:=100) (joinSmall (lo:=22906) (a:=49) (b:=50) sp22906 sp22955) (joinSmall (lo:=23005) (a:=50) (b:=50) sp23005 sp23055)))) (joinSmall (lo:=23105) (a:=398) (b:=399) (joinSmall (lo:=23105) (a:=199) (b:=199) (joinSmall (lo:=23105) (a:=99) (b:=100) (joinSmall (lo:=23105) (a:=49) (b:=50) sp23105 sp23154) (joinSmall (lo:=23204) (a:=50) (b:=50) sp23204 sp23254)) (joinSmall (lo:=23304) (a:=99) (b:=100) (joinSmall (lo:=23304) (a:=49) (b:=50) sp23304 sp23353) (joinSmall (lo:=23403) (a:=50) (b:=50) sp23403 sp23453))) (joinSmall (lo:=23503) (a:=199) (b:=200) (joinSmall (lo:=23503) (a:=99) (b:=100) (joinSmall (lo:=23503) (a:=49) (b:=50) sp23503 sp23552) (joinSmall (lo:=23602) (a:=50) (b:=50) sp23602 sp23652)) (joinSmall (lo:=23702) (a:=100) (b:=100) (joinSmall (lo:=23702) (a:=50) (b:=50) sp23702 sp23752) (joinSmall (lo:=23802) (a:=50) (b:=50) sp23802 sp23852))))) (joinSmall (lo:=23902) (a:=797) (b:=797) (joinSmall (lo:=23902) (a:=398) (b:=399) (joinSmall (lo:=23902) (a:=199) (b:=199) (joinSmall (lo:=23902) (a:=99) (b:=100) (joinSmall (lo:=23902) (a:=49) (b:=50) sp23902 sp23951) (joinSmall (lo:=24001) (a:=50) (b:=50) sp24001 sp24051)) (joinSmall (lo:=24101) (a:=99) (b:=100) (joinSmall (lo:=24101) (a:=49) (b:=50) sp24101 sp24150) (joinSmall (lo:=24200) (a:=50) (b:=50) sp24200 sp24250))) (joinSmall (lo:=24300) (a:=199) (b:=200) (joinSmall (lo:=24300) (a:=99) (b:=100) (joinSmall (lo:=24300) (a:=49) (b:=50) sp24300 sp24349) (joinSmall (lo:=24399) (a:=50) (b:=50) sp24399 sp24449)) (joinSmall (lo:=24499) (a:=100) (b:=100) (joinSmall (lo:=24499) (a:=50) (b:=50) sp24499 sp24549) (joinSmall (lo:=24599) (a:=50) (b:=50) sp24599 sp24649)))) (joinSmall (lo:=24699) (a:=398) (b:=399) (joinSmall (lo:=24699) (a:=199) (b:=199) (joinSmall (lo:=24699) (a:=99) (b:=100) (joinSmall (lo:=24699) (a:=49) (b:=50) sp24699 sp24748) (joinSmall (lo:=24798) (a:=50) (b:=50) sp24798 sp24848)) (joinSmall (lo:=24898) (a:=99) (b:=100) (joinSmall (lo:=24898) (a:=49) (b:=50) sp24898 sp24947) (joinSmall (lo:=24997) (a:=50) (b:=50) sp24997 sp25047))) (joinSmall (lo:=25097) (a:=199) (b:=200) (joinSmall (lo:=25097) (a:=99) (b:=100) (joinSmall (lo:=25097) (a:=49) (b:=50) sp25097 sp25146) (joinSmall (lo:=25196) (a:=50) (b:=50) sp25196 sp25246)) (joinSmall (lo:=25296) (a:=100) (b:=100) (joinSmall (lo:=25296) (a:=50) (b:=50) sp25296 sp25346) (joinSmall (lo:=25396) (a:=50) (b:=50) sp25396 sp25446)))))))))
  have good : (List.range 25496).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 650000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 25495 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 25495 := by
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


private def packet (i : ℕ) : ℕ := (if i < 165 then (if i < 82 then (if i < 41 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 7 then (if i < 6 then 0 else 0) else (if i < 8 then 0 else (if i < 9 then 0 else 0)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 0))) else (if i < 17 then (if i < 16 then 0 else 0) else (if i < 18 then 0 else (if i < 19 then 0 else 0))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then 0 else 0) else (if i < 23 then 0 else (if i < 24 then 0 else 0))) else (if i < 27 then (if i < 26 then 0 else 0) else (if i < 28 then 0 else (if i < 29 then 0 else 0)))) else (if i < 35 then (if i < 32 then (if i < 31 then 0 else 0) else (if i < 33 then 0 else (if i < 34 then 0 else 0))) else (if i < 38 then (if i < 36 then 0 else (if i < 37 then 0 else 0)) else (if i < 39 then 0 else (if i < 40 then 0 else 0)))))) else (if i < 61 then (if i < 51 then (if i < 46 then (if i < 43 then (if i < 42 then 0 else 0) else (if i < 44 then 0 else (if i < 45 then 0 else 0))) else (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else (if i < 50 then 0 else 0)))) else (if i < 56 then (if i < 53 then (if i < 52 then 0 else 0) else (if i < 54 then 0 else (if i < 55 then 0 else 0))) else (if i < 58 then (if i < 57 then 0 else 0) else (if i < 59 then 0 else (if i < 60 then 0 else 0))))) else (if i < 71 then (if i < 66 then (if i < 63 then (if i < 62 then 0 else 0) else (if i < 64 then 0 else (if i < 65 then 0 else 0))) else (if i < 68 then (if i < 67 then 0 else 0) else (if i < 69 then 0 else (if i < 70 then 0 else 0)))) else (if i < 76 then (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else (if i < 75 then 0 else 0))) else (if i < 79 then (if i < 77 then 0 else (if i < 78 then 0 else 0)) else (if i < 80 then 0 else (if i < 81 then 0 else 0))))))) else (if i < 123 then (if i < 102 then (if i < 92 then (if i < 87 then (if i < 84 then (if i < 83 then 0 else 0) else (if i < 85 then 0 else (if i < 86 then 0 else 0))) else (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else (if i < 91 then 0 else 0)))) else (if i < 97 then (if i < 94 then (if i < 93 then 0 else 0) else (if i < 95 then 0 else (if i < 96 then 0 else 0))) else (if i < 99 then (if i < 98 then 0 else 0) else (if i < 100 then 0 else (if i < 101 then 0 else 0))))) else (if i < 112 then (if i < 107 then (if i < 104 then (if i < 103 then 0 else 0) else (if i < 105 then 0 else (if i < 106 then 0 else 0))) else (if i < 109 then (if i < 108 then 0 else 0) else (if i < 110 then 0 else (if i < 111 then 0 else 0)))) else (if i < 117 then (if i < 114 then (if i < 113 then 0 else 0) else (if i < 115 then 0 else (if i < 116 then 0 else 0))) else (if i < 120 then (if i < 118 then 0 else (if i < 119 then 0 else 0)) else (if i < 121 then 0 else (if i < 122 then 0 else 0)))))) else (if i < 144 then (if i < 133 then (if i < 128 then (if i < 125 then (if i < 124 then 0 else 0) else (if i < 126 then 0 else (if i < 127 then 0 else 0))) else (if i < 130 then (if i < 129 then 0 else 0) else (if i < 131 then 0 else (if i < 132 then 0 else 0)))) else (if i < 138 then (if i < 135 then (if i < 134 then 0 else 0) else (if i < 136 then 0 else (if i < 137 then 0 else 0))) else (if i < 141 then (if i < 139 then 0 else (if i < 140 then 0 else 0)) else (if i < 142 then 0 else (if i < 143 then 0 else 0))))) else (if i < 154 then (if i < 149 then (if i < 146 then (if i < 145 then 0 else 0) else (if i < 147 then 0 else (if i < 148 then 0 else 0))) else (if i < 151 then (if i < 150 then 0 else 0) else (if i < 152 then 0 else (if i < 153 then 0 else 0)))) else (if i < 159 then (if i < 156 then (if i < 155 then 0 else 0) else (if i < 157 then 0 else (if i < 158 then 0 else 0))) else (if i < 162 then (if i < 160 then 0 else (if i < 161 then 0 else 0)) else (if i < 163 then 0 else (if i < 164 then 0 else 0)))))))) else (if i < 248 then (if i < 206 then (if i < 185 then (if i < 175 then (if i < 170 then (if i < 167 then (if i < 166 then 0 else 0) else (if i < 168 then 0 else (if i < 169 then 0 else 0))) else (if i < 172 then (if i < 171 then 0 else 0) else (if i < 173 then 0 else (if i < 174 then 0 else 0)))) else (if i < 180 then (if i < 177 then (if i < 176 then 0 else 0) else (if i < 178 then 0 else (if i < 179 then 0 else 0))) else (if i < 182 then (if i < 181 then 0 else 0) else (if i < 183 then 0 else (if i < 184 then 0 else 0))))) else (if i < 195 then (if i < 190 then (if i < 187 then (if i < 186 then 0 else 0) else (if i < 188 then 0 else (if i < 189 then 0 else 0))) else (if i < 192 then (if i < 191 then 0 else 0) else (if i < 193 then 0 else (if i < 194 then 0 else 0)))) else (if i < 200 then (if i < 197 then (if i < 196 then 0 else 0) else (if i < 198 then 0 else (if i < 199 then 0 else 0))) else (if i < 203 then (if i < 201 then 0 else (if i < 202 then 0 else 0)) else (if i < 204 then 0 else (if i < 205 then 0 else 0)))))) else (if i < 227 then (if i < 216 then (if i < 211 then (if i < 208 then (if i < 207 then 0 else 0) else (if i < 209 then 0 else (if i < 210 then 0 else 0))) else (if i < 213 then (if i < 212 then 0 else 0) else (if i < 214 then 0 else (if i < 215 then 0 else 0)))) else (if i < 221 then (if i < 218 then (if i < 217 then 0 else 0) else (if i < 219 then 0 else (if i < 220 then 0 else 0))) else (if i < 224 then (if i < 222 then 0 else (if i < 223 then 0 else 0)) else (if i < 225 then 0 else (if i < 226 then 0 else 0))))) else (if i < 237 then (if i < 232 then (if i < 229 then (if i < 228 then 0 else 0) else (if i < 230 then 0 else (if i < 231 then 0 else 0))) else (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else (if i < 236 then 0 else 0)))) else (if i < 242 then (if i < 239 then (if i < 238 then 0 else 0) else (if i < 240 then 0 else (if i < 241 then 0 else 0))) else (if i < 245 then (if i < 243 then 0 else (if i < 244 then 0 else 0)) else (if i < 246 then 0 else (if i < 247 then 0 else 0))))))) else (if i < 289 then (if i < 268 then (if i < 258 then (if i < 253 then (if i < 250 then (if i < 249 then 0 else 0) else (if i < 251 then 0 else (if i < 252 then 0 else 0))) else (if i < 255 then (if i < 254 then 0 else 0) else (if i < 256 then 0 else (if i < 257 then 0 else 0)))) else (if i < 263 then (if i < 260 then (if i < 259 then 0 else 0) else (if i < 261 then 0 else (if i < 262 then 0 else 0))) else (if i < 265 then (if i < 264 then 0 else 0) else (if i < 266 then 0 else (if i < 267 then 0 else 0))))) else (if i < 278 then (if i < 273 then (if i < 270 then (if i < 269 then 0 else 0) else (if i < 271 then 0 else (if i < 272 then 0 else 0))) else (if i < 275 then (if i < 274 then 0 else 0) else (if i < 276 then 0 else (if i < 277 then 0 else 0)))) else (if i < 283 then (if i < 280 then (if i < 279 then 0 else 0) else (if i < 281 then 0 else (if i < 282 then 0 else 0))) else (if i < 286 then (if i < 284 then 0 else (if i < 285 then 0 else 0)) else (if i < 287 then 0 else (if i < 288 then 0 else 0)))))) else (if i < 310 then (if i < 299 then (if i < 294 then (if i < 291 then (if i < 290 then 0 else 0) else (if i < 292 then 0 else (if i < 293 then 0 else 0))) else (if i < 296 then (if i < 295 then 0 else 0) else (if i < 297 then 0 else (if i < 298 then 0 else 0)))) else (if i < 304 then (if i < 301 then (if i < 300 then 0 else 0) else (if i < 302 then 0 else (if i < 303 then 0 else 0))) else (if i < 307 then (if i < 305 then 0 else (if i < 306 then 0 else 0)) else (if i < 308 then 0 else (if i < 309 then 0 else 0))))) else (if i < 320 then (if i < 315 then (if i < 312 then (if i < 311 then 0 else 0) else (if i < 313 then 0 else (if i < 314 then 0 else 0))) else (if i < 317 then (if i < 316 then 0 else 0) else (if i < 318 then 0x1f0f7f12b3940c9524511fc0e746882e714088a03a416c08d03040c000001f0f1fa2c9149499046b2090eac69c2f014908a439016e08903000ac00001f0ec052c994cc9aa47a20c0f086b430014f09003aa17208c833c0c800001f0e61d2bc945097245c1fd0e6c6862e714388bc3b017a08e831c0bc00001f0e0672ac93e893e4461fb0e706722d8141887839016608382b40a000001f0da6c2c814b899c46b20a8f006c6300150091c3dc19709703440c600001f0d4722d095109dc4882140f006ce30015809483da19509803200da00001f0ceb62b5940c9564532020e846922ee14608ac3b017108b83040c000001f0c8ae2d415389d84942190f5c6ee31a15a09683f619509903340cc00001f0c2c62c914c499a4772078eb06a42fb14e88e03b617708c02e80ac00001f0bcbe2d6153c9d248d2168f3c6dc30b15789343e818f09102fc0b600001f0b6c72cd950c9d44832128f006b82f714488b039416a085029809800001f0b0ed2ba14409624521fe8e806982e414488a83a216c08602d00c000001f0aafa2ca14d49a646f2068ef06b02f814f08b839217d08902d80a800001f0a4df2de155c9e24892128f246cc30315409343d618b096833c0d200001f09ef42c414a49904692080ed86a82f814988c438817208d82e40c400001f098fd2cc94cc9984732018ec868e2f114a08cc3a817208902e80be00001f093172c314949884601fe0e7c6802ee14608b839817b08c82d80ba00001f08d352c0145c97a45c2068edc6c02f414b08e83b217d09083040e600001f087582be94909784612060e846902e614188c038e16c08b82dc0c600001f081682d395109de4902188f686ec30815709303d618609383140c200001f07b7b2c514cc9ac4832110f006c830315109203cc18a09203200c000001f075832cc95149da49121b8f406de30215108d839a16e08d02bc0b000001f06f962cb14c49be47c2108ef46a02f714a08883a016608382d80c200001f069a72c814d49b847920f0f286bc30015409083b417308b02c40ca00001f063bb2cd95049c647e20f0f1c6c630714f890c3ba184097832c0b800001f05deb2bb148097a4621ff0e5c65e2d9140885836616208402a80a200001f057ef2cc94d49be4832148ef46b02f314b08c43a818008f82f80d800001f051f82cd94ec9aa4732050ecc6c02fe14d090c3ba17408582b40b600001f04c142c4148c9a44702088ecc6b630414e89303de19009383440d800001f0461f2cf14e89a84752090e986b62fc14408c83a017308882d40b000001f0401f2ca94c09904652068e8068e2f314408bc3a017608e82e40b000001f03a232d1952c9b84782080eac6a42ed14588d43aa17c08d03240c400001f034482bb147498a4752058ea06782d614288b43b217e09083200c400001f02e4e2cc14cc98a46b2040e8468e2e414a88d83ba18009483140be00001f0283f2d615049b247620b8ed46c02fe14a08e03d018608c82e00c000001f022592c1148c98a4571fb8e886862e614508bc39e17608d02f40be00001f01c562d695409e648d21e8f646fc31f15f094c3de19b09903380c000001f016752c3947496a44d1fa0e7467a2df138086c38016e08983200ca00001f010662d3950c9cc4892188f286e431915689503e418e09c83240c400001f00a6d2c794b89ac46d2070ec46be30815209243da19009203300ca00001f0046d2d1954c9f64a92198f2c6b630515509403de18309083000d000001effe752d315209b24732088eac6842e314808cc3a417008902dc0a200001eff8a22b894a09a446b2098ed46a42f314d88e43c818308c02f00bc00001eff2ea2a713c89344411f30e3463c2bb132880434c154082029c0a200001efecd22d595189d848c2158f046c230115488f03b417f08e03000c400001efe6e02c894d49bc47820d8ee46aa2f214688e43ae17a08f032c0d800001efe0e22cb94e49ba47a20b8ec069e2e014088a039617008d02f80b800001efdb332a713e89304381f10df464c2cf136887839217e09282f40b000001efd5282d495009d64882128f0c6d430714e89003c618c095833c0d800001efcf5c2b594549824591fb0e686622d0135086037e15f08682d40ca00001efc99b2b094289544521fd0e6c67a2ea14188a839816c08b82e80b400001efc3ce2b7944896a4591f80e5c66c2dc14608a439215f08382c40be00001efbdd42c894c89a44692058ec86a22dd13e88743a817d09303000bc00001efb7c82d494e49ae47a2098e9c6802df140088838e16408202d40b200001efb1cd2cf951c9bc47d20c8eb46942de143089439216e08d82e00ca00001efabe02c594e49a44732070eb86ba2f714b88d83b218109103180c600001efa5f22ca14cc9ae47c20d0ed06a02e814588a438e17808982e00ba00001efa01e2b2942c95a44b1f68e386462d413d086c38015c08082c40cc00001ef9a052dc95449d44902198f7071032916189a840019309682f80ba00001ef93ec2dd15609f049621d8f886fc32a16009603dc18509603400ce00001ef8dfd2cc14fc9bc47b2098ec06aa2fa15008f43b818109003180ca00001ef87ee2d895389ea4962180f306e031215d89283d018b09883300c400001ef822a2b214089444411f20e1465e2d914308b439a16f08182d80ba000 else (if i < 319 then 0x1f272ea2bc149098c45a2030ec06a02f214b88e83c018409202ec0b000001f26ce92cf95109cc47a2100f206b22f114c08fc3b217709183180ca00001f267072c614b89904712038ec06a82fa14c88e43ae17e09203300c000001f261232c2149498e46a2048eb869a2f914e08e83d018f09382e80b800001f25b172d315189ce48a2158f106ca30715108fc3d619009b03500da00001f2553b2c314b099646f20b8e8c69a2ec14b08e83be17b08d82f80c200001f24f5d2bf14789ac4722078e8c6762de140888c38e16408983240ae00001f249732c0147497e4612030e9c6822f114888b83a817108802a40a800001f243882c914c09ac47720a0ee06b22ee14308c83b217b09403100c800001f23db52b9949c98e4722068eac6942db14188c439a17208c82a80b400001f237bb2d295189bc4882128f006d430c15409083c018009603200ba00001f231c42cc94e49b048020d0f106ac2ef14508d43b216d08582b00b000001f22bbf2ca94d09a648120c8ec86b22fd15309243cc18109983040c000001f226042ae941095c4511fd8e9068c2e814688b03aa17c08d831c0c400001f220192c794c099647b2050ebc6922ec14788d43a617a08f02e80ba00001f21a0b2d5153c9ec48e2168f2c6cc30515589203c817f08e82f80c600001f214182cd14d099a46a2038ea068a2de139886038a16a08802cc0ae00001f20e392c914c89964702090ee46b62fd14e88e03bc18409282dc0bc00001f208382cf14fc9cc47f20f8f246e630e15409203dc193095832c0be00001f202492ca14b89a04792110ee46bc304150893c3de18b09303040be00001f1fc642c994f09bc47920b0edc6a22f214c08e43a817308a83140c200001f1f63b2df958ca044942158f2c6bc30d15589103be17909383180c600001f1f0452ce94f89c647a20d8f086c02fd14f89083d418b09383240d000001f1ea492d015189c24782070ec46a42ef14908c439c16e08802e00c800001f1e4312dd956c9e449b2148f0c6ac2ee14708c83a616c08802c80ae00001f1de652ba14609784491f50e106702dc142887038e16608582c80ac00001f1d8902bf94909724632058e9c67a2e614688ac38a16b08a83140d200001f1d2912cc150c9ce4882150f506ea315155894c3c619109383200c600001f1ccae2c2147c98e47220c8ef06bc2f515188c43a217508a83140be00001f1c6a52d795449c848d2120f046ae2ea143089c3ae17308f83140ce00001f1c0f82a894049524441f38e3065e2d013b089c39e17108302b009a00001f1bb032ca94ec9c648820d8ee069e2f114f88e03b417908f03240c200001f1b5082cd94dc9b24772088ecc6ac2f315289143f219609b83640d600001f1af212c0147898245f2020eb86a62f614a88d43ba17a08c02e409800001f1a9282cf94ec9a646e20b8ec06aa2f914c88f43a417408802d00aa00001f1a3572b6943497446a2038eb46982f214708a839a17608682940ba00001f19d612d014f09c447a2110f046c830815408f03c817508c02f00c200001f1975c2d495249ce48120e8edc6a6300151891c3dc18d08f031c0c200001f191862bb148c98245f2030eb46aa2fa14a89283da18809403000b800001f18b9b2c594b09904742060e846862e614808d03aa17808782d00b400001f185c92ba14709684521f90e5c6542d7142886436015b08402c00b800001f17fbc2d415309ca48821b8f6870632015a891c3c218509203040b000001f179f62b514649804691ff8e7c6882e814588e03aa17908b02d80a400001f1742f2b2942494a4561fe0ec06982ef14a08f43ca18608e82dc0b400001f16e4c2c2148897c45f2018ea06922e814508b438e16908b82f40be00001f168682c5149c9a44822128f146c830a15409043ca18809683040ca00001f1628d2c014989884642038eb06a62e6141089838e16908502c00ac00001f15c9c2c7149c9804622058ed06a02fe15208fc3b817a09303280c400001f156ac2c314bc9964762090ef46b62f714a88d03a217c09103240ca00001f1509d2d515049aa47a20f8eec6a62f515209043a417e09103180ca00001f14a9a2cf15109c64872118f3c6d430c156892c3d018709703440da00001f1449e2cc94e89ca4902138f186be30415389443de19509783140c600001f13ecf2b7146499e46d2080ecc6a62f614888c03b218009203100b600001f138c02d514f89ba4862128f286e631515889403f0192092830c0c000001f132d72c814d49b047d20c0efc6b02ff15609143c417d08b02e40c800001f12ce42cc14d49b247920a8ee86c430d15208e83b018008f82f00ba00001f126f32c314949a247620c0ee46ac2ef14f89083bc17708f02cc0ba00001f120ee2d314f89b647c20e8ecc69c2fe14d89183c218408f83140ba00001f11b2e2ae93f895244b1f78e946aa2ec14608c03a217808882d00b800001f1156b2b0143493643c1f40e0865c2de14688cc3a617308502b80ae00001f10f842c5948899e4702098ed46aa2f715009083c217c09182fc0cc00001f109742d495089b847c20c0eac69a2e814588a83c017d08f02d80b600001f1039d2c194a49a848020f8ef46d630515689243d218d09a03340d000001f0fdb22c794c89aa46f20a8ef46cc30415188d439816e08b03040c6000 else 0x1f3eed82d015189cc48a2178f1c6d430915909143be17b08e82bc0b000001f3e8f62c714d099e46e2038eb86862ef14708dc3ac17b08b02d40b800001f3e3142bd949099a47220c0f286da30e15209143ba17f08c82f40bc00001f3dd032d795309de4922120f086bc2f714c88f83c018208f83100c200001f3d71d2c194989784591fd0e986a02f214808ec3b217308a02f00be00001f3d1312c694b09b447b20b8eb06ae2f914c08b03ac17808d82c40b000001f3cb452c494a09884591f80e6067a2dd14308c439c17308d82e40a600001f3c54c2c814b49a44762048e9c6802e3147087c39016e08782f00b400001f3bf852b9146098846b2050e946982e214188a839817708c02e00bc00001f3b9a42c394949864662058e7c6ac2f914a08d43ba17809103180d000001f3b3db2bf14549804672010e9c69c2fa14a09043b017708d82e80b800001f3ae062bc145896c45a1ff8e886942f914d88f83bc17b08682cc0b800001f3a7ca2e59584a044a221f0f606dc30a15209103ce18309183000c600001f3a1d02d014ec9b647d2130f086d8303154893c3fa19809483240b600001f39bda2cd950c9c24862130f2c6e430f15709183d218509503180c600001f395d22d415309d248f2140f106cc30a15488f03c018609002c80b400001f38ff32be149898e45c2038eb46842dd13e08943a0168088030c0ca00001f38a2a2b6945496c4491f98e5c6602dd140087839617608e82ec0b200001f384022e395809ee4942188f486d630215008dc3a817d08f82fc0c200001f37e122cb15089d047b2050ed469e2f414888e43c618709503140bc00001f3783c2bb146497a45b1fe8e7c6a62ef14508c43b817f08982d80b800001f372502c0147497645a2050eac6a22f114b08cc3b017808f83140cc00001f36c662c414ac9a846f20d8ee86c62fd14d08b439c17308b02fc0c800001f3667c2c414c49a246f20c8eb46b02f614b08c03ae18008d03000c600001f360732d895349d048f2130f506e430715489403d6191098831c0c400001f35aaa2b6945896c4592008e7c6702d613f089438816a087030c0d200001f354ee2ad140c96645b2080eac6a22f814d08c83b017908d02f40b600001f34ee72d295349d648f2168ef86be30015609143be18009083100c800001f349152b314189544571fd0e786882e714588a039017209002fc0b600001f343252ca149498045b1ff0eac67a2e714888d83a817209002f80b800001f33d2c2cc94e89c24882160f306d631315a891c3d817d09203100d400001f337372cc14d09a447120a0eb46882e8140887c39416808802ec0cc00001f331612b914789964722098f006d630b15409383e219209b83340ba00001f32b7c2c794989a248020f8f106ba2fd14988ec3ac17c08c83080c800001f325972be149899247420c8ee46bc2f214d08ec3b617908c02f80be00001f31fbb2b994a099846f20a0ec46a230015209083c818f09883380d400001f319c92ca94c89a647220c8ecc6ae2f414a889039217308a02e00bc00001f313ad2d515289ce48e2158f006ba2f715089043ce17a090832c0c600001f30dc62c014609744692030e8c6822e1142088837e16f08482cc0b200001f307dc2c915049c047520a0ed86a02fa14c08d83b618009583340de00001f301d72cf151c9c648920f8f086c430815589383c617809003100c800001f2fbd12d795249cc4862100f006be2fe153091c3d218d09483280cc00001f2f6092ba94449784612030ebc6982f914908b43b017408b02f80be00001f2f0062cf15089bc47820c0ed46a62e614d08d03aa17b08c82f00ce00001f2ea1d2c094989964732010e9c6942e414588a43b217708b02e80bc00001f2e4402c514b899e4762100ee46b22f614a88f43c417b08f82fc0b000001f2de3e2d194d89ba4782090ec46b42eb14c88bc3a817509203380b600001f2d8582c2949c98446220a8ea068a2ef14b89103c417e09182e00d200001f2d2452df15789f24932170f2c6d430415409083ce18109182dc0c800001f2cc342d815509d648b2178f4c6e831515e89983f819709983480be00001f2c6622bb14509604571ff8e886b02fe14d08f43c618c08f02e00a000001f2c05c2d515009d048b2180f586f231115709443e418909182f00ba00001f2ba5e2d315249c648c2160f486ee31a15c094c3e219209683140b800001f2b4452da95589e849221a0f446e231615a892c3d218709202e80b400001f2ae622c094709a04712058e806782e014488b838c16f08902ec0a800001f2a8b72af142096845a1f50e3465c2d513b087038c17408e82f40b600001f2a2892e915bca1649f21e8f386da30d15909403d218d09203100dc00001f29c8e2ce14fc9ae48220f8f086c430214c09103ca18508d83000b000001f296802d815449d64972178efc6ce2f914908e43d218409082f40de00001f290a12bd14589864632040ea069e2e514688bc39e16b08a82f80ba00001f28ac82ba14889764572008ea468a2ea14908bc3b218009003080c400001f284b12de95509dc49521a8f4c6e030f15809203ca18709083080b800001f27eab2d695249ca48c2170f406ee31715a09243ce17b08502ac0b000001f278c32c314ac99e46e2030e9c6a02fa15108e83b017308e82d80c0000)))) else (if i < 325 then (if i < 322 then (if i < 321 then 0x1f569232bd944c95e4511fa0e706962f614a88d43a8181092032c0ba00001f5634c2bc148897a4642068e846762d513d889437c16808602d40ae00001f55d8a2ad93e093a43d1f28e2c64a2c5139089039a16408a02f00b600001f557cd2af13f892843b1f30e206582c8131883c37c16a07f82c40ae00001f551bc2d7956c9ec48d2168f106de31815689243da18b09403280c000001f54bdc2c214889944702068eb069e2f915088e43be18208d82d40b200001f545eb2c694d09ba47b20b0ecc6882eb14708b03a417308702c80ac00001f53fea2d2950c9aa46e2078ee46c82fd15209083d218f09703440d800001f53a382ad142093a4491f60e4866e2d513e089439416808702fc0c200001f534422cb14c49aa4742068ec46aa2f714c88ec3ac17608b02bc09c00001f52e7b2b1944497045c2058f046c230015089003bc17e09083000ca00001f528932ca95049b04862150f2c6ec30c15108f43c218409403340d400001f5228c2d014ec9ce47b20c8f046b82f314e08dc3a617008f03080c000001f51cb72b614409544491f48e386562d613f88803a017208b02e00c200001f516d82c214b49a24682070ed06a42ec14808a439816d08603000ae00001f5110c2b194009444431f50e346602d5138885c37c162085828809200001f50b1a2ca94f09c247c2018e686aa2f414888b03a817b08d82fc0ce00001f505372c094a09904682078ec06962f314d88dc3b817c08d02d80b600001f4ff4f2c314b09b24812118f086ac2f414888c03ba18409283280d400001f4f98e2b014349744652010e8066c2df13f089438616808082980ae00001f4f3a12ca14dc9a046e2070ea46a22e614c89103d418709583180c200001f4edbd2c3946898045d2010ecc6b42f814b89043c018508f83080ca00001f4e7ca2ce14c89a247a20e0f2c6d42fe14e88ec3aa16f08f82f80ca00001f4e1dc2cb94f89aa46e2088ed86bc306154892c3b8184092831c0c400001f4dbc92dc95349de4842100f106b830115289043be17e08b02f40c800001f4d5e92c3948c97645a2020e986982ee14e08e43c818509202fc0cc00001f4cfd42d615349d647c2100f046b82f914f08f83c217f09683040c200001f4c9f32c394a098645f1ff0e946922f114c88dc3c018208f82f80bc00001f4c3f52cc14c498c45c1ff0e8067e2e613e888439017108f02d00c600001f4be122c314ac99c4782088ed46a02ef14a08ec3c217a08e03180ce00001f4b8052da15309e84922180f706de30f15609483d418108e03280c200001f4b21c2c714b09a446e2008ea869c2f214d09003c618509683000cc00001f4ac372cb14d09a047620b8f186d230a15089043c818609083000be00001f4a6532c214ac99647620d0eb86882dd13e08c03c218408e02f40c000001f4a0452d615149ce4862120f006be30214f08fc3b218709383040c200001f49a5c2ca14f89b447b2108efc6aa2fb156093c3da18209303200c400001f4946b2cd94d899e47320c0ee06a82f614f08e43a017009282e009a00001f48e952bb147098046d20b0edc6ae2f114908a83a218108682d80bc00001f488af2c414a89a84702058e8c6a22eb14288b439c16d08802c80aa00001f4829c2d314f09b046d2060eb86aa30315189143b417908982f80ac00001f47cbe2bc94789824541f78e606682d813b088838015d08882fc0ba00001f476bd2d515149ba47d20f8f046c230514c88d83c618f09703240d000001f470ce2cb94d09924692068eb86b030215109143c217608902f00bc00001f46ae32c514f89b04812190f446e831415609383ca18c09003040c600001f4650d2be146c9744602018e7867a2de14408c43ba17908e82e40c200001f45f382be149c99e47a20b0e9867a2e213e088038415c08102bc0b400001f4595d2c2149c98a4632038ea46a62f414a08d439416f08602d40a800001f453b82a613e493c4421f48e3c6602d613a884c38216608582cc0a600001f44dc82cf15109d24872170f386b22fd14e08e03aa17d08e02d40b800001f447c92cb14b89ba47d2118f406cc30e15089103ba18209083200d200001f441db2ce95109cc4762098eb469e2eb14588a43a417b08f83180d800001f43bf62c614949824521ff8eac6962f414608dc3b417308a82d80bc00001f435f72ce95009c847f20a8ee06962f015209243cc18809483300c200001f430142c594c899847520d8ee46a82ef14588cc3b217b08d02ec0ca00001f429f92e01574a0449521e0f5c6f231015c89343d017d09403000c400001f4243c2ab93f496a45b1ff8e746862e614688b439e16d08b02f80b400001f41e3d2d315249da49c2210f8c710318158093c3f818d09803280d000001f4185e2c1949c98a4762048eac6a02f114788a039e17d09203000c000001f412812bd146c98e4601ff0e546822e9142886c39c17808d82c00ae00001f40c642d915389ec49d21e8f7070232615e89343dc18f097832c0dc00001f406862c1946c9884682068ee06942f314a08ac39817a09183280c000001f400d02ad140894a4461f70e5467a2e113f087839017608a03080c600001f3fadd2c814c49a446c2050ec46bc2fd14b08b83b217d09283280ca00001f3f4d22d7953c9c247f2108ef86bc2fc14c08d839816b08882e80b2000 else 0x1f6e41d2cd14d89bc47e20d0f1c6a62f915389703e0185097030c0d600001f6de0d2d315189cc4862138f206d22ff14c88e43b016808802d40a600001f6d8432af142495244f1fd8e7466a2df14408b438a16908702c00b600001f6d2522c614cc9b44722098f006b630b15509243cc18508c82ec0c000001f6cc8a2b5141c95844a1fe0e686922e214408c439617008a02dc0c600001f6c6a52c594bc99e4682070ed86ae2ec14788d43b017a08802ec0a600001f6c0ab2cd94e89b84872170f286d230614808d03b617508782f40c400001f6bab32cb94cc9a646d20d0eb069c2f214f89143c4189096032c0e400001f6b4d12c1947099246e2090ec86a82f114a88d439817708f02d40b800001f6aef82ba147c98c4632030e946a02ee14988e03ae17e08e82c80ae00001f6a9032c714f49b04812108ef46b22f414988b03a217308c02e00be00001f6a3242c1947497a4682098ee069e2ef145088039617308a82c809e00001f69d182d7951c9e249a21f8f746ee310152090c3b817608982d00aa00001f6971e2ca94d89c44862118f286c2303151091c3d418508f02f80ce00001f691612ae94109584511fd8e946942ee14088c83a416f08a82ec0c800001f68b8e2bf947897e45c1fd8e686662c5135882437815c07b028409000001f685d42b3141095644d1f58e586682d813e08b43a016b08402d809e00001f67fd72d615189ca47f2100ef06a82f914d893c3f619809703400e800001f67a022bf948c99c47d2138f186de308153090c3d018709803440dc00001f674132c2948097845f2028e8868e2ea14b88d43c018609803340ca00001f66e3f2bb949c98a4642030ea869a2ed14888fc3b418109103280c600001f668742b714809944632090ea46962ea14a08bc3aa17508d83000c200001f6626e2d295209c648020e8ed46982fc14e09143dc18809683540c600001f65ca52bd949898c4692060eb06902e9146089c3b017908b02f80ba00001f656872d8155ca0c49f2200fac710328164898c3fc1a309b036c0e600001f650c52b8946097a4611ff0e786802e914988f43cc18309203200ca00001f64ae32bf945c9824642030ebc69e2f014c090c3ce18f09a033c0dc00001f644cf2dd15649f04942170f506ce30715089043c217d08a82ec0be00001f63ec62d094fc9da4852160f246d030315509483e218d09403480cc00001f638cb2c994c49a447e2100ef06d830b154893c3e018a09002f00b200001f632f52bf945496e4672050eac6a62f414c09003c217e093030c0bc00001f62d172c4949098e46e2048ecc6c430815588f43c218409203380da00001f6271f2cf95009d048d2180f186c02f714d09243ca19309483000c400001f621592b5144c9864622030ea06942f614d09043ba17108282ac0b400001f61b6e2c714b89b247b20d8f106b830614a88d43b617808b82f80c200001f6157e2c694ac9a64772088ec069a2e714808a83a617309083180c200001f60f802d495049d24962168f246de31915d89683e819309483280bc00001f609a22c394849724602038e7c6902e314808dc3b418209002d80cc00001f603d52b914349524481f30e2c67a2c8136083035815f08182b409a00001f5fddc2cd95209c04822118eec6be30014e08f43ac18109182fc0bc00001f5f7c02d695349d447d2100efc6c62fe15388f03c618609303000a600001f5f1d62c714d49ac48220a8ed86aa2ec14c09003c817409183100c000001f5ebfb2c494a498045f2040ea06962ea14d08fc3b018408e833c0ca00001f5e63b2b013fc9444461f28e3c6562dc142089439617e08e83180d000001f5e05f2bd148096c4551fe0e846822e214188a039217108502e80be00001f5da4b2d395249e64942168f306e631115d091c3d218909002ec0b200001f5d4662c7949c9a24662070ee86b22f115009283da19309783240c800001f5ce732cc94d49b046d2080eb46922e7143888c3a417308c02fc0c400001f5c88e2c894d09b44762098ed06aa2f214608a43ac16c08a82d40b600001f5c2a72bf94a899647a20b8edc6982f715089143c217e08f82dc0ae00001f5bca82cc14dc9c048a2168f046ce30f15809383e418e09a03400f200001f5b6c92bc947c97644f1f90e5c6722e714b88d83a017608f82f80b600001f5b0c82d214ec9c64862138f3c6d6306151091c3b418208c02cc0c400001f5aaa52d895489da47d20d8ed86962eb144887c37016008903000c200001f5a4c02c414b49c447e2108ee06c430915609243f019409583380ca00001f59ed12c994ac99e47320d0eec6c02fe151892c3e219c09a03580d400001f598e42c6149098a46c2070e9068c2e414388e83bc17d09082f40ac00001f5930d2bf148c99447920e8f106cc30915209203d217908e03040c000001f58d052d615009c44802120f346d2319166099c3ee19509b03180c600001f587242bf14909644501f60e3c6582dd13d88ac3a017308f83080c200001f5811e2d415249ea4932130f306cc2ff14f08fc3b817b08e82f00b400001f57b0d2d915549f248e2130ef06ba2fd14d88e83a0177092830c0bc00001f574f92d515149c248621a0f4c6e230f152090c3ae18209103200c800001f56ef72cc95009a046c2058eb86902d713c887438a16908702cc0bc000) else (if i < 323 then 0x1f85ed62b6945c9764582038eb468e2ed14908d838c16c08402ac0a800001f858fe2c094a899247720a0ed86bc30d15a89703ee19109803380bc00001f852fc2cf95049c847a20d8eec6b22f414688b039416d08802e00b400001f84cdf2dd95549ea49021e8f746fc31b15a89403ce195094830c0cc00001f846df2d8156c9e649c2218f9c70a30b15509143ba17809102fc0d200001f841102b9145c97244e1f98e5866a2d2139084837416408582d00c400001f83b202c214989724601ff0e846742dd146889c39817208802f40bc00001f8353e2ca14d09b44872128f246e630f15208f43b418108e03080c600001f82f482ca94c498a4672038ec46922ef14808ac39017208882c40ac00001f829662bd149899c4732098ec86ba2f514d88b039a180092033c0e000001f823892c394a099047020f0ed86ac30014d08a839817708e02d80be00001f81dad2bf949498c46c2070eb86a02f814c88cc3b416e08982b409a00001f817d32b8145498e46b2060ec46b82f614a88cc3ac17808882e80b800001f811b32e015889fc49b21c0f586dc30714d89103da18609083180cc00001f80bc72c6147c97a4652090ed069e2f614708a038c16908802e80b400001f805f42bc14609664571fd0e706822d914308b039416f08a02d00b000001f7fff32d695549c04872168f4c6dc30614f88ec3c418a09402f80be00001f7fa142bc948096c4511f78e3466a2dc14288f03ba17909002fc0ca00001f7f4362bd14489844602018eac6862e214788a83a817308782dc0c200001f7ee442c694a49984762060ebc6aa2fd153892c3e418e09383000c000001f7e86b2bd146c97845f2060ea46862e414608bc3ba17d09183040be00001f7e2832c314a899647220e0f006c030615088f83cc17b08e82cc0b000001f7dcbe2b814209644401f30e706922f014b88a439617608a82f00c600001f7d6aa2d615589d04852110f186bc2f814d88f43aa16f08302d00ac00001f7d0b32cb14ec9c04862160f106be2f314988e03a817a09082f40c200001f7cb032aa93ec9384401f60e486862e514488d43ae17308c82dc0a600001f7c5222bb147496e4632060eb868c2ec14188903a217208b82d80c800001f7bf292cd95089ca47b2050ea46a02ec14388c83aa18109203300c800001f7b9302cc15009cc4892150f246d831315409483ea18b09683380c600001f7b33b2cc14ec9c447c20e0ef86ba2fe14908b43b217d08982bc0c800001f7ad372d115349d247d2120f246c830515488fc3ca18309103000bc00001f7a74f2c714f09c04802100ed86c2306156890c3d617d08d82dc0c800001f7a1572cf94f49be4812108f106c230214f88ec3bc17e09382ec0b200001f79b502cc150c9c648420e0eec6ac30114b88c03ac17308b02f80ac00001f7956d2c0949497c4672080ec86ae30314d88f43b417208f830c0d000001f78f9b2bd945496e4591fe0e686722d0138088038c16c08802f80be00001f789ae2c794889a64762080e9c6962ed14688d03ac17e09203200be00001f7839d2d415249be47920e0ec86ae2f514b88ec3b618209182f80c600001f77dab2c994c49a04672068e986882df14308c43be18108802f00c000001f777c32c914cc9ba48220b0eb868c2e614888a83aa18309883180c000001f771c22d295349c84782160f346de31115409483ee18e09b835c0e800001f76bd62c014b099a46a2088ec069a2eb14708d43a417408d83080c000001f7660a2bc945c9764601fe0e986902f114888d43a617509083040c200001f760052d515249c847b2110f046be30a15489143c617d09003180da00001f75a112c614dc9ba47b2108f486da30715489303de194096031c0b000001f754202ca94dc9a846d2078ea46902e614488dc3ae17a08c82dc0b000001f74e1c2ca94e09c047b20d0f146c830915509443c217d09382e00c600001f7481f2d095289e249221a8f246ca2fb15109103c018009302fc0b600001f7425b2ba148898447620b0ee06942e914909143c617c09003200be00001f73c722c694e09c648720d8ec469e2f114a08d83b418009283100c200001f736902bc14709884561ff0eb46a22fa14a89003b217208d82f80b400001f730e42a213bc92c42f1e80dc462e2c0136084c37e15d08382a80a800001f72afd2c994ac9ac4682040ea869c2f614f08f03ce17a09283080c600001f725312b113fc9264431ef0e0c6582de13c883438015f08282b80aa00001f71f4c2c594d49ca48c21b0f586de30e15409403e019709703540e800001f719502d415249c247e20d8f046b6302153090c3d017f09103240cc00001f713702c2149499046b2070e906942f614e88e43b018809003280be00001f70dab2b494249504541fb0e3c6822e413f886839616c08402d00b200001f707c82c994c89b047c20b0ee06c62ff14989043bc18209483240c800001f701da2c0948c98e4632048eb06862ec14508e03a417108e830c0cc00001f6fbea2cd15009ca4842118f106c82f814f89143b417808902f40c800001f6f5f42ce14f09ba4832128f246da31115689343c817b08b82f40c800001f6f0022cb94f09c247f2140f146be30515289303d417909203340dc00001f6ea102c794d49aa47e20c8ed86b430014c88e43b618309203200ca000 else (if i < 324 then 0x1f9da212d415309d048e2148f386d030214e88d43ac17708502b40aa00001f9d4162d7154c9e849621b8f286d630d14f08f83c218809102fc0c200001f9ce432b614389524541fe8e7c68e2e314108b43ae17808f82f80c800001f9c8372d4153c9ec49121b0f546e231515188fc3bc17308d02f00c000001f9c2672bc148896a45d1fc8ea46962f414b88cc3a217509083140d800001f9bc552d4952c9e44932128f046b230115389283c418609603340ea00001f9b6852b6945499046b2060eb46862ec14788a038c16c08d83140be00001f9b0772d315509d848e2178f086d2301150891c3c017e08e83200da00001f9aa952c4947c97a4642008e7066e2d8140888c39217208c82e80c200001f9a4c92b8145896e45f2028e846822e113f084c36a16508402d40c400001f99ec12d094d49ac4712090ec468e2e614608b43b817508c03040ca00001f998e72c0949c9904772068ed86ae2ef14588a038816808882cc0aa00001f992cc2d915349c648e2178f0c6d030b15b893c3e418609182e00c600001f98d132af944c9844562028ea46a42f414888cc3a416708582d40be00001f987382c514bc99647320c0ef86c830215609343ba19009982fc0b200001f981472ca14c899c4692080ee46b82fc14e88ec3ac17508b03140c800001f97b462d515649f848b2168f506fe31815489103ca19109603000b600001f975602c714949964642068ecc6a22f414808bc3ac17408d82e00be00001f96f722c194a89a046d20d0f106c2302152891c3c418209403240c200001f969942bc94a09844682058e9869c2f414889103cc18709182f40c000001f963bc2b594249584501fc0e8868c2e4141089439417708b83180c800001f95ddf2c1948c98a4642010e8468c2e5145088c39217508c82ec0cc00001f957ee2c994e89ac47320c0ef86c42fb14c88ec3a017908c02d00c400001f952102c294809aa47920e8ee46b42ff14808d43be18308d82e80b800001f94c2b2c1946497645b1fe8e806922e514888e43b418808e03100c200001f946412c614ac98846a1ff0e806782e1140889839016808382bc0ae00001f940292dc15449fc4a02238f8070431a16089403ee19009a03500d400001f93a162d9957c9f64a321f0f946f6321156892c3d2188098033c0ca00001f934512b2941093e43e1f70e3867e2de14488b03a217e09283080ca00001f92e6f2c494bc9a047d20d8ecc6ac2fb14a88f83be17f08d82ec0c000001f9288f2c3146498c4612048edc69e2f214a08ac38416c08b82e00b600001f9229a2cb94d09924612018e8c6762e914608d83bc18e09883140cc00001f91c7e2dd955ca024a321b8f946ee2ff15489483f6191094834c0c800001f9166c2d515149e04842170f506e231615489283d618f09403140c600001f910a22b7947097a4642078ecc6b030015008f83d018409502ec0be00001f90acb2bd14689644591f90e606842e414808d03a217608c82d40ae00001f904c82d095049ac4782088f006c22fe14e08f43b216808802d40b600001f8fecb2ca14c09a446920a0e9c6b62fb14988f83be18008f82e00ba00001f8f8a82e7157c9e84a221e8f806da320156893c3d618808c02e00d000001f8f2c32c394e09aa47a20c0f2c6d430c15009043ae17709002f40ce00001f8ecc42c914d49c64862158f306c22ff14e88e43ae17708d82ec0b000001f8e6b92da154c9e24962168f1c6c230315208ec3c417909203140ce00001f8e0d02c994c49a647d2128f206bc30315509143c017d09183180c600001f8dafc2be14849724561f78e6c68a2eb14688b43aa16a08982d00aa00001f8d50d2cb14f89a64762040e8868c2f014e88fc3c018409003000ba00001f8cf1e2c914b899e4622060eb46a42ee140087c38416708682dc0ba00001f8c93a2c114849a646b2040ea869e2f814608c43b818609082f80c200001f8c3272d415389ce48220e0f086ba2f414f09043bc17b09102f80b000001f8bd1f2d195289ce4892160f106d030814e88f83c617c09183180ce00001f8b76f2a793c89344471f20e0c6522cb13c088839a16c08302c40bc00001f8b1922c0149c99246a2060ebc6b82f914c09143c818909383040c200001f8ab802d915609ee49b21b8f346dc2fe15688f43be17308982b80ae00001f8a5772d295189ca4882138f406e831015789343c217e09202f80be00001f89f8f2c0147c96e4541fe0e806962f214d88cc3a617108882ec0bc00001f899b72ba947c9a04742090edc6ae2eb14688d03b417f09203240d000001f893d12c494d49aa47e2110f3c6fa32115f09683f2191090830c0cc00001f88de92c594dc9a647220b0ed069a2ec14808c43b6180091031c0c600001f888162b3141c96e4602050eb86b02fe15208ec3b418009083080c400001f8825b2ab13e893a4401f30e046442c1130883035815407d027809800001f87c602cc14c89984652020e806722de13e08c039c18009202c80be00001f876772c814dc9bc47c2098f006b22f915508e83c017709002e00b800001f870af2bb946897c45b2000e746922f014488ac39e17508d82e80cc00001f86ab32cd15109ce48d2168f386c22fd14f88d839e17608b83080d000001f864982e195789e448e2130f4c6da31b15c89303cc18309402f40c2000 else 0x1fb54dd2ce95309e04912190f1c6c030015289183c817d09082d80a000001fb4ede2ce94fc9ba48420d0ee06c22fd14e08e83a817d08982d40be00001fb48f92c214c498e46c2058eb86982ea14588d83a216c08c83000cc00001fb43112c794ac9864582040eb068e2ee14488b03aa17f09503200d400001fb3d352b9946898a4612038e746882ef14888cc3b2181095830c0c400001fb37522c6149899646c2098ef86b42ee14508b439e16a08882dc0ba00001fb31502c694bc9a246f2060ecc69c2ea14788d83c618309183100d200001fb2b882b614489664592000e606942f314e08ec3b817909283200c600001fb25a12c694d49aa47420a0ed46ae2f714f09103c618c09483240d000001fb1fe92b0940c9564451f50e5c6762d914408d43a216908f82f80c200001fb19fd2c814cc9ae47d20a0f146c630b15308fc3be18809603280d600001fb13f32d715449da49621b0f586ca308154893c3e819409683100c400001fb0e282be146496644a1fb8e506802e9143086438616b08682d00be00001fb085e2b114089444461f68e2c65e2d113b889039216508502c80b000001fb02532d115189da48f2158f206c630415289243d018409683080c000001fafc5b2cf94ec9ce4872128f186d831a15889483ec19b097030c0d800001faf69a2b5143896e45f2018e8869a2ed150090c3ce18c09583000d200001faf08f2da15489e649a21d0f7c6e831816309983f419309c03200ca00001faeaa52c794bc9ac47c2120efc6de30014c087c38415f08602c80b000001fae4b52c6149c9964692060ed86ac2fe15009303de18709482d40a800001fadea22d415649ea48b2190f406d030115509143c418d08e82d00ba00001fad8d02bd14449524471f78e406782e013e088439016508882c80b200001fad2f62c694e49c248320f0ef86b02ed14a88d03a817208a82e00ac00001faccfe2d194f09be4792100f186de30c15089043a817408802f00be00001fac7312be948898a4672020eb469c2f214488a039e17d08702cc0ae00001fac1332cf94f89c64882188f546dc30d14e88f03aa18109382ec0c400001fabb4c2bf149899046b2040eb46982ef14488b43ae17908e82c40b400001fab58d2b3942094c44b1fd0e686702d3137887c39617608d03140c000001faaf992ca94b49a446f20c0ef06c230115108dc3b217608802d40ba00001faa9832db15689dc48d2120f2c6e431015509303e6192095832c0cc00001faa3782d315049be4812120f3c6de30f15a09443de192092031c0bc00001fa9dba2b013e093c4471f68e6867c2e914388b83b017308902fc0d400001fa97ab2d7953c9ce4862158f2c6d6308152090c3cc19009503100c000001fa91be2ca94ec9b24782050ed06c22f815a095c3e018709202f80b000001fa8bd52c994ac98846e2090eb86ba2fe15289243be17a08d82e80b800001fa85e62c6149498e46a2080ebc6922dc13f887039e172092831c0c400001fa7ffe2c994e89b248020b8e946902e514708c43a217a090832c0d600001fa7a012cd95049b44852138f206d631215889403d618609102f40b800001fa74442b4140895e4501fe8e986a82fc14b08f43ca18009103200e200001fa6e6a2c094c49ac4852130f186ce306156893c3e018b09082f00a800001fa686d2ca14f09c047c20b8ed46aa2fa14f09183bc18008c83080d000001fa62882bd94909964722078ec86a02e914608a83b617f098032c0e600001fa5cba2b9944c9824642070e9c68c2ea146087838c15e07d82bc0b600001fa56b32cf94e49aa47c2100f146c830a157891c3d018a09083100ce00001fa50ea2b3145c97c4632048eac69e2e2139086838415e08402d40b800001fa4b252b6943496245c2090ec86b62f014a88dc3ba17b08d82fc0c600001fa45392c994b499c4652050e8468c2ea14a08d43bc17e08c02e40be00001fa3f3c2d114d099447320b0ee06b82f914a08ec3b817e09102ec0c000001fa39482c814d498846a2098edc6ae2fc14e88f83be18209503240cc00001fa33372da954c9de48f2158f2c6d02fc14e88f43bc18309482f80c400001fa2d572be946c96645b1fc8e786682da13c88a039c17309503300d600001fa27562cb94d09aa4832130f186c030014d88e83a817408f02f00c800001fa21632cd14e09b847f2100f086b82f314b08d83a018109182f80c600001fa1b542d815449e64942168f6070831715d09343de17f08c02e80ca00001fa15502cd94f49be47520c8ebc6a62f214b09103d018108802e00b400001fa0f762c214a099e47020b8ebc69e2fc14f88b838e16e08902e00a000001fa09832c794a499246e2070eec6a82eb14588bc3ba17708c82bc0ae00001fa03922c794a89904652090ed46bc30114d88dc3b217f08f02fc0bc00001f9fdad2c0946897e4632038ec86962e9143088c38616708702b00b400001f9f7d52bc147898447220b0ef06ca308155891c3cc180096031c0cc00001f9f1f22ba14589704552000e786862d9143888838a16608602f00c200001f9ebf12d2953c9ca48320f8efc6b830214f88f03c218b092831c0b000001f9e60a2c194949904732090ed06a62f714788d439417308a82e00c600001f9e02c2c414a09ac4622060ef06c62fb14d88ec3ca18409283080c8000))) else (if i < 328 then (if i < 326 then 0x1fccff02cd94d89a84702060ee46a82f615309403ec19609a83440d000001fcca272b6945c96845a2028e986a82fa14b89003cc18c09303100d800001fcc42c2ce94f49a44812120efc6da30b15209203da19109903140ce00001fcbe4d2ba14449724641ff8ea46962ea14988c83b017e08c82f00cc00001fcb85c2cb14c89b44902150f4c6f031215008e03ba17c094032c0d000001fcb2512cf15109ca48821a0f706f230d156092c3cc18409503240c200001fcac732c414bc9a04712058eb46982f714b08f83bc17308e02f80be00001fca6ac2b7146899045a1ff0ea069c2f414988e03b017808703080ca00001fca0a12d695449cc4902160f286c830315009403d618008f82bc0be00001fc9ac02c114ac9ac47220b0ef46ba2f414508a439816a08802b40b000001fc94c52d014f49b84852140f206cc31215789183d018609683300d200001fc8ebc2d2951c9be47e2178f0c6c630415389083c217a08b02c00aa00001fc88c42ce15189c447620c0ec86b42fb14c88e43b617a09103000cc00001fc82cb2cf94f49bc48120b8ec46bc2f615088f43c217c09102ec0b800001fc7d032ba945897c45c2000e8066e2e8142087c39616f08202c80b600001fc77192c494809a847a20d8f106da31415a89343cc18208e02e00ac00001fc712d2c914dc99246d2040ebc6942f914d88e43b217808c82f40c200001fc6b472c314a89a647520d8eec6a82fe14f88f43b8187096031c0ae00001fc657a2b394549624581fd0e7c67e2f214708c83a217c09003240c000001fc5f832d3950c9dc4952198f646de30915589083ce18c08f83000ce00001fc59912ce14dc9a847a2118f506e631315b09483e2192096031c0c200001fc53a42c614e09b64892178f586f030e15809403e219209503200c200001fc4db12cd94bc9ae4782100f006ae30014e08e43b017c08c02e80ba00001fc47a12d515289de4792068e986962ee14908fc3a816e08c02f40c000001fc41872db15349da4902198f306e831915589003b818009183340e000001fc3bdd2a513bc9384451ef0e4c66e2d413e888c38817308c02f00ac00001fc35c12da95209dc4902138f3c6e630f15a09443d6181097033c0de00001fc2fc62c794fc9be4802100f086ba2fe14c88f839c182090830c0c800001fc29f42bf947498a46b2070ec86be30a154090c3b017909503400ca00001fc23e32d495489d04802140f306da30015208f03c618509683280ca00001fc1ddd2d914e89bc47e2098ed46a82fe14f09043c217d091030c0b600001fc17e92cd94f49a246d2080ee06ae2ec14508e83b017408883080c600001fc12252b5943096e44e1f98e486662e414408c438e16c08d82f00c000001fc0c432c294ac9a24782108f006c030115008cc3b818409103300c400001fc06752b9143c9624531f80e5c66a2df146889438816408702cc0bc00001fc00a22bf146c9764662038ea86862ea14888dc3a617108a82f80ca00001fbfab52c614c49a44712088ee06b02ed14c08f83b617108b02ec0d200001fbf4c92cb14e89c447320c8eec6ca30414f89183c017e09102ec0c200001fbeec02ce14e89c847c20e8f286d830b15a092c3d218f098033c0c200001fbe8f82b2145896a45f2048eac69a2fd14e09203c218c09583200cc00001fbe2eb2d3155c9f44a221f0f546fc31315909243d018109082fc0ba00001fbdcf82c414d09a646d2048e786882f114708c839a16a08502e80ba00001fbd6fd2cc94d49a047820d0f106d030a15088e03bc183092830c0c800001fbd1182c3147097e4682090ebc6982f814d88ec3a016d08602e00c000001fbcb192cd15109c04802118f1c6c830115209403e819909b035c0d000001fbc54a2b7941c95c44d1f78e6868c2ea14308bc3a817608882f00ba00001fbbf432d515149c847d20e0f206c82fa14e08e83a217608802cc0c000001fbb9762b7945497845d1fe8e6c6822e6145889c38817308402f00c200001fbb35e2d895409ea49121a0f346e831516289983f219309402fc0c200001fbad682cd14ec9a446e2038e846902ef14588cc39e16d08802f80c200001fba7b12a693e09504471f80e686962ec143888c39416e08502c80b600001fba1d52c2949099a46b20c0eec6d230214e08e43b017308a02f00c200001fb9c1f2b1942c94043b1f40e206562cd134085c37615908682d80ba00001fb960e2da15409e448c2138f006be30914e89003c617d09103000c000001fb90362bd947c9884632048e946902eb14f08f43d4189090030c0d400001fb8a302d194fc9c848b2160f346f431b16209803ea19209703140c800001fb844b2c814bc9aa46e20d8ecc6ac2f315009043ca18008e82f40be00001fb7e462cd14e09b246f2068ecc6b82fe15089243d418f09183040be00001fb78522c994c49a24712050e9067e2e114608a03ae17108882fc0b400001fb72592cc94ec9d44922160f246d230e15509243ba18509683040b800001fb6c582d315189ee48a2188f106ba2fd150890c3c018309503000c400001fb66a02ad13fc95e4571fb8e5c6742d814388a039416e08802cc0c600001fb60b12c514a49984772088ed46962f314788dc3a6179082829809e00001fb5acc2c594bc9ac47f2118f146cc309157090c3c417f09282f00bc000 else (if i < 327 then 0x1fe4a462d095049de4872170f406f231b15b893c3e418f09683400be00001fe44392cf14d49c04862120f0c6b830315589403cc17f08e82e40be00001fe3e722b6942495644f1fc0e906842ea149089c3a416908c83000d000001fe389a2be948c99e47220b8ee86b22f614a88b03b017908e83040c800001fe32b32be14789764571fe8ea46aa2f814a08f03b817508b82d40be00001fe2cee2b714389664561f78e286642db13c887437e16608602e40bc00001fe27222b414349724531f60e2c6622d0136083835615708182c80b800001fe21312c494889844692020ebc6a82f014588a43a017708f83140d000001fe1b3d2d095049c048320e8ed06c430015108e43ac17a09283080bc00001fe15572c614cc9a847e20a0ebc6ae2f714b08c03a216808a82cc0b600001fe0f772bf94a49984692070eb86962e514508c83a217a08a82d40aa00001fe09642d515249dc48720e8ef06bc30315208d03b417308a02ec09e00001fe03522d395109c84832120f146c6309150891c3c218209002f00ae00001fdfd5a2d495049b847820c8ed06c0300153892c3cc18108f03140d000001fdf79d2af941896243c1f20e346822d313d088038216608782b40b800001fdf1b52c414b89ac47d20c8ef06ae2ef14888c839e17908b02d80ba00001fdebe12bd946c9884631ff0e9c6902e514508ac39e17508b832c0c800001fde5f02c994c09c44812120f386da31315589383d218609203040ba00001fde0182bb949097445d1fc8e9068c2ea13f886c3a417808782d00c600001fdda1f2c895009c447e20d0ee86ae2fb14d88d83ac16c08803000bc00001fdd4202cb94b099446a2020e8868e2e714808c83a217208e02e80ba00001fdce022e39584a044a42200f7c6fe31c15889483e619509a03340be00001fdc80a2c894a09a446c2000e946962f114788c43c218108f83200de00001fdc2382ba94389444481f00dfc6562d4139884c36015808302c00bc00001fdbc5d2c2947c9804672068eac6822e114008903a416b08182bc0b600001fdb6912b3944895844f1f50e6c66a2d513c88b43ac17b08c83040c400001fdb09b2cd150c9bc47a2098edc6b22fe14e88d03a617008b02e40bc00001fdaab72c2948098845b1fd0e4866e2de13f088438416308682e40a200001fda4d02c894ec9b447f2138f306ea30c154894c3e819609983280c800001fd9ef62c014649884672038e7467a2f714a08d43ce18308f03280ca00001fd99292b8144c96444b1f98e346782d013c88a039617b09183180c200001fd93572b6942496244f1fc8e806802e314488c03b017b09482f80bc00001fd8d7b2bc145496044e1fe0e606742d913a085838a17008602dc0b600001fd878d2c494bc9aa4672090ee46b630214d08d83d218809182ec0ba00001fd81b22bd945497245b2060ec86c0301155892c3c418c09583500de00001fd7bc72c614809a247920d0ef46ba2f614988c43a817b094831c0c400001fd75de2c594b099e46c2070ec86b22f515108fc3b617508c02d00b000001fd6ffe2c694c49a047220b8ebc6a62f414908d83b417308c03100b800001fd6a052d114d49ac4812120ee06b22f414908b43b017308e02c00b400001fd644c2b093d093a4451f18e3066c2d513e086c38016a08402c80b600001fd5e662c194a899a4691fd0e9868c2d913b087438616c08502c40ae00001fd586a2cb14ec9b848020e8efc6be30415008ec3c419309c03540d800001fd526d2cb950c9b247e2098ec06a02f714a88d83b418609703340d200001fd4c972c1944c95a4451fb0e7066a2e114608d83a417808a82f80b400001fd46a92c694ac9a24642048e9067e2e414808bc3aa17909302f40c000001fd40a12d695509e448a2148eec6be2ff14788d439016e08702b80c000001fd3ac02ba145c99246a2060eb469c2ec14488c03a217c09103240c200001fd34d02c894d09aa47420d8f146b02f914d08f43b217a08d02f00ac00001fd2eb22e195a0a0e4a021c8f4c6e0310157894c3f018f09903300de00001fd28ad2d195009be47920d0f006ce30715109043ca18509483140d000001fd22c52c894c09a047220e8ef46c4303155892c3e219109c83480d400001fd1cce2cd94d09b846c2030e906a42f014708dc3ba17e09082e40ae00001fd16f02c3147097045f1ff0e7067c2e1143089c39e16808a83000c600001fd110a2c194909864511f88e4067c2e414408b039617808e02ec0ae00001fd0b0e2cd14c89a446f2098ef06c62fe15589243d418909183080c000001fd05272c794e49ae47b20d0ecc6ba2f9151891c3ca18c09703300c600001fcff512c4947c9924732098ed46ae30114e091c3c418508f83180d000001fcf9622c214d89a248220c0edc69c2eb14608e83bc17b09303380d400001fcf36a2d015089ca49b2220f6c6de30915109003bc18709483340ce00001fceda12b7141894644d1f28e4867c2e213f088438616a08482e40bc00001fce7c42c0949898c46b2038ea06aa2ff15188fc3bc18408882e40c600001fce1ec2c1147c98a4772098ecc6a02ff14a88e43aa17108b03180b400001fcdbde2db155c9ca4842110f1c6be30515209343d019709903200c400001fcd5ef2c494a899c47920c0ee86bc2fa14f89203b017a09002f80ae000 else 0x1ffc3e42c694a499c46a2058ec068c2ef14688ac3aa17908c82c80ac00001ffbdfc2c1948098e4782088ea46ac2f414f09283ba17f09002e40c200001ffb8102c3147097e4692070eb86b22e914508c83ae17708a82bc0a000001ffb2612aa140495a4521fb8e606782de13b088039c17708d82f80ae00001ffac812bb146c9764612008e9869e2ee14788c83be17e08f82c40b400001ffa6582de957ca0a4a12188f246d231115789343cc17d08d03000c000001ffa07c2c094a497c4632078ec06942f614c88e43a817b08882f40b400001ff9a5e2dc15309c247d20f8eec6ba2f915709283cc185095030c0b200001ff947b2c014a498c4682080ec06a02f514b88f83b616f08482b00a200001ff8e762d715309d248221a0f406f230c14e08e03c218109503180c000001ff88d02a813a493043b1f00e0065e2d413d086c38616508982e80b200001ff82f22be947096e4541f88e706922ed14c88c83bc18e09683080c600001ff7d1b2bd947096446e2090ed86a42f714c88b438a16608302d00aa00001ff77452b514509664611fc0e9068a2e814288bc3aa17b08e82dc0b200001ff714d2ce14e09a647e2128f146c82fd150092c3e818e096032c0b400001ff6b752bf14649964642038ee86a02eb148089439416b08382b80a000001ff657b2ca14ec9ac47220a8ed06a62ee14d89243d418108c02cc0c600001ff5fa12c1148898a4642028e746602d2139884c37815e08482a80b400001ff59d12b8946098c45b1fe8e786862e3143088838216708682f00c800001ff53e02c594ac9a646f2050ec069c2f214b88f83c618009102f40ae00001ff4df52c914fc9d648d2110f186c62fb152891c3d418908f82f40ce00001ff48192bf94b099a4722098ec86aa2fc14a08d83b018309003240c400001ff42332c594b099a47120b8ee46a82f714788c03a615d08282b40b800001ff3c402c814b099c47420a0f086c02fc15489183ce181090030c0aa00001ff36552c895109ba47a2120f1c6c630815589143c6191096833c0c400001ff308c2ba946498846b20c0ebc69a2f614408ac3ae17508c82d40ac00001ff2ac72b794909824612088eb46a62ff14b08e43a817809002f40c000001ff24ea2c014949b04702008e7c67a2e714988b839416c08602c40be00001ff1efe2cc95109e04892130ee46b02f714f092c3d418908e02dc0c400001ff19112c594c09a447120a0ed06aa2f114808b43aa17e09183380d000001ff13182cd14dc9aa47220c0f106ce30114a88e83c018008d031c0ca00001ff0d5a2b2942c9504501fa8e786602de140086c38816508b82f00ce00001ff07722c3146096645d2020e706682d513d886839016b08c02dc0b800001ff01a32b8146c9864612008e9468a2ef14508c43a017908d02ec0cc00001fefb732e595a4a1a4ad2280fb06f432515d096c3ee19609d03500d600001fef5912c4149c99447320b8ed86ac2ee142089439a17508c82f80c800001feef842d795449f249a2210f606de30b15789283ba17b08f03200cc00001fee9b92b5944c96c45a1fc0e7c6822dd13f889439016d08882e00bc00001fee3d22c614a098846f2088eac68a2e614588ac39e17508882cc0c400001feddec2c514c098e46b2068ea06962f414e09143bc18309482f80c000001fed8192c0948897e45d2020eb06b22ff14f88f83b618709483040b200001fed2302c994c49ac4692058ec06a430315189143ca182093030c0cc00001fecc462c994b89ac46c2070edc6bc2f714a88d43b417409003200b600001fec62e2da954c9e649f21f8f606e631015d89483e218f09483100be00001fec01d2d815189d448020f0f3c6c42fc14e89003b217608d03040c200001feba7d2a193b492643b1ee0df86602d313c887436a15807d027009e00001feb4842cd14e49b847d20d8eec6bc2ff14a88fc3c017508a02fc0b600001feaec92b214089544491f88e7867a2d2136086037816808782d80b800001fea8d52c794cc9b84812130f0c6ae2fa14b08f83b616d08703000c600001fea2ff2c094b49a446b2038eb86922e914608a039417508c02e80b000001fe9d092c794cc99c4612008ea86902e414808dc3b417f08b02f80b800001fe97182c994f49a046e2080ec46a42fc14f88e83c018909282fc0c200001fe91412c1946497445f2048ec86a22ed13d888438c16108702b00b200001fe8b5b2bc149c9a247120b8ee86a02f014988cc3b017908a82ec0aa00001fe857b2c014b099846c2088ee06a82f614a08dc39a16e08782c00a400001fe7f9b2bd948498c4642010e8469a2e614f88fc3b217408e02f40bc00001fe79c42bd945c97646620c0ee46c42fd14d09003c818e09803240ca00001fe73cf2ca94fc9c447c2120f106c430815289403e219909983680d600001fe6e062b5944c97c45b2030e8c68a2df14708a438c16f08782dc0b600001fe67f32dc95109d64972190f606e2315159094c3f219509b03680d000001fe62132c3148c99c47420b8ec06942f014a88c83a617308802f00b400001fe5c112d115409ce48a2148f046c62ff15209143e0187096031c0d200001fe56372bd948498246f20a0f046ca30815409083ba17b08b02ec0bc00001fe50492c314a09724531f48e6c6802df144089c37a16708c82ec0d4000)) else (if i < 329 then 0x2013f212c214709844642028e9c6aa2f114b88d83ca17f08b02dc0ac0000201393f2bb945896a45e2020ea46982ef14688c03a217f08e02d00b4000020133752b2942094443d1f20e386482d114088b039c17c08c83000c400002012d862c794e09b048620d8edc6c82fa14b88fc3ac17f08d83280d4000020127af2bf94b499847720b8ef86b62fc14b88cc3b417908e83140c6000020121b62d315289b84802140f186da31115a096c3f8192090830c0cc00002011bdd2b4941896444f1fa8e406922e413f889039616608882c00ac000020115db2d295189cc4912138ef06c02fa14d08d83c218709403100c000002010ffc2c394c499c4692080ed46a02f114b88e43b617908882f80b6000020109f02d915389d848120d8eec6c830515289103c217f08d82ec0c00000201040c2c2949098e47020a0ed869a2f414a88d03b617f09083100cc0000200fe172cb14f09c447f20b8f046be30014d88f03bc18009202f00b60000200f8382be145c97244d1fe8e7c6922eb14888cc3b217508a82c80b20000200f2242d815489d449021c8f546f430f15809443ee19209683100d80000200ec292d015149aa4752078ed46982f914e88e83b217a08e02fc0c00000200e63b2c394a498a46a20d0edc6b430114f08f03b217c08f82fc0ca0000200e0522c714d49ca47e2110f006ae30114b89143c617b08d03040b00000200da6e2c294a899045d2030e906aa2f014488c03a417f09383480b80000200d4832c994d89a847920b8ee46bc2f3142888c38816e08a02d80b40000200ceb82bc94749804642018ea869a2ee14708c839816c08702bc0ae0000200c8dc2c0149c9904692060eb467c2de14388a8390162085829009c0000200c30a2be14789704632070ea06b82ff15289303cc18e09503280d80000200bd2c2c3948499446a2068ea069c2fc14f88fc3b218b094834c0d60000200b72e2d395189e84902128f0c6ce30414b88d43be17d09203180d00000200b1562c594989a646a2070e946922ec14908a839e17608982f80c60000200ab442d595589ec4932180f306ce2fe15088dc3aa17e08f83100ae0000200a55f2c794a89964672078ecc69c2e9143888037e16108282b80b200002009f8e2c0145c97e46920b8ee86b830414d89203c217908e82f40be000020099772dc95749f849d2160f446dc30315009203e4195095831c0c0000020093a52be149099847320f0efc6b62ff15588e83b817708902bc0b800002008db52c494a899846c1fd8e6067e2ec14408b43ba17e09482f40c6000020087b72c894d49ae47e2140f346c430614e08a83b417e08e83180d8000020081b92cd94e09b64872190ef86c42fd15188f43b817608982dc0b600002007bee2b714509704511fb8e506742d2139887c38616a08902d00ae000020075fd2cc94f49ba47820e0edc6bc30015308f83ce17308902ec0c2000020070112c1949499447020b0edc6c42fe14a88c439816b08682d80aa00002006a192d294f09c04872120f106c22f114808e03a417909302fc0be000020064312bd14a49a647a20d8ee46ca30715509243ae17608e02d80b400002005e1c2da15649e84982218f746e030e154090c3d818e09102fc0ca000020058582b2945895a4561fb0e746742da13a087037416108202a80b0000020052852b994409664581fb0e8c6822dc14588c43b217108e82dc0c000002004c932cd94fc9d047f2100ef46ae2f114909003c218909283340d8000020046702e49588a0049b2270fa470232315d09543f8193096034c0ce0000200406b2d495409f649f2200f8470031e15f89584001a309c83400d200002003a632d295349c448120e0edc6ba30014f89003ac17408b03140ba000020034602ce95089c048120d0f246c42f114908a039416708b82ec0b400002002e792c914d09b047b20e8efc6c42f5151094c3d418d09583180c20000200285a2de95909f249421a0f4c6d430615309203d018509283180be000020022712c394a89a447720d8f086c02ff14e88e839c17308782d40b000002001c902c0946c97e4591fb8e5c6942ed14a08c03ac17b08e82d40b20000200168e2d395049dc48c21b0f546f6318159895c3ca18a09703240d6000020010ba2bc145c96e4632000e9c6962ed14688bc3b617e08e82e00b400002000ac52c694b49aa4752050eb06a42e914508c43b017c094030c0b4000020004e92c194849944641fc0e746842dc14288843a417408902c00c400001ffff1c2bc94649744571fe8e7867a2e614208b03a417108983000b000001fff9072db15409d44892148f246c430015189283e818f09583340d000001fff3552b1940c9404411f38e386622e313d88bc3a618309403080b000001ffed402dd15709fe4a021f0f686ea31615608f03c817e08d03080d000001ffe73f2d395149d64862158f286de308155092c3d818f09303040c600001ffe1782b4945c97c4592010e9c6842e114088b439017108c02f40b000001ffdb8f2c514c49a84752108ef86ac2ec14308a039616d08702c80c000001ffd5922d094f49c64842118f3c6ec32215f898040419109503080b600001ffcf9b2ca94b099846b20c8f046c8306152892c3dc19009883200ce00001ffc9da2b4943896045b1fb8e6067c2de14488b43be18509803380c8000 else (if i < 330 then 0x202b9f82a993e493643e1ea0e046542d714588b038e16d08a02ec0c00000202b3f72cf15049b847e20e0eec6b62f414388a839e16d08c83000ca0000202ae352b6147098446a2010e9067a2e9143889039817408d83040be0000202a85f2ba94549724581fc8e6c6882eb14c08ec3c418009102dc0ba0000202a2782c594bc9a44672070eac6a82f914d08fc3c018909682f80ca00002029c782d314e49ba47d2120f206ce30515909583f41a60a003680e80000202968c2c894ac99c4722088ecc6a82f314508c43a016c08782cc0b00000202909d2c4147499a47820a0edc6b230715389143e618009082e40b200002028a8c2d9952c9c84812148f1c6b62f214d09303cc18909283140cc000020284c82b5142494e4561ff8e906822e514608d83a618408e02e80ae00002027ef32bb144095e4481f58e306402cb13e086037615b07e82940c4000020278ff2c594a89a246d2068ed86ac2ee14308b439e17809103000d2000020272e02df955c9ec49621a0f486ee31816089743fc19a099833c0ce00002026ce02d715449e248a2170f386e8309157892c3e018d09803540d4000020267052c2148c9a44752068ed06aa2f114f09243d218d098834c0ce000020261232c5149c97c4642060ebc6a02e514488b038e15d085029c0be00002025b502bb94809944692018ea069c2e9142088c37a15f08902b009a0000202554f2cf14f09cc47f2118f3c6d031115809403de19809703280dc00002024f7a2bb147c99247820f8f186b630515308ec3c817908e82f40c40000202495d2dd957c9e04952168f206be2ff15088e83b017808b02d40b0000020243832ba948099045d1fe8eac6982e314188ac3aa18008a82e00b200002023d8d2c794cc99046d2058eac6a82f614e091c3c817b08c82f80b8000020237a72c3147c9684571fb8e786802e0140089839616b08882d40ba000020231e62b1941c94c4521fe8e746782e114488c03a617508c83080d600002022c102c1147c9864672088ee46a830715309103ce18708f02fc0bc000020225f92dc952c9ba47d2140f046c4304154893c3d618609183180d8000020220342b994749904621ff0eb46982f814d89043c418409383140be00002021a4a2c294d49c047f2110f286d630b15108fc3d0184092032c0e6000020214562c714e89a847c2108f146c22fa14e88fc3c218009383040c600002020e602c894f09c247720e8ef86b82f614888d03a417308902bc0b20000202087f2c1949c98c46f2040ebc6922dc14508c83ae17308f82f80ce000020202822cf94e89bc4852158f446de30b156892c3d018f09783240d20000201fca22c814ec99c46e2080e8869e2ed14708d83b216d08f03080b20000201f69f2d415249c648520f0f146ae2f715009043ac17a08f02f00ca0000201f0c22be149899847120d0f106c230c15408f43c617b08f02f80c60000201eae02c594c499446f20e0f086a82fa14b08d43a417408e02e40b60000201e4c92df9588a124ac2240f8c71632616789b44101a809c034c0de0000201deba2d9952c9d24782110f246c42f514f08f43be18008d02d40b20000201d8e82bd945497e4581fc0e386802e014188e43ba17f091030c0d80000201d3072c2949097a45e2000e546782e514408bc39617908e02e40c00000201cd232c5148c9744581ff0e7469c2e714c08d039e17108682b00ac0000201c7612b8943c96645e2000eb06882ef14708bc39a17508b82c00b00000201c1582d095289b847820c0ee86942f314e09103c018208e82d80c60000201bb782c194889a84772100ee86a22f514909043a617808e82d80ba0000201b5922c594a09804652040e9869a2f314d08ec3b417f09082d40c00000201af912d315089ca47c20c0ed06a22f314208cc39016908b82f80ba0000201a9a32c494d09be47d20d8ee86b630715409143c618a09503440d40000201a3ae2d094f09cc4922198f486c030315109003ba17e08f02ec0ba00002019dea2b413e894844d1fa0e7c6882e3140089837e16e09083080c0000020197fb2c894ac9a245f2020e586942e114508bc3a417609082f40c8000020191eb2d7952c9dc4872110f206d830515209303dc183098033c0d200002018c012c114a098e46f2050ec46a42ee14588d03ac17908802cc09c0000201862b2b894509744581ff8ea46902f514b88ac39e17108602f40b0000020180352c994d89c447920b8ecc6a42f915188f83be18909483080ce00002017a272d395349ca4882140ef06be2ff14888c83aa16c08b82f80b6000020174422c3149c99a47d2158f386ce30d15a89403d418c096033c0d600002016e422d315089ce48c2140f146d830b15989243da18f09683100c20000201685a2c794c898e4672010e806842e4140889438e16e08682bc0ba0000201626b2c914dc99a46d20c0efc6b22f514a08ec3a217c09083040c000002015c7f2c814cc99c4652060e986942eb14408ac39e17009383040c8000020156852cd94dc9ac47320a0eec6ae2f714988b43aa17f08f82c00b2000020150a32c414bc9a44702108ee46b630714f89143da18909283300c800002014ad72bb945495a4471f80e446542d613c08a438615608082b40b00000201450e2b9945496644f1f88e4c67e2de140888037815f08102bc0b0000 else 0x203a079000148497e4642050eb06802e714288ac39c17108d02e00c800002039a952c594bc9924671f70e446722db13f088c39016408782ac0a8000020394a12ce14f89c44862130f146d830515308f03b817908982ec0c200002038eac2ce94f49b44832108f286ce30714f88f83b017e09083100ca000020388cf2bd148098e47020a0ec86c22fe15189143da18709383340cc000020382f62bc94a099046a2098ef06c830315109183bc18309403300ce00002037ced2d6952c9e849421b8f386b430414e88f83b217a08c02e40ac0000203771b2bb944896044b1f50e4066a2d9140088838016b08202d80bc000020371422be948c98846b2050ea86a430215309003ac18109002d00b600002036b712bb94449664531fc0e8468a2e7143089039216f08c03280c80000203656d2d014ec9b047b2108f146d231015589343d618509002f00ae00002035f802c814d89b647520e0edc6b22ee14788b039a17308682b80b0000020359b12b8146c9664551f68e406682e214288a43a617608b82d00c8000020353b62cc14b09b047120b8e986842df14688e43a617308f82b80bc00002034dc82c714b89ae47d20e8ee06c831215789183cc18008d83100b8000020347a42de15849f04a021b8f5c6e031215b09443e619409303080ca000020341a82d095089bc4832158f1c6d630f15688fc3c2183094031c0d000002033bce2bf94649824632040e9c68a2e8144089039217708602cc0c4000020335ca2d214f89c248520c8f006b430315008f43d018709503300de0000203302d2a293ac9284441f20e3c65c2d013e888439017108882cc0b200002032a542b614409664551f70e446782ef14d89043c418308f82d40b0000020324462da95089ba47020e0eec6b82f014a88a03aa16f08d82e40b000002031e5e2c914bc98e47420b8ef46a22e614588ac39417408602d80c6000020318762c2149099a47020c8ef06be2fa14a08d83ac17908d02e00c0000020312812cd14f89b847a2060ebc68c2e013e88b03aa17909083140ce00002030c8c2c914f49d04902188f3c6fc32616509a03ec19f09b03680d2000020306ba2b6140c94c4491fa0e4865a2d413c088037a16408282b00aa000020300ac2d515189d048520d8ed86c02f914d08c83a2182099032c0c60000202fadb2b794549764561fe0e6c67e2ea147888c39216f08602b40aa0000202f4e92ca94c09944702040e8c68e2eb14908d43d0185099832c0ce0000202ef1d2b4943096a4572010e946902eb14788c83a217d090831c0ce0000202e9172d415149bc47820a0ecc6b22f0145088039416208802ec0ae0000202e32b2c414b89a647520c8ed86a230014f09043ca17f09403180b40000202dd3a2ca94c09de4842118f206a42f415188e439a17609083140c20000202d7452c694c499246a20c8f006c430915389183ba18308e83000c00000202d1742b493f494c4481f88e586762da14608c439e17908a02d00c60000202cb6a2dc1580a0c4a72200f386ee30614f890c3b818709183280c40000202c57f2c914f49ac47f2118f146bc30415409003d018409603440e00000202bfbb2b5142096e4601fc0e746862e614888d83b817f08e82e00ba000)))))))))

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



private theorem b325482 : covered 325482 325564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325564 : covered 325564 325647 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325647 : covered 325647 325729 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325729 : covered 325729 325812 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325812 : covered 325812 325895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325895 : covered 325895 325978 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b325978 : covered 325978 326060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326060 : covered 326060 326143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326143 : covered 326143 326225 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326225 : covered 326225 326308 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326308 : covered 326308 326390 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326390 : covered 326390 326473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326473 : covered 326473 326556 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326556 : covered 326556 326639 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326639 : covered 326639 326721 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326721 : covered 326721 326804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326804 : covered 326804 326886 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326886 : covered 326886 326969 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b326969 : covered 326969 327051 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327051 : covered 327051 327134 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327134 : covered 327134 327217 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327217 : covered 327217 327300 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327300 : covered 327300 327382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327382 : covered 327382 327465 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327465 : covered 327465 327548 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327548 : covered 327548 327631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327631 : covered 327631 327713 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327713 : covered 327713 327796 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327796 : covered 327796 327879 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327879 : covered 327879 327962 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b327962 : covered 327962 328044 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328044 : covered 328044 328127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328127 : covered 328127 328209 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328209 : covered 328209 328292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328292 : covered 328292 328374 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328374 : covered 328374 328457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328457 : covered 328457 328540 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328540 : covered 328540 328623 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328623 : covered 328623 328705 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328705 : covered 328705 328788 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328788 : covered 328788 328870 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328870 : covered 328870 328953 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b328953 : covered 328953 329035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329035 : covered 329035 329118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329118 : covered 329118 329201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329201 : covered 329201 329284 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329284 : covered 329284 329366 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329366 : covered 329366 329449 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329449 : covered 329449 329531 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329531 : covered 329531 329614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329614 : covered 329614 329696 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329696 : covered 329696 329779 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329779 : covered 329779 329862 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329862 : covered 329862 329945 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b329945 : covered 329945 330027 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330027 : covered 330027 330110 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330110 : covered 330110 330193 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330193 : covered 330193 330276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330276 : covered 330276 330358 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330358 : covered 330358 330441 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330441 : covered 330441 330524 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330524 : covered 330524 330607 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330607 : covered 330607 330689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330689 : covered 330689 330772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330772 : covered 330772 330854 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330854 : covered 330854 330937 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b330937 : covered 330937 331019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331019 : covered 331019 331102 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331102 : covered 331102 331185 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331185 : covered 331185 331268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331268 : covered 331268 331350 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331350 : covered 331350 331433 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331433 : covered 331433 331515 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331515 : covered 331515 331598 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331598 : covered 331598 331680 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331680 : covered 331680 331763 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331763 : covered 331763 331846 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331846 : covered 331846 331929 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b331929 : covered 331929 332011 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332011 : covered 332011 332094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332094 : covered 332094 332176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332176 : covered 332176 332259 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332259 : covered 332259 332341 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332341 : covered 332341 332424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332424 : covered 332424 332507 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332507 : covered 332507 332590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332590 : covered 332590 332672 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332672 : covered 332672 332755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332755 : covered 332755 332838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332838 : covered 332838 332921 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b332921 : covered 332921 333003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333003 : covered 333003 333086 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333086 : covered 333086 333169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333169 : covered 333169 333252 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333252 : covered 333252 333334 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333334 : covered 333334 333417 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333417 : covered 333417 333499 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333499 : covered 333499 333582 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333582 : covered 333582 333664 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333664 : covered 333664 333747 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333747 : covered 333747 333830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333830 : covered 333830 333913 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333913 : covered 333913 333995 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b333995 : covered 333995 334078 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334078 : covered 334078 334160 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334160 : covered 334160 334243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334243 : covered 334243 334325 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334325 : covered 334325 334408 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334408 : covered 334408 334491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334491 : covered 334491 334574 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334574 : covered 334574 334656 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334656 : covered 334656 334739 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334739 : covered 334739 334821 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334821 : covered 334821 334904 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334904 : covered 334904 334986 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b334986 : covered 334986 335069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335069 : covered 335069 335152 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335152 : covered 335152 335235 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335235 : covered 335235 335317 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335317 : covered 335317 335400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335400 : covered 335400 335483 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335483 : covered 335483 335566 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335566 : covered 335566 335648 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335648 : covered 335648 335731 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335731 : covered 335731 335814 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335814 : covered 335814 335897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335897 : covered 335897 335979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b335979 : covered 335979 336062 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336062 : covered 336062 336144 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336144 : covered 336144 336227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336227 : covered 336227 336309 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336309 : covered 336309 336392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336392 : covered 336392 336475 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336475 : covered 336475 336558 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336558 : covered 336558 336640 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336640 : covered 336640 336723 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336723 : covered 336723 336805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336805 : covered 336805 336888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336888 : covered 336888 336970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b336970 : covered 336970 337053 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337053 : covered 337053 337136 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337136 : covered 337136 337219 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337219 : covered 337219 337301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337301 : covered 337301 337384 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337384 : covered 337384 337466 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337466 : covered 337466 337549 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337549 : covered 337549 337631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337631 : covered 337631 337714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337714 : covered 337714 337797 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337797 : covered 337797 337880 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337880 : covered 337880 337962 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b337962 : covered 337962 338045 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338045 : covered 338045 338128 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338128 : covered 338128 338211 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338211 : covered 338211 338293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338293 : covered 338293 338376 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338376 : covered 338376 338459 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b338459 : covered 338459 338542 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 325482 338542 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b325482 b325564) (joinCoverage b325647 b325729)) (joinCoverage (joinCoverage b325812 b325895) (joinCoverage b325978 (joinCoverage b326060 b326143)))) (joinCoverage (joinCoverage (joinCoverage b326225 b326308) (joinCoverage b326390 (joinCoverage b326473 b326556))) (joinCoverage (joinCoverage b326639 b326721) (joinCoverage b326804 (joinCoverage b326886 b326969))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b327051 b327134) (joinCoverage b327217 (joinCoverage b327300 b327382))) (joinCoverage (joinCoverage b327465 b327548) (joinCoverage b327631 (joinCoverage b327713 b327796)))) (joinCoverage (joinCoverage (joinCoverage b327879 b327962) (joinCoverage b328044 (joinCoverage b328127 b328209))) (joinCoverage (joinCoverage b328292 b328374) (joinCoverage b328457 (joinCoverage b328540 b328623)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b328705 b328788) (joinCoverage b328870 (joinCoverage b328953 b329035))) (joinCoverage (joinCoverage b329118 b329201) (joinCoverage b329284 (joinCoverage b329366 b329449)))) (joinCoverage (joinCoverage (joinCoverage b329531 b329614) (joinCoverage b329696 (joinCoverage b329779 b329862))) (joinCoverage (joinCoverage b329945 b330027) (joinCoverage b330110 (joinCoverage b330193 b330276))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b330358 b330441) (joinCoverage b330524 (joinCoverage b330607 b330689))) (joinCoverage (joinCoverage b330772 b330854) (joinCoverage b330937 (joinCoverage b331019 b331102)))) (joinCoverage (joinCoverage (joinCoverage b331185 b331268) (joinCoverage b331350 (joinCoverage b331433 b331515))) (joinCoverage (joinCoverage b331598 b331680) (joinCoverage b331763 (joinCoverage b331846 b331929))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b332011 b332094) (joinCoverage b332176 b332259)) (joinCoverage (joinCoverage b332341 b332424) (joinCoverage b332507 (joinCoverage b332590 b332672)))) (joinCoverage (joinCoverage (joinCoverage b332755 b332838) (joinCoverage b332921 (joinCoverage b333003 b333086))) (joinCoverage (joinCoverage b333169 b333252) (joinCoverage b333334 (joinCoverage b333417 b333499))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b333582 b333664) (joinCoverage b333747 (joinCoverage b333830 b333913))) (joinCoverage (joinCoverage b333995 b334078) (joinCoverage b334160 (joinCoverage b334243 b334325)))) (joinCoverage (joinCoverage (joinCoverage b334408 b334491) (joinCoverage b334574 (joinCoverage b334656 b334739))) (joinCoverage (joinCoverage b334821 b334904) (joinCoverage b334986 (joinCoverage b335069 b335152)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b335235 b335317) (joinCoverage b335400 (joinCoverage b335483 b335566))) (joinCoverage (joinCoverage b335648 b335731) (joinCoverage b335814 (joinCoverage b335897 b335979)))) (joinCoverage (joinCoverage (joinCoverage b336062 b336144) (joinCoverage b336227 (joinCoverage b336309 b336392))) (joinCoverage (joinCoverage b336475 b336558) (joinCoverage b336640 (joinCoverage b336723 b336805))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b336888 b336970) (joinCoverage b337053 (joinCoverage b337136 b337219))) (joinCoverage (joinCoverage b337301 b337384) (joinCoverage b337466 (joinCoverage b337549 b337631)))) (joinCoverage (joinCoverage (joinCoverage b337714 b337797) (joinCoverage b337880 (joinCoverage b337962 b338045))) (joinCoverage (joinCoverage b338128 b338211) (joinCoverage b338293 (joinCoverage b338376 b338459))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 325482 ≤ index 625000000/512 := by decide +kernel
private theorem starting_value : fast 625000000=32560335 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 625000000=32560335) (n : ℕ) (low : 625000000≤n) (bound : n≤650000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=625000000
    · rw [first,anchor]
      exact starting_value
    · have past : 625000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤650000000 by omega)
        have within : index n / 512 < 338542 := by omega
        have lower : index 625000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤650000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ625000000To650000000
