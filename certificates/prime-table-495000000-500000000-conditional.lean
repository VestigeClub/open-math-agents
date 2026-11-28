import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ495000000To500000000

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




private def radical : ℕ := 0x390151a2cd328a659f1171d1626d7649f6f0ec5a5b159b68201b17e01d94ef0cb752596f3df4ed28bb0f8c1b385c7ffdbe7858721073f4fcbbcaf7ec36b32875441aaa141dc7ed5a6445007eb097f4eaa60d81ab47c55bdd0bb08c3a1a85b1366dcf1175b4bacc4625a020593abc8812efef50b807fc2becce4f1980d64b708267f4f21a8a95079a14516258c7d7e258374f56360ea874e32049533fe667739680faf4c3be32a6cacb0dc8836c5549b1351d13e241d2430ad8ac4bd0af57f8ee1d5d8d87b40f0072ac7663a53e204d6669c036d3e1ec2d7c4e0bae317043e03e6a08c6a9db27465b5ce80fdfb41157d12dd3e6228aa258db137dfb9dc54e9093ed1e6b37255ce8ed0d3f09ac01d6dd5b0e23a3f8f4667fefc76b18dd4e87045b76b6aaf791b1da77e0b3ce3105930af54568a3d0e4dc62a4bdf15e910693e34da7c01e6fc74eff52131c3807887af00875f5c9b95e94b302ba984978306e6457d1f16f761e6b3aa73925abc9268b444581e4ee4b82a1a91a08593f71c40549176f61f2b951871475cab46d8d74c0200a9c080514fb648c1b14e5b7d24d4e687be973336a98e03a889ab64b54320c29335c6ae4ae79f28661306fa7af0f379b6cb71aab26bcb098e1444498b33a110c64739cd69a2c1a3d480ad9259e374b9c073602c31ee837d9ac5d7e5b0432245b4dab7a1a2645ab86661223faab25cc68a9a8c0e14943dc5dfe98fb5cdaa7db316db02d87950ab08996996097a7e2bcfc460c6176537ec1364eaace016f326e4d8ea82e035586bba6492707ec64f54eb6d462a52f6c7da8065d6809b9817e1cf31211dae84be5ac6a7bcb217a389a7d0380f9ed4686388e46c4343444e5438b5295fa1a88f5d7b5f1d4e0e7337561d245e96a51b485063ee89901127efff09d622f26b96ed9c50d43c35cbbcb3f1c208b48172d446c4ecc2b665f1e1b8ed6a962df514e81e07084b96e788e25e5f30a2e754c78374a555423aed71f4054bda3aedd4669119093aa9ced2e976904d25ea828a39115292fd7e5b81bd5f95220c2d312ad1b36f13c084fe34de1eb4730b23ff553040a04bc5f67b61ce5a9659b2623e8b1adc3a0d60d818a8826f11007fc0620cb5bf158a3a7436e2b3bff89600dceb43ddec1606093b39c5d0eedf9ac6be3926920d8e8283e0473cebc4e846472c12866a9735c37f057984376cf7892a350b6e8bf576b1123bee8b93be2bef49869097ae0899a127ba3126e7993b11a2a7f9900874b718692ffedb79f387160d73fa5edb4eaadadde7e53b8be69488742f43a2b4b991173b0700b021bd1fe3401d7a7e4170e22d2717fab91d4498e3808548eddbc2c4d4b6f053202d31b18362f9c2a2a1f1f9cec2b7b038c10f2c8a1a211facb4490ab22fc93bd3ec546f3ce0135e3840dbce5cb65238bfb40d9fe70a965cdd6697ff9fff44924445a418c0627df0e48d6b8aad48e4b01811b17974d09b890106a11951e91b241961f0f04316ea218d35dcc531bdace67342af3ab0770a3e42e58b2aa970aa3f040ebac94df9cb0fe5eb992cc434fe5269718db1409512071320b19406a55618d63f54465c9813cbf8623b0954ac9190dec346f504f672f2c2c52518d294407af3681b85e5bdde15c56a31c3e989fefce28c2e74e92bb4ce26411c8e19026d1056ad952aa2a6361824a499f8a6ab2f555e4d8847c685a183154b677d30979097aa38d970ff94a240e4f73926fdd5042d2e9c6bafc099ff8b1acb6ad9ea9369ba8adb6a1f5f60ad1e72757e6509061a8cef445a36cf982f8cd000b847a3ac2e9bff0f93225115cbd72f76f65c752a799e031f005793dde4166c971d654915cc6f01ec1fb763c080bdec327b5f72bde54861bedc5a49eae6ea397376faefa9b1bc14993201d3fbba230ad07e8a364ce6df39f8839e87a52827095954489d4b4be00dbee9a67ce6da5087649a35419b507bad555ff2eb7e2367f7567178e47ad735ba30929c2c7b8a779019349fd2bd452d03001992c29befa48dfba90fa9b42fd2ecefdce951b604f6db723accadf8a75ca6a8de916fae113ffcfa7eb3b14f08ee121a45b7005b89e7e54883c835b07e22112e4ec9db38c6064f8017785d2b07e74eb01ba09aaa963513370c5b8a3b56d30ae3a06bc730d0f48d8fbb2d2603baf74351277e7bdbcaf64bd4070d886191e1547ecb56acbb3ac8fb4e3efc2ade876297110401586027596cb3ab6717d6a06cef826999861d8f439bee349373bacf095b2639f19c66c16a0ef10723ca15c736e928c2e8aed0ff16a1ed36fda13ebbd724f901330cb4f6fc15f32c2fe81c18bd2f0b57e87b26c9d9d7c0295026775cb9140cc78ef915e78920727e763fbc99c864bbcd12ac645e6c2111caabf3cdf0d345db876eebb29c01f2b3b3b86dc3542a841b392443d120b40dbdbcaddfa34c340d196faf417b4894b54860622285535647032e2fe364073e9d9e5f5e7bbdb90f393441e1f68d26b7ff998526b3054050cf5df120495958f0539f627c4943fc1dfda960c98deef96dbd651145d3f20cdcadb0ba586b209da0a78de4a8349f44e8c297e0134c66faca566424d8266aa76b6f44dd8754b7d0802c6ae196c51126ccc7d9abadeb67becdaff562f7c07308202f449a7d898936354d20993af9b3f9f19cc75ed91c129ef73df1cd3f59ee9e1872206928053f847918121f74a0946358232439d3b9c9d7188d818810ce54d18d1f114498f43a7eb5b5cb01f6a44e1190de46faf938248667a67b137278c62794505f621ab00e99e7ff12992531254ed907905673f6f19eb5efde193d590189f0a262a0596ab2e09719ebf7d47f999f4126b3398b9948b78f6d933653f0a6905d4754b610304eac156fcd711c5bd97b8bf12df5e74380fa7ec1879dccef0f406640af96b976e7d177021f50a20d19b237a7a249563aafe5642fa5b705a95c30856dadfce2774a2e8768c60286de388de9e2b055e243f91533b20ead96279347eba0e7716f6b8fbbf801f06bc6ae1f0d1444d36721faa683e8a083aaf576883bff68ceaf9396d34e397a23bc7c9e258a4ae766d3e77e808a4fe46fd545e2c4c15e0aa61e215ca9aecdaba3267d3f927c49d1f2ec0f931cf34e749b2d44d8d583ca29b960e2d4e49279240d2197c8ecb71325282c10f7bfff8c03b0323def16800794fdf155897ef858e87175759561663144d768d066785368f782de8651ed2d2ebfede09f1b18c4b7ea61e3bd7b572eb0d43080ed410e10fad71b6d403865811f81eff98a924886461c8c6f8230419bf0249e96bc611ce698848b5e575fa9e5e7a1f8ce7a35ccfd88abde099b1fc459017c281f951aef85d5e12aaa41e0959a6b98b206fdf8cb127d2e494cba757e04061551464db056dbc978c0899dd033c27f24f6a7dfdb3d37ed8b0c1700c9d723a0e1b3a8a0351a4b0589540332056abd7a93f5bd3fa42098f58478b037db38c83aee539594043a84625042b1e981fb6ab7a0e8333fbdb529f30abbd29561ad50bb012a59924bd8b2da58aa50abc9947e1bdfd13f27aa58246fc5a0a7190a441ce15019fab79894964ed83497cccb43c32ac871e48da273b8f6b59f9e2e54043a199fd0173e964bcb601c937cd6027c8528fe5ce3e439ccd00130185d4510564e15b2e4f41175b55ab78b3cf30c7c35671a9d83ad4d99709dc7c6cd55c27dde379da8e0da7af84f6ff96479e940b6b47adf6671da1ba8dd2b8f1919c2ba524d9185c6fd2b6ebaba09a264a28afb6fab323393a33d0b7392ef517de027d358a583d87e928ddca739fc19a6f0bf820824ffea71bf31015eeb459e9ab52aa25d47b221599c05b2807151873394dc57586ba1d6191c5f468b7b19455339abfadf6ff1290702b99924bf4608342d62b290395dbe791c2cc3910f7b463c25c50a1b50073d76dcda5ee95c80b7f46e27b08521f3b5065937a830c6410598b78ebed0519b7f75550d4aca6a6fbdc43cc3ad2bd5e84f74c4eb7ec0c120cdeb37a400cb36acfd08d6da8356bcb72bc5835ea51550e3af4e2089aa3e07208f69c68335e00cd4aaa12b03121127502f20bb5304daa415be9e8e6d819f18f2b38c0329956ae278069ed094bbf503adf29ca8ee3a8d13eb010d858a2ebf3e87379707ea90550128a7bd6b9ba9bdab1b7031873c77c882fdb6ecf92d501f8b7a95f40c7a39069f70a8de8de4cb6fb7d607ca1f79c148c9b2fb8b505f7a9b55c3cafd5e1d391a4850627560bf57fe41e028df8d0382459a0ea3482d23f62c0384c3d714bfd6044a007f68abdadfcf75d3f4d60c2f0daa36ec2bd48ff2ec4614b6e1c665b8add72b7c8572f791d54174ae3632f7331bcf2c69bddd816db5ca6b39f43fed11ef4af416dc4cd4c489453dca5d92ae155807b8b70284b31b648bfb81004d2c44d8a75ca8d1b6cf2b974a2e079bf8ce536d53a01d848d915843ff97672b24a4bf526364f2f4ca6b5b6377843a1edb8766c9d8c573c031d29b60cdf409fa70944824c2bcfb18dc83d9f64731949a3952da504c163ea2b7af7252e6be931913f9668a6072a17656cb45e2377de76984b0888d0a33a13136a68186b201c83745f5e46bb9b259854482c5132bc0bd07741aa1a294a716560ba7d4e66e83e44537eea8705d7990bbb1fa0ca92b6a544bc47e9ce09f5e9fe138914711e8bd7b5fd3c86ba308c7a89f8e2c4f939958e22acf899501a009f8cc9b4c147272351661c3ed7de69685dbf5475a6fcda3a5f5dd1c07414407c8acafe24755cf66fce554c1a69d26a112b1b8f4fec4cf07e17072b67ed7246280c276c97b7774301fe3964df701d170bfff959dd5ed1d202cc7b91d383893c45df88455a9d7d51efacdbcf5e7dbde9d43fa351636a04048fb087acbf460c9b84b6a2e94216047e2de0497d5aa4c5d0f8ee321cb78bf5570a04c6ac0c5831a614a1ee6937917f17f29d8a8c5f1adb15e29b64ed075602a2d0ae27140245c1b2ba8c764e66d3c380c612aa875d75ae426070c29b70b033024a33b0aab42d04b58b66ddbfdb495b20b7222acadc53fd0749b3cfb417cb231918b8856f0e6cca4ec7d94b03635ef80729cf525fa92e2516df68b03adcde183c470d3080b7ad090ec2c0dc12d3a111e6fc9bd5adbc822c304530ea6ca101dc34974e31260e1926d51e81f561403cccdfc1c9a2d55d76202546dfca79e37e42bea165a1e4e24ff77014f8a42d02a8f26e2058fc7a05c0dffc2ccec0f25754f67b5a63528f3d4ab24fceac254e0ada28149b8586803c560d276ab6124db89be592005a7546f6ec2891cddfdd4a7f51fe1d6f1afa2e753e52c8caf3e40a83f8254a815deac3f22580bfbfbe918618fbfaea5a420676e7f7d92b5ef00b4fe10420ee4c39ef2cec26568253876d48ccf48ff42f79d373fcf5f9a3753ecda7484bed1a2725e2d69926c9324a39c840eefc0cb067478b0f614c6fd64bc700f1099f71bcbfa645f6b80b73ea4d9bf999d3867c32e0c7def4d6343797f056b20b5f309448fcfab806e7bf131d8bc4537c706451efa7beeb2f5124ad7129504c4bed77b050a34fcf1d5f1ceee9dc60eb6f08a09d760002f905ef1cfadd762864c858662fa025aa5bdf2c79952eac0f7dd21a8229a2401a199e48d516

private def light (n : ℕ) : Bool :=
  if n≤149 then decide n.Prime else n.gcd 380892263763056972698595524350736933545970238573408427883655838887865527498969322620843829924502074302514052524979028027751108334657896696442372994639480443832950613971571859528835715269633083149369445271480789636247481797836800000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤22360) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 149 = 380892263763056972698595524350736933545970238573408427883655838887865527498969322620843829924502074302514052524979028027751108334657896696442372994639480443832950613971571859528835715269633083149369445271480789636247481797836800000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 149 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤22360 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 43 := by unfold smallValid; decide +kernel

private theorem sp43 : smallValid 43 44 := by unfold smallValid; decide +kernel

private theorem sp87 : smallValid 87 43 := by unfold smallValid; decide +kernel

private theorem sp130 : smallValid 130 44 := by unfold smallValid; decide +kernel

private theorem sp174 : smallValid 174 43 := by unfold smallValid; decide +kernel

private theorem sp217 : smallValid 217 44 := by unfold smallValid; decide +kernel

private theorem sp261 : smallValid 261 44 := by unfold smallValid; decide +kernel

private theorem sp305 : smallValid 305 44 := by unfold smallValid; decide +kernel

private theorem sp349 : smallValid 349 43 := by unfold smallValid; decide +kernel

private theorem sp392 : smallValid 392 44 := by unfold smallValid; decide +kernel

private theorem sp436 : smallValid 436 43 := by unfold smallValid; decide +kernel

private theorem sp479 : smallValid 479 44 := by unfold smallValid; decide +kernel

private theorem sp523 : smallValid 523 43 := by unfold smallValid; decide +kernel

private theorem sp566 : smallValid 566 44 := by unfold smallValid; decide +kernel

private theorem sp610 : smallValid 610 44 := by unfold smallValid; decide +kernel

private theorem sp654 : smallValid 654 44 := by unfold smallValid; decide +kernel

private theorem sp698 : smallValid 698 43 := by unfold smallValid; decide +kernel

private theorem sp741 : smallValid 741 44 := by unfold smallValid; decide +kernel

private theorem sp785 : smallValid 785 43 := by unfold smallValid; decide +kernel

private theorem sp828 : smallValid 828 44 := by unfold smallValid; decide +kernel

private theorem sp872 : smallValid 872 43 := by unfold smallValid; decide +kernel

private theorem sp915 : smallValid 915 44 := by unfold smallValid; decide +kernel

private theorem sp959 : smallValid 959 44 := by unfold smallValid; decide +kernel

private theorem sp1003 : smallValid 1003 44 := by unfold smallValid; decide +kernel

private theorem sp1047 : smallValid 1047 43 := by unfold smallValid; decide +kernel

private theorem sp1090 : smallValid 1090 44 := by unfold smallValid; decide +kernel

private theorem sp1134 : smallValid 1134 44 := by unfold smallValid; decide +kernel

private theorem sp1178 : smallValid 1178 44 := by unfold smallValid; decide +kernel

private theorem sp1222 : smallValid 1222 43 := by unfold smallValid; decide +kernel

private theorem sp1265 : smallValid 1265 44 := by unfold smallValid; decide +kernel

private theorem sp1309 : smallValid 1309 44 := by unfold smallValid; decide +kernel

private theorem sp1353 : smallValid 1353 44 := by unfold smallValid; decide +kernel

private theorem sp1397 : smallValid 1397 43 := by unfold smallValid; decide +kernel

private theorem sp1440 : smallValid 1440 44 := by unfold smallValid; decide +kernel

private theorem sp1484 : smallValid 1484 43 := by unfold smallValid; decide +kernel

private theorem sp1527 : smallValid 1527 44 := by unfold smallValid; decide +kernel

private theorem sp1571 : smallValid 1571 43 := by unfold smallValid; decide +kernel

private theorem sp1614 : smallValid 1614 44 := by unfold smallValid; decide +kernel

private theorem sp1658 : smallValid 1658 44 := by unfold smallValid; decide +kernel

private theorem sp1702 : smallValid 1702 44 := by unfold smallValid; decide +kernel

private theorem sp1746 : smallValid 1746 43 := by unfold smallValid; decide +kernel

private theorem sp1789 : smallValid 1789 44 := by unfold smallValid; decide +kernel

private theorem sp1833 : smallValid 1833 44 := by unfold smallValid; decide +kernel

private theorem sp1877 : smallValid 1877 44 := by unfold smallValid; decide +kernel

private theorem sp1921 : smallValid 1921 43 := by unfold smallValid; decide +kernel

private theorem sp1964 : smallValid 1964 44 := by unfold smallValid; decide +kernel

private theorem sp2008 : smallValid 2008 44 := by unfold smallValid; decide +kernel

private theorem sp2052 : smallValid 2052 44 := by unfold smallValid; decide +kernel

private theorem sp2096 : smallValid 2096 43 := by unfold smallValid; decide +kernel

private theorem sp2139 : smallValid 2139 44 := by unfold smallValid; decide +kernel

private theorem sp2183 : smallValid 2183 43 := by unfold smallValid; decide +kernel

private theorem sp2226 : smallValid 2226 44 := by unfold smallValid; decide +kernel

private theorem sp2270 : smallValid 2270 43 := by unfold smallValid; decide +kernel

private theorem sp2313 : smallValid 2313 44 := by unfold smallValid; decide +kernel

private theorem sp2357 : smallValid 2357 44 := by unfold smallValid; decide +kernel

private theorem sp2401 : smallValid 2401 44 := by unfold smallValid; decide +kernel

private theorem sp2445 : smallValid 2445 43 := by unfold smallValid; decide +kernel

private theorem sp2488 : smallValid 2488 44 := by unfold smallValid; decide +kernel

private theorem sp2532 : smallValid 2532 44 := by unfold smallValid; decide +kernel

private theorem sp2576 : smallValid 2576 44 := by unfold smallValid; decide +kernel

private theorem sp2620 : smallValid 2620 43 := by unfold smallValid; decide +kernel

private theorem sp2663 : smallValid 2663 44 := by unfold smallValid; decide +kernel

private theorem sp2707 : smallValid 2707 44 := by unfold smallValid; decide +kernel

private theorem sp2751 : smallValid 2751 44 := by unfold smallValid; decide +kernel

private theorem sp2795 : smallValid 2795 43 := by unfold smallValid; decide +kernel

private theorem sp2838 : smallValid 2838 44 := by unfold smallValid; decide +kernel

private theorem sp2882 : smallValid 2882 43 := by unfold smallValid; decide +kernel

private theorem sp2925 : smallValid 2925 44 := by unfold smallValid; decide +kernel

private theorem sp2969 : smallValid 2969 43 := by unfold smallValid; decide +kernel

private theorem sp3012 : smallValid 3012 44 := by unfold smallValid; decide +kernel

private theorem sp3056 : smallValid 3056 44 := by unfold smallValid; decide +kernel

private theorem sp3100 : smallValid 3100 44 := by unfold smallValid; decide +kernel

private theorem sp3144 : smallValid 3144 43 := by unfold smallValid; decide +kernel

private theorem sp3187 : smallValid 3187 44 := by unfold smallValid; decide +kernel

private theorem sp3231 : smallValid 3231 43 := by unfold smallValid; decide +kernel

private theorem sp3274 : smallValid 3274 44 := by unfold smallValid; decide +kernel

private theorem sp3318 : smallValid 3318 43 := by unfold smallValid; decide +kernel

private theorem sp3361 : smallValid 3361 44 := by unfold smallValid; decide +kernel

private theorem sp3405 : smallValid 3405 44 := by unfold smallValid; decide +kernel

private theorem sp3449 : smallValid 3449 44 := by unfold smallValid; decide +kernel

private theorem sp3493 : smallValid 3493 43 := by unfold smallValid; decide +kernel

private theorem sp3536 : smallValid 3536 44 := by unfold smallValid; decide +kernel

private theorem sp3580 : smallValid 3580 43 := by unfold smallValid; decide +kernel

private theorem sp3623 : smallValid 3623 44 := by unfold smallValid; decide +kernel

private theorem sp3667 : smallValid 3667 43 := by unfold smallValid; decide +kernel

private theorem sp3710 : smallValid 3710 44 := by unfold smallValid; decide +kernel

private theorem sp3754 : smallValid 3754 44 := by unfold smallValid; decide +kernel

private theorem sp3798 : smallValid 3798 44 := by unfold smallValid; decide +kernel

private theorem sp3842 : smallValid 3842 43 := by unfold smallValid; decide +kernel

private theorem sp3885 : smallValid 3885 44 := by unfold smallValid; decide +kernel

private theorem sp3929 : smallValid 3929 44 := by unfold smallValid; decide +kernel

private theorem sp3973 : smallValid 3973 44 := by unfold smallValid; decide +kernel

private theorem sp4017 : smallValid 4017 43 := by unfold smallValid; decide +kernel

private theorem sp4060 : smallValid 4060 44 := by unfold smallValid; decide +kernel

private theorem sp4104 : smallValid 4104 44 := by unfold smallValid; decide +kernel

private theorem sp4148 : smallValid 4148 44 := by unfold smallValid; decide +kernel

private theorem sp4192 : smallValid 4192 43 := by unfold smallValid; decide +kernel

private theorem sp4235 : smallValid 4235 44 := by unfold smallValid; decide +kernel

private theorem sp4279 : smallValid 4279 43 := by unfold smallValid; decide +kernel

private theorem sp4322 : smallValid 4322 44 := by unfold smallValid; decide +kernel

private theorem sp4366 : smallValid 4366 43 := by unfold smallValid; decide +kernel

private theorem sp4409 : smallValid 4409 44 := by unfold smallValid; decide +kernel

private theorem sp4453 : smallValid 4453 44 := by unfold smallValid; decide +kernel

private theorem sp4497 : smallValid 4497 44 := by unfold smallValid; decide +kernel

private theorem sp4541 : smallValid 4541 43 := by unfold smallValid; decide +kernel

private theorem sp4584 : smallValid 4584 44 := by unfold smallValid; decide +kernel

private theorem sp4628 : smallValid 4628 44 := by unfold smallValid; decide +kernel

private theorem sp4672 : smallValid 4672 44 := by unfold smallValid; decide +kernel

private theorem sp4716 : smallValid 4716 43 := by unfold smallValid; decide +kernel

private theorem sp4759 : smallValid 4759 44 := by unfold smallValid; decide +kernel

private theorem sp4803 : smallValid 4803 44 := by unfold smallValid; decide +kernel

private theorem sp4847 : smallValid 4847 44 := by unfold smallValid; decide +kernel

private theorem sp4891 : smallValid 4891 43 := by unfold smallValid; decide +kernel

private theorem sp4934 : smallValid 4934 44 := by unfold smallValid; decide +kernel

private theorem sp4978 : smallValid 4978 43 := by unfold smallValid; decide +kernel

private theorem sp5021 : smallValid 5021 44 := by unfold smallValid; decide +kernel

private theorem sp5065 : smallValid 5065 43 := by unfold smallValid; decide +kernel

private theorem sp5108 : smallValid 5108 44 := by unfold smallValid; decide +kernel

private theorem sp5152 : smallValid 5152 44 := by unfold smallValid; decide +kernel

private theorem sp5196 : smallValid 5196 44 := by unfold smallValid; decide +kernel

private theorem sp5240 : smallValid 5240 43 := by unfold smallValid; decide +kernel

private theorem sp5283 : smallValid 5283 44 := by unfold smallValid; decide +kernel

private theorem sp5327 : smallValid 5327 44 := by unfold smallValid; decide +kernel

private theorem sp5371 : smallValid 5371 44 := by unfold smallValid; decide +kernel

private theorem sp5415 : smallValid 5415 43 := by unfold smallValid; decide +kernel

private theorem sp5458 : smallValid 5458 44 := by unfold smallValid; decide +kernel

private theorem sp5502 : smallValid 5502 44 := by unfold smallValid; decide +kernel

private theorem sp5546 : smallValid 5546 44 := by unfold smallValid; decide +kernel

private theorem sp5590 : smallValid 5590 43 := by unfold smallValid; decide +kernel

private theorem sp5633 : smallValid 5633 44 := by unfold smallValid; decide +kernel

private theorem sp5677 : smallValid 5677 43 := by unfold smallValid; decide +kernel

private theorem sp5720 : smallValid 5720 44 := by unfold smallValid; decide +kernel

private theorem sp5764 : smallValid 5764 43 := by unfold smallValid; decide +kernel

private theorem sp5807 : smallValid 5807 44 := by unfold smallValid; decide +kernel

private theorem sp5851 : smallValid 5851 44 := by unfold smallValid; decide +kernel

private theorem sp5895 : smallValid 5895 44 := by unfold smallValid; decide +kernel

private theorem sp5939 : smallValid 5939 43 := by unfold smallValid; decide +kernel

private theorem sp5982 : smallValid 5982 44 := by unfold smallValid; decide +kernel

private theorem sp6026 : smallValid 6026 43 := by unfold smallValid; decide +kernel

private theorem sp6069 : smallValid 6069 44 := by unfold smallValid; decide +kernel

private theorem sp6113 : smallValid 6113 43 := by unfold smallValid; decide +kernel

private theorem sp6156 : smallValid 6156 44 := by unfold smallValid; decide +kernel

private theorem sp6200 : smallValid 6200 44 := by unfold smallValid; decide +kernel

private theorem sp6244 : smallValid 6244 44 := by unfold smallValid; decide +kernel

private theorem sp6288 : smallValid 6288 43 := by unfold smallValid; decide +kernel

private theorem sp6331 : smallValid 6331 44 := by unfold smallValid; decide +kernel

private theorem sp6375 : smallValid 6375 43 := by unfold smallValid; decide +kernel

private theorem sp6418 : smallValid 6418 44 := by unfold smallValid; decide +kernel

private theorem sp6462 : smallValid 6462 43 := by unfold smallValid; decide +kernel

private theorem sp6505 : smallValid 6505 44 := by unfold smallValid; decide +kernel

private theorem sp6549 : smallValid 6549 44 := by unfold smallValid; decide +kernel

private theorem sp6593 : smallValid 6593 44 := by unfold smallValid; decide +kernel

private theorem sp6637 : smallValid 6637 43 := by unfold smallValid; decide +kernel

private theorem sp6680 : smallValid 6680 44 := by unfold smallValid; decide +kernel

private theorem sp6724 : smallValid 6724 44 := by unfold smallValid; decide +kernel

private theorem sp6768 : smallValid 6768 44 := by unfold smallValid; decide +kernel

private theorem sp6812 : smallValid 6812 43 := by unfold smallValid; decide +kernel

private theorem sp6855 : smallValid 6855 44 := by unfold smallValid; decide +kernel

private theorem sp6899 : smallValid 6899 44 := by unfold smallValid; decide +kernel

private theorem sp6943 : smallValid 6943 44 := by unfold smallValid; decide +kernel

private theorem sp6987 : smallValid 6987 43 := by unfold smallValid; decide +kernel

private theorem sp7030 : smallValid 7030 44 := by unfold smallValid; decide +kernel

private theorem sp7074 : smallValid 7074 43 := by unfold smallValid; decide +kernel

private theorem sp7117 : smallValid 7117 44 := by unfold smallValid; decide +kernel

private theorem sp7161 : smallValid 7161 43 := by unfold smallValid; decide +kernel

private theorem sp7204 : smallValid 7204 44 := by unfold smallValid; decide +kernel

private theorem sp7248 : smallValid 7248 44 := by unfold smallValid; decide +kernel

private theorem sp7292 : smallValid 7292 44 := by unfold smallValid; decide +kernel

private theorem sp7336 : smallValid 7336 43 := by unfold smallValid; decide +kernel

private theorem sp7379 : smallValid 7379 44 := by unfold smallValid; decide +kernel

private theorem sp7423 : smallValid 7423 44 := by unfold smallValid; decide +kernel

private theorem sp7467 : smallValid 7467 44 := by unfold smallValid; decide +kernel

private theorem sp7511 : smallValid 7511 43 := by unfold smallValid; decide +kernel

private theorem sp7554 : smallValid 7554 44 := by unfold smallValid; decide +kernel

private theorem sp7598 : smallValid 7598 44 := by unfold smallValid; decide +kernel

private theorem sp7642 : smallValid 7642 44 := by unfold smallValid; decide +kernel

private theorem sp7686 : smallValid 7686 43 := by unfold smallValid; decide +kernel

private theorem sp7729 : smallValid 7729 44 := by unfold smallValid; decide +kernel

private theorem sp7773 : smallValid 7773 43 := by unfold smallValid; decide +kernel

private theorem sp7816 : smallValid 7816 44 := by unfold smallValid; decide +kernel

private theorem sp7860 : smallValid 7860 43 := by unfold smallValid; decide +kernel

private theorem sp7903 : smallValid 7903 44 := by unfold smallValid; decide +kernel

private theorem sp7947 : smallValid 7947 44 := by unfold smallValid; decide +kernel

private theorem sp7991 : smallValid 7991 44 := by unfold smallValid; decide +kernel

private theorem sp8035 : smallValid 8035 43 := by unfold smallValid; decide +kernel

private theorem sp8078 : smallValid 8078 44 := by unfold smallValid; decide +kernel

private theorem sp8122 : smallValid 8122 44 := by unfold smallValid; decide +kernel

private theorem sp8166 : smallValid 8166 44 := by unfold smallValid; decide +kernel

private theorem sp8210 : smallValid 8210 43 := by unfold smallValid; decide +kernel

private theorem sp8253 : smallValid 8253 44 := by unfold smallValid; decide +kernel

private theorem sp8297 : smallValid 8297 44 := by unfold smallValid; decide +kernel

private theorem sp8341 : smallValid 8341 44 := by unfold smallValid; decide +kernel

private theorem sp8385 : smallValid 8385 43 := by unfold smallValid; decide +kernel

private theorem sp8428 : smallValid 8428 44 := by unfold smallValid; decide +kernel

private theorem sp8472 : smallValid 8472 43 := by unfold smallValid; decide +kernel

private theorem sp8515 : smallValid 8515 44 := by unfold smallValid; decide +kernel

private theorem sp8559 : smallValid 8559 43 := by unfold smallValid; decide +kernel

private theorem sp8602 : smallValid 8602 44 := by unfold smallValid; decide +kernel

private theorem sp8646 : smallValid 8646 44 := by unfold smallValid; decide +kernel

private theorem sp8690 : smallValid 8690 44 := by unfold smallValid; decide +kernel

private theorem sp8734 : smallValid 8734 43 := by unfold smallValid; decide +kernel

private theorem sp8777 : smallValid 8777 44 := by unfold smallValid; decide +kernel

private theorem sp8821 : smallValid 8821 43 := by unfold smallValid; decide +kernel

private theorem sp8864 : smallValid 8864 44 := by unfold smallValid; decide +kernel

private theorem sp8908 : smallValid 8908 43 := by unfold smallValid; decide +kernel

private theorem sp8951 : smallValid 8951 44 := by unfold smallValid; decide +kernel

private theorem sp8995 : smallValid 8995 44 := by unfold smallValid; decide +kernel

private theorem sp9039 : smallValid 9039 44 := by unfold smallValid; decide +kernel

private theorem sp9083 : smallValid 9083 43 := by unfold smallValid; decide +kernel

private theorem sp9126 : smallValid 9126 44 := by unfold smallValid; decide +kernel

private theorem sp9170 : smallValid 9170 43 := by unfold smallValid; decide +kernel

private theorem sp9213 : smallValid 9213 44 := by unfold smallValid; decide +kernel

private theorem sp9257 : smallValid 9257 43 := by unfold smallValid; decide +kernel

private theorem sp9300 : smallValid 9300 44 := by unfold smallValid; decide +kernel

private theorem sp9344 : smallValid 9344 44 := by unfold smallValid; decide +kernel

private theorem sp9388 : smallValid 9388 44 := by unfold smallValid; decide +kernel

private theorem sp9432 : smallValid 9432 43 := by unfold smallValid; decide +kernel

private theorem sp9475 : smallValid 9475 44 := by unfold smallValid; decide +kernel

private theorem sp9519 : smallValid 9519 44 := by unfold smallValid; decide +kernel

private theorem sp9563 : smallValid 9563 44 := by unfold smallValid; decide +kernel

private theorem sp9607 : smallValid 9607 43 := by unfold smallValid; decide +kernel

private theorem sp9650 : smallValid 9650 44 := by unfold smallValid; decide +kernel

private theorem sp9694 : smallValid 9694 44 := by unfold smallValid; decide +kernel

private theorem sp9738 : smallValid 9738 44 := by unfold smallValid; decide +kernel

private theorem sp9782 : smallValid 9782 43 := by unfold smallValid; decide +kernel

private theorem sp9825 : smallValid 9825 44 := by unfold smallValid; decide +kernel

private theorem sp9869 : smallValid 9869 43 := by unfold smallValid; decide +kernel

private theorem sp9912 : smallValid 9912 44 := by unfold smallValid; decide +kernel

private theorem sp9956 : smallValid 9956 43 := by unfold smallValid; decide +kernel

private theorem sp9999 : smallValid 9999 44 := by unfold smallValid; decide +kernel

private theorem sp10043 : smallValid 10043 44 := by unfold smallValid; decide +kernel

private theorem sp10087 : smallValid 10087 44 := by unfold smallValid; decide +kernel

private theorem sp10131 : smallValid 10131 43 := by unfold smallValid; decide +kernel

private theorem sp10174 : smallValid 10174 44 := by unfold smallValid; decide +kernel

private theorem sp10218 : smallValid 10218 44 := by unfold smallValid; decide +kernel

private theorem sp10262 : smallValid 10262 44 := by unfold smallValid; decide +kernel

private theorem sp10306 : smallValid 10306 43 := by unfold smallValid; decide +kernel

private theorem sp10349 : smallValid 10349 44 := by unfold smallValid; decide +kernel

private theorem sp10393 : smallValid 10393 44 := by unfold smallValid; decide +kernel

private theorem sp10437 : smallValid 10437 44 := by unfold smallValid; decide +kernel

private theorem sp10481 : smallValid 10481 43 := by unfold smallValid; decide +kernel

private theorem sp10524 : smallValid 10524 44 := by unfold smallValid; decide +kernel

private theorem sp10568 : smallValid 10568 43 := by unfold smallValid; decide +kernel

private theorem sp10611 : smallValid 10611 44 := by unfold smallValid; decide +kernel

private theorem sp10655 : smallValid 10655 43 := by unfold smallValid; decide +kernel

private theorem sp10698 : smallValid 10698 44 := by unfold smallValid; decide +kernel

private theorem sp10742 : smallValid 10742 44 := by unfold smallValid; decide +kernel

private theorem sp10786 : smallValid 10786 44 := by unfold smallValid; decide +kernel

private theorem sp10830 : smallValid 10830 43 := by unfold smallValid; decide +kernel

private theorem sp10873 : smallValid 10873 44 := by unfold smallValid; decide +kernel

private theorem sp10917 : smallValid 10917 44 := by unfold smallValid; decide +kernel

private theorem sp10961 : smallValid 10961 44 := by unfold smallValid; decide +kernel

private theorem sp11005 : smallValid 11005 43 := by unfold smallValid; decide +kernel

private theorem sp11048 : smallValid 11048 44 := by unfold smallValid; decide +kernel

private theorem sp11092 : smallValid 11092 44 := by unfold smallValid; decide +kernel

private theorem sp11136 : smallValid 11136 44 := by unfold smallValid; decide +kernel

private theorem sp11180 : smallValid 11180 43 := by unfold smallValid; decide +kernel

private theorem sp11223 : smallValid 11223 44 := by unfold smallValid; decide +kernel

private theorem sp11267 : smallValid 11267 43 := by unfold smallValid; decide +kernel

private theorem sp11310 : smallValid 11310 44 := by unfold smallValid; decide +kernel

private theorem sp11354 : smallValid 11354 43 := by unfold smallValid; decide +kernel

private theorem sp11397 : smallValid 11397 44 := by unfold smallValid; decide +kernel

private theorem sp11441 : smallValid 11441 44 := by unfold smallValid; decide +kernel

private theorem sp11485 : smallValid 11485 44 := by unfold smallValid; decide +kernel

private theorem sp11529 : smallValid 11529 43 := by unfold smallValid; decide +kernel

private theorem sp11572 : smallValid 11572 44 := by unfold smallValid; decide +kernel

private theorem sp11616 : smallValid 11616 43 := by unfold smallValid; decide +kernel

private theorem sp11659 : smallValid 11659 44 := by unfold smallValid; decide +kernel

private theorem sp11703 : smallValid 11703 43 := by unfold smallValid; decide +kernel

private theorem sp11746 : smallValid 11746 44 := by unfold smallValid; decide +kernel

private theorem sp11790 : smallValid 11790 44 := by unfold smallValid; decide +kernel

private theorem sp11834 : smallValid 11834 44 := by unfold smallValid; decide +kernel

private theorem sp11878 : smallValid 11878 43 := by unfold smallValid; decide +kernel

private theorem sp11921 : smallValid 11921 44 := by unfold smallValid; decide +kernel

private theorem sp11965 : smallValid 11965 43 := by unfold smallValid; decide +kernel

private theorem sp12008 : smallValid 12008 44 := by unfold smallValid; decide +kernel

private theorem sp12052 : smallValid 12052 43 := by unfold smallValid; decide +kernel

private theorem sp12095 : smallValid 12095 44 := by unfold smallValid; decide +kernel

private theorem sp12139 : smallValid 12139 44 := by unfold smallValid; decide +kernel

private theorem sp12183 : smallValid 12183 44 := by unfold smallValid; decide +kernel

private theorem sp12227 : smallValid 12227 43 := by unfold smallValid; decide +kernel

private theorem sp12270 : smallValid 12270 44 := by unfold smallValid; decide +kernel

private theorem sp12314 : smallValid 12314 44 := by unfold smallValid; decide +kernel

private theorem sp12358 : smallValid 12358 44 := by unfold smallValid; decide +kernel

private theorem sp12402 : smallValid 12402 43 := by unfold smallValid; decide +kernel

private theorem sp12445 : smallValid 12445 44 := by unfold smallValid; decide +kernel

private theorem sp12489 : smallValid 12489 44 := by unfold smallValid; decide +kernel

private theorem sp12533 : smallValid 12533 44 := by unfold smallValid; decide +kernel

private theorem sp12577 : smallValid 12577 43 := by unfold smallValid; decide +kernel

private theorem sp12620 : smallValid 12620 44 := by unfold smallValid; decide +kernel

private theorem sp12664 : smallValid 12664 43 := by unfold smallValid; decide +kernel

private theorem sp12707 : smallValid 12707 44 := by unfold smallValid; decide +kernel

private theorem sp12751 : smallValid 12751 43 := by unfold smallValid; decide +kernel

private theorem sp12794 : smallValid 12794 44 := by unfold smallValid; decide +kernel

private theorem sp12838 : smallValid 12838 44 := by unfold smallValid; decide +kernel

private theorem sp12882 : smallValid 12882 44 := by unfold smallValid; decide +kernel

private theorem sp12926 : smallValid 12926 43 := by unfold smallValid; decide +kernel

private theorem sp12969 : smallValid 12969 44 := by unfold smallValid; decide +kernel

private theorem sp13013 : smallValid 13013 44 := by unfold smallValid; decide +kernel

private theorem sp13057 : smallValid 13057 44 := by unfold smallValid; decide +kernel

private theorem sp13101 : smallValid 13101 43 := by unfold smallValid; decide +kernel

private theorem sp13144 : smallValid 13144 44 := by unfold smallValid; decide +kernel

private theorem sp13188 : smallValid 13188 44 := by unfold smallValid; decide +kernel

private theorem sp13232 : smallValid 13232 44 := by unfold smallValid; decide +kernel

private theorem sp13276 : smallValid 13276 43 := by unfold smallValid; decide +kernel

private theorem sp13319 : smallValid 13319 44 := by unfold smallValid; decide +kernel

private theorem sp13363 : smallValid 13363 43 := by unfold smallValid; decide +kernel

private theorem sp13406 : smallValid 13406 44 := by unfold smallValid; decide +kernel

private theorem sp13450 : smallValid 13450 43 := by unfold smallValid; decide +kernel

private theorem sp13493 : smallValid 13493 44 := by unfold smallValid; decide +kernel

private theorem sp13537 : smallValid 13537 44 := by unfold smallValid; decide +kernel

private theorem sp13581 : smallValid 13581 44 := by unfold smallValid; decide +kernel

private theorem sp13625 : smallValid 13625 43 := by unfold smallValid; decide +kernel

private theorem sp13668 : smallValid 13668 44 := by unfold smallValid; decide +kernel

private theorem sp13712 : smallValid 13712 44 := by unfold smallValid; decide +kernel

private theorem sp13756 : smallValid 13756 44 := by unfold smallValid; decide +kernel

private theorem sp13800 : smallValid 13800 43 := by unfold smallValid; decide +kernel

private theorem sp13843 : smallValid 13843 44 := by unfold smallValid; decide +kernel

private theorem sp13887 : smallValid 13887 44 := by unfold smallValid; decide +kernel

private theorem sp13931 : smallValid 13931 44 := by unfold smallValid; decide +kernel

private theorem sp13975 : smallValid 13975 43 := by unfold smallValid; decide +kernel

private theorem sp14018 : smallValid 14018 44 := by unfold smallValid; decide +kernel

private theorem sp14062 : smallValid 14062 43 := by unfold smallValid; decide +kernel

private theorem sp14105 : smallValid 14105 44 := by unfold smallValid; decide +kernel

private theorem sp14149 : smallValid 14149 43 := by unfold smallValid; decide +kernel

private theorem sp14192 : smallValid 14192 44 := by unfold smallValid; decide +kernel

private theorem sp14236 : smallValid 14236 44 := by unfold smallValid; decide +kernel

private theorem sp14280 : smallValid 14280 44 := by unfold smallValid; decide +kernel

private theorem sp14324 : smallValid 14324 43 := by unfold smallValid; decide +kernel

private theorem sp14367 : smallValid 14367 44 := by unfold smallValid; decide +kernel

private theorem sp14411 : smallValid 14411 43 := by unfold smallValid; decide +kernel

private theorem sp14454 : smallValid 14454 44 := by unfold smallValid; decide +kernel

private theorem sp14498 : smallValid 14498 43 := by unfold smallValid; decide +kernel

private theorem sp14541 : smallValid 14541 44 := by unfold smallValid; decide +kernel

private theorem sp14585 : smallValid 14585 44 := by unfold smallValid; decide +kernel

private theorem sp14629 : smallValid 14629 44 := by unfold smallValid; decide +kernel

private theorem sp14673 : smallValid 14673 43 := by unfold smallValid; decide +kernel

private theorem sp14716 : smallValid 14716 44 := by unfold smallValid; decide +kernel

private theorem sp14760 : smallValid 14760 43 := by unfold smallValid; decide +kernel

private theorem sp14803 : smallValid 14803 44 := by unfold smallValid; decide +kernel

private theorem sp14847 : smallValid 14847 43 := by unfold smallValid; decide +kernel

private theorem sp14890 : smallValid 14890 44 := by unfold smallValid; decide +kernel

private theorem sp14934 : smallValid 14934 44 := by unfold smallValid; decide +kernel

private theorem sp14978 : smallValid 14978 44 := by unfold smallValid; decide +kernel

private theorem sp15022 : smallValid 15022 43 := by unfold smallValid; decide +kernel

private theorem sp15065 : smallValid 15065 44 := by unfold smallValid; decide +kernel

private theorem sp15109 : smallValid 15109 44 := by unfold smallValid; decide +kernel

private theorem sp15153 : smallValid 15153 44 := by unfold smallValid; decide +kernel

private theorem sp15197 : smallValid 15197 43 := by unfold smallValid; decide +kernel

private theorem sp15240 : smallValid 15240 44 := by unfold smallValid; decide +kernel

private theorem sp15284 : smallValid 15284 44 := by unfold smallValid; decide +kernel

private theorem sp15328 : smallValid 15328 44 := by unfold smallValid; decide +kernel

private theorem sp15372 : smallValid 15372 43 := by unfold smallValid; decide +kernel

private theorem sp15415 : smallValid 15415 44 := by unfold smallValid; decide +kernel

private theorem sp15459 : smallValid 15459 43 := by unfold smallValid; decide +kernel

private theorem sp15502 : smallValid 15502 44 := by unfold smallValid; decide +kernel

private theorem sp15546 : smallValid 15546 43 := by unfold smallValid; decide +kernel

private theorem sp15589 : smallValid 15589 44 := by unfold smallValid; decide +kernel

private theorem sp15633 : smallValid 15633 44 := by unfold smallValid; decide +kernel

private theorem sp15677 : smallValid 15677 44 := by unfold smallValid; decide +kernel

private theorem sp15721 : smallValid 15721 43 := by unfold smallValid; decide +kernel

private theorem sp15764 : smallValid 15764 44 := by unfold smallValid; decide +kernel

private theorem sp15808 : smallValid 15808 44 := by unfold smallValid; decide +kernel

private theorem sp15852 : smallValid 15852 44 := by unfold smallValid; decide +kernel

private theorem sp15896 : smallValid 15896 43 := by unfold smallValid; decide +kernel

private theorem sp15939 : smallValid 15939 44 := by unfold smallValid; decide +kernel

private theorem sp15983 : smallValid 15983 44 := by unfold smallValid; decide +kernel

private theorem sp16027 : smallValid 16027 44 := by unfold smallValid; decide +kernel

private theorem sp16071 : smallValid 16071 43 := by unfold smallValid; decide +kernel

private theorem sp16114 : smallValid 16114 44 := by unfold smallValid; decide +kernel

private theorem sp16158 : smallValid 16158 43 := by unfold smallValid; decide +kernel

private theorem sp16201 : smallValid 16201 44 := by unfold smallValid; decide +kernel

private theorem sp16245 : smallValid 16245 43 := by unfold smallValid; decide +kernel

private theorem sp16288 : smallValid 16288 44 := by unfold smallValid; decide +kernel

private theorem sp16332 : smallValid 16332 44 := by unfold smallValid; decide +kernel

private theorem sp16376 : smallValid 16376 44 := by unfold smallValid; decide +kernel

private theorem sp16420 : smallValid 16420 43 := by unfold smallValid; decide +kernel

private theorem sp16463 : smallValid 16463 44 := by unfold smallValid; decide +kernel

private theorem sp16507 : smallValid 16507 44 := by unfold smallValid; decide +kernel

private theorem sp16551 : smallValid 16551 44 := by unfold smallValid; decide +kernel

private theorem sp16595 : smallValid 16595 43 := by unfold smallValid; decide +kernel

private theorem sp16638 : smallValid 16638 44 := by unfold smallValid; decide +kernel

private theorem sp16682 : smallValid 16682 44 := by unfold smallValid; decide +kernel

private theorem sp16726 : smallValid 16726 44 := by unfold smallValid; decide +kernel

private theorem sp16770 : smallValid 16770 43 := by unfold smallValid; decide +kernel

private theorem sp16813 : smallValid 16813 44 := by unfold smallValid; decide +kernel

private theorem sp16857 : smallValid 16857 43 := by unfold smallValid; decide +kernel

private theorem sp16900 : smallValid 16900 44 := by unfold smallValid; decide +kernel

private theorem sp16944 : smallValid 16944 43 := by unfold smallValid; decide +kernel

private theorem sp16987 : smallValid 16987 44 := by unfold smallValid; decide +kernel

private theorem sp17031 : smallValid 17031 44 := by unfold smallValid; decide +kernel

private theorem sp17075 : smallValid 17075 44 := by unfold smallValid; decide +kernel

private theorem sp17119 : smallValid 17119 43 := by unfold smallValid; decide +kernel

private theorem sp17162 : smallValid 17162 44 := by unfold smallValid; decide +kernel

private theorem sp17206 : smallValid 17206 43 := by unfold smallValid; decide +kernel

private theorem sp17249 : smallValid 17249 44 := by unfold smallValid; decide +kernel

private theorem sp17293 : smallValid 17293 43 := by unfold smallValid; decide +kernel

private theorem sp17336 : smallValid 17336 44 := by unfold smallValid; decide +kernel

private theorem sp17380 : smallValid 17380 44 := by unfold smallValid; decide +kernel

private theorem sp17424 : smallValid 17424 44 := by unfold smallValid; decide +kernel

private theorem sp17468 : smallValid 17468 43 := by unfold smallValid; decide +kernel

private theorem sp17511 : smallValid 17511 44 := by unfold smallValid; decide +kernel

private theorem sp17555 : smallValid 17555 43 := by unfold smallValid; decide +kernel

private theorem sp17598 : smallValid 17598 44 := by unfold smallValid; decide +kernel

private theorem sp17642 : smallValid 17642 43 := by unfold smallValid; decide +kernel

private theorem sp17685 : smallValid 17685 44 := by unfold smallValid; decide +kernel

private theorem sp17729 : smallValid 17729 44 := by unfold smallValid; decide +kernel

private theorem sp17773 : smallValid 17773 44 := by unfold smallValid; decide +kernel

private theorem sp17817 : smallValid 17817 43 := by unfold smallValid; decide +kernel

private theorem sp17860 : smallValid 17860 44 := by unfold smallValid; decide +kernel

private theorem sp17904 : smallValid 17904 44 := by unfold smallValid; decide +kernel

private theorem sp17948 : smallValid 17948 44 := by unfold smallValid; decide +kernel

private theorem sp17992 : smallValid 17992 43 := by unfold smallValid; decide +kernel

private theorem sp18035 : smallValid 18035 44 := by unfold smallValid; decide +kernel

private theorem sp18079 : smallValid 18079 44 := by unfold smallValid; decide +kernel

private theorem sp18123 : smallValid 18123 44 := by unfold smallValid; decide +kernel

private theorem sp18167 : smallValid 18167 43 := by unfold smallValid; decide +kernel

private theorem sp18210 : smallValid 18210 44 := by unfold smallValid; decide +kernel

private theorem sp18254 : smallValid 18254 43 := by unfold smallValid; decide +kernel

private theorem sp18297 : smallValid 18297 44 := by unfold smallValid; decide +kernel

private theorem sp18341 : smallValid 18341 43 := by unfold smallValid; decide +kernel

private theorem sp18384 : smallValid 18384 44 := by unfold smallValid; decide +kernel

private theorem sp18428 : smallValid 18428 44 := by unfold smallValid; decide +kernel

private theorem sp18472 : smallValid 18472 44 := by unfold smallValid; decide +kernel

private theorem sp18516 : smallValid 18516 43 := by unfold smallValid; decide +kernel

private theorem sp18559 : smallValid 18559 44 := by unfold smallValid; decide +kernel

private theorem sp18603 : smallValid 18603 44 := by unfold smallValid; decide +kernel

private theorem sp18647 : smallValid 18647 44 := by unfold smallValid; decide +kernel

private theorem sp18691 : smallValid 18691 43 := by unfold smallValid; decide +kernel

private theorem sp18734 : smallValid 18734 44 := by unfold smallValid; decide +kernel

private theorem sp18778 : smallValid 18778 44 := by unfold smallValid; decide +kernel

private theorem sp18822 : smallValid 18822 44 := by unfold smallValid; decide +kernel

private theorem sp18866 : smallValid 18866 43 := by unfold smallValid; decide +kernel

private theorem sp18909 : smallValid 18909 44 := by unfold smallValid; decide +kernel

private theorem sp18953 : smallValid 18953 43 := by unfold smallValid; decide +kernel

private theorem sp18996 : smallValid 18996 44 := by unfold smallValid; decide +kernel

private theorem sp19040 : smallValid 19040 43 := by unfold smallValid; decide +kernel

private theorem sp19083 : smallValid 19083 44 := by unfold smallValid; decide +kernel

private theorem sp19127 : smallValid 19127 44 := by unfold smallValid; decide +kernel

private theorem sp19171 : smallValid 19171 44 := by unfold smallValid; decide +kernel

private theorem sp19215 : smallValid 19215 43 := by unfold smallValid; decide +kernel

private theorem sp19258 : smallValid 19258 44 := by unfold smallValid; decide +kernel

private theorem sp19302 : smallValid 19302 44 := by unfold smallValid; decide +kernel

private theorem sp19346 : smallValid 19346 44 := by unfold smallValid; decide +kernel

private theorem sp19390 : smallValid 19390 43 := by unfold smallValid; decide +kernel

private theorem sp19433 : smallValid 19433 44 := by unfold smallValid; decide +kernel

private theorem sp19477 : smallValid 19477 44 := by unfold smallValid; decide +kernel

private theorem sp19521 : smallValid 19521 44 := by unfold smallValid; decide +kernel

private theorem sp19565 : smallValid 19565 43 := by unfold smallValid; decide +kernel

private theorem sp19608 : smallValid 19608 44 := by unfold smallValid; decide +kernel

private theorem sp19652 : smallValid 19652 43 := by unfold smallValid; decide +kernel

private theorem sp19695 : smallValid 19695 44 := by unfold smallValid; decide +kernel

private theorem sp19739 : smallValid 19739 43 := by unfold smallValid; decide +kernel

private theorem sp19782 : smallValid 19782 44 := by unfold smallValid; decide +kernel

private theorem sp19826 : smallValid 19826 44 := by unfold smallValid; decide +kernel

private theorem sp19870 : smallValid 19870 44 := by unfold smallValid; decide +kernel

private theorem sp19914 : smallValid 19914 43 := by unfold smallValid; decide +kernel

private theorem sp19957 : smallValid 19957 44 := by unfold smallValid; decide +kernel

private theorem sp20001 : smallValid 20001 44 := by unfold smallValid; decide +kernel

private theorem sp20045 : smallValid 20045 44 := by unfold smallValid; decide +kernel

private theorem sp20089 : smallValid 20089 43 := by unfold smallValid; decide +kernel

private theorem sp20132 : smallValid 20132 44 := by unfold smallValid; decide +kernel

private theorem sp20176 : smallValid 20176 44 := by unfold smallValid; decide +kernel

private theorem sp20220 : smallValid 20220 44 := by unfold smallValid; decide +kernel

private theorem sp20264 : smallValid 20264 43 := by unfold smallValid; decide +kernel

private theorem sp20307 : smallValid 20307 44 := by unfold smallValid; decide +kernel

private theorem sp20351 : smallValid 20351 43 := by unfold smallValid; decide +kernel

private theorem sp20394 : smallValid 20394 44 := by unfold smallValid; decide +kernel

private theorem sp20438 : smallValid 20438 43 := by unfold smallValid; decide +kernel

private theorem sp20481 : smallValid 20481 44 := by unfold smallValid; decide +kernel

private theorem sp20525 : smallValid 20525 44 := by unfold smallValid; decide +kernel

private theorem sp20569 : smallValid 20569 44 := by unfold smallValid; decide +kernel

private theorem sp20613 : smallValid 20613 43 := by unfold smallValid; decide +kernel

private theorem sp20656 : smallValid 20656 44 := by unfold smallValid; decide +kernel

private theorem sp20700 : smallValid 20700 44 := by unfold smallValid; decide +kernel

private theorem sp20744 : smallValid 20744 44 := by unfold smallValid; decide +kernel

private theorem sp20788 : smallValid 20788 43 := by unfold smallValid; decide +kernel

private theorem sp20831 : smallValid 20831 44 := by unfold smallValid; decide +kernel

private theorem sp20875 : smallValid 20875 44 := by unfold smallValid; decide +kernel

private theorem sp20919 : smallValid 20919 44 := by unfold smallValid; decide +kernel

private theorem sp20963 : smallValid 20963 43 := by unfold smallValid; decide +kernel

private theorem sp21006 : smallValid 21006 44 := by unfold smallValid; decide +kernel

private theorem sp21050 : smallValid 21050 43 := by unfold smallValid; decide +kernel

private theorem sp21093 : smallValid 21093 44 := by unfold smallValid; decide +kernel

private theorem sp21137 : smallValid 21137 43 := by unfold smallValid; decide +kernel

private theorem sp21180 : smallValid 21180 44 := by unfold smallValid; decide +kernel

private theorem sp21224 : smallValid 21224 44 := by unfold smallValid; decide +kernel

private theorem sp21268 : smallValid 21268 44 := by unfold smallValid; decide +kernel

private theorem sp21312 : smallValid 21312 43 := by unfold smallValid; decide +kernel

private theorem sp21355 : smallValid 21355 44 := by unfold smallValid; decide +kernel

private theorem sp21399 : smallValid 21399 44 := by unfold smallValid; decide +kernel

private theorem sp21443 : smallValid 21443 44 := by unfold smallValid; decide +kernel

private theorem sp21487 : smallValid 21487 43 := by unfold smallValid; decide +kernel

private theorem sp21530 : smallValid 21530 44 := by unfold smallValid; decide +kernel

private theorem sp21574 : smallValid 21574 44 := by unfold smallValid; decide +kernel

private theorem sp21618 : smallValid 21618 44 := by unfold smallValid; decide +kernel

private theorem sp21662 : smallValid 21662 43 := by unfold smallValid; decide +kernel

private theorem sp21705 : smallValid 21705 44 := by unfold smallValid; decide +kernel

private theorem sp21749 : smallValid 21749 43 := by unfold smallValid; decide +kernel

private theorem sp21792 : smallValid 21792 44 := by unfold smallValid; decide +kernel

private theorem sp21836 : smallValid 21836 43 := by unfold smallValid; decide +kernel

private theorem sp21879 : smallValid 21879 44 := by unfold smallValid; decide +kernel

private theorem sp21923 : smallValid 21923 44 := by unfold smallValid; decide +kernel

private theorem sp21967 : smallValid 21967 44 := by unfold smallValid; decide +kernel

private theorem sp22011 : smallValid 22011 43 := by unfold smallValid; decide +kernel

private theorem sp22054 : smallValid 22054 44 := by unfold smallValid; decide +kernel

private theorem sp22098 : smallValid 22098 44 := by unfold smallValid; decide +kernel

private theorem sp22142 : smallValid 22142 44 := by unfold smallValid; decide +kernel

private theorem sp22186 : smallValid 22186 43 := by unfold smallValid; decide +kernel

private theorem sp22229 : smallValid 22229 44 := by unfold smallValid; decide +kernel

private theorem sp22273 : smallValid 22273 44 := by unfold smallValid; decide +kernel

private theorem sp22317 : smallValid 22317 44 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤22360) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 22361 := (joinSmall (lo:=0) (a:=11180) (b:=11181) (joinSmall (lo:=0) (a:=5590) (b:=5590) (joinSmall (lo:=0) (a:=2795) (b:=2795) (joinSmall (lo:=0) (a:=1397) (b:=1398) (joinSmall (lo:=0) (a:=698) (b:=699) (joinSmall (lo:=0) (a:=349) (b:=349) (joinSmall (lo:=0) (a:=174) (b:=175) (joinSmall (lo:=0) (a:=87) (b:=87) (joinSmall (lo:=0) (a:=43) (b:=44) sp0 sp43) (joinSmall (lo:=87) (a:=43) (b:=44) sp87 sp130)) (joinSmall (lo:=174) (a:=87) (b:=88) (joinSmall (lo:=174) (a:=43) (b:=44) sp174 sp217) (joinSmall (lo:=261) (a:=44) (b:=44) sp261 sp305))) (joinSmall (lo:=349) (a:=174) (b:=175) (joinSmall (lo:=349) (a:=87) (b:=87) (joinSmall (lo:=349) (a:=43) (b:=44) sp349 sp392) (joinSmall (lo:=436) (a:=43) (b:=44) sp436 sp479)) (joinSmall (lo:=523) (a:=87) (b:=88) (joinSmall (lo:=523) (a:=43) (b:=44) sp523 sp566) (joinSmall (lo:=610) (a:=44) (b:=44) sp610 sp654)))) (joinSmall (lo:=698) (a:=349) (b:=350) (joinSmall (lo:=698) (a:=174) (b:=175) (joinSmall (lo:=698) (a:=87) (b:=87) (joinSmall (lo:=698) (a:=43) (b:=44) sp698 sp741) (joinSmall (lo:=785) (a:=43) (b:=44) sp785 sp828)) (joinSmall (lo:=872) (a:=87) (b:=88) (joinSmall (lo:=872) (a:=43) (b:=44) sp872 sp915) (joinSmall (lo:=959) (a:=44) (b:=44) sp959 sp1003))) (joinSmall (lo:=1047) (a:=175) (b:=175) (joinSmall (lo:=1047) (a:=87) (b:=88) (joinSmall (lo:=1047) (a:=43) (b:=44) sp1047 sp1090) (joinSmall (lo:=1134) (a:=44) (b:=44) sp1134 sp1178)) (joinSmall (lo:=1222) (a:=87) (b:=88) (joinSmall (lo:=1222) (a:=43) (b:=44) sp1222 sp1265) (joinSmall (lo:=1309) (a:=44) (b:=44) sp1309 sp1353))))) (joinSmall (lo:=1397) (a:=699) (b:=699) (joinSmall (lo:=1397) (a:=349) (b:=350) (joinSmall (lo:=1397) (a:=174) (b:=175) (joinSmall (lo:=1397) (a:=87) (b:=87) (joinSmall (lo:=1397) (a:=43) (b:=44) sp1397 sp1440) (joinSmall (lo:=1484) (a:=43) (b:=44) sp1484 sp1527)) (joinSmall (lo:=1571) (a:=87) (b:=88) (joinSmall (lo:=1571) (a:=43) (b:=44) sp1571 sp1614) (joinSmall (lo:=1658) (a:=44) (b:=44) sp1658 sp1702))) (joinSmall (lo:=1746) (a:=175) (b:=175) (joinSmall (lo:=1746) (a:=87) (b:=88) (joinSmall (lo:=1746) (a:=43) (b:=44) sp1746 sp1789) (joinSmall (lo:=1833) (a:=44) (b:=44) sp1833 sp1877)) (joinSmall (lo:=1921) (a:=87) (b:=88) (joinSmall (lo:=1921) (a:=43) (b:=44) sp1921 sp1964) (joinSmall (lo:=2008) (a:=44) (b:=44) sp2008 sp2052)))) (joinSmall (lo:=2096) (a:=349) (b:=350) (joinSmall (lo:=2096) (a:=174) (b:=175) (joinSmall (lo:=2096) (a:=87) (b:=87) (joinSmall (lo:=2096) (a:=43) (b:=44) sp2096 sp2139) (joinSmall (lo:=2183) (a:=43) (b:=44) sp2183 sp2226)) (joinSmall (lo:=2270) (a:=87) (b:=88) (joinSmall (lo:=2270) (a:=43) (b:=44) sp2270 sp2313) (joinSmall (lo:=2357) (a:=44) (b:=44) sp2357 sp2401))) (joinSmall (lo:=2445) (a:=175) (b:=175) (joinSmall (lo:=2445) (a:=87) (b:=88) (joinSmall (lo:=2445) (a:=43) (b:=44) sp2445 sp2488) (joinSmall (lo:=2532) (a:=44) (b:=44) sp2532 sp2576)) (joinSmall (lo:=2620) (a:=87) (b:=88) (joinSmall (lo:=2620) (a:=43) (b:=44) sp2620 sp2663) (joinSmall (lo:=2707) (a:=44) (b:=44) sp2707 sp2751)))))) (joinSmall (lo:=2795) (a:=1397) (b:=1398) (joinSmall (lo:=2795) (a:=698) (b:=699) (joinSmall (lo:=2795) (a:=349) (b:=349) (joinSmall (lo:=2795) (a:=174) (b:=175) (joinSmall (lo:=2795) (a:=87) (b:=87) (joinSmall (lo:=2795) (a:=43) (b:=44) sp2795 sp2838) (joinSmall (lo:=2882) (a:=43) (b:=44) sp2882 sp2925)) (joinSmall (lo:=2969) (a:=87) (b:=88) (joinSmall (lo:=2969) (a:=43) (b:=44) sp2969 sp3012) (joinSmall (lo:=3056) (a:=44) (b:=44) sp3056 sp3100))) (joinSmall (lo:=3144) (a:=174) (b:=175) (joinSmall (lo:=3144) (a:=87) (b:=87) (joinSmall (lo:=3144) (a:=43) (b:=44) sp3144 sp3187) (joinSmall (lo:=3231) (a:=43) (b:=44) sp3231 sp3274)) (joinSmall (lo:=3318) (a:=87) (b:=88) (joinSmall (lo:=3318) (a:=43) (b:=44) sp3318 sp3361) (joinSmall (lo:=3405) (a:=44) (b:=44) sp3405 sp3449)))) (joinSmall (lo:=3493) (a:=349) (b:=350) (joinSmall (lo:=3493) (a:=174) (b:=175) (joinSmall (lo:=3493) (a:=87) (b:=87) (joinSmall (lo:=3493) (a:=43) (b:=44) sp3493 sp3536) (joinSmall (lo:=3580) (a:=43) (b:=44) sp3580 sp3623)) (joinSmall (lo:=3667) (a:=87) (b:=88) (joinSmall (lo:=3667) (a:=43) (b:=44) sp3667 sp3710) (joinSmall (lo:=3754) (a:=44) (b:=44) sp3754 sp3798))) (joinSmall (lo:=3842) (a:=175) (b:=175) (joinSmall (lo:=3842) (a:=87) (b:=88) (joinSmall (lo:=3842) (a:=43) (b:=44) sp3842 sp3885) (joinSmall (lo:=3929) (a:=44) (b:=44) sp3929 sp3973)) (joinSmall (lo:=4017) (a:=87) (b:=88) (joinSmall (lo:=4017) (a:=43) (b:=44) sp4017 sp4060) (joinSmall (lo:=4104) (a:=44) (b:=44) sp4104 sp4148))))) (joinSmall (lo:=4192) (a:=699) (b:=699) (joinSmall (lo:=4192) (a:=349) (b:=350) (joinSmall (lo:=4192) (a:=174) (b:=175) (joinSmall (lo:=4192) (a:=87) (b:=87) (joinSmall (lo:=4192) (a:=43) (b:=44) sp4192 sp4235) (joinSmall (lo:=4279) (a:=43) (b:=44) sp4279 sp4322)) (joinSmall (lo:=4366) (a:=87) (b:=88) (joinSmall (lo:=4366) (a:=43) (b:=44) sp4366 sp4409) (joinSmall (lo:=4453) (a:=44) (b:=44) sp4453 sp4497))) (joinSmall (lo:=4541) (a:=175) (b:=175) (joinSmall (lo:=4541) (a:=87) (b:=88) (joinSmall (lo:=4541) (a:=43) (b:=44) sp4541 sp4584) (joinSmall (lo:=4628) (a:=44) (b:=44) sp4628 sp4672)) (joinSmall (lo:=4716) (a:=87) (b:=88) (joinSmall (lo:=4716) (a:=43) (b:=44) sp4716 sp4759) (joinSmall (lo:=4803) (a:=44) (b:=44) sp4803 sp4847)))) (joinSmall (lo:=4891) (a:=349) (b:=350) (joinSmall (lo:=4891) (a:=174) (b:=175) (joinSmall (lo:=4891) (a:=87) (b:=87) (joinSmall (lo:=4891) (a:=43) (b:=44) sp4891 sp4934) (joinSmall (lo:=4978) (a:=43) (b:=44) sp4978 sp5021)) (joinSmall (lo:=5065) (a:=87) (b:=88) (joinSmall (lo:=5065) (a:=43) (b:=44) sp5065 sp5108) (joinSmall (lo:=5152) (a:=44) (b:=44) sp5152 sp5196))) (joinSmall (lo:=5240) (a:=175) (b:=175) (joinSmall (lo:=5240) (a:=87) (b:=88) (joinSmall (lo:=5240) (a:=43) (b:=44) sp5240 sp5283) (joinSmall (lo:=5327) (a:=44) (b:=44) sp5327 sp5371)) (joinSmall (lo:=5415) (a:=87) (b:=88) (joinSmall (lo:=5415) (a:=43) (b:=44) sp5415 sp5458) (joinSmall (lo:=5502) (a:=44) (b:=44) sp5502 sp5546))))))) (joinSmall (lo:=5590) (a:=2795) (b:=2795) (joinSmall (lo:=5590) (a:=1397) (b:=1398) (joinSmall (lo:=5590) (a:=698) (b:=699) (joinSmall (lo:=5590) (a:=349) (b:=349) (joinSmall (lo:=5590) (a:=174) (b:=175) (joinSmall (lo:=5590) (a:=87) (b:=87) (joinSmall (lo:=5590) (a:=43) (b:=44) sp5590 sp5633) (joinSmall (lo:=5677) (a:=43) (b:=44) sp5677 sp5720)) (joinSmall (lo:=5764) (a:=87) (b:=88) (joinSmall (lo:=5764) (a:=43) (b:=44) sp5764 sp5807) (joinSmall (lo:=5851) (a:=44) (b:=44) sp5851 sp5895))) (joinSmall (lo:=5939) (a:=174) (b:=175) (joinSmall (lo:=5939) (a:=87) (b:=87) (joinSmall (lo:=5939) (a:=43) (b:=44) sp5939 sp5982) (joinSmall (lo:=6026) (a:=43) (b:=44) sp6026 sp6069)) (joinSmall (lo:=6113) (a:=87) (b:=88) (joinSmall (lo:=6113) (a:=43) (b:=44) sp6113 sp6156) (joinSmall (lo:=6200) (a:=44) (b:=44) sp6200 sp6244)))) (joinSmall (lo:=6288) (a:=349) (b:=350) (joinSmall (lo:=6288) (a:=174) (b:=175) (joinSmall (lo:=6288) (a:=87) (b:=87) (joinSmall (lo:=6288) (a:=43) (b:=44) sp6288 sp6331) (joinSmall (lo:=6375) (a:=43) (b:=44) sp6375 sp6418)) (joinSmall (lo:=6462) (a:=87) (b:=88) (joinSmall (lo:=6462) (a:=43) (b:=44) sp6462 sp6505) (joinSmall (lo:=6549) (a:=44) (b:=44) sp6549 sp6593))) (joinSmall (lo:=6637) (a:=175) (b:=175) (joinSmall (lo:=6637) (a:=87) (b:=88) (joinSmall (lo:=6637) (a:=43) (b:=44) sp6637 sp6680) (joinSmall (lo:=6724) (a:=44) (b:=44) sp6724 sp6768)) (joinSmall (lo:=6812) (a:=87) (b:=88) (joinSmall (lo:=6812) (a:=43) (b:=44) sp6812 sp6855) (joinSmall (lo:=6899) (a:=44) (b:=44) sp6899 sp6943))))) (joinSmall (lo:=6987) (a:=699) (b:=699) (joinSmall (lo:=6987) (a:=349) (b:=350) (joinSmall (lo:=6987) (a:=174) (b:=175) (joinSmall (lo:=6987) (a:=87) (b:=87) (joinSmall (lo:=6987) (a:=43) (b:=44) sp6987 sp7030) (joinSmall (lo:=7074) (a:=43) (b:=44) sp7074 sp7117)) (joinSmall (lo:=7161) (a:=87) (b:=88) (joinSmall (lo:=7161) (a:=43) (b:=44) sp7161 sp7204) (joinSmall (lo:=7248) (a:=44) (b:=44) sp7248 sp7292))) (joinSmall (lo:=7336) (a:=175) (b:=175) (joinSmall (lo:=7336) (a:=87) (b:=88) (joinSmall (lo:=7336) (a:=43) (b:=44) sp7336 sp7379) (joinSmall (lo:=7423) (a:=44) (b:=44) sp7423 sp7467)) (joinSmall (lo:=7511) (a:=87) (b:=88) (joinSmall (lo:=7511) (a:=43) (b:=44) sp7511 sp7554) (joinSmall (lo:=7598) (a:=44) (b:=44) sp7598 sp7642)))) (joinSmall (lo:=7686) (a:=349) (b:=350) (joinSmall (lo:=7686) (a:=174) (b:=175) (joinSmall (lo:=7686) (a:=87) (b:=87) (joinSmall (lo:=7686) (a:=43) (b:=44) sp7686 sp7729) (joinSmall (lo:=7773) (a:=43) (b:=44) sp7773 sp7816)) (joinSmall (lo:=7860) (a:=87) (b:=88) (joinSmall (lo:=7860) (a:=43) (b:=44) sp7860 sp7903) (joinSmall (lo:=7947) (a:=44) (b:=44) sp7947 sp7991))) (joinSmall (lo:=8035) (a:=175) (b:=175) (joinSmall (lo:=8035) (a:=87) (b:=88) (joinSmall (lo:=8035) (a:=43) (b:=44) sp8035 sp8078) (joinSmall (lo:=8122) (a:=44) (b:=44) sp8122 sp8166)) (joinSmall (lo:=8210) (a:=87) (b:=88) (joinSmall (lo:=8210) (a:=43) (b:=44) sp8210 sp8253) (joinSmall (lo:=8297) (a:=44) (b:=44) sp8297 sp8341)))))) (joinSmall (lo:=8385) (a:=1397) (b:=1398) (joinSmall (lo:=8385) (a:=698) (b:=699) (joinSmall (lo:=8385) (a:=349) (b:=349) (joinSmall (lo:=8385) (a:=174) (b:=175) (joinSmall (lo:=8385) (a:=87) (b:=87) (joinSmall (lo:=8385) (a:=43) (b:=44) sp8385 sp8428) (joinSmall (lo:=8472) (a:=43) (b:=44) sp8472 sp8515)) (joinSmall (lo:=8559) (a:=87) (b:=88) (joinSmall (lo:=8559) (a:=43) (b:=44) sp8559 sp8602) (joinSmall (lo:=8646) (a:=44) (b:=44) sp8646 sp8690))) (joinSmall (lo:=8734) (a:=174) (b:=175) (joinSmall (lo:=8734) (a:=87) (b:=87) (joinSmall (lo:=8734) (a:=43) (b:=44) sp8734 sp8777) (joinSmall (lo:=8821) (a:=43) (b:=44) sp8821 sp8864)) (joinSmall (lo:=8908) (a:=87) (b:=88) (joinSmall (lo:=8908) (a:=43) (b:=44) sp8908 sp8951) (joinSmall (lo:=8995) (a:=44) (b:=44) sp8995 sp9039)))) (joinSmall (lo:=9083) (a:=349) (b:=350) (joinSmall (lo:=9083) (a:=174) (b:=175) (joinSmall (lo:=9083) (a:=87) (b:=87) (joinSmall (lo:=9083) (a:=43) (b:=44) sp9083 sp9126) (joinSmall (lo:=9170) (a:=43) (b:=44) sp9170 sp9213)) (joinSmall (lo:=9257) (a:=87) (b:=88) (joinSmall (lo:=9257) (a:=43) (b:=44) sp9257 sp9300) (joinSmall (lo:=9344) (a:=44) (b:=44) sp9344 sp9388))) (joinSmall (lo:=9432) (a:=175) (b:=175) (joinSmall (lo:=9432) (a:=87) (b:=88) (joinSmall (lo:=9432) (a:=43) (b:=44) sp9432 sp9475) (joinSmall (lo:=9519) (a:=44) (b:=44) sp9519 sp9563)) (joinSmall (lo:=9607) (a:=87) (b:=88) (joinSmall (lo:=9607) (a:=43) (b:=44) sp9607 sp9650) (joinSmall (lo:=9694) (a:=44) (b:=44) sp9694 sp9738))))) (joinSmall (lo:=9782) (a:=699) (b:=699) (joinSmall (lo:=9782) (a:=349) (b:=350) (joinSmall (lo:=9782) (a:=174) (b:=175) (joinSmall (lo:=9782) (a:=87) (b:=87) (joinSmall (lo:=9782) (a:=43) (b:=44) sp9782 sp9825) (joinSmall (lo:=9869) (a:=43) (b:=44) sp9869 sp9912)) (joinSmall (lo:=9956) (a:=87) (b:=88) (joinSmall (lo:=9956) (a:=43) (b:=44) sp9956 sp9999) (joinSmall (lo:=10043) (a:=44) (b:=44) sp10043 sp10087))) (joinSmall (lo:=10131) (a:=175) (b:=175) (joinSmall (lo:=10131) (a:=87) (b:=88) (joinSmall (lo:=10131) (a:=43) (b:=44) sp10131 sp10174) (joinSmall (lo:=10218) (a:=44) (b:=44) sp10218 sp10262)) (joinSmall (lo:=10306) (a:=87) (b:=88) (joinSmall (lo:=10306) (a:=43) (b:=44) sp10306 sp10349) (joinSmall (lo:=10393) (a:=44) (b:=44) sp10393 sp10437)))) (joinSmall (lo:=10481) (a:=349) (b:=350) (joinSmall (lo:=10481) (a:=174) (b:=175) (joinSmall (lo:=10481) (a:=87) (b:=87) (joinSmall (lo:=10481) (a:=43) (b:=44) sp10481 sp10524) (joinSmall (lo:=10568) (a:=43) (b:=44) sp10568 sp10611)) (joinSmall (lo:=10655) (a:=87) (b:=88) (joinSmall (lo:=10655) (a:=43) (b:=44) sp10655 sp10698) (joinSmall (lo:=10742) (a:=44) (b:=44) sp10742 sp10786))) (joinSmall (lo:=10830) (a:=175) (b:=175) (joinSmall (lo:=10830) (a:=87) (b:=88) (joinSmall (lo:=10830) (a:=43) (b:=44) sp10830 sp10873) (joinSmall (lo:=10917) (a:=44) (b:=44) sp10917 sp10961)) (joinSmall (lo:=11005) (a:=87) (b:=88) (joinSmall (lo:=11005) (a:=43) (b:=44) sp11005 sp11048) (joinSmall (lo:=11092) (a:=44) (b:=44) sp11092 sp11136)))))))) (joinSmall (lo:=11180) (a:=5590) (b:=5591) (joinSmall (lo:=11180) (a:=2795) (b:=2795) (joinSmall (lo:=11180) (a:=1397) (b:=1398) (joinSmall (lo:=11180) (a:=698) (b:=699) (joinSmall (lo:=11180) (a:=349) (b:=349) (joinSmall (lo:=11180) (a:=174) (b:=175) (joinSmall (lo:=11180) (a:=87) (b:=87) (joinSmall (lo:=11180) (a:=43) (b:=44) sp11180 sp11223) (joinSmall (lo:=11267) (a:=43) (b:=44) sp11267 sp11310)) (joinSmall (lo:=11354) (a:=87) (b:=88) (joinSmall (lo:=11354) (a:=43) (b:=44) sp11354 sp11397) (joinSmall (lo:=11441) (a:=44) (b:=44) sp11441 sp11485))) (joinSmall (lo:=11529) (a:=174) (b:=175) (joinSmall (lo:=11529) (a:=87) (b:=87) (joinSmall (lo:=11529) (a:=43) (b:=44) sp11529 sp11572) (joinSmall (lo:=11616) (a:=43) (b:=44) sp11616 sp11659)) (joinSmall (lo:=11703) (a:=87) (b:=88) (joinSmall (lo:=11703) (a:=43) (b:=44) sp11703 sp11746) (joinSmall (lo:=11790) (a:=44) (b:=44) sp11790 sp11834)))) (joinSmall (lo:=11878) (a:=349) (b:=350) (joinSmall (lo:=11878) (a:=174) (b:=175) (joinSmall (lo:=11878) (a:=87) (b:=87) (joinSmall (lo:=11878) (a:=43) (b:=44) sp11878 sp11921) (joinSmall (lo:=11965) (a:=43) (b:=44) sp11965 sp12008)) (joinSmall (lo:=12052) (a:=87) (b:=88) (joinSmall (lo:=12052) (a:=43) (b:=44) sp12052 sp12095) (joinSmall (lo:=12139) (a:=44) (b:=44) sp12139 sp12183))) (joinSmall (lo:=12227) (a:=175) (b:=175) (joinSmall (lo:=12227) (a:=87) (b:=88) (joinSmall (lo:=12227) (a:=43) (b:=44) sp12227 sp12270) (joinSmall (lo:=12314) (a:=44) (b:=44) sp12314 sp12358)) (joinSmall (lo:=12402) (a:=87) (b:=88) (joinSmall (lo:=12402) (a:=43) (b:=44) sp12402 sp12445) (joinSmall (lo:=12489) (a:=44) (b:=44) sp12489 sp12533))))) (joinSmall (lo:=12577) (a:=699) (b:=699) (joinSmall (lo:=12577) (a:=349) (b:=350) (joinSmall (lo:=12577) (a:=174) (b:=175) (joinSmall (lo:=12577) (a:=87) (b:=87) (joinSmall (lo:=12577) (a:=43) (b:=44) sp12577 sp12620) (joinSmall (lo:=12664) (a:=43) (b:=44) sp12664 sp12707)) (joinSmall (lo:=12751) (a:=87) (b:=88) (joinSmall (lo:=12751) (a:=43) (b:=44) sp12751 sp12794) (joinSmall (lo:=12838) (a:=44) (b:=44) sp12838 sp12882))) (joinSmall (lo:=12926) (a:=175) (b:=175) (joinSmall (lo:=12926) (a:=87) (b:=88) (joinSmall (lo:=12926) (a:=43) (b:=44) sp12926 sp12969) (joinSmall (lo:=13013) (a:=44) (b:=44) sp13013 sp13057)) (joinSmall (lo:=13101) (a:=87) (b:=88) (joinSmall (lo:=13101) (a:=43) (b:=44) sp13101 sp13144) (joinSmall (lo:=13188) (a:=44) (b:=44) sp13188 sp13232)))) (joinSmall (lo:=13276) (a:=349) (b:=350) (joinSmall (lo:=13276) (a:=174) (b:=175) (joinSmall (lo:=13276) (a:=87) (b:=87) (joinSmall (lo:=13276) (a:=43) (b:=44) sp13276 sp13319) (joinSmall (lo:=13363) (a:=43) (b:=44) sp13363 sp13406)) (joinSmall (lo:=13450) (a:=87) (b:=88) (joinSmall (lo:=13450) (a:=43) (b:=44) sp13450 sp13493) (joinSmall (lo:=13537) (a:=44) (b:=44) sp13537 sp13581))) (joinSmall (lo:=13625) (a:=175) (b:=175) (joinSmall (lo:=13625) (a:=87) (b:=88) (joinSmall (lo:=13625) (a:=43) (b:=44) sp13625 sp13668) (joinSmall (lo:=13712) (a:=44) (b:=44) sp13712 sp13756)) (joinSmall (lo:=13800) (a:=87) (b:=88) (joinSmall (lo:=13800) (a:=43) (b:=44) sp13800 sp13843) (joinSmall (lo:=13887) (a:=44) (b:=44) sp13887 sp13931)))))) (joinSmall (lo:=13975) (a:=1397) (b:=1398) (joinSmall (lo:=13975) (a:=698) (b:=699) (joinSmall (lo:=13975) (a:=349) (b:=349) (joinSmall (lo:=13975) (a:=174) (b:=175) (joinSmall (lo:=13975) (a:=87) (b:=87) (joinSmall (lo:=13975) (a:=43) (b:=44) sp13975 sp14018) (joinSmall (lo:=14062) (a:=43) (b:=44) sp14062 sp14105)) (joinSmall (lo:=14149) (a:=87) (b:=88) (joinSmall (lo:=14149) (a:=43) (b:=44) sp14149 sp14192) (joinSmall (lo:=14236) (a:=44) (b:=44) sp14236 sp14280))) (joinSmall (lo:=14324) (a:=174) (b:=175) (joinSmall (lo:=14324) (a:=87) (b:=87) (joinSmall (lo:=14324) (a:=43) (b:=44) sp14324 sp14367) (joinSmall (lo:=14411) (a:=43) (b:=44) sp14411 sp14454)) (joinSmall (lo:=14498) (a:=87) (b:=88) (joinSmall (lo:=14498) (a:=43) (b:=44) sp14498 sp14541) (joinSmall (lo:=14585) (a:=44) (b:=44) sp14585 sp14629)))) (joinSmall (lo:=14673) (a:=349) (b:=350) (joinSmall (lo:=14673) (a:=174) (b:=175) (joinSmall (lo:=14673) (a:=87) (b:=87) (joinSmall (lo:=14673) (a:=43) (b:=44) sp14673 sp14716) (joinSmall (lo:=14760) (a:=43) (b:=44) sp14760 sp14803)) (joinSmall (lo:=14847) (a:=87) (b:=88) (joinSmall (lo:=14847) (a:=43) (b:=44) sp14847 sp14890) (joinSmall (lo:=14934) (a:=44) (b:=44) sp14934 sp14978))) (joinSmall (lo:=15022) (a:=175) (b:=175) (joinSmall (lo:=15022) (a:=87) (b:=88) (joinSmall (lo:=15022) (a:=43) (b:=44) sp15022 sp15065) (joinSmall (lo:=15109) (a:=44) (b:=44) sp15109 sp15153)) (joinSmall (lo:=15197) (a:=87) (b:=88) (joinSmall (lo:=15197) (a:=43) (b:=44) sp15197 sp15240) (joinSmall (lo:=15284) (a:=44) (b:=44) sp15284 sp15328))))) (joinSmall (lo:=15372) (a:=699) (b:=699) (joinSmall (lo:=15372) (a:=349) (b:=350) (joinSmall (lo:=15372) (a:=174) (b:=175) (joinSmall (lo:=15372) (a:=87) (b:=87) (joinSmall (lo:=15372) (a:=43) (b:=44) sp15372 sp15415) (joinSmall (lo:=15459) (a:=43) (b:=44) sp15459 sp15502)) (joinSmall (lo:=15546) (a:=87) (b:=88) (joinSmall (lo:=15546) (a:=43) (b:=44) sp15546 sp15589) (joinSmall (lo:=15633) (a:=44) (b:=44) sp15633 sp15677))) (joinSmall (lo:=15721) (a:=175) (b:=175) (joinSmall (lo:=15721) (a:=87) (b:=88) (joinSmall (lo:=15721) (a:=43) (b:=44) sp15721 sp15764) (joinSmall (lo:=15808) (a:=44) (b:=44) sp15808 sp15852)) (joinSmall (lo:=15896) (a:=87) (b:=88) (joinSmall (lo:=15896) (a:=43) (b:=44) sp15896 sp15939) (joinSmall (lo:=15983) (a:=44) (b:=44) sp15983 sp16027)))) (joinSmall (lo:=16071) (a:=349) (b:=350) (joinSmall (lo:=16071) (a:=174) (b:=175) (joinSmall (lo:=16071) (a:=87) (b:=87) (joinSmall (lo:=16071) (a:=43) (b:=44) sp16071 sp16114) (joinSmall (lo:=16158) (a:=43) (b:=44) sp16158 sp16201)) (joinSmall (lo:=16245) (a:=87) (b:=88) (joinSmall (lo:=16245) (a:=43) (b:=44) sp16245 sp16288) (joinSmall (lo:=16332) (a:=44) (b:=44) sp16332 sp16376))) (joinSmall (lo:=16420) (a:=175) (b:=175) (joinSmall (lo:=16420) (a:=87) (b:=88) (joinSmall (lo:=16420) (a:=43) (b:=44) sp16420 sp16463) (joinSmall (lo:=16507) (a:=44) (b:=44) sp16507 sp16551)) (joinSmall (lo:=16595) (a:=87) (b:=88) (joinSmall (lo:=16595) (a:=43) (b:=44) sp16595 sp16638) (joinSmall (lo:=16682) (a:=44) (b:=44) sp16682 sp16726))))))) (joinSmall (lo:=16770) (a:=2795) (b:=2796) (joinSmall (lo:=16770) (a:=1397) (b:=1398) (joinSmall (lo:=16770) (a:=698) (b:=699) (joinSmall (lo:=16770) (a:=349) (b:=349) (joinSmall (lo:=16770) (a:=174) (b:=175) (joinSmall (lo:=16770) (a:=87) (b:=87) (joinSmall (lo:=16770) (a:=43) (b:=44) sp16770 sp16813) (joinSmall (lo:=16857) (a:=43) (b:=44) sp16857 sp16900)) (joinSmall (lo:=16944) (a:=87) (b:=88) (joinSmall (lo:=16944) (a:=43) (b:=44) sp16944 sp16987) (joinSmall (lo:=17031) (a:=44) (b:=44) sp17031 sp17075))) (joinSmall (lo:=17119) (a:=174) (b:=175) (joinSmall (lo:=17119) (a:=87) (b:=87) (joinSmall (lo:=17119) (a:=43) (b:=44) sp17119 sp17162) (joinSmall (lo:=17206) (a:=43) (b:=44) sp17206 sp17249)) (joinSmall (lo:=17293) (a:=87) (b:=88) (joinSmall (lo:=17293) (a:=43) (b:=44) sp17293 sp17336) (joinSmall (lo:=17380) (a:=44) (b:=44) sp17380 sp17424)))) (joinSmall (lo:=17468) (a:=349) (b:=350) (joinSmall (lo:=17468) (a:=174) (b:=175) (joinSmall (lo:=17468) (a:=87) (b:=87) (joinSmall (lo:=17468) (a:=43) (b:=44) sp17468 sp17511) (joinSmall (lo:=17555) (a:=43) (b:=44) sp17555 sp17598)) (joinSmall (lo:=17642) (a:=87) (b:=88) (joinSmall (lo:=17642) (a:=43) (b:=44) sp17642 sp17685) (joinSmall (lo:=17729) (a:=44) (b:=44) sp17729 sp17773))) (joinSmall (lo:=17817) (a:=175) (b:=175) (joinSmall (lo:=17817) (a:=87) (b:=88) (joinSmall (lo:=17817) (a:=43) (b:=44) sp17817 sp17860) (joinSmall (lo:=17904) (a:=44) (b:=44) sp17904 sp17948)) (joinSmall (lo:=17992) (a:=87) (b:=88) (joinSmall (lo:=17992) (a:=43) (b:=44) sp17992 sp18035) (joinSmall (lo:=18079) (a:=44) (b:=44) sp18079 sp18123))))) (joinSmall (lo:=18167) (a:=699) (b:=699) (joinSmall (lo:=18167) (a:=349) (b:=350) (joinSmall (lo:=18167) (a:=174) (b:=175) (joinSmall (lo:=18167) (a:=87) (b:=87) (joinSmall (lo:=18167) (a:=43) (b:=44) sp18167 sp18210) (joinSmall (lo:=18254) (a:=43) (b:=44) sp18254 sp18297)) (joinSmall (lo:=18341) (a:=87) (b:=88) (joinSmall (lo:=18341) (a:=43) (b:=44) sp18341 sp18384) (joinSmall (lo:=18428) (a:=44) (b:=44) sp18428 sp18472))) (joinSmall (lo:=18516) (a:=175) (b:=175) (joinSmall (lo:=18516) (a:=87) (b:=88) (joinSmall (lo:=18516) (a:=43) (b:=44) sp18516 sp18559) (joinSmall (lo:=18603) (a:=44) (b:=44) sp18603 sp18647)) (joinSmall (lo:=18691) (a:=87) (b:=88) (joinSmall (lo:=18691) (a:=43) (b:=44) sp18691 sp18734) (joinSmall (lo:=18778) (a:=44) (b:=44) sp18778 sp18822)))) (joinSmall (lo:=18866) (a:=349) (b:=350) (joinSmall (lo:=18866) (a:=174) (b:=175) (joinSmall (lo:=18866) (a:=87) (b:=87) (joinSmall (lo:=18866) (a:=43) (b:=44) sp18866 sp18909) (joinSmall (lo:=18953) (a:=43) (b:=44) sp18953 sp18996)) (joinSmall (lo:=19040) (a:=87) (b:=88) (joinSmall (lo:=19040) (a:=43) (b:=44) sp19040 sp19083) (joinSmall (lo:=19127) (a:=44) (b:=44) sp19127 sp19171))) (joinSmall (lo:=19215) (a:=175) (b:=175) (joinSmall (lo:=19215) (a:=87) (b:=88) (joinSmall (lo:=19215) (a:=43) (b:=44) sp19215 sp19258) (joinSmall (lo:=19302) (a:=44) (b:=44) sp19302 sp19346)) (joinSmall (lo:=19390) (a:=87) (b:=88) (joinSmall (lo:=19390) (a:=43) (b:=44) sp19390 sp19433) (joinSmall (lo:=19477) (a:=44) (b:=44) sp19477 sp19521)))))) (joinSmall (lo:=19565) (a:=1398) (b:=1398) (joinSmall (lo:=19565) (a:=699) (b:=699) (joinSmall (lo:=19565) (a:=349) (b:=350) (joinSmall (lo:=19565) (a:=174) (b:=175) (joinSmall (lo:=19565) (a:=87) (b:=87) (joinSmall (lo:=19565) (a:=43) (b:=44) sp19565 sp19608) (joinSmall (lo:=19652) (a:=43) (b:=44) sp19652 sp19695)) (joinSmall (lo:=19739) (a:=87) (b:=88) (joinSmall (lo:=19739) (a:=43) (b:=44) sp19739 sp19782) (joinSmall (lo:=19826) (a:=44) (b:=44) sp19826 sp19870))) (joinSmall (lo:=19914) (a:=175) (b:=175) (joinSmall (lo:=19914) (a:=87) (b:=88) (joinSmall (lo:=19914) (a:=43) (b:=44) sp19914 sp19957) (joinSmall (lo:=20001) (a:=44) (b:=44) sp20001 sp20045)) (joinSmall (lo:=20089) (a:=87) (b:=88) (joinSmall (lo:=20089) (a:=43) (b:=44) sp20089 sp20132) (joinSmall (lo:=20176) (a:=44) (b:=44) sp20176 sp20220)))) (joinSmall (lo:=20264) (a:=349) (b:=350) (joinSmall (lo:=20264) (a:=174) (b:=175) (joinSmall (lo:=20264) (a:=87) (b:=87) (joinSmall (lo:=20264) (a:=43) (b:=44) sp20264 sp20307) (joinSmall (lo:=20351) (a:=43) (b:=44) sp20351 sp20394)) (joinSmall (lo:=20438) (a:=87) (b:=88) (joinSmall (lo:=20438) (a:=43) (b:=44) sp20438 sp20481) (joinSmall (lo:=20525) (a:=44) (b:=44) sp20525 sp20569))) (joinSmall (lo:=20613) (a:=175) (b:=175) (joinSmall (lo:=20613) (a:=87) (b:=88) (joinSmall (lo:=20613) (a:=43) (b:=44) sp20613 sp20656) (joinSmall (lo:=20700) (a:=44) (b:=44) sp20700 sp20744)) (joinSmall (lo:=20788) (a:=87) (b:=88) (joinSmall (lo:=20788) (a:=43) (b:=44) sp20788 sp20831) (joinSmall (lo:=20875) (a:=44) (b:=44) sp20875 sp20919))))) (joinSmall (lo:=20963) (a:=699) (b:=699) (joinSmall (lo:=20963) (a:=349) (b:=350) (joinSmall (lo:=20963) (a:=174) (b:=175) (joinSmall (lo:=20963) (a:=87) (b:=87) (joinSmall (lo:=20963) (a:=43) (b:=44) sp20963 sp21006) (joinSmall (lo:=21050) (a:=43) (b:=44) sp21050 sp21093)) (joinSmall (lo:=21137) (a:=87) (b:=88) (joinSmall (lo:=21137) (a:=43) (b:=44) sp21137 sp21180) (joinSmall (lo:=21224) (a:=44) (b:=44) sp21224 sp21268))) (joinSmall (lo:=21312) (a:=175) (b:=175) (joinSmall (lo:=21312) (a:=87) (b:=88) (joinSmall (lo:=21312) (a:=43) (b:=44) sp21312 sp21355) (joinSmall (lo:=21399) (a:=44) (b:=44) sp21399 sp21443)) (joinSmall (lo:=21487) (a:=87) (b:=88) (joinSmall (lo:=21487) (a:=43) (b:=44) sp21487 sp21530) (joinSmall (lo:=21574) (a:=44) (b:=44) sp21574 sp21618)))) (joinSmall (lo:=21662) (a:=349) (b:=350) (joinSmall (lo:=21662) (a:=174) (b:=175) (joinSmall (lo:=21662) (a:=87) (b:=87) (joinSmall (lo:=21662) (a:=43) (b:=44) sp21662 sp21705) (joinSmall (lo:=21749) (a:=43) (b:=44) sp21749 sp21792)) (joinSmall (lo:=21836) (a:=87) (b:=88) (joinSmall (lo:=21836) (a:=43) (b:=44) sp21836 sp21879) (joinSmall (lo:=21923) (a:=44) (b:=44) sp21923 sp21967))) (joinSmall (lo:=22011) (a:=175) (b:=175) (joinSmall (lo:=22011) (a:=87) (b:=88) (joinSmall (lo:=22011) (a:=43) (b:=44) sp22011 sp22054) (joinSmall (lo:=22098) (a:=44) (b:=44) sp22098 sp22142)) (joinSmall (lo:=22186) (a:=87) (b:=88) (joinSmall (lo:=22186) (a:=43) (b:=44) sp22186 sp22229) (joinSmall (lo:=22273) (a:=44) (b:=44) sp22273 sp22317)))))))))
  have good : (List.range 22361).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 500000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 22360 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 22360 := by
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


private def packet (i : ℕ) : ℕ := (if i < 127 then (if i < 63 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0 else 0) else (if i < 10 then 0 else 0)) else (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else 0)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0 else 0) else (if i < 18 then 0 else 0)) else (if i < 21 then (if i < 20 then 0 else 0) else (if i < 22 then 0 else 0))) else (if i < 27 then (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else 0)) else (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else 0))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then 0 else 0) else (if i < 34 then 0 else 0)) else (if i < 37 then (if i < 36 then 0 else 0) else (if i < 38 then 0 else 0))) else (if i < 43 then (if i < 41 then (if i < 40 then 0 else 0) else (if i < 42 then 0 else 0)) else (if i < 45 then (if i < 44 then 0 else 0) else (if i < 46 then 0 else 0)))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then 0 else 0) else (if i < 50 then 0 else 0)) else (if i < 53 then (if i < 52 then 0 else 0) else (if i < 54 then 0 else 0))) else (if i < 59 then (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else 0)) else (if i < 61 then (if i < 60 then 0 else 0) else (if i < 62 then 0 else 0)))))) else (if i < 95 then (if i < 79 then (if i < 71 then (if i < 67 then (if i < 65 then (if i < 64 then 0 else 0) else (if i < 66 then 0 else 0)) else (if i < 69 then (if i < 68 then 0 else 0) else (if i < 70 then 0 else 0))) else (if i < 75 then (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else 0)) else (if i < 77 then (if i < 76 then 0 else 0) else (if i < 78 then 0 else 0)))) else (if i < 87 then (if i < 83 then (if i < 81 then (if i < 80 then 0 else 0) else (if i < 82 then 0 else 0)) else (if i < 85 then (if i < 84 then 0 else 0) else (if i < 86 then 0 else 0))) else (if i < 91 then (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else 0)) else (if i < 93 then (if i < 92 then 0 else 0) else (if i < 94 then 0 else 0))))) else (if i < 111 then (if i < 103 then (if i < 99 then (if i < 97 then (if i < 96 then 0 else 0) else (if i < 98 then 0 else 0)) else (if i < 101 then (if i < 100 then 0 else 0) else (if i < 102 then 0 else 0))) else (if i < 107 then (if i < 105 then (if i < 104 then 0 else 0) else (if i < 106 then 0 else 0)) else (if i < 109 then (if i < 108 then 0 else 0) else (if i < 110 then 0 else 0)))) else (if i < 119 then (if i < 115 then (if i < 113 then (if i < 112 then 0 else 0) else (if i < 114 then 0 else 0)) else (if i < 117 then (if i < 116 then 0 else 0) else (if i < 118 then 0 else 0))) else (if i < 123 then (if i < 121 then (if i < 120 then 0 else 0) else (if i < 122 then 0 else 0)) else (if i < 125 then (if i < 124 then 0 else 0) else (if i < 126 then 0 else 0))))))) else (if i < 191 then (if i < 159 then (if i < 143 then (if i < 135 then (if i < 131 then (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else 0)) else (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else 0))) else (if i < 139 then (if i < 137 then (if i < 136 then 0 else 0) else (if i < 138 then 0 else 0)) else (if i < 141 then (if i < 140 then 0 else 0) else (if i < 142 then 0 else 0)))) else (if i < 151 then (if i < 147 then (if i < 145 then (if i < 144 then 0 else 0) else (if i < 146 then 0 else 0)) else (if i < 149 then (if i < 148 then 0 else 0) else (if i < 150 then 0 else 0))) else (if i < 155 then (if i < 153 then (if i < 152 then 0 else 0) else (if i < 154 then 0 else 0)) else (if i < 157 then (if i < 156 then 0 else 0) else (if i < 158 then 0 else 0))))) else (if i < 175 then (if i < 167 then (if i < 163 then (if i < 161 then (if i < 160 then 0 else 0) else (if i < 162 then 0 else 0)) else (if i < 165 then (if i < 164 then 0 else 0) else (if i < 166 then 0 else 0))) else (if i < 171 then (if i < 169 then (if i < 168 then 0 else 0) else (if i < 170 then 0 else 0)) else (if i < 173 then (if i < 172 then 0 else 0) else (if i < 174 then 0 else 0)))) else (if i < 183 then (if i < 179 then (if i < 177 then (if i < 176 then 0 else 0) else (if i < 178 then 0 else 0)) else (if i < 181 then (if i < 180 then 0 else 0) else (if i < 182 then 0 else 0))) else (if i < 187 then (if i < 185 then (if i < 184 then 0 else 0) else (if i < 186 then 0 else 0)) else (if i < 189 then (if i < 188 then 0 else 0) else (if i < 190 then 0 else 0)))))) else (if i < 223 then (if i < 207 then (if i < 199 then (if i < 195 then (if i < 193 then (if i < 192 then 0 else 0) else (if i < 194 then 0 else 0)) else (if i < 197 then (if i < 196 then 0 else 0) else (if i < 198 then 0 else 0))) else (if i < 203 then (if i < 201 then (if i < 200 then 0 else 0) else (if i < 202 then 0 else 0)) else (if i < 205 then (if i < 204 then 0 else 0) else (if i < 206 then 0 else 0)))) else (if i < 215 then (if i < 211 then (if i < 209 then (if i < 208 then 0 else 0) else (if i < 210 then 0 else 0)) else (if i < 213 then (if i < 212 then 0 else 0) else (if i < 214 then 0 else 0))) else (if i < 219 then (if i < 217 then (if i < 216 then 0 else 0) else (if i < 218 then 0 else 0)) else (if i < 221 then (if i < 220 then 0 else 0) else (if i < 222 then 0 else 0))))) else (if i < 239 then (if i < 231 then (if i < 227 then (if i < 225 then (if i < 224 then 0 else 0) else (if i < 226 then 0 else 0)) else (if i < 229 then (if i < 228 then 0 else 0) else (if i < 230 then 0 else 0))) else (if i < 235 then (if i < 233 then (if i < 232 then 0 else 0) else (if i < 234 then 0 else 0)) else (if i < 237 then (if i < 236 then 0 else 0) else (if i < 238 then 0 else 0)))) else (if i < 247 then (if i < 243 then (if i < 241 then (if i < 240 then 0 else 0) else (if i < 242 then 0 else 0)) else (if i < 245 then (if i < 244 then 0 else 0) else (if i < 246 then 0 else 0))) else (if i < 251 then (if i < 249 then (if i < 248 then 0 else 0) else (if i < 250 then 0 else 0)) else (if i < 253 then (if i < 252 then 0x18eabaa2cd94f09ca4842128f006b02f214a08b839417108a82e00cc000018ea5ba2c3148c99846c2058ec46a42f214788e43b617d09203280ce000018e9fae2d694f89b647d20e8f046d030a155094c3fa19309c031c0ba000018e999f2d4153c9d24912180f446de31115609583d8180091831c0d0000018e93912d7954c9ec49b21b8f586d22fe151890c3b618609203100c0000018e8d9c2d095089bc48320e8f106d830b15009083c017f09182fc0cc000018e87792da15349d048b2148f206d630915789083b817a08f03280c6000018e81802ce95109b84832138f086d630c15089143be18409483140cc000018e7b602de159c9f64972188f1c6c830415689343d018509403100be000018e753a2e21558a044912200f586f831f15c09483e8190095032c0e8000018e6f362d395309d048d2158f686dc30c15809203e019609a03380c8000018e69362d595209d64852100ef86c230515209183ee18409503040d4000018e63392cc94a499047520a0ed46ba2ff15088f43ba17c08882c80a8000018e5d5d2be14709804652070e986962e514808d039617f08e83100b6000018e57412de959ca0049a21a0f546e030115389443d218608c02fc0ca000018e51262db95389d648420f8f146c22f614f891c3d618308e82f80b6000018e4b3b2c914f89ba48720e0f346de31115309303da17f08e83180c0000018e45462cd95209d64862130f1c6d4307155891c3ce18009183100d2000018e3f572cd14c099e46820a8ea86ac2fd14b08c43ac17208c82fc0ae000018e39422d615649ec4872108f146cc30415109083c218209183040c8000018e335a2c8948c97a4561fc0e486822ef14e08d03a217308982cc0aa000018e2d4a2dc15889fa4a421c8f606e830e154893c3e618e09083140be000018e274f2cf95189c047d2158f1c6c22fd14d88f83bc17608d82f00c4000018e21662c494a497a45a2030e746782e114188883a017708e02f40b4000018e1b612d395389d848a20f8ec46942f414b88e439c17408c02e00ba000018e15652ce950c9a247020d0f046b230815188e83b617908f02f40c4000018e0f6c2cc94f49d24852108ee86c42fa15008d43b417b09003000b4000018e096b2cc14dc9be4882148f306ca307151890c3c418609383300ca000018e03602d995509e24932210f5c6de30d15989283e218f09783340d6000018dfd772c394b498e4642020e906602d513a087c38216c08602d80b6000018df7542df95789fc49e21b8f5c70431715889543fc19009883280ce000018df17b2c194889864662010e8069a30515289043cc18408f82e80be000018deb642db9578a0049e2210f946f231215509183da18709183000ba000018de56e2c714a898a45c1fe0e746762d013e08b03ae16d08982e40b4000018ddf712cf14dc9c048d2178f346ca30415289283d617f09002d00b8000018dd96c2d015109de49421c0f406e431315809083b818108f030c0c2000018dd3732d095049d447c2110eec6aa2ee14808f03d018809603400d0000018dcd4f2e315889fe4992188f286d230c15e89443e018809282dc0a0000018dc7322e0958c9fc49e2208f646f031715c098040019409603100ce000018dc1812ad94189604551f90e3065a2c8135089438216f08a82f00b2000018dbb862c6948498e4612008e886aa2ef147889439c17608c031c0ca000018db57a2d295349c44762020eac67a2ea14588d83a617508f82fc0aa000018daf922c694a89b84822108f006be2fe14f09203cc18309003100cc000018da9ad2c194b098a4692098ee069c2f014908d43aa17108882d40be000018da39e2d515289f048a2170f346d430d156093c3f619009c031c0ce000018d9dd62b694289684682010e5467c2ec14c891c3ce18108f82f80ce000018d97ce2d895449e649521c0f0c6c62fe15189243ce17508c02f80b8000018d91e22ca15109d847920b8eec6a42ed14888ec3cc18a08f02fc0c4000018d8bb12e395789ec4902150f306d830c156091c3e418108a82d00b8000018d858e2db958ca0e49f2220f906f2313155092c3d619009303180c8000018d7f9e2ce951c9e248a2160f0c6d030a14f08f83c417a09683340c6000018d799a2ce14d09ae47120b0eb469a2f214708f43a417309103040b0000018d737b2d795109b647b20f0ef86c82ff15009203c417d08a02e00b4000018d6d382f61648a524c622c0fc072031f16109783f819109903200ba000018d67462c594f49ae47d2120f286c430815b89443e418d09583280cc000018d613f2d0951c9c84872160f1c6d830315509103c618d08f02e80a8000018d5b4b2cc94909884702068e9c6842eb14888d03a217008a82dc0bc000018d55462d095289d048a2120f0469e2e914c08f43be18309003240c2000018d4f282e31598a084a321b8f606e632216089803ea18909a032c0cc000018d49502c014889824612020eb069c2ef14688e03c8182094030c0d2000018d43382da15609e04902180f586e2307153090c3d018709102e40b6000018d3d262d815149e04852130f086b430115309303d618d09983140be000018d37352c6149c98e45b1ff0eac6a62f814e09183aa17c08d83040ca000018d31402c914b898046c2048e8c67a2e5142089c39217408d82dc0ac000 else 0x1902bb52c914dc9b247820d8ed46ae30014f88fc3b6182090830c0d00000190258e2de95549da48a21b8f306ce305153090c3d417a08a02d40be00001901fa52c694cc99c4722090ed46ae2f814f09003b218408e02f40be000019019932d595189ce4832148f306d831e15809203de19709c834c0ce000019013b12c194889884662050eb869c2e514788a039016908b03040bc00001900dbe2ca94e49be48720f0ef46a82ff15288fc3ba18709003380d4000019007bc2cd14d89ae47620c8ee06b02fa14d88e43a017b08f83100be000019001ab2da15309c248420f8ee06b42f915509203c618809382fc0be000018ffba82d294e49b247b20c8ed46a42ea14488a03a017508b82c40ac000018ff5a22ce95049c047b20e0ed06a02f014308a03a416b08502c00ac000018fef8e2d9955c9f049b2210f806f031d15b89543e418c09803340d4000018fe9812d7953c9e24a02178f186d430215789183c418009282cc0b2000018fe3612df15409ce47f20e0f006d431215e89543ee18e09683280cc000018fdd562d395589b04782128f006d030314b08f83be188093831c0c6000018fd7622c814ec9b248020d0ef06c430715688fc3ae17d08f02fc0be000018fd1652ca14d09a847620b0eb46882f914e88f43ba18709202f80ac000018fcb5a2d495089ba4822100f186ca30615408f43cc18008882a40a8000018fc58c2b614489584551fb0e9069e2ec14708b43b417108f02e00a0000018fbf7e2dd1574a0449c2188f486dc30515189383de18f08f83300c0000018fb97f2d495389f048f21a8f546e6309154892c3da18409182f40b6000018fb3642d3952c9de48f2160f106b02f414508b83a617609082d80c0000018fad722c714e09aa47820c8ec46ae2f614a88ec3ca19009003000bc000018fa7952bb14a899246c2090eb46982ee14808f43c218409302fc0b8000018fa1b12c5149499246b2058ea06aa2f914b09103ba18008f02dc0ac000018f9ba32d715209d048f20e0ee06ae30414f89043b417708a82ec0b6000018f958e2e095649f049c21a0f3c6d430d15589143cc18209082f00ca000018f8f9f2c614b09b647a20b0ed46a82f114688b03a417308982a80b0000018f89a22d315489ea48c2158ef86da30515109183c818809182e40c0000018f839c2d315049c248520f0f206d430515189203c818308f03080b8000018f7d822d915549ea49221c8f446bc30a15289343ea191094830c0bc000018f77712d695489d24852138f346d630b15309043a218308e03180c8000018f71662d415049ca4812148f286dc30b154897c3da18b095831c0c8000018f6b812c1149899046f2090edc68e2e4141089c39817008d82cc0cc000018f658f2c814a89844621fd0e7467c2e0143889038416908302c80c2000018f5f9c2ca14b09964682050e986862eb14a888438e15a08902bc0ba000018f596c2e495989f849721e0f8870832516189903f4194096834c0ce000018f53942c0148c98e46d2028e8067e2dd142889c38e16308a82dc0be000018f4da42c494889a44662090ec86c430414c890c3ce18709503240b4000018f479d2d8954c9d64862108ee86ba2fc15208e83b217c091832c0c8000018f41dc2b1941c9564511fc0e6066a2d113d08a03a217c090031c0b4000018f3bbc2e0156c9ee48c2178f006ce30115609343d218e096031c0ce000018f35f32b1942895e45c1fc0e746802f014908d03b417b09002f00b4000018f2fd92e215889f64972228f9c6f631d15909243b818409103100d4000018f29e72c794889a84742050ec06ac2ef14b88fc3b417a08d82ec0c0000018f23c12df95989f44962198f486cc30b15d89743de18508f82f80b6000018f1dca2c814ec9bc4802118f0c6c42fd14f08e03ca18109802fc0c6000018f17c32d315049b84832118f106dc30915009083d018709183140c4000018f119f2e395809f44952190f606ea30c15609383ec19d09f03580da000018f0b7f2e115909fa49e21b8f446d831415909243ce17a08a02e80be000018f056c2da155c9da48220c0ecc6ba30c15409083c218509083180c6000018eff4a2e39580a0649e2218f8870c32216089743f419d0a203500d8000018ef93f2d9956c9f049721b8f6c70831e160097c40a19709983300d6000018ef3722b6946496044d1fa0e4c6622d313e887439216b08682d80a6000018eed472e1955c9ec49021c8f546da30415189043be17508c02f40cc000018ee7802af13f09364451f60e2c6642d213b086c38c16c08802a80a0000018ee16a2da15349d448a2110efc6aa2f814d88fc3d4189092033c0d6000018edb982be947499246b2030e846742dd13f08cc39e16d08502dc0ba000018ed5882d795709ce4862150f206e22fe14608d039a16f08202cc0d6000018ecf982c614d899447320d8f146d630715189203ec18e09b834c0cc000018ec9a42cc14ec9c84842108f106b62ff14b08e83b417108402bc0b8000018ec3ae2c794c89944742060ebc67e2e214608e03b616c08982d00ba000018ebdca2c994c09a24732068e8c6a42f714488d039e16f08682c00a4000018eb7e12c214b49a04702080eec6ae2fe15289183c218608f82dc0b6000018eb1ac2eb95b49fe4a32228f906e230c15709403e218408c02dc0c6000) else (if i < 254 then 0x191aa812ea158ca064aa2240f8c6f831b15c093c3d419209583380cc0000191a4a12be14a498a4612030e8869a2ee14788f43b618a09703180b400001919e832df15649ec4912168f506e030f15809183d218d08d82d80a4000019198992c614a09a04702100f086cc30a15589443ca18309083140b0000019192ad2c694b49a447320d0ef46a82f814c89003c417c08e03000c000001918c972d695409dc4872140f1c6ee31d167897c3ce17908982d00b20000191868a2d0151c9bc4832118ef06ba2fb14c88b439a17308782bc0b2000019180a12c694a89a04621ff8e806942f6149089437216708d02d40a600001917ab12c714bc9924672068ec46a22f414b08b439c17508e03000be000019174b32d1950c9cc4852100ee86da30d15809543da18b09683140c200001916eeb2b7947099045d1fa8e706742e814388943a216e08782f00c8000019168c82e715d0a024a021e8f646de30b15c89383d218109002f40bc000019162c52d015189cc48a2170f4c6dc30014f090c3d018a09003300c600001915cdf2c094a89a047120a8ec069e2f314e09003a417608682b80a0000019157012c1147097e4642048ecc6a82f514688d83ce17c08e03080ae000019150dc2df95549e24892160f106da31515789383dc18a093832c0dc00001914b002bb14909b847620d0ed06b22ea14588d83ac17008f82e40a4000019145282bb14489624582028ea06982e714608c43ac17408c02f40b000001913f072e1957c9e648b2188f306dc30415389003c017e08e02f00b6000019139142c994d09bc4852100f246b830015289143c418d09503180be000019133292c614d49b24822180f586f831615609343da18308e02f00be00001912cf32ea15a8a1c4aa2258fa471433216289683de18f09503040c6000019126fd2cb94bc9ae47d2128f286c630d15288fc3c217f08e02fc0b4000019121272be948098a45d2050ed46ba2f814c88f43b418009483100be00001911b3b2bd147898c46d2050eb069e2fc14888d03b417c08b82d00b0000019115442cb94bc9a04702070ee06ca30c153893c3d618509403100ba00001910f272de95309d248f2158f4c6ce30f15489003da18e09303040c4000019109312d5152c9de49021d0f586e431015709443f419809c83700d0000019103352ca94c899246b20a0ebc69c2f314d88d83b017c08e03040bc0000190fd262da15749f249a21e8f886ea31e15a89583e618d09803400c00000190f71b2d295349de4952190f3c6e831915a09483de18e09e03200b60000190f11f2c994c09aa4882130f186b02f314608c03a017208d82d40ce0000190eb252d0952c9e648b21c0f486d231015789503ea19309503480dc0000190e5402c614a09844682030e906882de14588e83b417f09003100c80000190df5b2c794bc9be47e20f8efc6be30215309183d419209403140d00000190d9362e515689f849c21f0f7871231715a09343dc18e095832c0cc0000190d3172e095609f849321a0f586e031215c89543e419109303040c20000190cd052d895289c247e2148f306de31615b09583ee18308f82e80c60000190c7032d195009f249321b0f686d630615789003be17e08b82ec0c40000190c1022d5953c9e849821b8f706ee31b15889303d819009803240dc0000190bb232bd945c9824642078eb869c2f114789003b417208782c80bc0000190b5232d095189c64842118f086b02ec14408f03a417608982c00b00000190af1b2d615309cc47b2140f306d230315188f03b217708a82f00ac0000190a9122d095389c04892130f1c6ba303154892c3d618909182f80ba0000190a32e2c1949c98e4652048e9c68a2e714488e43b817f09002ec0aa00001909d312d014f09b247820b8ee46962e8145088438e17608a02e40c0000019097482c294989944662020e9869a2f414d88e83aa17208c82ec0aa000019091502cb150c9e64922158f2c6e431515b89243c218908d02f00bc00001908b392dc1580a004a22238f8070a31615f89783e018709403080b20000190853b2d495149c84892178f8070230f15d89544021a009a83440d400001907f702b4941c9424431fa0e8c6902f214908c83a016808682c809c000019079832cb15049cc4902140efc6b22ef14888c03ae17d08e02c00b8000019073832cf94d09b047f20d0f086bc2f614808e43aa18208f02e80bc00001906d882d014f09ae46f20f0efc6ce31215a89383d218b09383040c4000019067862cd15149c84812128f206ec31415c09483c218709202fc0ce000019061912d315209d84892180f406e630d158092c3e019209a83500e200001905bbb2b8146898c45f2010e946862e614408883b417808a02d009e000019055a12da15389ca4842100ef06ca30e15809303d618408d82e40c000001904fa92d395109d44842188f446e4313159094c3dc18c09403140ca000019049a22d495149da48c21a0f206b42f714d89003c217608d03100c2000019043852dd15749f84942180f206d62ff158094c3dc18909402f80be00001903d982cb94e49b24802148f486ea31015f09583f419b09c83480e4000019037b92c014b49aa47620e0ecc6a02f214b88c83ac17308e83100b4000019031aa2da95549ec48b20f8ec86a82f614d08d83a617508d03180d6000 else 0x192285400000000000000000000000000000000000000000000000da0000192224d2d094f89ae4772100ef06c630a155893c3de17f09002f00c000001921c3b2db15409e84902190f286be30315809543ec19a09883500e0000019216352d815409d649521a8f4c6e230715188f43bc18608f02c80b0000019210462cd14d49b246d2080ec06a22f414588a038e16808882dc0bc00001920a622c6149098e47420a8ef86d030214e88ec3b018609583000b2000019204712c794d098c46620b0eb46922ef14b08f03b217608e83140c40000191fe992c094a09a64742058e8c6922eb14608d43a016c08602cc0a40000191f88c2d294ec9a646c20b8f286da30d15309243ca18a095830c0b80000191f2912cb94f49be4872140f1c6d430c15609243c617f09183200ca0000191eca52c894b09984602028eb469c2f114b88c83ca19009803340c80000191e6af2c994ec9bc47b20f0f246c6300154090c3c217a08d82c00b60000191e09e2dc95509e84a121e0f806f231115b094c3f61a009a83100cc0000191dac22c194b897e45e1fc8e6068a2e014588bc3a217208c02cc0b80000191d4932e31594a024a32200f686ec31715c09503dc18409303240ba0000191ce8b2d094dc9c44912130f106d630714e88e03c017c09383140c80000191c88e2ca14909824672040ec46b630014e890c3c616e08382d40c00000191c2792d495249d048721b0f586de30615288f83b4186092030c0d80000191bc9e2bf948499647c20c0eec6c42fb14e89003ca19509b833c0c60000191b6ae2c6948c9864621ff8ec06a82f814c08fc3a617608f02e00b60000191b0aa2d69544a0049921b8f4c70431815d09603e418d09a83280d0000))))))))

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



private theorem b257745 : covered 257745 257873 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b257873 : covered 257873 258000 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b258000 : covered 258000 258127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b258127 : covered 258127 258254 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b258254 : covered 258254 258382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b258382 : covered 258382 258509 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b258509 : covered 258509 258636 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b258636 : covered 258636 258763 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b258763 : covered 258763 258890 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b258890 : covered 258890 259017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b259017 : covered 259017 259144 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b259144 : covered 259144 259271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b259271 : covered 259271 259399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b259399 : covered 259399 259526 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b259526 : covered 259526 259653 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b259653 : covered 259653 259780 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b259780 : covered 259780 259908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b259908 : covered 259908 260035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260035 : covered 260035 260162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260162 : covered 260162 260289 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260289 : covered 260289 260417 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 257745 260417 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage b257745 b257873) (joinCoverage b258000 (joinCoverage b258127 b258254))) (joinCoverage (joinCoverage b258382 b258509) (joinCoverage b258636 (joinCoverage b258763 b258890)))) (joinCoverage (joinCoverage (joinCoverage b259017 b259144) (joinCoverage b259271 (joinCoverage b259399 b259526))) (joinCoverage (joinCoverage b259653 (joinCoverage b259780 b259908)) (joinCoverage b260035 (joinCoverage b260162 b260289)))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 257745 ≤ index 495000000/512 := by decide +kernel
private theorem starting_value : fast 495000000=26106107 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 495000000=26106107) (n : ℕ) (low : 495000000≤n) (bound : n≤500000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=495000000
    · rw [first,anchor]
      exact starting_value
    · have past : 495000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤500000000 by omega)
        have within : index n / 512 < 260417 := by omega
        have lower : index 495000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤500000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ495000000To500000000
