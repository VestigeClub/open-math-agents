import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ320000000To345000000

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




private def radical : ℕ := 0x521b27b024f9db3596a39b6e25640241d893e70ee4750b6d6026a51240fe44b26246ebf691b0158941a76e918e5b98cd58854e7f4e2c59ed646343c85805592b7e0c27fb1882fd06a1d11bd083f593691682a366ab45932312b8c49a2ba6726c7c112372150b0abcc822eeb3b90d3c653c4fcc1e7027b15c5f5190d57cd5e62fdbceabfcc908a8a771bf8a1889ab98d3c78cafd8648013f400ab131440ccde9a8f54d590d2d15ac040616a29ca19c79566ede5dd2a4d2614835f2c2e4ee34923ed39512cb4078dbfe0bdbd717460e430a36e9845ae9fefa906f2cd9593b39f03ba5ec2f6ae8315f5f736c758f4b9d2bc8a1a609045a5609542a23bb8627af3993add8d5401563af5f062953f46c5dbb4ce293c599a9b02e544ef63acc200bb1bfda56c0bcfa0e5bb90f4d2d6fe99d63e0fbd8d97791aabceee50565c451f6bcd090c1947d8ed22e0c5c4eb2d63432d1332542cdad48ec8e2b861c1b68e55a025a1f590c43e751587da9330e7f5edf37348df660342f5e93f4c7d9192c54574a0c272207b722b5df28ec4655c231666df20cd17f277d4b768493c3e526584325079c795d2e61bc454436b3b9ea56cd0ce083bcc706b836c2771808ec892cbea314d3abcb9ff6402c522bf52007a1f13f8dfa42f9d106f62c3db0502543e7070c9574558aeecdeca8cd69c43452d81025eed043ee1636f52f925997331f4fded9b02e4dbb2a8fb05a492ed70dc92d55fad3ac42116bd7d4990f56ec7c4640ee7f88126375d53ded0ecf841eda071476822c913cb205065dc2d06cd6be8ac1266bf2fba6d2e18622f67a3f07d7b89b04b268b33bb846ec3394677f8e048c3b42fe972681df37c3e9f9580e8ba7caa03a2ad448d8a79e7bab58a8a22d26385fd86296c159595712aada4e8c96a0cf2f5810d203b00eb71faaf4d7285aa9e25030f5a3ddbe6c734aa5274dcb4a68ff1352f66f75f26d1053e05106c3399439b357414e9e3b47176a5eb4e180c31dfe5e5f7614bff8dcefbd72e1d7e21fb048c0e2af1299e2aec798e07ab8494dda8cc411831bfa5d7b0e8eb353bb4c7ad005b41c156264df889d9937a48d9caae2eae0c4e9a72e99f23f6058295b5bfe313f870c5d8781202cc14257076f835d9ea142bd9f26d2bd195c8d0b402b4c917762c38687904d26987ecf04ab35252860dbd434a3de18d990ce7190674f4682f989dfba2503a01b46e0606382ffff6875b79974b4d2a99bd673bbe38ecde8b0d2b5180fd868065d27f9db5d27e2081abcbd4a4a08f4e4d6ad79537224ca46cd31e0175022b0c539bacbd063b0ba148baac86c98f6a103046085fc0d1be9677eee64fd3feed0eee163d0966d5dabcc8adfc756b2404b36d26aeb2a0c83da4a97d0dded6469348f15c8dbd6e05c621ecc6d1849289dbc9ec0637cdde0d8676a920d81c320ac9c7dc7fa12af00795f1fe5b6d1f57101217f285c292694e4d65f700d3a7eca148b846100507598bcafb44f37722be181e2bc85890352ebe12fa36966b8d4ad4481711f4c748de5cc0b4ae0fd60c071a1b903d8bb9f4051533d2bf2c1b28aeae2b2f8d7e9b32ce0b0134f4ab9b2321af44c439d75c201b763c1c458155c5b4ae93130662936b60863cfaccd1536ad4c5b2478753194101cfa8394101027cc6d94acfd94cec40f2daf4840062a825813e3e10c415441eeec3e48eeb57916038a63596ad882259a4c4152d5c4b74f6675b6298d0543f48814368399862abef6ea1b03fec88b2882b23e0d9b90a2a7122558c9f4806c984c867ec6b1201052d9ebd97dd4c8c784e1c488ba5d144fc67a9c9932645d7cf1e8d467c8de0df9792efde1332a112b686e5e8f0970cb194767eb1be0bf454804c2b62e35df67dd400ed7c282717a70659dc40dafb78c5877c4c17ca2fc3d6013e2625127eeedc1aec88e5aeeaa45ad2467c6799dbf77330a72745c6fb84494457974d203a41a104828c68f367d5ea6edb6a795d4d1f9630204de799fc59594b877117bf24c13024a87e8fea9be9531dd27e8332b30d5c62d27a207a9a6972e679e02a22c8f7333cd435bffd906d90e0f9dd8c06d7aadfbfe676a5733cff5f0d9c633942a387e073c61eec55e756ce9ff376395358fa8de0c7aace599ebe0e3b293c6a8a477684b494bfc851217b7dda17a6bff548efcd3348de3b95b2638bced79811df2869591dcd29fac50a3bf4688a92614c6cc966568de10452d1a9236cab077c3c879a47c1d9f4fe8440343b0fa1a658f82869f5e22254f5815556af730cbbaf6a225412da2fd84a9f415e6335eddd1fcca0ceff7866b735c2e74f99658860ddb2147849236c213d2ff8ce8857368929f23ab5f939d670565b4bd369e4e86fba1bea3ee2bf6889c6d1f91ff5fd396d8758541da1cd4b813cc09f497e6976154b73f1e648ec645416febefced47e78db8cf11ed2fb71cb1a8fcd79e3d79741622d45514f1077a40b04d91b4aa24d0d2bfa19647a57ef9bf75374f1aa0ce73e024eb868dce650410c0e519c1bb8c5b0593a3a822b00345b1f41ee85aac6428c9b35108365eac22f1e922f9dff99d9beb39febe8f277c65b2891767c52b435e989e1f802d311138903401193494fa6b0a47ee2cc947087935a795024e47e9175521b6b29b44bca59fce5631bc4f96c2e7b59c79dcb311c0b151892a10a22ff9eb3d055fef4236bff7dc26ccf9d5694ee980403b6ec1aeecea5980cdea2b59415930f84074cab61a8c1fae3b550dcf214e0a0c6c621cf32b0978bd339d95a7efa4a37a9ceb2201ea994af3e0c4033159246b780c156b9e026fbfb5654137355be426e6146b8ca1bd46d82ec97782d36fbc04a4e5b9c029fa4f41db248f850ab041184b4d0f94f439e37f8549f6a76237755a3c60c6ef7dae8683ca45aa9b077f9ae4bd8413580c7ef0d023ad6b1c5f6553a046949ecc5eba6af170385fb2f5a9ada59426f61c35d5044dc3ba326a43e7535abd796691bb3e6f0ae37f5f5705fd9c87725254f1771c6af34b9b6291f291622c9202ea98be03a84c3793bf60ff4e805a44b4257491d240c5c745942865c43086cf322c291ca889df06d6734323cf1f421013dceeb342efe973984840c9f0f0e3695b7b549ee6f50d7d1648e5e8e98574b475eecf833eed3e2f8723d66eec44fd0c1d52d7f7abb82d9e0b5d0a43a06eb3c38d2f17fde0a7704f22594be4ba62eef183a50376ec14973b580542174abaa60c32c3d301123d949ab8740919ef471c9a7f043f713160bcfab6b1126d2c1133501d7e4f487f37bbb6c9017bdcf72bf40448ee289cfb0121c225c7a39a9e13bd7d5047f515b8d850fb4a617c1d72ad5ba755d64befe6db02be594cb96eb026d1ed2d76d612f9ac01f6e9752f79c2c0fe159801d59f367280abf240ae8932dcac8204913950e09cabbcb36dd949cdc30d38661cee9cde3f21cbb29a9d5406b3ac21104e609c4a6b8952f7f02ab625aadc456d68719ba4f7271ac8cbb9bbfa723ab1d7e3ae3bf2508c894acc001aab015e075e6f2a52dfdb390dfbd0c3ee6e1ba802b3758a30c0ca376b4a315e025ebb8a4b33e44f55f9c23f21755c99d24276ba80d2e848797a643989acf00db3d18b50bec80090a9162eb732ddd1949ab6c8bf10c607596e80b8135f483b59d06bf65faf87f483990316d7a8127d1be2f775cf431330e51bb5a2f8613e1a14d36f8316d774a5f43ba992451b39b2598bf36be012f4cb01288104af69c6f4cfe300c6f5607ad566d7a1cb9ca34ba99295b55fec393f9ad4071aac6b8291ae4ed8210940f50d00b64af4efc57f42a6aae4f891abbc915d7fa3b8bf2c077b4c8f2f09dc42a61fe156ccb7d6810db76db0225b7e6f2001d3cbcfc17eb140af23096b53434e0467fe93f7c1f35202883fc253e464eadf78e457be3a65272b1d128bc371d83eb45e2ffdfee4e87764e61c9a45755de5a60216f50342b7f447b9c75fa677bd0ea61858c8b5456326567938fb0027baedca0aff484639be1281b7bebb8b0d432aca2a2d79fc7dd3b1fdb2376192503e40a1274395a63c9c7c056a5442a40cc54b88c21be367497b166b424d461068ded0a6621fc97cd6a6e0bb71d646b821156d55699babc7f5191b9f3530d3e3141f891a4ff0f8e7b323d30ec2341a22cec2cfa0f13111796e8c1973af9206dc6031ceeaff3b483ca67dc6f4f97bdb93b07b9ebffbc311c5fc4d939937d89158b0833684dc18e98c129efa481e742fa95b679913b7c266f1fc4a4342790afae4315b859d41e16e1dfcf56e6c1980bd448cec23dfa0fc411afdc8997f7922e38041a110c382a01d432369bdd56475311d30f1f37bcda72979352729b8ad7db6e4068272880bc87657a6615779fa0ddd2f646f6b548435ef5c4cfd3a8d61cbb92a2120fb6e8c5814e83cbfe1e191d83859f27c0e0f3708ed978864112b6ba3390fb89ef76c67db9622021d3fbfd477b3ce21b4a4bfe8b489919329da60c37acb1798b164ccda6f665c15ad777f205c0e378c03a0d4961da890fcc75b6bbb2bcd6c3939650b1c63548889822b3017ab03a359ddb0280b94688b6041fe6b193809a5aaab518a8d1a558f23ee8e2ff8b83995e78c4d9c527a54baff96b9f2a9f95e05313bcc760c596d219a76572bac70168a9b509134a19abd3b03451be13fffef8dd42849a48a9ef4ddcd6f15c6

private def light (n : ℕ) : Bool :=
  if n≤136 then decide n.Prime else n.gcd 36590428819525486576897272205198933454286172951815726156123815101405189582089242773975735166401987907830880230417721361838572072126683305250473185240276110436058808776620558462614334914409164842205184000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤18574) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 136 = 36590428819525486576897272205198933454286172951815726156123815101405189582089242773975735166401987907830880230417721361838572072126683305250473185240276110436058808776620558462614334914409164842205184000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 136 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤18574 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 36 := by unfold smallValid; decide +kernel

private theorem sp36 : smallValid 36 36 := by unfold smallValid; decide +kernel

private theorem sp72 : smallValid 72 36 := by unfold smallValid; decide +kernel

private theorem sp108 : smallValid 108 37 := by unfold smallValid; decide +kernel

private theorem sp145 : smallValid 145 36 := by unfold smallValid; decide +kernel

private theorem sp181 : smallValid 181 36 := by unfold smallValid; decide +kernel

private theorem sp217 : smallValid 217 36 := by unfold smallValid; decide +kernel

private theorem sp253 : smallValid 253 37 := by unfold smallValid; decide +kernel

private theorem sp290 : smallValid 290 36 := by unfold smallValid; decide +kernel

private theorem sp326 : smallValid 326 36 := by unfold smallValid; decide +kernel

private theorem sp362 : smallValid 362 36 := by unfold smallValid; decide +kernel

private theorem sp398 : smallValid 398 37 := by unfold smallValid; decide +kernel

private theorem sp435 : smallValid 435 36 := by unfold smallValid; decide +kernel

private theorem sp471 : smallValid 471 36 := by unfold smallValid; decide +kernel

private theorem sp507 : smallValid 507 36 := by unfold smallValid; decide +kernel

private theorem sp543 : smallValid 543 37 := by unfold smallValid; decide +kernel

private theorem sp580 : smallValid 580 36 := by unfold smallValid; decide +kernel

private theorem sp616 : smallValid 616 36 := by unfold smallValid; decide +kernel

private theorem sp652 : smallValid 652 36 := by unfold smallValid; decide +kernel

private theorem sp688 : smallValid 688 37 := by unfold smallValid; decide +kernel

private theorem sp725 : smallValid 725 36 := by unfold smallValid; decide +kernel

private theorem sp761 : smallValid 761 36 := by unfold smallValid; decide +kernel

private theorem sp797 : smallValid 797 36 := by unfold smallValid; decide +kernel

private theorem sp833 : smallValid 833 37 := by unfold smallValid; decide +kernel

private theorem sp870 : smallValid 870 36 := by unfold smallValid; decide +kernel

private theorem sp906 : smallValid 906 36 := by unfold smallValid; decide +kernel

private theorem sp942 : smallValid 942 36 := by unfold smallValid; decide +kernel

private theorem sp978 : smallValid 978 37 := by unfold smallValid; decide +kernel

private theorem sp1015 : smallValid 1015 36 := by unfold smallValid; decide +kernel

private theorem sp1051 : smallValid 1051 36 := by unfold smallValid; decide +kernel

private theorem sp1087 : smallValid 1087 36 := by unfold smallValid; decide +kernel

private theorem sp1123 : smallValid 1123 37 := by unfold smallValid; decide +kernel

private theorem sp1160 : smallValid 1160 36 := by unfold smallValid; decide +kernel

private theorem sp1196 : smallValid 1196 36 := by unfold smallValid; decide +kernel

private theorem sp1232 : smallValid 1232 36 := by unfold smallValid; decide +kernel

private theorem sp1268 : smallValid 1268 37 := by unfold smallValid; decide +kernel

private theorem sp1305 : smallValid 1305 36 := by unfold smallValid; decide +kernel

private theorem sp1341 : smallValid 1341 36 := by unfold smallValid; decide +kernel

private theorem sp1377 : smallValid 1377 36 := by unfold smallValid; decide +kernel

private theorem sp1413 : smallValid 1413 37 := by unfold smallValid; decide +kernel

private theorem sp1450 : smallValid 1450 36 := by unfold smallValid; decide +kernel

private theorem sp1486 : smallValid 1486 36 := by unfold smallValid; decide +kernel

private theorem sp1522 : smallValid 1522 36 := by unfold smallValid; decide +kernel

private theorem sp1558 : smallValid 1558 37 := by unfold smallValid; decide +kernel

private theorem sp1595 : smallValid 1595 36 := by unfold smallValid; decide +kernel

private theorem sp1631 : smallValid 1631 36 := by unfold smallValid; decide +kernel

private theorem sp1667 : smallValid 1667 36 := by unfold smallValid; decide +kernel

private theorem sp1703 : smallValid 1703 37 := by unfold smallValid; decide +kernel

private theorem sp1740 : smallValid 1740 36 := by unfold smallValid; decide +kernel

private theorem sp1776 : smallValid 1776 36 := by unfold smallValid; decide +kernel

private theorem sp1812 : smallValid 1812 36 := by unfold smallValid; decide +kernel

private theorem sp1848 : smallValid 1848 37 := by unfold smallValid; decide +kernel

private theorem sp1885 : smallValid 1885 36 := by unfold smallValid; decide +kernel

private theorem sp1921 : smallValid 1921 36 := by unfold smallValid; decide +kernel

private theorem sp1957 : smallValid 1957 36 := by unfold smallValid; decide +kernel

private theorem sp1993 : smallValid 1993 37 := by unfold smallValid; decide +kernel

private theorem sp2030 : smallValid 2030 36 := by unfold smallValid; decide +kernel

private theorem sp2066 : smallValid 2066 36 := by unfold smallValid; decide +kernel

private theorem sp2102 : smallValid 2102 36 := by unfold smallValid; decide +kernel

private theorem sp2138 : smallValid 2138 37 := by unfold smallValid; decide +kernel

private theorem sp2175 : smallValid 2175 36 := by unfold smallValid; decide +kernel

private theorem sp2211 : smallValid 2211 37 := by unfold smallValid; decide +kernel

private theorem sp2248 : smallValid 2248 36 := by unfold smallValid; decide +kernel

private theorem sp2284 : smallValid 2284 37 := by unfold smallValid; decide +kernel

private theorem sp2321 : smallValid 2321 36 := by unfold smallValid; decide +kernel

private theorem sp2357 : smallValid 2357 36 := by unfold smallValid; decide +kernel

private theorem sp2393 : smallValid 2393 36 := by unfold smallValid; decide +kernel

private theorem sp2429 : smallValid 2429 37 := by unfold smallValid; decide +kernel

private theorem sp2466 : smallValid 2466 36 := by unfold smallValid; decide +kernel

private theorem sp2502 : smallValid 2502 36 := by unfold smallValid; decide +kernel

private theorem sp2538 : smallValid 2538 36 := by unfold smallValid; decide +kernel

private theorem sp2574 : smallValid 2574 37 := by unfold smallValid; decide +kernel

private theorem sp2611 : smallValid 2611 36 := by unfold smallValid; decide +kernel

private theorem sp2647 : smallValid 2647 36 := by unfold smallValid; decide +kernel

private theorem sp2683 : smallValid 2683 36 := by unfold smallValid; decide +kernel

private theorem sp2719 : smallValid 2719 37 := by unfold smallValid; decide +kernel

private theorem sp2756 : smallValid 2756 36 := by unfold smallValid; decide +kernel

private theorem sp2792 : smallValid 2792 36 := by unfold smallValid; decide +kernel

private theorem sp2828 : smallValid 2828 36 := by unfold smallValid; decide +kernel

private theorem sp2864 : smallValid 2864 37 := by unfold smallValid; decide +kernel

private theorem sp2901 : smallValid 2901 36 := by unfold smallValid; decide +kernel

private theorem sp2937 : smallValid 2937 36 := by unfold smallValid; decide +kernel

private theorem sp2973 : smallValid 2973 36 := by unfold smallValid; decide +kernel

private theorem sp3009 : smallValid 3009 37 := by unfold smallValid; decide +kernel

private theorem sp3046 : smallValid 3046 36 := by unfold smallValid; decide +kernel

private theorem sp3082 : smallValid 3082 36 := by unfold smallValid; decide +kernel

private theorem sp3118 : smallValid 3118 36 := by unfold smallValid; decide +kernel

private theorem sp3154 : smallValid 3154 37 := by unfold smallValid; decide +kernel

private theorem sp3191 : smallValid 3191 36 := by unfold smallValid; decide +kernel

private theorem sp3227 : smallValid 3227 36 := by unfold smallValid; decide +kernel

private theorem sp3263 : smallValid 3263 36 := by unfold smallValid; decide +kernel

private theorem sp3299 : smallValid 3299 37 := by unfold smallValid; decide +kernel

private theorem sp3336 : smallValid 3336 36 := by unfold smallValid; decide +kernel

private theorem sp3372 : smallValid 3372 37 := by unfold smallValid; decide +kernel

private theorem sp3409 : smallValid 3409 36 := by unfold smallValid; decide +kernel

private theorem sp3445 : smallValid 3445 37 := by unfold smallValid; decide +kernel

private theorem sp3482 : smallValid 3482 36 := by unfold smallValid; decide +kernel

private theorem sp3518 : smallValid 3518 36 := by unfold smallValid; decide +kernel

private theorem sp3554 : smallValid 3554 36 := by unfold smallValid; decide +kernel

private theorem sp3590 : smallValid 3590 37 := by unfold smallValid; decide +kernel

private theorem sp3627 : smallValid 3627 36 := by unfold smallValid; decide +kernel

private theorem sp3663 : smallValid 3663 36 := by unfold smallValid; decide +kernel

private theorem sp3699 : smallValid 3699 36 := by unfold smallValid; decide +kernel

private theorem sp3735 : smallValid 3735 37 := by unfold smallValid; decide +kernel

private theorem sp3772 : smallValid 3772 36 := by unfold smallValid; decide +kernel

private theorem sp3808 : smallValid 3808 36 := by unfold smallValid; decide +kernel

private theorem sp3844 : smallValid 3844 36 := by unfold smallValid; decide +kernel

private theorem sp3880 : smallValid 3880 37 := by unfold smallValid; decide +kernel

private theorem sp3917 : smallValid 3917 36 := by unfold smallValid; decide +kernel

private theorem sp3953 : smallValid 3953 36 := by unfold smallValid; decide +kernel

private theorem sp3989 : smallValid 3989 36 := by unfold smallValid; decide +kernel

private theorem sp4025 : smallValid 4025 37 := by unfold smallValid; decide +kernel

private theorem sp4062 : smallValid 4062 36 := by unfold smallValid; decide +kernel

private theorem sp4098 : smallValid 4098 36 := by unfold smallValid; decide +kernel

private theorem sp4134 : smallValid 4134 36 := by unfold smallValid; decide +kernel

private theorem sp4170 : smallValid 4170 37 := by unfold smallValid; decide +kernel

private theorem sp4207 : smallValid 4207 36 := by unfold smallValid; decide +kernel

private theorem sp4243 : smallValid 4243 36 := by unfold smallValid; decide +kernel

private theorem sp4279 : smallValid 4279 36 := by unfold smallValid; decide +kernel

private theorem sp4315 : smallValid 4315 37 := by unfold smallValid; decide +kernel

private theorem sp4352 : smallValid 4352 36 := by unfold smallValid; decide +kernel

private theorem sp4388 : smallValid 4388 36 := by unfold smallValid; decide +kernel

private theorem sp4424 : smallValid 4424 36 := by unfold smallValid; decide +kernel

private theorem sp4460 : smallValid 4460 37 := by unfold smallValid; decide +kernel

private theorem sp4497 : smallValid 4497 36 := by unfold smallValid; decide +kernel

private theorem sp4533 : smallValid 4533 37 := by unfold smallValid; decide +kernel

private theorem sp4570 : smallValid 4570 36 := by unfold smallValid; decide +kernel

private theorem sp4606 : smallValid 4606 37 := by unfold smallValid; decide +kernel

private theorem sp4643 : smallValid 4643 36 := by unfold smallValid; decide +kernel

private theorem sp4679 : smallValid 4679 36 := by unfold smallValid; decide +kernel

private theorem sp4715 : smallValid 4715 36 := by unfold smallValid; decide +kernel

private theorem sp4751 : smallValid 4751 37 := by unfold smallValid; decide +kernel

private theorem sp4788 : smallValid 4788 36 := by unfold smallValid; decide +kernel

private theorem sp4824 : smallValid 4824 36 := by unfold smallValid; decide +kernel

private theorem sp4860 : smallValid 4860 36 := by unfold smallValid; decide +kernel

private theorem sp4896 : smallValid 4896 37 := by unfold smallValid; decide +kernel

private theorem sp4933 : smallValid 4933 36 := by unfold smallValid; decide +kernel

private theorem sp4969 : smallValid 4969 36 := by unfold smallValid; decide +kernel

private theorem sp5005 : smallValid 5005 36 := by unfold smallValid; decide +kernel

private theorem sp5041 : smallValid 5041 37 := by unfold smallValid; decide +kernel

private theorem sp5078 : smallValid 5078 36 := by unfold smallValid; decide +kernel

private theorem sp5114 : smallValid 5114 36 := by unfold smallValid; decide +kernel

private theorem sp5150 : smallValid 5150 36 := by unfold smallValid; decide +kernel

private theorem sp5186 : smallValid 5186 37 := by unfold smallValid; decide +kernel

private theorem sp5223 : smallValid 5223 36 := by unfold smallValid; decide +kernel

private theorem sp5259 : smallValid 5259 36 := by unfold smallValid; decide +kernel

private theorem sp5295 : smallValid 5295 36 := by unfold smallValid; decide +kernel

private theorem sp5331 : smallValid 5331 37 := by unfold smallValid; decide +kernel

private theorem sp5368 : smallValid 5368 36 := by unfold smallValid; decide +kernel

private theorem sp5404 : smallValid 5404 36 := by unfold smallValid; decide +kernel

private theorem sp5440 : smallValid 5440 36 := by unfold smallValid; decide +kernel

private theorem sp5476 : smallValid 5476 37 := by unfold smallValid; decide +kernel

private theorem sp5513 : smallValid 5513 36 := by unfold smallValid; decide +kernel

private theorem sp5549 : smallValid 5549 36 := by unfold smallValid; decide +kernel

private theorem sp5585 : smallValid 5585 36 := by unfold smallValid; decide +kernel

private theorem sp5621 : smallValid 5621 37 := by unfold smallValid; decide +kernel

private theorem sp5658 : smallValid 5658 36 := by unfold smallValid; decide +kernel

private theorem sp5694 : smallValid 5694 37 := by unfold smallValid; decide +kernel

private theorem sp5731 : smallValid 5731 36 := by unfold smallValid; decide +kernel

private theorem sp5767 : smallValid 5767 37 := by unfold smallValid; decide +kernel

private theorem sp5804 : smallValid 5804 36 := by unfold smallValid; decide +kernel

private theorem sp5840 : smallValid 5840 36 := by unfold smallValid; decide +kernel

private theorem sp5876 : smallValid 5876 36 := by unfold smallValid; decide +kernel

private theorem sp5912 : smallValid 5912 37 := by unfold smallValid; decide +kernel

private theorem sp5949 : smallValid 5949 36 := by unfold smallValid; decide +kernel

private theorem sp5985 : smallValid 5985 36 := by unfold smallValid; decide +kernel

private theorem sp6021 : smallValid 6021 36 := by unfold smallValid; decide +kernel

private theorem sp6057 : smallValid 6057 37 := by unfold smallValid; decide +kernel

private theorem sp6094 : smallValid 6094 36 := by unfold smallValid; decide +kernel

private theorem sp6130 : smallValid 6130 36 := by unfold smallValid; decide +kernel

private theorem sp6166 : smallValid 6166 36 := by unfold smallValid; decide +kernel

private theorem sp6202 : smallValid 6202 37 := by unfold smallValid; decide +kernel

private theorem sp6239 : smallValid 6239 36 := by unfold smallValid; decide +kernel

private theorem sp6275 : smallValid 6275 36 := by unfold smallValid; decide +kernel

private theorem sp6311 : smallValid 6311 36 := by unfold smallValid; decide +kernel

private theorem sp6347 : smallValid 6347 37 := by unfold smallValid; decide +kernel

private theorem sp6384 : smallValid 6384 36 := by unfold smallValid; decide +kernel

private theorem sp6420 : smallValid 6420 36 := by unfold smallValid; decide +kernel

private theorem sp6456 : smallValid 6456 36 := by unfold smallValid; decide +kernel

private theorem sp6492 : smallValid 6492 37 := by unfold smallValid; decide +kernel

private theorem sp6529 : smallValid 6529 36 := by unfold smallValid; decide +kernel

private theorem sp6565 : smallValid 6565 36 := by unfold smallValid; decide +kernel

private theorem sp6601 : smallValid 6601 36 := by unfold smallValid; decide +kernel

private theorem sp6637 : smallValid 6637 37 := by unfold smallValid; decide +kernel

private theorem sp6674 : smallValid 6674 36 := by unfold smallValid; decide +kernel

private theorem sp6710 : smallValid 6710 36 := by unfold smallValid; decide +kernel

private theorem sp6746 : smallValid 6746 36 := by unfold smallValid; decide +kernel

private theorem sp6782 : smallValid 6782 37 := by unfold smallValid; decide +kernel

private theorem sp6819 : smallValid 6819 36 := by unfold smallValid; decide +kernel

private theorem sp6855 : smallValid 6855 37 := by unfold smallValid; decide +kernel

private theorem sp6892 : smallValid 6892 36 := by unfold smallValid; decide +kernel

private theorem sp6928 : smallValid 6928 37 := by unfold smallValid; decide +kernel

private theorem sp6965 : smallValid 6965 36 := by unfold smallValid; decide +kernel

private theorem sp7001 : smallValid 7001 36 := by unfold smallValid; decide +kernel

private theorem sp7037 : smallValid 7037 36 := by unfold smallValid; decide +kernel

private theorem sp7073 : smallValid 7073 37 := by unfold smallValid; decide +kernel

private theorem sp7110 : smallValid 7110 36 := by unfold smallValid; decide +kernel

private theorem sp7146 : smallValid 7146 36 := by unfold smallValid; decide +kernel

private theorem sp7182 : smallValid 7182 36 := by unfold smallValid; decide +kernel

private theorem sp7218 : smallValid 7218 37 := by unfold smallValid; decide +kernel

private theorem sp7255 : smallValid 7255 36 := by unfold smallValid; decide +kernel

private theorem sp7291 : smallValid 7291 36 := by unfold smallValid; decide +kernel

private theorem sp7327 : smallValid 7327 36 := by unfold smallValid; decide +kernel

private theorem sp7363 : smallValid 7363 37 := by unfold smallValid; decide +kernel

private theorem sp7400 : smallValid 7400 36 := by unfold smallValid; decide +kernel

private theorem sp7436 : smallValid 7436 36 := by unfold smallValid; decide +kernel

private theorem sp7472 : smallValid 7472 36 := by unfold smallValid; decide +kernel

private theorem sp7508 : smallValid 7508 37 := by unfold smallValid; decide +kernel

private theorem sp7545 : smallValid 7545 36 := by unfold smallValid; decide +kernel

private theorem sp7581 : smallValid 7581 36 := by unfold smallValid; decide +kernel

private theorem sp7617 : smallValid 7617 36 := by unfold smallValid; decide +kernel

private theorem sp7653 : smallValid 7653 37 := by unfold smallValid; decide +kernel

private theorem sp7690 : smallValid 7690 36 := by unfold smallValid; decide +kernel

private theorem sp7726 : smallValid 7726 36 := by unfold smallValid; decide +kernel

private theorem sp7762 : smallValid 7762 36 := by unfold smallValid; decide +kernel

private theorem sp7798 : smallValid 7798 37 := by unfold smallValid; decide +kernel

private theorem sp7835 : smallValid 7835 36 := by unfold smallValid; decide +kernel

private theorem sp7871 : smallValid 7871 36 := by unfold smallValid; decide +kernel

private theorem sp7907 : smallValid 7907 36 := by unfold smallValid; decide +kernel

private theorem sp7943 : smallValid 7943 37 := by unfold smallValid; decide +kernel

private theorem sp7980 : smallValid 7980 36 := by unfold smallValid; decide +kernel

private theorem sp8016 : smallValid 8016 37 := by unfold smallValid; decide +kernel

private theorem sp8053 : smallValid 8053 36 := by unfold smallValid; decide +kernel

private theorem sp8089 : smallValid 8089 37 := by unfold smallValid; decide +kernel

private theorem sp8126 : smallValid 8126 36 := by unfold smallValid; decide +kernel

private theorem sp8162 : smallValid 8162 36 := by unfold smallValid; decide +kernel

private theorem sp8198 : smallValid 8198 36 := by unfold smallValid; decide +kernel

private theorem sp8234 : smallValid 8234 37 := by unfold smallValid; decide +kernel

private theorem sp8271 : smallValid 8271 36 := by unfold smallValid; decide +kernel

private theorem sp8307 : smallValid 8307 36 := by unfold smallValid; decide +kernel

private theorem sp8343 : smallValid 8343 36 := by unfold smallValid; decide +kernel

private theorem sp8379 : smallValid 8379 37 := by unfold smallValid; decide +kernel

private theorem sp8416 : smallValid 8416 36 := by unfold smallValid; decide +kernel

private theorem sp8452 : smallValid 8452 36 := by unfold smallValid; decide +kernel

private theorem sp8488 : smallValid 8488 36 := by unfold smallValid; decide +kernel

private theorem sp8524 : smallValid 8524 37 := by unfold smallValid; decide +kernel

private theorem sp8561 : smallValid 8561 36 := by unfold smallValid; decide +kernel

private theorem sp8597 : smallValid 8597 36 := by unfold smallValid; decide +kernel

private theorem sp8633 : smallValid 8633 36 := by unfold smallValid; decide +kernel

private theorem sp8669 : smallValid 8669 37 := by unfold smallValid; decide +kernel

private theorem sp8706 : smallValid 8706 36 := by unfold smallValid; decide +kernel

private theorem sp8742 : smallValid 8742 36 := by unfold smallValid; decide +kernel

private theorem sp8778 : smallValid 8778 36 := by unfold smallValid; decide +kernel

private theorem sp8814 : smallValid 8814 37 := by unfold smallValid; decide +kernel

private theorem sp8851 : smallValid 8851 36 := by unfold smallValid; decide +kernel

private theorem sp8887 : smallValid 8887 36 := by unfold smallValid; decide +kernel

private theorem sp8923 : smallValid 8923 36 := by unfold smallValid; decide +kernel

private theorem sp8959 : smallValid 8959 37 := by unfold smallValid; decide +kernel

private theorem sp8996 : smallValid 8996 36 := by unfold smallValid; decide +kernel

private theorem sp9032 : smallValid 9032 36 := by unfold smallValid; decide +kernel

private theorem sp9068 : smallValid 9068 36 := by unfold smallValid; decide +kernel

private theorem sp9104 : smallValid 9104 37 := by unfold smallValid; decide +kernel

private theorem sp9141 : smallValid 9141 36 := by unfold smallValid; decide +kernel

private theorem sp9177 : smallValid 9177 37 := by unfold smallValid; decide +kernel

private theorem sp9214 : smallValid 9214 36 := by unfold smallValid; decide +kernel

private theorem sp9250 : smallValid 9250 37 := by unfold smallValid; decide +kernel

private theorem sp9287 : smallValid 9287 36 := by unfold smallValid; decide +kernel

private theorem sp9323 : smallValid 9323 36 := by unfold smallValid; decide +kernel

private theorem sp9359 : smallValid 9359 36 := by unfold smallValid; decide +kernel

private theorem sp9395 : smallValid 9395 37 := by unfold smallValid; decide +kernel

private theorem sp9432 : smallValid 9432 36 := by unfold smallValid; decide +kernel

private theorem sp9468 : smallValid 9468 36 := by unfold smallValid; decide +kernel

private theorem sp9504 : smallValid 9504 36 := by unfold smallValid; decide +kernel

private theorem sp9540 : smallValid 9540 37 := by unfold smallValid; decide +kernel

private theorem sp9577 : smallValid 9577 36 := by unfold smallValid; decide +kernel

private theorem sp9613 : smallValid 9613 36 := by unfold smallValid; decide +kernel

private theorem sp9649 : smallValid 9649 36 := by unfold smallValid; decide +kernel

private theorem sp9685 : smallValid 9685 37 := by unfold smallValid; decide +kernel

private theorem sp9722 : smallValid 9722 36 := by unfold smallValid; decide +kernel

private theorem sp9758 : smallValid 9758 36 := by unfold smallValid; decide +kernel

private theorem sp9794 : smallValid 9794 36 := by unfold smallValid; decide +kernel

private theorem sp9830 : smallValid 9830 37 := by unfold smallValid; decide +kernel

private theorem sp9867 : smallValid 9867 36 := by unfold smallValid; decide +kernel

private theorem sp9903 : smallValid 9903 36 := by unfold smallValid; decide +kernel

private theorem sp9939 : smallValid 9939 36 := by unfold smallValid; decide +kernel

private theorem sp9975 : smallValid 9975 37 := by unfold smallValid; decide +kernel

private theorem sp10012 : smallValid 10012 36 := by unfold smallValid; decide +kernel

private theorem sp10048 : smallValid 10048 36 := by unfold smallValid; decide +kernel

private theorem sp10084 : smallValid 10084 36 := by unfold smallValid; decide +kernel

private theorem sp10120 : smallValid 10120 37 := by unfold smallValid; decide +kernel

private theorem sp10157 : smallValid 10157 36 := by unfold smallValid; decide +kernel

private theorem sp10193 : smallValid 10193 36 := by unfold smallValid; decide +kernel

private theorem sp10229 : smallValid 10229 36 := by unfold smallValid; decide +kernel

private theorem sp10265 : smallValid 10265 37 := by unfold smallValid; decide +kernel

private theorem sp10302 : smallValid 10302 36 := by unfold smallValid; decide +kernel

private theorem sp10338 : smallValid 10338 37 := by unfold smallValid; decide +kernel

private theorem sp10375 : smallValid 10375 36 := by unfold smallValid; decide +kernel

private theorem sp10411 : smallValid 10411 37 := by unfold smallValid; decide +kernel

private theorem sp10448 : smallValid 10448 36 := by unfold smallValid; decide +kernel

private theorem sp10484 : smallValid 10484 36 := by unfold smallValid; decide +kernel

private theorem sp10520 : smallValid 10520 36 := by unfold smallValid; decide +kernel

private theorem sp10556 : smallValid 10556 37 := by unfold smallValid; decide +kernel

private theorem sp10593 : smallValid 10593 36 := by unfold smallValid; decide +kernel

private theorem sp10629 : smallValid 10629 36 := by unfold smallValid; decide +kernel

private theorem sp10665 : smallValid 10665 36 := by unfold smallValid; decide +kernel

private theorem sp10701 : smallValid 10701 37 := by unfold smallValid; decide +kernel

private theorem sp10738 : smallValid 10738 36 := by unfold smallValid; decide +kernel

private theorem sp10774 : smallValid 10774 36 := by unfold smallValid; decide +kernel

private theorem sp10810 : smallValid 10810 36 := by unfold smallValid; decide +kernel

private theorem sp10846 : smallValid 10846 37 := by unfold smallValid; decide +kernel

private theorem sp10883 : smallValid 10883 36 := by unfold smallValid; decide +kernel

private theorem sp10919 : smallValid 10919 36 := by unfold smallValid; decide +kernel

private theorem sp10955 : smallValid 10955 36 := by unfold smallValid; decide +kernel

private theorem sp10991 : smallValid 10991 37 := by unfold smallValid; decide +kernel

private theorem sp11028 : smallValid 11028 36 := by unfold smallValid; decide +kernel

private theorem sp11064 : smallValid 11064 36 := by unfold smallValid; decide +kernel

private theorem sp11100 : smallValid 11100 36 := by unfold smallValid; decide +kernel

private theorem sp11136 : smallValid 11136 37 := by unfold smallValid; decide +kernel

private theorem sp11173 : smallValid 11173 36 := by unfold smallValid; decide +kernel

private theorem sp11209 : smallValid 11209 36 := by unfold smallValid; decide +kernel

private theorem sp11245 : smallValid 11245 36 := by unfold smallValid; decide +kernel

private theorem sp11281 : smallValid 11281 37 := by unfold smallValid; decide +kernel

private theorem sp11318 : smallValid 11318 36 := by unfold smallValid; decide +kernel

private theorem sp11354 : smallValid 11354 36 := by unfold smallValid; decide +kernel

private theorem sp11390 : smallValid 11390 36 := by unfold smallValid; decide +kernel

private theorem sp11426 : smallValid 11426 37 := by unfold smallValid; decide +kernel

private theorem sp11463 : smallValid 11463 36 := by unfold smallValid; decide +kernel

private theorem sp11499 : smallValid 11499 37 := by unfold smallValid; decide +kernel

private theorem sp11536 : smallValid 11536 36 := by unfold smallValid; decide +kernel

private theorem sp11572 : smallValid 11572 37 := by unfold smallValid; decide +kernel

private theorem sp11609 : smallValid 11609 36 := by unfold smallValid; decide +kernel

private theorem sp11645 : smallValid 11645 36 := by unfold smallValid; decide +kernel

private theorem sp11681 : smallValid 11681 36 := by unfold smallValid; decide +kernel

private theorem sp11717 : smallValid 11717 37 := by unfold smallValid; decide +kernel

private theorem sp11754 : smallValid 11754 36 := by unfold smallValid; decide +kernel

private theorem sp11790 : smallValid 11790 36 := by unfold smallValid; decide +kernel

private theorem sp11826 : smallValid 11826 36 := by unfold smallValid; decide +kernel

private theorem sp11862 : smallValid 11862 37 := by unfold smallValid; decide +kernel

private theorem sp11899 : smallValid 11899 36 := by unfold smallValid; decide +kernel

private theorem sp11935 : smallValid 11935 36 := by unfold smallValid; decide +kernel

private theorem sp11971 : smallValid 11971 36 := by unfold smallValid; decide +kernel

private theorem sp12007 : smallValid 12007 37 := by unfold smallValid; decide +kernel

private theorem sp12044 : smallValid 12044 36 := by unfold smallValid; decide +kernel

private theorem sp12080 : smallValid 12080 36 := by unfold smallValid; decide +kernel

private theorem sp12116 : smallValid 12116 36 := by unfold smallValid; decide +kernel

private theorem sp12152 : smallValid 12152 37 := by unfold smallValid; decide +kernel

private theorem sp12189 : smallValid 12189 36 := by unfold smallValid; decide +kernel

private theorem sp12225 : smallValid 12225 36 := by unfold smallValid; decide +kernel

private theorem sp12261 : smallValid 12261 36 := by unfold smallValid; decide +kernel

private theorem sp12297 : smallValid 12297 37 := by unfold smallValid; decide +kernel

private theorem sp12334 : smallValid 12334 36 := by unfold smallValid; decide +kernel

private theorem sp12370 : smallValid 12370 36 := by unfold smallValid; decide +kernel

private theorem sp12406 : smallValid 12406 36 := by unfold smallValid; decide +kernel

private theorem sp12442 : smallValid 12442 37 := by unfold smallValid; decide +kernel

private theorem sp12479 : smallValid 12479 36 := by unfold smallValid; decide +kernel

private theorem sp12515 : smallValid 12515 36 := by unfold smallValid; decide +kernel

private theorem sp12551 : smallValid 12551 36 := by unfold smallValid; decide +kernel

private theorem sp12587 : smallValid 12587 37 := by unfold smallValid; decide +kernel

private theorem sp12624 : smallValid 12624 36 := by unfold smallValid; decide +kernel

private theorem sp12660 : smallValid 12660 37 := by unfold smallValid; decide +kernel

private theorem sp12697 : smallValid 12697 36 := by unfold smallValid; decide +kernel

private theorem sp12733 : smallValid 12733 37 := by unfold smallValid; decide +kernel

private theorem sp12770 : smallValid 12770 36 := by unfold smallValid; decide +kernel

private theorem sp12806 : smallValid 12806 36 := by unfold smallValid; decide +kernel

private theorem sp12842 : smallValid 12842 36 := by unfold smallValid; decide +kernel

private theorem sp12878 : smallValid 12878 37 := by unfold smallValid; decide +kernel

private theorem sp12915 : smallValid 12915 36 := by unfold smallValid; decide +kernel

private theorem sp12951 : smallValid 12951 36 := by unfold smallValid; decide +kernel

private theorem sp12987 : smallValid 12987 36 := by unfold smallValid; decide +kernel

private theorem sp13023 : smallValid 13023 37 := by unfold smallValid; decide +kernel

private theorem sp13060 : smallValid 13060 36 := by unfold smallValid; decide +kernel

private theorem sp13096 : smallValid 13096 36 := by unfold smallValid; decide +kernel

private theorem sp13132 : smallValid 13132 36 := by unfold smallValid; decide +kernel

private theorem sp13168 : smallValid 13168 37 := by unfold smallValid; decide +kernel

private theorem sp13205 : smallValid 13205 36 := by unfold smallValid; decide +kernel

private theorem sp13241 : smallValid 13241 36 := by unfold smallValid; decide +kernel

private theorem sp13277 : smallValid 13277 36 := by unfold smallValid; decide +kernel

private theorem sp13313 : smallValid 13313 37 := by unfold smallValid; decide +kernel

private theorem sp13350 : smallValid 13350 36 := by unfold smallValid; decide +kernel

private theorem sp13386 : smallValid 13386 36 := by unfold smallValid; decide +kernel

private theorem sp13422 : smallValid 13422 36 := by unfold smallValid; decide +kernel

private theorem sp13458 : smallValid 13458 37 := by unfold smallValid; decide +kernel

private theorem sp13495 : smallValid 13495 36 := by unfold smallValid; decide +kernel

private theorem sp13531 : smallValid 13531 36 := by unfold smallValid; decide +kernel

private theorem sp13567 : smallValid 13567 36 := by unfold smallValid; decide +kernel

private theorem sp13603 : smallValid 13603 37 := by unfold smallValid; decide +kernel

private theorem sp13640 : smallValid 13640 36 := by unfold smallValid; decide +kernel

private theorem sp13676 : smallValid 13676 36 := by unfold smallValid; decide +kernel

private theorem sp13712 : smallValid 13712 36 := by unfold smallValid; decide +kernel

private theorem sp13748 : smallValid 13748 37 := by unfold smallValid; decide +kernel

private theorem sp13785 : smallValid 13785 36 := by unfold smallValid; decide +kernel

private theorem sp13821 : smallValid 13821 37 := by unfold smallValid; decide +kernel

private theorem sp13858 : smallValid 13858 36 := by unfold smallValid; decide +kernel

private theorem sp13894 : smallValid 13894 37 := by unfold smallValid; decide +kernel

private theorem sp13931 : smallValid 13931 36 := by unfold smallValid; decide +kernel

private theorem sp13967 : smallValid 13967 36 := by unfold smallValid; decide +kernel

private theorem sp14003 : smallValid 14003 36 := by unfold smallValid; decide +kernel

private theorem sp14039 : smallValid 14039 37 := by unfold smallValid; decide +kernel

private theorem sp14076 : smallValid 14076 36 := by unfold smallValid; decide +kernel

private theorem sp14112 : smallValid 14112 36 := by unfold smallValid; decide +kernel

private theorem sp14148 : smallValid 14148 36 := by unfold smallValid; decide +kernel

private theorem sp14184 : smallValid 14184 37 := by unfold smallValid; decide +kernel

private theorem sp14221 : smallValid 14221 36 := by unfold smallValid; decide +kernel

private theorem sp14257 : smallValid 14257 36 := by unfold smallValid; decide +kernel

private theorem sp14293 : smallValid 14293 36 := by unfold smallValid; decide +kernel

private theorem sp14329 : smallValid 14329 37 := by unfold smallValid; decide +kernel

private theorem sp14366 : smallValid 14366 36 := by unfold smallValid; decide +kernel

private theorem sp14402 : smallValid 14402 36 := by unfold smallValid; decide +kernel

private theorem sp14438 : smallValid 14438 36 := by unfold smallValid; decide +kernel

private theorem sp14474 : smallValid 14474 37 := by unfold smallValid; decide +kernel

private theorem sp14511 : smallValid 14511 36 := by unfold smallValid; decide +kernel

private theorem sp14547 : smallValid 14547 36 := by unfold smallValid; decide +kernel

private theorem sp14583 : smallValid 14583 36 := by unfold smallValid; decide +kernel

private theorem sp14619 : smallValid 14619 37 := by unfold smallValid; decide +kernel

private theorem sp14656 : smallValid 14656 36 := by unfold smallValid; decide +kernel

private theorem sp14692 : smallValid 14692 36 := by unfold smallValid; decide +kernel

private theorem sp14728 : smallValid 14728 36 := by unfold smallValid; decide +kernel

private theorem sp14764 : smallValid 14764 37 := by unfold smallValid; decide +kernel

private theorem sp14801 : smallValid 14801 36 := by unfold smallValid; decide +kernel

private theorem sp14837 : smallValid 14837 36 := by unfold smallValid; decide +kernel

private theorem sp14873 : smallValid 14873 36 := by unfold smallValid; decide +kernel

private theorem sp14909 : smallValid 14909 37 := by unfold smallValid; decide +kernel

private theorem sp14946 : smallValid 14946 36 := by unfold smallValid; decide +kernel

private theorem sp14982 : smallValid 14982 37 := by unfold smallValid; decide +kernel

private theorem sp15019 : smallValid 15019 36 := by unfold smallValid; decide +kernel

private theorem sp15055 : smallValid 15055 37 := by unfold smallValid; decide +kernel

private theorem sp15092 : smallValid 15092 36 := by unfold smallValid; decide +kernel

private theorem sp15128 : smallValid 15128 36 := by unfold smallValid; decide +kernel

private theorem sp15164 : smallValid 15164 36 := by unfold smallValid; decide +kernel

private theorem sp15200 : smallValid 15200 37 := by unfold smallValid; decide +kernel

private theorem sp15237 : smallValid 15237 36 := by unfold smallValid; decide +kernel

private theorem sp15273 : smallValid 15273 36 := by unfold smallValid; decide +kernel

private theorem sp15309 : smallValid 15309 36 := by unfold smallValid; decide +kernel

private theorem sp15345 : smallValid 15345 37 := by unfold smallValid; decide +kernel

private theorem sp15382 : smallValid 15382 36 := by unfold smallValid; decide +kernel

private theorem sp15418 : smallValid 15418 36 := by unfold smallValid; decide +kernel

private theorem sp15454 : smallValid 15454 36 := by unfold smallValid; decide +kernel

private theorem sp15490 : smallValid 15490 37 := by unfold smallValid; decide +kernel

private theorem sp15527 : smallValid 15527 36 := by unfold smallValid; decide +kernel

private theorem sp15563 : smallValid 15563 36 := by unfold smallValid; decide +kernel

private theorem sp15599 : smallValid 15599 36 := by unfold smallValid; decide +kernel

private theorem sp15635 : smallValid 15635 37 := by unfold smallValid; decide +kernel

private theorem sp15672 : smallValid 15672 36 := by unfold smallValid; decide +kernel

private theorem sp15708 : smallValid 15708 36 := by unfold smallValid; decide +kernel

private theorem sp15744 : smallValid 15744 36 := by unfold smallValid; decide +kernel

private theorem sp15780 : smallValid 15780 37 := by unfold smallValid; decide +kernel

private theorem sp15817 : smallValid 15817 36 := by unfold smallValid; decide +kernel

private theorem sp15853 : smallValid 15853 36 := by unfold smallValid; decide +kernel

private theorem sp15889 : smallValid 15889 36 := by unfold smallValid; decide +kernel

private theorem sp15925 : smallValid 15925 37 := by unfold smallValid; decide +kernel

private theorem sp15962 : smallValid 15962 36 := by unfold smallValid; decide +kernel

private theorem sp15998 : smallValid 15998 36 := by unfold smallValid; decide +kernel

private theorem sp16034 : smallValid 16034 36 := by unfold smallValid; decide +kernel

private theorem sp16070 : smallValid 16070 37 := by unfold smallValid; decide +kernel

private theorem sp16107 : smallValid 16107 36 := by unfold smallValid; decide +kernel

private theorem sp16143 : smallValid 16143 37 := by unfold smallValid; decide +kernel

private theorem sp16180 : smallValid 16180 36 := by unfold smallValid; decide +kernel

private theorem sp16216 : smallValid 16216 37 := by unfold smallValid; decide +kernel

private theorem sp16253 : smallValid 16253 36 := by unfold smallValid; decide +kernel

private theorem sp16289 : smallValid 16289 36 := by unfold smallValid; decide +kernel

private theorem sp16325 : smallValid 16325 36 := by unfold smallValid; decide +kernel

private theorem sp16361 : smallValid 16361 37 := by unfold smallValid; decide +kernel

private theorem sp16398 : smallValid 16398 36 := by unfold smallValid; decide +kernel

private theorem sp16434 : smallValid 16434 36 := by unfold smallValid; decide +kernel

private theorem sp16470 : smallValid 16470 36 := by unfold smallValid; decide +kernel

private theorem sp16506 : smallValid 16506 37 := by unfold smallValid; decide +kernel

private theorem sp16543 : smallValid 16543 36 := by unfold smallValid; decide +kernel

private theorem sp16579 : smallValid 16579 36 := by unfold smallValid; decide +kernel

private theorem sp16615 : smallValid 16615 36 := by unfold smallValid; decide +kernel

private theorem sp16651 : smallValid 16651 37 := by unfold smallValid; decide +kernel

private theorem sp16688 : smallValid 16688 36 := by unfold smallValid; decide +kernel

private theorem sp16724 : smallValid 16724 36 := by unfold smallValid; decide +kernel

private theorem sp16760 : smallValid 16760 36 := by unfold smallValid; decide +kernel

private theorem sp16796 : smallValid 16796 37 := by unfold smallValid; decide +kernel

private theorem sp16833 : smallValid 16833 36 := by unfold smallValid; decide +kernel

private theorem sp16869 : smallValid 16869 36 := by unfold smallValid; decide +kernel

private theorem sp16905 : smallValid 16905 36 := by unfold smallValid; decide +kernel

private theorem sp16941 : smallValid 16941 37 := by unfold smallValid; decide +kernel

private theorem sp16978 : smallValid 16978 36 := by unfold smallValid; decide +kernel

private theorem sp17014 : smallValid 17014 36 := by unfold smallValid; decide +kernel

private theorem sp17050 : smallValid 17050 36 := by unfold smallValid; decide +kernel

private theorem sp17086 : smallValid 17086 37 := by unfold smallValid; decide +kernel

private theorem sp17123 : smallValid 17123 36 := by unfold smallValid; decide +kernel

private theorem sp17159 : smallValid 17159 36 := by unfold smallValid; decide +kernel

private theorem sp17195 : smallValid 17195 36 := by unfold smallValid; decide +kernel

private theorem sp17231 : smallValid 17231 37 := by unfold smallValid; decide +kernel

private theorem sp17268 : smallValid 17268 36 := by unfold smallValid; decide +kernel

private theorem sp17304 : smallValid 17304 37 := by unfold smallValid; decide +kernel

private theorem sp17341 : smallValid 17341 36 := by unfold smallValid; decide +kernel

private theorem sp17377 : smallValid 17377 37 := by unfold smallValid; decide +kernel

private theorem sp17414 : smallValid 17414 36 := by unfold smallValid; decide +kernel

private theorem sp17450 : smallValid 17450 36 := by unfold smallValid; decide +kernel

private theorem sp17486 : smallValid 17486 36 := by unfold smallValid; decide +kernel

private theorem sp17522 : smallValid 17522 37 := by unfold smallValid; decide +kernel

private theorem sp17559 : smallValid 17559 36 := by unfold smallValid; decide +kernel

private theorem sp17595 : smallValid 17595 36 := by unfold smallValid; decide +kernel

private theorem sp17631 : smallValid 17631 36 := by unfold smallValid; decide +kernel

private theorem sp17667 : smallValid 17667 37 := by unfold smallValid; decide +kernel

private theorem sp17704 : smallValid 17704 36 := by unfold smallValid; decide +kernel

private theorem sp17740 : smallValid 17740 36 := by unfold smallValid; decide +kernel

private theorem sp17776 : smallValid 17776 36 := by unfold smallValid; decide +kernel

private theorem sp17812 : smallValid 17812 37 := by unfold smallValid; decide +kernel

private theorem sp17849 : smallValid 17849 36 := by unfold smallValid; decide +kernel

private theorem sp17885 : smallValid 17885 36 := by unfold smallValid; decide +kernel

private theorem sp17921 : smallValid 17921 36 := by unfold smallValid; decide +kernel

private theorem sp17957 : smallValid 17957 37 := by unfold smallValid; decide +kernel

private theorem sp17994 : smallValid 17994 36 := by unfold smallValid; decide +kernel

private theorem sp18030 : smallValid 18030 36 := by unfold smallValid; decide +kernel

private theorem sp18066 : smallValid 18066 36 := by unfold smallValid; decide +kernel

private theorem sp18102 : smallValid 18102 37 := by unfold smallValid; decide +kernel

private theorem sp18139 : smallValid 18139 36 := by unfold smallValid; decide +kernel

private theorem sp18175 : smallValid 18175 36 := by unfold smallValid; decide +kernel

private theorem sp18211 : smallValid 18211 36 := by unfold smallValid; decide +kernel

private theorem sp18247 : smallValid 18247 37 := by unfold smallValid; decide +kernel

private theorem sp18284 : smallValid 18284 36 := by unfold smallValid; decide +kernel

private theorem sp18320 : smallValid 18320 36 := by unfold smallValid; decide +kernel

private theorem sp18356 : smallValid 18356 36 := by unfold smallValid; decide +kernel

private theorem sp18392 : smallValid 18392 37 := by unfold smallValid; decide +kernel

private theorem sp18429 : smallValid 18429 36 := by unfold smallValid; decide +kernel

private theorem sp18465 : smallValid 18465 37 := by unfold smallValid; decide +kernel

private theorem sp18502 : smallValid 18502 36 := by unfold smallValid; decide +kernel

private theorem sp18538 : smallValid 18538 37 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤18574) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 18575 := (joinSmall (lo:=0) (a:=9287) (b:=9288) (joinSmall (lo:=0) (a:=4643) (b:=4644) (joinSmall (lo:=0) (a:=2321) (b:=2322) (joinSmall (lo:=0) (a:=1160) (b:=1161) (joinSmall (lo:=0) (a:=580) (b:=580) (joinSmall (lo:=0) (a:=290) (b:=290) (joinSmall (lo:=0) (a:=145) (b:=145) (joinSmall (lo:=0) (a:=72) (b:=73) (joinSmall (lo:=0) (a:=36) (b:=36) sp0 sp36) (joinSmall (lo:=72) (a:=36) (b:=37) sp72 sp108)) (joinSmall (lo:=145) (a:=72) (b:=73) (joinSmall (lo:=145) (a:=36) (b:=36) sp145 sp181) (joinSmall (lo:=217) (a:=36) (b:=37) sp217 sp253))) (joinSmall (lo:=290) (a:=145) (b:=145) (joinSmall (lo:=290) (a:=72) (b:=73) (joinSmall (lo:=290) (a:=36) (b:=36) sp290 sp326) (joinSmall (lo:=362) (a:=36) (b:=37) sp362 sp398)) (joinSmall (lo:=435) (a:=72) (b:=73) (joinSmall (lo:=435) (a:=36) (b:=36) sp435 sp471) (joinSmall (lo:=507) (a:=36) (b:=37) sp507 sp543)))) (joinSmall (lo:=580) (a:=290) (b:=290) (joinSmall (lo:=580) (a:=145) (b:=145) (joinSmall (lo:=580) (a:=72) (b:=73) (joinSmall (lo:=580) (a:=36) (b:=36) sp580 sp616) (joinSmall (lo:=652) (a:=36) (b:=37) sp652 sp688)) (joinSmall (lo:=725) (a:=72) (b:=73) (joinSmall (lo:=725) (a:=36) (b:=36) sp725 sp761) (joinSmall (lo:=797) (a:=36) (b:=37) sp797 sp833))) (joinSmall (lo:=870) (a:=145) (b:=145) (joinSmall (lo:=870) (a:=72) (b:=73) (joinSmall (lo:=870) (a:=36) (b:=36) sp870 sp906) (joinSmall (lo:=942) (a:=36) (b:=37) sp942 sp978)) (joinSmall (lo:=1015) (a:=72) (b:=73) (joinSmall (lo:=1015) (a:=36) (b:=36) sp1015 sp1051) (joinSmall (lo:=1087) (a:=36) (b:=37) sp1087 sp1123))))) (joinSmall (lo:=1160) (a:=580) (b:=581) (joinSmall (lo:=1160) (a:=290) (b:=290) (joinSmall (lo:=1160) (a:=145) (b:=145) (joinSmall (lo:=1160) (a:=72) (b:=73) (joinSmall (lo:=1160) (a:=36) (b:=36) sp1160 sp1196) (joinSmall (lo:=1232) (a:=36) (b:=37) sp1232 sp1268)) (joinSmall (lo:=1305) (a:=72) (b:=73) (joinSmall (lo:=1305) (a:=36) (b:=36) sp1305 sp1341) (joinSmall (lo:=1377) (a:=36) (b:=37) sp1377 sp1413))) (joinSmall (lo:=1450) (a:=145) (b:=145) (joinSmall (lo:=1450) (a:=72) (b:=73) (joinSmall (lo:=1450) (a:=36) (b:=36) sp1450 sp1486) (joinSmall (lo:=1522) (a:=36) (b:=37) sp1522 sp1558)) (joinSmall (lo:=1595) (a:=72) (b:=73) (joinSmall (lo:=1595) (a:=36) (b:=36) sp1595 sp1631) (joinSmall (lo:=1667) (a:=36) (b:=37) sp1667 sp1703)))) (joinSmall (lo:=1740) (a:=290) (b:=291) (joinSmall (lo:=1740) (a:=145) (b:=145) (joinSmall (lo:=1740) (a:=72) (b:=73) (joinSmall (lo:=1740) (a:=36) (b:=36) sp1740 sp1776) (joinSmall (lo:=1812) (a:=36) (b:=37) sp1812 sp1848)) (joinSmall (lo:=1885) (a:=72) (b:=73) (joinSmall (lo:=1885) (a:=36) (b:=36) sp1885 sp1921) (joinSmall (lo:=1957) (a:=36) (b:=37) sp1957 sp1993))) (joinSmall (lo:=2030) (a:=145) (b:=146) (joinSmall (lo:=2030) (a:=72) (b:=73) (joinSmall (lo:=2030) (a:=36) (b:=36) sp2030 sp2066) (joinSmall (lo:=2102) (a:=36) (b:=37) sp2102 sp2138)) (joinSmall (lo:=2175) (a:=73) (b:=73) (joinSmall (lo:=2175) (a:=36) (b:=37) sp2175 sp2211) (joinSmall (lo:=2248) (a:=36) (b:=37) sp2248 sp2284)))))) (joinSmall (lo:=2321) (a:=1161) (b:=1161) (joinSmall (lo:=2321) (a:=580) (b:=581) (joinSmall (lo:=2321) (a:=290) (b:=290) (joinSmall (lo:=2321) (a:=145) (b:=145) (joinSmall (lo:=2321) (a:=72) (b:=73) (joinSmall (lo:=2321) (a:=36) (b:=36) sp2321 sp2357) (joinSmall (lo:=2393) (a:=36) (b:=37) sp2393 sp2429)) (joinSmall (lo:=2466) (a:=72) (b:=73) (joinSmall (lo:=2466) (a:=36) (b:=36) sp2466 sp2502) (joinSmall (lo:=2538) (a:=36) (b:=37) sp2538 sp2574))) (joinSmall (lo:=2611) (a:=145) (b:=145) (joinSmall (lo:=2611) (a:=72) (b:=73) (joinSmall (lo:=2611) (a:=36) (b:=36) sp2611 sp2647) (joinSmall (lo:=2683) (a:=36) (b:=37) sp2683 sp2719)) (joinSmall (lo:=2756) (a:=72) (b:=73) (joinSmall (lo:=2756) (a:=36) (b:=36) sp2756 sp2792) (joinSmall (lo:=2828) (a:=36) (b:=37) sp2828 sp2864)))) (joinSmall (lo:=2901) (a:=290) (b:=291) (joinSmall (lo:=2901) (a:=145) (b:=145) (joinSmall (lo:=2901) (a:=72) (b:=73) (joinSmall (lo:=2901) (a:=36) (b:=36) sp2901 sp2937) (joinSmall (lo:=2973) (a:=36) (b:=37) sp2973 sp3009)) (joinSmall (lo:=3046) (a:=72) (b:=73) (joinSmall (lo:=3046) (a:=36) (b:=36) sp3046 sp3082) (joinSmall (lo:=3118) (a:=36) (b:=37) sp3118 sp3154))) (joinSmall (lo:=3191) (a:=145) (b:=146) (joinSmall (lo:=3191) (a:=72) (b:=73) (joinSmall (lo:=3191) (a:=36) (b:=36) sp3191 sp3227) (joinSmall (lo:=3263) (a:=36) (b:=37) sp3263 sp3299)) (joinSmall (lo:=3336) (a:=73) (b:=73) (joinSmall (lo:=3336) (a:=36) (b:=37) sp3336 sp3372) (joinSmall (lo:=3409) (a:=36) (b:=37) sp3409 sp3445))))) (joinSmall (lo:=3482) (a:=580) (b:=581) (joinSmall (lo:=3482) (a:=290) (b:=290) (joinSmall (lo:=3482) (a:=145) (b:=145) (joinSmall (lo:=3482) (a:=72) (b:=73) (joinSmall (lo:=3482) (a:=36) (b:=36) sp3482 sp3518) (joinSmall (lo:=3554) (a:=36) (b:=37) sp3554 sp3590)) (joinSmall (lo:=3627) (a:=72) (b:=73) (joinSmall (lo:=3627) (a:=36) (b:=36) sp3627 sp3663) (joinSmall (lo:=3699) (a:=36) (b:=37) sp3699 sp3735))) (joinSmall (lo:=3772) (a:=145) (b:=145) (joinSmall (lo:=3772) (a:=72) (b:=73) (joinSmall (lo:=3772) (a:=36) (b:=36) sp3772 sp3808) (joinSmall (lo:=3844) (a:=36) (b:=37) sp3844 sp3880)) (joinSmall (lo:=3917) (a:=72) (b:=73) (joinSmall (lo:=3917) (a:=36) (b:=36) sp3917 sp3953) (joinSmall (lo:=3989) (a:=36) (b:=37) sp3989 sp4025)))) (joinSmall (lo:=4062) (a:=290) (b:=291) (joinSmall (lo:=4062) (a:=145) (b:=145) (joinSmall (lo:=4062) (a:=72) (b:=73) (joinSmall (lo:=4062) (a:=36) (b:=36) sp4062 sp4098) (joinSmall (lo:=4134) (a:=36) (b:=37) sp4134 sp4170)) (joinSmall (lo:=4207) (a:=72) (b:=73) (joinSmall (lo:=4207) (a:=36) (b:=36) sp4207 sp4243) (joinSmall (lo:=4279) (a:=36) (b:=37) sp4279 sp4315))) (joinSmall (lo:=4352) (a:=145) (b:=146) (joinSmall (lo:=4352) (a:=72) (b:=73) (joinSmall (lo:=4352) (a:=36) (b:=36) sp4352 sp4388) (joinSmall (lo:=4424) (a:=36) (b:=37) sp4424 sp4460)) (joinSmall (lo:=4497) (a:=73) (b:=73) (joinSmall (lo:=4497) (a:=36) (b:=37) sp4497 sp4533) (joinSmall (lo:=4570) (a:=36) (b:=37) sp4570 sp4606))))))) (joinSmall (lo:=4643) (a:=2322) (b:=2322) (joinSmall (lo:=4643) (a:=1161) (b:=1161) (joinSmall (lo:=4643) (a:=580) (b:=581) (joinSmall (lo:=4643) (a:=290) (b:=290) (joinSmall (lo:=4643) (a:=145) (b:=145) (joinSmall (lo:=4643) (a:=72) (b:=73) (joinSmall (lo:=4643) (a:=36) (b:=36) sp4643 sp4679) (joinSmall (lo:=4715) (a:=36) (b:=37) sp4715 sp4751)) (joinSmall (lo:=4788) (a:=72) (b:=73) (joinSmall (lo:=4788) (a:=36) (b:=36) sp4788 sp4824) (joinSmall (lo:=4860) (a:=36) (b:=37) sp4860 sp4896))) (joinSmall (lo:=4933) (a:=145) (b:=145) (joinSmall (lo:=4933) (a:=72) (b:=73) (joinSmall (lo:=4933) (a:=36) (b:=36) sp4933 sp4969) (joinSmall (lo:=5005) (a:=36) (b:=37) sp5005 sp5041)) (joinSmall (lo:=5078) (a:=72) (b:=73) (joinSmall (lo:=5078) (a:=36) (b:=36) sp5078 sp5114) (joinSmall (lo:=5150) (a:=36) (b:=37) sp5150 sp5186)))) (joinSmall (lo:=5223) (a:=290) (b:=291) (joinSmall (lo:=5223) (a:=145) (b:=145) (joinSmall (lo:=5223) (a:=72) (b:=73) (joinSmall (lo:=5223) (a:=36) (b:=36) sp5223 sp5259) (joinSmall (lo:=5295) (a:=36) (b:=37) sp5295 sp5331)) (joinSmall (lo:=5368) (a:=72) (b:=73) (joinSmall (lo:=5368) (a:=36) (b:=36) sp5368 sp5404) (joinSmall (lo:=5440) (a:=36) (b:=37) sp5440 sp5476))) (joinSmall (lo:=5513) (a:=145) (b:=146) (joinSmall (lo:=5513) (a:=72) (b:=73) (joinSmall (lo:=5513) (a:=36) (b:=36) sp5513 sp5549) (joinSmall (lo:=5585) (a:=36) (b:=37) sp5585 sp5621)) (joinSmall (lo:=5658) (a:=73) (b:=73) (joinSmall (lo:=5658) (a:=36) (b:=37) sp5658 sp5694) (joinSmall (lo:=5731) (a:=36) (b:=37) sp5731 sp5767))))) (joinSmall (lo:=5804) (a:=580) (b:=581) (joinSmall (lo:=5804) (a:=290) (b:=290) (joinSmall (lo:=5804) (a:=145) (b:=145) (joinSmall (lo:=5804) (a:=72) (b:=73) (joinSmall (lo:=5804) (a:=36) (b:=36) sp5804 sp5840) (joinSmall (lo:=5876) (a:=36) (b:=37) sp5876 sp5912)) (joinSmall (lo:=5949) (a:=72) (b:=73) (joinSmall (lo:=5949) (a:=36) (b:=36) sp5949 sp5985) (joinSmall (lo:=6021) (a:=36) (b:=37) sp6021 sp6057))) (joinSmall (lo:=6094) (a:=145) (b:=145) (joinSmall (lo:=6094) (a:=72) (b:=73) (joinSmall (lo:=6094) (a:=36) (b:=36) sp6094 sp6130) (joinSmall (lo:=6166) (a:=36) (b:=37) sp6166 sp6202)) (joinSmall (lo:=6239) (a:=72) (b:=73) (joinSmall (lo:=6239) (a:=36) (b:=36) sp6239 sp6275) (joinSmall (lo:=6311) (a:=36) (b:=37) sp6311 sp6347)))) (joinSmall (lo:=6384) (a:=290) (b:=291) (joinSmall (lo:=6384) (a:=145) (b:=145) (joinSmall (lo:=6384) (a:=72) (b:=73) (joinSmall (lo:=6384) (a:=36) (b:=36) sp6384 sp6420) (joinSmall (lo:=6456) (a:=36) (b:=37) sp6456 sp6492)) (joinSmall (lo:=6529) (a:=72) (b:=73) (joinSmall (lo:=6529) (a:=36) (b:=36) sp6529 sp6565) (joinSmall (lo:=6601) (a:=36) (b:=37) sp6601 sp6637))) (joinSmall (lo:=6674) (a:=145) (b:=146) (joinSmall (lo:=6674) (a:=72) (b:=73) (joinSmall (lo:=6674) (a:=36) (b:=36) sp6674 sp6710) (joinSmall (lo:=6746) (a:=36) (b:=37) sp6746 sp6782)) (joinSmall (lo:=6819) (a:=73) (b:=73) (joinSmall (lo:=6819) (a:=36) (b:=37) sp6819 sp6855) (joinSmall (lo:=6892) (a:=36) (b:=37) sp6892 sp6928)))))) (joinSmall (lo:=6965) (a:=1161) (b:=1161) (joinSmall (lo:=6965) (a:=580) (b:=581) (joinSmall (lo:=6965) (a:=290) (b:=290) (joinSmall (lo:=6965) (a:=145) (b:=145) (joinSmall (lo:=6965) (a:=72) (b:=73) (joinSmall (lo:=6965) (a:=36) (b:=36) sp6965 sp7001) (joinSmall (lo:=7037) (a:=36) (b:=37) sp7037 sp7073)) (joinSmall (lo:=7110) (a:=72) (b:=73) (joinSmall (lo:=7110) (a:=36) (b:=36) sp7110 sp7146) (joinSmall (lo:=7182) (a:=36) (b:=37) sp7182 sp7218))) (joinSmall (lo:=7255) (a:=145) (b:=145) (joinSmall (lo:=7255) (a:=72) (b:=73) (joinSmall (lo:=7255) (a:=36) (b:=36) sp7255 sp7291) (joinSmall (lo:=7327) (a:=36) (b:=37) sp7327 sp7363)) (joinSmall (lo:=7400) (a:=72) (b:=73) (joinSmall (lo:=7400) (a:=36) (b:=36) sp7400 sp7436) (joinSmall (lo:=7472) (a:=36) (b:=37) sp7472 sp7508)))) (joinSmall (lo:=7545) (a:=290) (b:=291) (joinSmall (lo:=7545) (a:=145) (b:=145) (joinSmall (lo:=7545) (a:=72) (b:=73) (joinSmall (lo:=7545) (a:=36) (b:=36) sp7545 sp7581) (joinSmall (lo:=7617) (a:=36) (b:=37) sp7617 sp7653)) (joinSmall (lo:=7690) (a:=72) (b:=73) (joinSmall (lo:=7690) (a:=36) (b:=36) sp7690 sp7726) (joinSmall (lo:=7762) (a:=36) (b:=37) sp7762 sp7798))) (joinSmall (lo:=7835) (a:=145) (b:=146) (joinSmall (lo:=7835) (a:=72) (b:=73) (joinSmall (lo:=7835) (a:=36) (b:=36) sp7835 sp7871) (joinSmall (lo:=7907) (a:=36) (b:=37) sp7907 sp7943)) (joinSmall (lo:=7980) (a:=73) (b:=73) (joinSmall (lo:=7980) (a:=36) (b:=37) sp7980 sp8016) (joinSmall (lo:=8053) (a:=36) (b:=37) sp8053 sp8089))))) (joinSmall (lo:=8126) (a:=580) (b:=581) (joinSmall (lo:=8126) (a:=290) (b:=290) (joinSmall (lo:=8126) (a:=145) (b:=145) (joinSmall (lo:=8126) (a:=72) (b:=73) (joinSmall (lo:=8126) (a:=36) (b:=36) sp8126 sp8162) (joinSmall (lo:=8198) (a:=36) (b:=37) sp8198 sp8234)) (joinSmall (lo:=8271) (a:=72) (b:=73) (joinSmall (lo:=8271) (a:=36) (b:=36) sp8271 sp8307) (joinSmall (lo:=8343) (a:=36) (b:=37) sp8343 sp8379))) (joinSmall (lo:=8416) (a:=145) (b:=145) (joinSmall (lo:=8416) (a:=72) (b:=73) (joinSmall (lo:=8416) (a:=36) (b:=36) sp8416 sp8452) (joinSmall (lo:=8488) (a:=36) (b:=37) sp8488 sp8524)) (joinSmall (lo:=8561) (a:=72) (b:=73) (joinSmall (lo:=8561) (a:=36) (b:=36) sp8561 sp8597) (joinSmall (lo:=8633) (a:=36) (b:=37) sp8633 sp8669)))) (joinSmall (lo:=8706) (a:=290) (b:=291) (joinSmall (lo:=8706) (a:=145) (b:=145) (joinSmall (lo:=8706) (a:=72) (b:=73) (joinSmall (lo:=8706) (a:=36) (b:=36) sp8706 sp8742) (joinSmall (lo:=8778) (a:=36) (b:=37) sp8778 sp8814)) (joinSmall (lo:=8851) (a:=72) (b:=73) (joinSmall (lo:=8851) (a:=36) (b:=36) sp8851 sp8887) (joinSmall (lo:=8923) (a:=36) (b:=37) sp8923 sp8959))) (joinSmall (lo:=8996) (a:=145) (b:=146) (joinSmall (lo:=8996) (a:=72) (b:=73) (joinSmall (lo:=8996) (a:=36) (b:=36) sp8996 sp9032) (joinSmall (lo:=9068) (a:=36) (b:=37) sp9068 sp9104)) (joinSmall (lo:=9141) (a:=73) (b:=73) (joinSmall (lo:=9141) (a:=36) (b:=37) sp9141 sp9177) (joinSmall (lo:=9214) (a:=36) (b:=37) sp9214 sp9250)))))))) (joinSmall (lo:=9287) (a:=4644) (b:=4644) (joinSmall (lo:=9287) (a:=2322) (b:=2322) (joinSmall (lo:=9287) (a:=1161) (b:=1161) (joinSmall (lo:=9287) (a:=580) (b:=581) (joinSmall (lo:=9287) (a:=290) (b:=290) (joinSmall (lo:=9287) (a:=145) (b:=145) (joinSmall (lo:=9287) (a:=72) (b:=73) (joinSmall (lo:=9287) (a:=36) (b:=36) sp9287 sp9323) (joinSmall (lo:=9359) (a:=36) (b:=37) sp9359 sp9395)) (joinSmall (lo:=9432) (a:=72) (b:=73) (joinSmall (lo:=9432) (a:=36) (b:=36) sp9432 sp9468) (joinSmall (lo:=9504) (a:=36) (b:=37) sp9504 sp9540))) (joinSmall (lo:=9577) (a:=145) (b:=145) (joinSmall (lo:=9577) (a:=72) (b:=73) (joinSmall (lo:=9577) (a:=36) (b:=36) sp9577 sp9613) (joinSmall (lo:=9649) (a:=36) (b:=37) sp9649 sp9685)) (joinSmall (lo:=9722) (a:=72) (b:=73) (joinSmall (lo:=9722) (a:=36) (b:=36) sp9722 sp9758) (joinSmall (lo:=9794) (a:=36) (b:=37) sp9794 sp9830)))) (joinSmall (lo:=9867) (a:=290) (b:=291) (joinSmall (lo:=9867) (a:=145) (b:=145) (joinSmall (lo:=9867) (a:=72) (b:=73) (joinSmall (lo:=9867) (a:=36) (b:=36) sp9867 sp9903) (joinSmall (lo:=9939) (a:=36) (b:=37) sp9939 sp9975)) (joinSmall (lo:=10012) (a:=72) (b:=73) (joinSmall (lo:=10012) (a:=36) (b:=36) sp10012 sp10048) (joinSmall (lo:=10084) (a:=36) (b:=37) sp10084 sp10120))) (joinSmall (lo:=10157) (a:=145) (b:=146) (joinSmall (lo:=10157) (a:=72) (b:=73) (joinSmall (lo:=10157) (a:=36) (b:=36) sp10157 sp10193) (joinSmall (lo:=10229) (a:=36) (b:=37) sp10229 sp10265)) (joinSmall (lo:=10302) (a:=73) (b:=73) (joinSmall (lo:=10302) (a:=36) (b:=37) sp10302 sp10338) (joinSmall (lo:=10375) (a:=36) (b:=37) sp10375 sp10411))))) (joinSmall (lo:=10448) (a:=580) (b:=581) (joinSmall (lo:=10448) (a:=290) (b:=290) (joinSmall (lo:=10448) (a:=145) (b:=145) (joinSmall (lo:=10448) (a:=72) (b:=73) (joinSmall (lo:=10448) (a:=36) (b:=36) sp10448 sp10484) (joinSmall (lo:=10520) (a:=36) (b:=37) sp10520 sp10556)) (joinSmall (lo:=10593) (a:=72) (b:=73) (joinSmall (lo:=10593) (a:=36) (b:=36) sp10593 sp10629) (joinSmall (lo:=10665) (a:=36) (b:=37) sp10665 sp10701))) (joinSmall (lo:=10738) (a:=145) (b:=145) (joinSmall (lo:=10738) (a:=72) (b:=73) (joinSmall (lo:=10738) (a:=36) (b:=36) sp10738 sp10774) (joinSmall (lo:=10810) (a:=36) (b:=37) sp10810 sp10846)) (joinSmall (lo:=10883) (a:=72) (b:=73) (joinSmall (lo:=10883) (a:=36) (b:=36) sp10883 sp10919) (joinSmall (lo:=10955) (a:=36) (b:=37) sp10955 sp10991)))) (joinSmall (lo:=11028) (a:=290) (b:=291) (joinSmall (lo:=11028) (a:=145) (b:=145) (joinSmall (lo:=11028) (a:=72) (b:=73) (joinSmall (lo:=11028) (a:=36) (b:=36) sp11028 sp11064) (joinSmall (lo:=11100) (a:=36) (b:=37) sp11100 sp11136)) (joinSmall (lo:=11173) (a:=72) (b:=73) (joinSmall (lo:=11173) (a:=36) (b:=36) sp11173 sp11209) (joinSmall (lo:=11245) (a:=36) (b:=37) sp11245 sp11281))) (joinSmall (lo:=11318) (a:=145) (b:=146) (joinSmall (lo:=11318) (a:=72) (b:=73) (joinSmall (lo:=11318) (a:=36) (b:=36) sp11318 sp11354) (joinSmall (lo:=11390) (a:=36) (b:=37) sp11390 sp11426)) (joinSmall (lo:=11463) (a:=73) (b:=73) (joinSmall (lo:=11463) (a:=36) (b:=37) sp11463 sp11499) (joinSmall (lo:=11536) (a:=36) (b:=37) sp11536 sp11572)))))) (joinSmall (lo:=11609) (a:=1161) (b:=1161) (joinSmall (lo:=11609) (a:=580) (b:=581) (joinSmall (lo:=11609) (a:=290) (b:=290) (joinSmall (lo:=11609) (a:=145) (b:=145) (joinSmall (lo:=11609) (a:=72) (b:=73) (joinSmall (lo:=11609) (a:=36) (b:=36) sp11609 sp11645) (joinSmall (lo:=11681) (a:=36) (b:=37) sp11681 sp11717)) (joinSmall (lo:=11754) (a:=72) (b:=73) (joinSmall (lo:=11754) (a:=36) (b:=36) sp11754 sp11790) (joinSmall (lo:=11826) (a:=36) (b:=37) sp11826 sp11862))) (joinSmall (lo:=11899) (a:=145) (b:=145) (joinSmall (lo:=11899) (a:=72) (b:=73) (joinSmall (lo:=11899) (a:=36) (b:=36) sp11899 sp11935) (joinSmall (lo:=11971) (a:=36) (b:=37) sp11971 sp12007)) (joinSmall (lo:=12044) (a:=72) (b:=73) (joinSmall (lo:=12044) (a:=36) (b:=36) sp12044 sp12080) (joinSmall (lo:=12116) (a:=36) (b:=37) sp12116 sp12152)))) (joinSmall (lo:=12189) (a:=290) (b:=291) (joinSmall (lo:=12189) (a:=145) (b:=145) (joinSmall (lo:=12189) (a:=72) (b:=73) (joinSmall (lo:=12189) (a:=36) (b:=36) sp12189 sp12225) (joinSmall (lo:=12261) (a:=36) (b:=37) sp12261 sp12297)) (joinSmall (lo:=12334) (a:=72) (b:=73) (joinSmall (lo:=12334) (a:=36) (b:=36) sp12334 sp12370) (joinSmall (lo:=12406) (a:=36) (b:=37) sp12406 sp12442))) (joinSmall (lo:=12479) (a:=145) (b:=146) (joinSmall (lo:=12479) (a:=72) (b:=73) (joinSmall (lo:=12479) (a:=36) (b:=36) sp12479 sp12515) (joinSmall (lo:=12551) (a:=36) (b:=37) sp12551 sp12587)) (joinSmall (lo:=12624) (a:=73) (b:=73) (joinSmall (lo:=12624) (a:=36) (b:=37) sp12624 sp12660) (joinSmall (lo:=12697) (a:=36) (b:=37) sp12697 sp12733))))) (joinSmall (lo:=12770) (a:=580) (b:=581) (joinSmall (lo:=12770) (a:=290) (b:=290) (joinSmall (lo:=12770) (a:=145) (b:=145) (joinSmall (lo:=12770) (a:=72) (b:=73) (joinSmall (lo:=12770) (a:=36) (b:=36) sp12770 sp12806) (joinSmall (lo:=12842) (a:=36) (b:=37) sp12842 sp12878)) (joinSmall (lo:=12915) (a:=72) (b:=73) (joinSmall (lo:=12915) (a:=36) (b:=36) sp12915 sp12951) (joinSmall (lo:=12987) (a:=36) (b:=37) sp12987 sp13023))) (joinSmall (lo:=13060) (a:=145) (b:=145) (joinSmall (lo:=13060) (a:=72) (b:=73) (joinSmall (lo:=13060) (a:=36) (b:=36) sp13060 sp13096) (joinSmall (lo:=13132) (a:=36) (b:=37) sp13132 sp13168)) (joinSmall (lo:=13205) (a:=72) (b:=73) (joinSmall (lo:=13205) (a:=36) (b:=36) sp13205 sp13241) (joinSmall (lo:=13277) (a:=36) (b:=37) sp13277 sp13313)))) (joinSmall (lo:=13350) (a:=290) (b:=291) (joinSmall (lo:=13350) (a:=145) (b:=145) (joinSmall (lo:=13350) (a:=72) (b:=73) (joinSmall (lo:=13350) (a:=36) (b:=36) sp13350 sp13386) (joinSmall (lo:=13422) (a:=36) (b:=37) sp13422 sp13458)) (joinSmall (lo:=13495) (a:=72) (b:=73) (joinSmall (lo:=13495) (a:=36) (b:=36) sp13495 sp13531) (joinSmall (lo:=13567) (a:=36) (b:=37) sp13567 sp13603))) (joinSmall (lo:=13640) (a:=145) (b:=146) (joinSmall (lo:=13640) (a:=72) (b:=73) (joinSmall (lo:=13640) (a:=36) (b:=36) sp13640 sp13676) (joinSmall (lo:=13712) (a:=36) (b:=37) sp13712 sp13748)) (joinSmall (lo:=13785) (a:=73) (b:=73) (joinSmall (lo:=13785) (a:=36) (b:=37) sp13785 sp13821) (joinSmall (lo:=13858) (a:=36) (b:=37) sp13858 sp13894))))))) (joinSmall (lo:=13931) (a:=2322) (b:=2322) (joinSmall (lo:=13931) (a:=1161) (b:=1161) (joinSmall (lo:=13931) (a:=580) (b:=581) (joinSmall (lo:=13931) (a:=290) (b:=290) (joinSmall (lo:=13931) (a:=145) (b:=145) (joinSmall (lo:=13931) (a:=72) (b:=73) (joinSmall (lo:=13931) (a:=36) (b:=36) sp13931 sp13967) (joinSmall (lo:=14003) (a:=36) (b:=37) sp14003 sp14039)) (joinSmall (lo:=14076) (a:=72) (b:=73) (joinSmall (lo:=14076) (a:=36) (b:=36) sp14076 sp14112) (joinSmall (lo:=14148) (a:=36) (b:=37) sp14148 sp14184))) (joinSmall (lo:=14221) (a:=145) (b:=145) (joinSmall (lo:=14221) (a:=72) (b:=73) (joinSmall (lo:=14221) (a:=36) (b:=36) sp14221 sp14257) (joinSmall (lo:=14293) (a:=36) (b:=37) sp14293 sp14329)) (joinSmall (lo:=14366) (a:=72) (b:=73) (joinSmall (lo:=14366) (a:=36) (b:=36) sp14366 sp14402) (joinSmall (lo:=14438) (a:=36) (b:=37) sp14438 sp14474)))) (joinSmall (lo:=14511) (a:=290) (b:=291) (joinSmall (lo:=14511) (a:=145) (b:=145) (joinSmall (lo:=14511) (a:=72) (b:=73) (joinSmall (lo:=14511) (a:=36) (b:=36) sp14511 sp14547) (joinSmall (lo:=14583) (a:=36) (b:=37) sp14583 sp14619)) (joinSmall (lo:=14656) (a:=72) (b:=73) (joinSmall (lo:=14656) (a:=36) (b:=36) sp14656 sp14692) (joinSmall (lo:=14728) (a:=36) (b:=37) sp14728 sp14764))) (joinSmall (lo:=14801) (a:=145) (b:=146) (joinSmall (lo:=14801) (a:=72) (b:=73) (joinSmall (lo:=14801) (a:=36) (b:=36) sp14801 sp14837) (joinSmall (lo:=14873) (a:=36) (b:=37) sp14873 sp14909)) (joinSmall (lo:=14946) (a:=73) (b:=73) (joinSmall (lo:=14946) (a:=36) (b:=37) sp14946 sp14982) (joinSmall (lo:=15019) (a:=36) (b:=37) sp15019 sp15055))))) (joinSmall (lo:=15092) (a:=580) (b:=581) (joinSmall (lo:=15092) (a:=290) (b:=290) (joinSmall (lo:=15092) (a:=145) (b:=145) (joinSmall (lo:=15092) (a:=72) (b:=73) (joinSmall (lo:=15092) (a:=36) (b:=36) sp15092 sp15128) (joinSmall (lo:=15164) (a:=36) (b:=37) sp15164 sp15200)) (joinSmall (lo:=15237) (a:=72) (b:=73) (joinSmall (lo:=15237) (a:=36) (b:=36) sp15237 sp15273) (joinSmall (lo:=15309) (a:=36) (b:=37) sp15309 sp15345))) (joinSmall (lo:=15382) (a:=145) (b:=145) (joinSmall (lo:=15382) (a:=72) (b:=73) (joinSmall (lo:=15382) (a:=36) (b:=36) sp15382 sp15418) (joinSmall (lo:=15454) (a:=36) (b:=37) sp15454 sp15490)) (joinSmall (lo:=15527) (a:=72) (b:=73) (joinSmall (lo:=15527) (a:=36) (b:=36) sp15527 sp15563) (joinSmall (lo:=15599) (a:=36) (b:=37) sp15599 sp15635)))) (joinSmall (lo:=15672) (a:=290) (b:=291) (joinSmall (lo:=15672) (a:=145) (b:=145) (joinSmall (lo:=15672) (a:=72) (b:=73) (joinSmall (lo:=15672) (a:=36) (b:=36) sp15672 sp15708) (joinSmall (lo:=15744) (a:=36) (b:=37) sp15744 sp15780)) (joinSmall (lo:=15817) (a:=72) (b:=73) (joinSmall (lo:=15817) (a:=36) (b:=36) sp15817 sp15853) (joinSmall (lo:=15889) (a:=36) (b:=37) sp15889 sp15925))) (joinSmall (lo:=15962) (a:=145) (b:=146) (joinSmall (lo:=15962) (a:=72) (b:=73) (joinSmall (lo:=15962) (a:=36) (b:=36) sp15962 sp15998) (joinSmall (lo:=16034) (a:=36) (b:=37) sp16034 sp16070)) (joinSmall (lo:=16107) (a:=73) (b:=73) (joinSmall (lo:=16107) (a:=36) (b:=37) sp16107 sp16143) (joinSmall (lo:=16180) (a:=36) (b:=37) sp16180 sp16216)))))) (joinSmall (lo:=16253) (a:=1161) (b:=1161) (joinSmall (lo:=16253) (a:=580) (b:=581) (joinSmall (lo:=16253) (a:=290) (b:=290) (joinSmall (lo:=16253) (a:=145) (b:=145) (joinSmall (lo:=16253) (a:=72) (b:=73) (joinSmall (lo:=16253) (a:=36) (b:=36) sp16253 sp16289) (joinSmall (lo:=16325) (a:=36) (b:=37) sp16325 sp16361)) (joinSmall (lo:=16398) (a:=72) (b:=73) (joinSmall (lo:=16398) (a:=36) (b:=36) sp16398 sp16434) (joinSmall (lo:=16470) (a:=36) (b:=37) sp16470 sp16506))) (joinSmall (lo:=16543) (a:=145) (b:=145) (joinSmall (lo:=16543) (a:=72) (b:=73) (joinSmall (lo:=16543) (a:=36) (b:=36) sp16543 sp16579) (joinSmall (lo:=16615) (a:=36) (b:=37) sp16615 sp16651)) (joinSmall (lo:=16688) (a:=72) (b:=73) (joinSmall (lo:=16688) (a:=36) (b:=36) sp16688 sp16724) (joinSmall (lo:=16760) (a:=36) (b:=37) sp16760 sp16796)))) (joinSmall (lo:=16833) (a:=290) (b:=291) (joinSmall (lo:=16833) (a:=145) (b:=145) (joinSmall (lo:=16833) (a:=72) (b:=73) (joinSmall (lo:=16833) (a:=36) (b:=36) sp16833 sp16869) (joinSmall (lo:=16905) (a:=36) (b:=37) sp16905 sp16941)) (joinSmall (lo:=16978) (a:=72) (b:=73) (joinSmall (lo:=16978) (a:=36) (b:=36) sp16978 sp17014) (joinSmall (lo:=17050) (a:=36) (b:=37) sp17050 sp17086))) (joinSmall (lo:=17123) (a:=145) (b:=146) (joinSmall (lo:=17123) (a:=72) (b:=73) (joinSmall (lo:=17123) (a:=36) (b:=36) sp17123 sp17159) (joinSmall (lo:=17195) (a:=36) (b:=37) sp17195 sp17231)) (joinSmall (lo:=17268) (a:=73) (b:=73) (joinSmall (lo:=17268) (a:=36) (b:=37) sp17268 sp17304) (joinSmall (lo:=17341) (a:=36) (b:=37) sp17341 sp17377))))) (joinSmall (lo:=17414) (a:=580) (b:=581) (joinSmall (lo:=17414) (a:=290) (b:=290) (joinSmall (lo:=17414) (a:=145) (b:=145) (joinSmall (lo:=17414) (a:=72) (b:=73) (joinSmall (lo:=17414) (a:=36) (b:=36) sp17414 sp17450) (joinSmall (lo:=17486) (a:=36) (b:=37) sp17486 sp17522)) (joinSmall (lo:=17559) (a:=72) (b:=73) (joinSmall (lo:=17559) (a:=36) (b:=36) sp17559 sp17595) (joinSmall (lo:=17631) (a:=36) (b:=37) sp17631 sp17667))) (joinSmall (lo:=17704) (a:=145) (b:=145) (joinSmall (lo:=17704) (a:=72) (b:=73) (joinSmall (lo:=17704) (a:=36) (b:=36) sp17704 sp17740) (joinSmall (lo:=17776) (a:=36) (b:=37) sp17776 sp17812)) (joinSmall (lo:=17849) (a:=72) (b:=73) (joinSmall (lo:=17849) (a:=36) (b:=36) sp17849 sp17885) (joinSmall (lo:=17921) (a:=36) (b:=37) sp17921 sp17957)))) (joinSmall (lo:=17994) (a:=290) (b:=291) (joinSmall (lo:=17994) (a:=145) (b:=145) (joinSmall (lo:=17994) (a:=72) (b:=73) (joinSmall (lo:=17994) (a:=36) (b:=36) sp17994 sp18030) (joinSmall (lo:=18066) (a:=36) (b:=37) sp18066 sp18102)) (joinSmall (lo:=18139) (a:=72) (b:=73) (joinSmall (lo:=18139) (a:=36) (b:=36) sp18139 sp18175) (joinSmall (lo:=18211) (a:=36) (b:=37) sp18211 sp18247))) (joinSmall (lo:=18284) (a:=145) (b:=146) (joinSmall (lo:=18284) (a:=72) (b:=73) (joinSmall (lo:=18284) (a:=36) (b:=36) sp18284 sp18320) (joinSmall (lo:=18356) (a:=36) (b:=37) sp18356 sp18392)) (joinSmall (lo:=18429) (a:=73) (b:=73) (joinSmall (lo:=18429) (a:=36) (b:=37) sp18429 sp18465) (joinSmall (lo:=18502) (a:=36) (b:=37) sp18502 sp18538)))))))))
  have good : (List.range 18575).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 345000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 18574 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 18574 := by
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


private def packet (i : ℕ) : ℕ := (if i < 88 then (if i < 44 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 8 then (if i < 6 then 0 else (if i < 7 then 0 else 0)) else (if i < 9 then 0 else (if i < 10 then 0 else 0)))) else (if i < 16 then (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else (if i < 15 then 0 else 0))) else (if i < 19 then (if i < 17 then 0 else (if i < 18 then 0 else 0)) else (if i < 20 then 0 else (if i < 21 then 0 else 0))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else (if i < 26 then 0 else 0))) else (if i < 30 then (if i < 28 then 0 else (if i < 29 then 0 else 0)) else (if i < 31 then 0 else (if i < 32 then 0 else 0)))) else (if i < 38 then (if i < 35 then (if i < 34 then 0 else 0) else (if i < 36 then 0 else (if i < 37 then 0 else 0))) else (if i < 41 then (if i < 39 then 0 else (if i < 40 then 0 else 0)) else (if i < 42 then 0 else (if i < 43 then 0 else 0)))))) else (if i < 66 then (if i < 55 then (if i < 49 then (if i < 46 then (if i < 45 then 0 else 0) else (if i < 47 then 0 else (if i < 48 then 0 else 0))) else (if i < 52 then (if i < 50 then 0 else (if i < 51 then 0 else 0)) else (if i < 53 then 0 else (if i < 54 then 0 else 0)))) else (if i < 60 then (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else (if i < 59 then 0 else 0))) else (if i < 63 then (if i < 61 then 0 else (if i < 62 then 0 else 0)) else (if i < 64 then 0 else (if i < 65 then 0 else 0))))) else (if i < 77 then (if i < 71 then (if i < 68 then (if i < 67 then 0 else 0) else (if i < 69 then 0 else (if i < 70 then 0 else 0))) else (if i < 74 then (if i < 72 then 0 else (if i < 73 then 0 else 0)) else (if i < 75 then 0 else (if i < 76 then 0 else 0)))) else (if i < 82 then (if i < 79 then (if i < 78 then 0 else 0) else (if i < 80 then 0 else (if i < 81 then 0 else 0))) else (if i < 85 then (if i < 83 then 0 else (if i < 84 then 0 else 0)) else (if i < 86 then 0 else (if i < 87 then 0 else 0))))))) else (if i < 132 then (if i < 110 then (if i < 99 then (if i < 93 then (if i < 90 then (if i < 89 then 0 else 0) else (if i < 91 then 0 else (if i < 92 then 0 else 0))) else (if i < 96 then (if i < 94 then 0 else (if i < 95 then 0 else 0)) else (if i < 97 then 0 else (if i < 98 then 0 else 0)))) else (if i < 104 then (if i < 101 then (if i < 100 then 0 else 0) else (if i < 102 then 0 else (if i < 103 then 0 else 0))) else (if i < 107 then (if i < 105 then 0 else (if i < 106 then 0 else 0)) else (if i < 108 then 0 else (if i < 109 then 0 else 0))))) else (if i < 121 then (if i < 115 then (if i < 112 then (if i < 111 then 0 else 0) else (if i < 113 then 0 else (if i < 114 then 0 else 0))) else (if i < 118 then (if i < 116 then 0 else (if i < 117 then 0 else 0)) else (if i < 119 then 0 else (if i < 120 then 0 else 0)))) else (if i < 126 then (if i < 123 then (if i < 122 then 0 else 0) else (if i < 124 then 0 else (if i < 125 then 0 else 0))) else (if i < 129 then (if i < 127 then 0 else (if i < 128 then 0 else 0)) else (if i < 130 then 0 else (if i < 131 then 0 else 0)))))) else (if i < 154 then (if i < 143 then (if i < 137 then (if i < 134 then (if i < 133 then 0 else 0) else (if i < 135 then 0 else (if i < 136 then 0 else 0))) else (if i < 140 then (if i < 138 then 0 else (if i < 139 then 0 else 0)) else (if i < 141 then 0 else (if i < 142 then 0 else 0)))) else (if i < 148 then (if i < 145 then (if i < 144 then 0 else 0) else (if i < 146 then 0 else (if i < 147 then 0 else 0))) else (if i < 151 then (if i < 149 then 0 else (if i < 150 then 0 else 0)) else (if i < 152 then 0 else (if i < 153 then 0 else 0))))) else (if i < 165 then (if i < 159 then (if i < 156 then (if i < 155 then 0 else 0) else (if i < 157 then 0 else (if i < 158 then 0 else 0))) else (if i < 162 then (if i < 160 then 0 else (if i < 161 then 0 else 0)) else (if i < 163 then 0x107f0f62e015689ee4a12160f246b830a15809383c818409003380d00000107eae92d3951c9c848c2178f246e030915509483de18b091830c0b40000107e4c62e29598a0c4ab21f8f486ce30514a88dc3c017d08f02f00c60000107de972de156c9d04882170f446c82fe14c89003b217d08e83080c00000107d8772db95409ea48f2188f606e830715109003a617808e02dc0b80000107d26b2dd9584a0449c21d0f506e230f15789443e018c091031c0cc0000107cc512de15909e648e2170f206d030915309083d017f09703000d20000107c6132ef95b8a124ad2250fcc72e33916909dc4181a70a103540d00000107bff82db15849dc49a21b0f486e831015889483e418c09503000b80000107b9db2e195809fc4a221c8f586f632215c89203c817f08b82c00b20000107b3c72d495249de4942180f306d031815c89903fe1a509d03480d20000107adbe2d4152c9ce4822100eec6b42f714a88cc3b017708b83100ca0000107a7752f615d0a324ba22d0fac71a32b16609a840219509683300c20000107a16f2d2154c9ea48b2118f146c030915408f03c018309082fc0ca00001079b412de95909fa4aa2240f8c6f432515c095c3e018d09483040c40000107952a2dc1554a0049e21b8f506f832416109783e41970a0037c0f600001078f252d6954c9e448c2160f406d230714f08f83be17c08e82e40ac000010788f92e795a8a0c4982130f106b830215089103c618a09203080c8000010782e02d895309d848b2188f5c6e831d15a89303e618d09403200cc00001077cb32e295589ec49821c0f4c6ec30815288ec3c018109302ec0a80000107767d2ea95c0a284ad2260fa872633216889944041a309983300cc000010770712d295189d04852170f1c6e631815789383e618d09403380ca00001076a6f2ce95049be4812138f2c6de31015609303ca186090830c0c20000107643c2df955c9fc49c2178f346ec31815689243dc18a094030c0c800001075e252e115749ea4942228f7470831f15f09703fc19209483280ca000010757e12f015f0a464b722b0fec72c32516209803fc19509203000c6000010751d92d4953c9d048d21a8f606f831315b097840c19b09703200ce00001074bb42dc155c9f048e2190f306fa31915a89703fe19709b03240c8000010745912e315749fc4962198f346c82ff15089383e418909183340ca00001073f712dc9560a064962188f2c6c02fb153892c3e218b09902f40ac000010739462e295689f64a92210f706ea31315008e83a417d08c82e40ba000010733462d115109d44862160f4c6d030e15889483d018709403300d600001072d2b2da15449dc48f2178f386ee31115c09443e418908f02f80c2000010727152de15609ea49521b8f586f231114e08ec3c618a09503380cc000010720e82e695c8a224b822b0fbc6fc315158893c3dc18409083180da00001071aad2eb95c0a244ac2250f8070431515f09603e618e09502dc0b4000010714632f095e4a0a4a22200f9070631c15d095c3f618709483140ca00001070e5c2d595209d84822110f046c02fb14b88bc3ac17f090030c0ca0000107084b2d8156ca0249c21a8f3c6d830614d89043c818008a82f80b8000010702402ce94f49bc47e20d0ee86ae305158095c3e018809783100ca0000106fc0a2e31584a104ad2250f646e8311156096c40e19909e03740d20000106f5bb2f6961ca3c4c32280fac6fe31c15d896c3d017a08d03300d40000106efae2d895249d048e2158f406ba30015209183ca18709383400c80000106e9822e595b8a0c49c21d0f8870e32015709403e2191095030c0ca0000106e3992c914bc9b64762098edc6c430715489183ae17308b02f40c00000106dd6c2e39594a084a12220f9870831715d09583ea191096830c0ca0000106d7672d595089d048420e8ef46c82fe14d08d43aa16f08882ac09c0000106d1432e095609f84962198f546d630c15809743f019b09c03400be0000106cb3d2d615209de48b2158f106d030715489343ce18608f83080c20000106c5352d194fc9ba47c2140f146d230815589143c218008d02d40cc0000106bf1d2db157c9f649921c0f506d430414c08c43a017708c82e40c60000106b9082dd956c9dc4912178f1c6d230815109343d618d09202ec0ae0000106b2bb2f015d8a244b22288fc472c334167099c40819b098832c0ca0000106acc22d4150c9ce48e2128f086aa30815009243be17408f83000c60000106a6aa2de153c9e04942188f386dc30e15589043c017a09002f00b80000106a0822e395a4a084a421f0f546ea31415a09503fa19609903280d800001069a4e2eb95c8a024992190f206da31b158093c3d018809603300c6000010694312df15a09f24a32200f846d630f15109083c818b09083080b600001068e092e315889fc49a21b8f5c6e230d15409303dc18d09603240d8000010688022d415189d84882170f306d031015709143da17d08e02d80a6000010681f12d7153c9e649f2190f446d630f15488ec3a416e08a82cc0be00001067bc32e915aca324b22278fc871631f163099441019709a033c0cc0000106757c2f49610a3a4c52318ff872232a16689984101a60a083740d600001066f6c2d795349c84822120f206de30d15b09583d618b095032c0d8000 else (if i < 164 then 0x10978ca2e315749ec4922160f086d42f814e08d03ac16a08602d80b2000010972a52e09578a064992170f0c6d030c15a09443dc183096031c0cc00001096c612f195f0a324af2270f9072432a16489943e819409a03540ce000010966692ce14d49b64802098ec46a02f214f88f83be18109203040d2000010960492e2157c9ee4922188f586ea318156091c3b418308d82fc0b200001095a292dc9570a0e49c2208f7070231315b09383d419009783300d4000010953ec2ed95e4a1a4b122c8fc471e32816209503f618d097032c0ce00001094de02d415209c04882140f0c6d030b156893c3cc18409102f00ae000010947da2d895189bc48320e0f0c6cc30414d89083d218e09403140d6000010941a92ea95d0a2e4ba22f0fc471433016989943f419309983440d000001093b8c2dd95289c448220f8f046b630414f892c3ce17308d03140c2000010935592e31578a0849821c8f286ec32115c89503f019309c03300e000001092f382e015649e649521b8f846f231415709143c218609002f80a8000010929272de15709ea4a021e0f506da30e15489083c017c09003280e40000109230b2da15309cc48f2198f686d630815809443d217a08f83140ce00001091cdf2df9588a004a52240f506cc30815289343b218809103080b0000010916d02d5951c9ba48520d8f006c62f614c090c3ce18609783080bc000010910a02e795c4a204af21f8f7870c32d15e89703e018a09783240c800001090a832dc15789fa4a221e0f646e631315a89543e019008f02dc0ba0000109046d2df154c9f84a42228f9c70a32015b094c3e019109803100d60000108fe762d1150c9b24762090edc6a82fb14f890c3c818109282fc0bc0000108f84e2dd95509ea49e2220f806ee31f16209643ee18e09b030c0c40000108f2162ed95eca0c4ae21f8f446d431415909443ee19309703140d80000108ec0b2d695209ce48b2128f1c6da30815709143b418409183140cc0000108e6172cf95089c44802128f006d431215a09783ea197098833c0ca0000108dfe92e395809fa4902130f106c030415589003da18409683200ca0000108d9c22e215a8a104ac22a8fd871a31d15d09543e0183096030c0c20000108d3d92c594ac9a447b20e8ee46ca305155092c3bc17b09503140bc0000108cd862f61624a504c422c8fbc70831b15f89703f81a109c034c0c60000108c7622e795a8a124a721f0f786ec307154890c3ba17d08c82d00b00000108c1412df158c9fa48f2150f106ca30615409283cc18309183380d80000108bb2f2d4152c9da48d2138f246d430c14a88e83a417b08882b80b80000108b5372d015189d64912160f206ca30d15809583de18c094032c0c00000108af362cb14f49a847a20f0ef86be30214f09103c6183093030c0b60000108a9062e515849fe4952160f506d830015208e83a017308d82fc0be0000108a2e32df15549f04962168f286ca303153891c3c217808e03000a600001089cc22de95689ec48f2180f4c6d431415d09343ba18509383500d6000010896b62d295189d647420b0eec6ac2e914688b43ac18008b83040b40000108908c2e515c0a0e4a82270f9c70c31715709343ca17d08d830c0d000001088a792d795249c247b2120eec6d631015308f83be18009202dc0be000010884552e595689d04852120f086c62fd14908fc3c418208f02f00c800001087e312dc957c9e248f2110ef86cc30d15008d43c618209283300cc0000108782f2cf951c9c848520f0eec6ac2f614c88f43b816d08d03080d4000010871f52ea15b8a264ad22b8fd4718319160096c3ec19309683300ca00001086bd52e3156c9e04922188f306da31115609383e819008f83100c2000010865a62e195a4a0c4a521e0f7c6f031115609403e818d09403080ba00001085f8a2dc15709f049121b8f546de30915909403ce18809603240d2000010859832cf151c9da48d2130eec6b02e914388c43b217808e030c0d0000010853602dd95609f649b2250fa46fc31415689543ce18109303100c400001084d4b2db15289ca4892190f406c22f814a08e03c4189094831c0cc000010847432d515049c44822130f386ca30915609183d018509203180bc000010841032ed15f8a304af2240f786fc31415a09583e618f09683080b400001083af92d395249d04892188f3c6ca30715a091c3c418009002e40b0000010834ca2e515b8a0e4a021f8f906f831d155092c3d618f09683000c000001082eb02df95989fa49421d8f906f431715c89443d418f095831c0e2000010828682f115cca144b322b0fc071232015e89543e619709603180d0000010822272f195f8a364b922d8fe471231d15f896c3e818e09382f40cc00001081be92e59598a044a121d8f706f2316154090c3ba18308e02f80c6000010815bc2e315889ea4982170f546e230c15688f83c217f08c031c0bc00001080f8b2e515ac9f449721d0f7c6de30e15589343e218a09303340d00000108097a2d394e49ba4812130f046de30a15689303ca18208e03180b6000010803672dc15689d048220f0ee46b430314d08f03b817108a82ec0c00000107fd3f2e215b89fc4912188f586e632015a89243d818c098031c0be0000107f71b2e315789f849b2180f586e630e15609083ca18808f03000c2000 else 0x10b00ac2c514d099246a2078e946882e7144889439016808882c00b4000010afa9e2db15309ca48e20e8f046ba2f414c08c83ae17108b02ec0be000010af4a32cf14b89a44692068eb069c2e714308a839a17008702dc0a8000010aeea92c794b099c4742078e8c6902e3142089839c17208c02e80b4000010ae88a2da15489ec4a021a0f2c6de30c157093c3ec18e09203080d2000010ae2702de95349de4852108efc6c630015409503e819809682dc0b8000010adc412e11578a004a32210f8870831915a89783f419009703200ba000010ad5fb2f215f4a444c6234100074833b16e09e44301b50a983b80ee000010ad0132c994e89ac4812110f5c6cc2fc14809203c617e09083380f0000010aca1a2c714b499046e2058ea06962f114a08e43c417f08902dc0d2000010ac4122d995349cc4832140f086ba2f914b08c43a216e08a82fc0ae000010abdf02e41598a0a49e2210f8c70e32015809343d818008e03180cc000010ab7c12e5159ca124ac2268f9070031b15c09743fa18809102e40c0000010ab1c42cb15089ca48c2190f306c230b15a09383e819009803200d0000010aab722f29618a424c722f8fc071232e16089783f219809f03540c6000010aa52e2f195e4a0e4a921f8f606d631315b89843da19009683180c2000010a9f0c2dd15989fe49c21d8f546ee31515e896c3f219a09883400da000010a98eb2e215b0a0e49f21e0f806ee312159895c3ee19509483100c0000010a92e82d115089c047620b8ee86c2300150091c3d819209282f80b8000010a8cbe2e3154c9f64902190f2c6d230d15809143d218c09283380d0000010a86872f095aca124a62238f7c70031815909403ca18509603140c6000010a804f2e815dca3e4bb2298fd872033216a89c03fa1a309b033c0ce000010a7a2a2e295b0a0e4a02228f9871232a161097c40019f09983400bc000010a74062e2158c9f449721d0f986f631015489243b8181098833c0dc000010a6de32e0955c9e04882110f246d030614f88fc3c418008f03080b2000010a678030216a4a824e023d904474e34317289f041e1a409d83380cc000010a61622dc15489ec48f2180f406de31915789303d217f08c02f40ba000010a5b4f2d795449dc49221c0f906fe31e15989203d218e09583300ce000010a55212e79590a144af2260f8c6f031615a897c3f619709e83380ca000010a4f212d115389d248620f8ef46aa2e814288b83a417108902c40ae000010a48ce2f4962ca6a4d1235102074e34317109d041019f09c834c0d2000010a42bf2d6951c9b447820b8ef46c630215789383d418108f82f00c2000010a3cc12ca94d09aa4722110f246d830e15409103b818108a02c80c0000010a36d12ce94e49bc47620f8ed46bc2f714e89083c218208e82f40c2000010a30962ee95bca224a92210ff074233a16a89c44321b00a283440d4000010a2a692ea95d0a184ac2230f886fe32616109843de19409503040cc000010a24492e295a8a0c4a42200f606f231915588ec3cc17c08d82ec0be000010a1e192e4155c9e84992178f2c6c830815089043ae17808f03140ce000010a180b2d715389dc47d2150f586de30d15609003d018f08f03180ca000010a12072cc94f09b84872128f2c6d230b15309203be18209302ec0bc000010a0be82e015589e84922118f186b230915509043c018e094833c0d4000010a05da2da15209ce48c2118f146c230915189083c417609083080b60000109ffa62f115e8a1a4a62228fb471e32115d89583ea18f09003040d20000109f98e2db15649e24962198f146d22ff14c89003ba18309102f40b80000109f37d2d995209c448c2188f606e831215409283de191098033c0e80000109ed532e415a4a0849e21a0f506ec31815809403be18809282d80cc0000109e71a2eb95c0a164a32218f606fe32a165098c40c19909883400cc0000109e0df2eb15a89fc4962198f806f631e160895c3e019109583180d00000109dad52d594ec9b448f2138ef46b82fb14d08f83b617708b02e40ae0000109d4a02e81598a244ae2268f9071032415e89703f819109e83280d20000109ce972d695149c44792090ec46922e814808ac39416c08c82f40b00000109c86f2e715d4a3e4c02320fd471e32c160897c3f419b09803400d40000109c2832c694b89b247d20d0f1c6d6307151890039c17208882d80b40000109bc592df1580a0449b21c0f546e030f15709243ca18309302d80b60000109b6302e615e0a2c4b32268fa070431d15e09703e618808a82e40a60000109b00d2dd15649e648d2160f106da30b15b891c3bc17508d82e80a60000109aa042d014d49a64682078ea068a2e914888dc3b217e09403080c40000109a4022cf14ec9ba47620e8f0c6ce2fa14f88ec3a818109883100c400001099dd32e4157c9fc49f2220fa470c31715809483c417909083300d0000010997b52da95349ce49321a8f486e030b15909683d418909103180c2000010991742e795b4a184a92230fc06fa31915a89283e818d09383080ce00001098b4c2e615d8a124a021b0f406fa31815b89683e218709503300ca000010985202d995489d84892140f3c6d2307156091c3c417d09002d40b400001097ef12e115649f849821d8f7c71032d15f09783ea19309283180de000)))) else (if i < 170 then (if i < 167 then (if i < 166 then 0x10c89322d014fc9ba4882180f586fa31515a89203d818b09283300d2000010c83382ce15009c04802150f146dc30615289183b0180091830c0d8000010c7d032ec95eca3e4b922a0fa871232215a092c3d017b09003000d2000010c76dd2e295aca0649f21a8f546f231815709143d218609383240c2000010c70b92d715309d04812110ef06bc30415109343d018709203240ca000010c6a8d2e815bca3c4c6230901473433716c09cc4121a409d03400d6000010c643f2f395f4a404c122d0fc471c32515f09583e018b09603380d4000010c5e142e415bca284b82290fd06f631715608e43c417b08f82f80c2000010c57ea2e615b0a044a62258fb871431615609303bc18909402fc0ba000010c51c92dd95709e448d2178f306da31515a09203c218209482fc0d0000010c4ba12e01594a0e49b21a0f486ea318160097c3d818509202f00b8000010c45652e59598a164a42208f9870431a15e89643da18709583000c6000010c3f742ca14c499c4782100f006ba2f214a88fc3b417908b82d00b0000010c394a2e6959ca0249c21a0f606f431615b09383de18a09303100c2000010c332a2e1158c9f24a62248f8c6e431e15f89483d418d09483440c2000010c2cec2ed95e0a1c4a12248f706ee31515e09643f819e09f83680da000010c268a2fe1648a544c8232901873833f16a89c841019f09e03400ce000010c20bb2bb14489604541fc8e6466c2e714088ac39a17308802dc0c2000010c1a8a2e515c4a2a4bf2290fd471632416689b44201ab0a0835c0ea000010c144d2f29614a364b02200f3c6e831015709043bc18308c82ec0b4000010c0e472d294e89bc47920d8ed06a82f814d08ec3b417b08d82d40aa000010c08612c194a89a04722110f186c430115109183ba18108f82f80b2000010c02352e09590a1a4a421f8f8870832915e09603f819c09e03480be000010bfc0f2e31598a004a32198f1c6da30514d88f43ae17508f83040b6000010bf5e22e7158ca184a12210f846e230a15289383ce17c09082f40b8000010befd92d995409f04972180f346dc309151890039e18008f02f40c4000010be9b32dd15709de4892190f206e831215809303cc18309483100c0000010be3a82d915149d64832160f2c6cc2fc14a88e43be18509003040ca000010bdd712e515bca424b02278fc472232e16309643d018c09503100b0000010bd7782c414ac99a47320a8edc6aa2ef14d08f03da18b09303000ae000010bd16b2d8955c9f64932170f3c6ce30915409083c0180092031c0c4000010bcb362ea95c0a1a4b22288fb870832416309803f2191095031c0c4000010bc51c2d795649e448d21b8f586e031215889383ce18209103040bc000010bbed92f19614a524bd2280fc070032216309703e619209883140b6000010bb8aa2e91600a3e4b82300fb471631d15e89503ec19009383180d4000010bb29c2d815689d64862118f186ba2f414c88d03a217508e82c40b8000010bac502f41648a5a4ce231100873c33f16b09dc4181a109f83680ce000010ba6582c994d89a64872148f4c6e8313153092c3c6180093031c0cc000010ba03e2dd95589de49721b8f746e630d15489003c618b09883000cc000010b9a192dd95909fa4a221b8f486d22fb14808ec3bc17408982f80b8000010b93be2f61638a644d323b902874c34e16a89b44061a809f03580cc000010b8db72d415209f04a521c8f7c6fe32415c89583c017a09082e80b8000010b87a62dd15409ea4962170f2c6e231315789343ce18509002e40c4000010b81652ea15aca0c4952150f186d02ff15189103cc18208c03100c0000010b7b3e2de154c9e649c2218f846f230e15a89343c417908b82e40b8000010b75222da953c9e04932198f706ee31815889343ee19409703240c0000010b6eef2ef15d8a224ae2268f906fc31d15d89483e819609c03440d2000010b68b72e995a4a0449a2190f546f031115f09543cc18509483440d8000010b62a02de15709da48a21a8f646d830b15309303ce18e09903400d0000010b5c8f2db95489e049421a8f406d6308152894c3d418c09502fc0c8000010b56492ee1624a424c12330fdc724336163897c40a1a409c03380be000010b50332d895589e44932190f506e231915a89443d018a09182fc0ca000010b4a1b2dd95509f04902190f486e0312159895c3e018608e02f40c0000010b44352c194b099a4682058ea46a62fc150091c3ae17508c02f00ba000010b3dfb2f095eca1e4aa2220f8c6f431415f89783f618d095033c0dc000010b37d92e1957ca0c4a32230f6c70832316209944161a209b83480d4000010b31ab2e0956c9fc49e21f0f7c70232715f897c3e818b09282ec0aa000010b2b9a2cf952c9d44882160f286e631115a09283d018a09a83240d6000010b25502f69614a364b922a8fa4724338166898c4041a90a383700d4000010b1f322e315509ec49e21a0f3c6de30e15389303d418d091830c0e0000010b19202d995349ee49a2218f686e231015709083ca199094830c0c0000010b12e22eb15c0a224ad2290fc072633216489343de18a094032c0c0000010b0cb72e1959ca244b02290fc471832616589a43fc19f09803340d0000010b069f2de95609e64922198f186b4305150090c3c817808b02f00c6000 else 0x10e11202ae941495644c1f78e746802de14308b43b017708b82f80be000010e0afe2e2157c9e449221a0f486dc30b15488f83aa16908802c40aa000010e04cc2ea15c0a104af2278fb470232516309683d8188093831c0cc000010dfe792fb1668a6c4cd23590087443461758a244421b10a483740d6000010df8482eb15b4a0e49d2190f206e030c15309143d218a09702ec0b6000010df2482d115109cc4762060eb46862e413f889438c16808582cc0be000010dec1d2e795a8a164b222a0fc871232f16509743f018e092831c0ba000010de5f72e395809e849721a8f4c6ea31615b89643ec191097834c0c2000010ddfd92db151c9b64862118f346d031615c89303b017f08f83180d0000010dd9d02d5154c9e04912198f406e630915b89583d418d09503280cc000010dd3d32d0950c9e248c2118f0c6c830a15308fc3c218309483100d2000010dcd992ed95d8a404ba233901c73033516809ac40a19909b83400c4000010dc7712ea15b8a0a4ab2220f8070031615d09403ec194097032c0c8000010dc1432e715f0a0e4a92218f6870632516509a840219b09483140cc000010dbaf42f315eca364be2260f9c6f631e15789583ec18b09703100b8000010db4e22d6152c9be4852180f446ee31215809343c818108e03000c4000010daec92dc9570a004902118f286d830f15588f83be18d09683380c8000010da8c02d3954c9e248d2198f2c6ec31715a09583ea19a09583080d0000010da29f2e0955c9ea49521b0f1c6dc317158093c3dc188091830c0c0000010d9c672eb1598a0649c2230f7470431c15d89783e218009103240c6000010d963b2ed95e4a3e4c222e8fd470832215889503e019009503000c4000010d90142e61594a024922178f3c6e231a15989303e618a096832c0c2000010d89e42e095749fc49721d8f3c6ce30515489443d619609a83740e4000010d83d32e2155ca0249b2178f5070832115d894c3e018909202f80ce000010d7dbe2dc95389cc47e20b0ee86ae2ec142888c38e15e08602cc0b6000010d779c2e215809e44892138f006dc30e158891c3be17a08c82e00ac000010d71512f395cca1e4b72268fb86f831315a09383b217908c82e40ba000010d6b3b2df156c9f44962178f306d230b15a893c3da188097831c0ca000010d65112df15549e84862150f086d030014b08ec3b418408e83180ce000010d5f132ca94b099a4672020ea06a02ec14a88b839c17508e82fc0ce000010d58de2e31580a0849d21e0f706de30c15689583d218909603140ce000010d52df2d094fc9ba4852128edc6b82f714a89003b617208682c00b0000010d4cc52e1155c9f049c21e8f606f031815e89683ec18e09a030c0c8000010d46932e815d8a204a121f0f706d42ff15388fc3ba17b09202dc0b2000010d40812e115689f24992198f1c6c430014f08d83c218709283200ca000010d3a5f2dd15349e04892150f146e430d15389183d218909483400c8000010d34562d915489e24912198f506e6311154892c3ee19509c03180ca000010d2e1f2e815a4a1249f21d0f446b42f414588bc3ae17408a82c40be000010d28082d615589e24852110f2c6ca30014f08ec3b0181093031c0dc000010d21fd2d715289da49421c8f546e631a15b09543f419309803340e6000010d1bc62e895b0a164a32248fa071032515e09483d018609502f40ac000010d15b42d715489de48b2158f146d430e15189103de18809583300c4000010d0f942e4959ca124ae2258fd470e320162099040219909b03480ba000010d09712e995b4a244ab2230f9c70832115b892c3cc18509083240be000010d03592dd155c9e849621b0f6c6e631515589283be18208f82e80c6000010cfd2a2e395a0a064a42208f7470231915e895c3fc189091832c0ba000010cf7002e495909f449b21b8f786e231115588fc3c418608e82d80b0000010cf0dc2de952c9da48e2130f0c6bc30215509303cc18709303040b0000010ceaa32e795a4a1a4b12250f8c70a328162096840019809c03440c4000010ce4a32ce95189c64842118f046d230215989283c6184092032c0c6000010cde942d7153c9e44952190f406c0306157891c3d0187096832c0c4000010cd8852d215089d84902150f386da30314d890c3b2181096831c0d8000010cd2792dd15809ea49b2168f386dc2ff15289483d618208f82e40b4000010ccc5b2df9580a0048e2188f746fc30f159091c3e218d09a833c0ca000010cc6582d3151c9bc4842120ee06c22fe15388f83ba181095832c0c4000010cc0422e09548a084a62218f686fe31f16289783f818909402e00ba000010cba202e2158c9f64a62240f706ee31915709503de18b09183040c6000010cb3e62f1160ca204b522a0fc872833416b89c441019f09a834c0ca000010cade12dc95789f84922198f306d230915208e43b018409583500da000010ca7ac2e595a8a244a92268fa472633516389a43f418f09783400c4000010ca18b2db95649f24922130f246ba2fe14d09083ca18509203040b4000010c9b6e2df158ca224ae2270fc071a32b16289a03ea18509683340c2000010c954a2e215489ea49621e8f806dc31315a89883f8193095032c0d2000010c8f2a2e415889f849c2248f8c70a32215f09603d6188094033c0ea000) else (if i < 168 then 0x10f980a2c0948c99846f2080ea06962e814408c43b017208b02ec0ac000010f91f72d715249e649721d0f686ee31a162899c4101a209883040c2000010f8bde2da952c9c84832130f106c030614d89183ba17c08a82d00ae000010f85ab2e015589f04972190f3c6d830514f88f03a817408402dc0a8000010f7f882e3159c9f649d21f0f9870a31a15e89703e018c09303000aa000010f79822d415549e048c2140f346d630a14f89243b217608d02f80c0000010f73882ca14e49c247c2128f186dc31115609203d619109683200c2000010f6d6f2e1158ca124ae2258fa871c33316409843ec19d09d033c0d4000010f67542d915309de49421c0f606e631a15f89703f819c09a032c0d4000010f614e2d695289c84882128f0c6c831115709443e819109903300cc000010f5b3a2d795309b047420a8ec06ac2ed14808c03aa16f08402b40a0000010f55152e095589d44872118f146b02f314d08e03b417508b02d80b2000010f4ee62e09594a1a4a22220f746e430b15389083d819109a83540dc000010f49042c5949899a4732100f146ce31215a89903f819209382f40c6000010f42f12d615349e849221d8f4c6e831215589103c417d09103040c2000010f3cc82e915ac9fc49521b8f6c6d62ff14d08e43ae17f090830c0ba000010f369d2e915b4a164b922a8f9470832516609c841a1a109a03440cc000010f307c2e395a4a0449821d0f846d631215809383c818808d831c0c0000010f2a762d6951c9ee48f2128ed46a02f814d88e03be18409482f40bc000010f24452e2958c9ec49921a0f486e630a15389343c418608f82f40c0000010f1e262df95789fe49f21a0f506ec31515989403da186093033c0ca000010f17df2ee95f8a224b72280f886f831815989483e818c09603300d0000010f11d92d0952c9c047f20e0ef86ca30215088ec3ce17608b02ec0ba000010f0b952f7162ca464c322d8fc071031c15b894c3d818d08c02e80c4000010f058b2d495289c647720a0ec869a2e714708c43a417008b82d00b6000010eff652e015549de49321d8f586f431e15b09303cc18409083040c4000010ef91a2f1960ca324bf2290f9870a318158092c3c817f08f82fc0c6000010ef2d42f19618a344b922c8ff071832b16189643d019309503440d4000010eec7d2fa962ca4e4c422d8fd072233416209703f819f0a1834c0d2000010ee6562e615c8a244ac22a8fc470031c15d894c3e017d09283040c8000010ee03e2de95589e44932178f4c6de30415109143d818909482f80c8000010eda142de95a0a0a49c21e8f7c6e031816089683da18109803280dc000010ed4182cf150c9d44872140f146cc30614f08cc38e16708602f00b4000010ecdf72dc95649d647e20e0ed469e2f114988f43a017808c82dc0b6000010ec7dd2d895409f249a2180f446ca30114e89103c418108f02fc0c2000010ec1c22dc1568a0049f21e8f5c6e430f15588dc3ae17809003000bc000010ebb952e11584a044a221c8f586ec31215d09903fe19a09b83440c8000010eb5c22bb946c97645c2020ea869a2f714888c03ba17e08e83040ca000010eaf8b2e515a0a144aa2278fcc72233016289503ee18d09583180c4000010ea9642e295749fa4922190f3c6e631a16009443d0185091831c0bc000010ea33e2dc156ca164a721b8f8070831d15e09343d618009183000b4000010e9d082e615a8a124b12280f946f8321161091c3d418809083200c2000010e97022d495189ea4932160f2c6cc30f157094c3ca17b09583280ba000010e90bc2f11618a524c12328fec72632b16589803e018e09203180c2000010e8ab32ce950c9d248721b8f506d230915008fc3a417d08d02dc0c4000010e84822e495789ea49f21e0f6070632b16209703fa19609303180c6000010e7e632e095809e248f2188f306d830615509103d018d09003000b4000010e78392eb15b8a264a52248fa470c32b163893c3d418209383080cc000010e721b2e3159c9ee49521a0f586d030e15609103b418509103000c6000010e6bef2e515b8a164ac2208f6c6f431215989583de18308f82fc0b2000010e65f42c914d09a84742060eac6922e114a88e43aa17508c03140c0000010e5fe52d89574a004a221b0f486d431315909243c817f09183140ce000010e59dd2d81550a0449221d0f746f231015589043ac17508c030c0c2000010e53d92d515149c24872178f246b630014f090c3c618809383380cc000010e4dc42d815489de4902190f206b62f814908ec3b417508e83080c4000010e47ae2d495509f448f2110f1c6d430f15709183be17f09002e40c0000010e41822e995b0a1c4ab21f0f7c70032015c096840819b09903380be000010e3ba32c1149099c4692068ee46b82f814d08b039c16d08482d80b0000010e357c2e115989f84942180f4c6d430315489443ee18809583200c6000010e2f592e095689dc49121e0f446d830615409143c417f08f830c0b4000010e291f2f19608a3e4b72298fe872e32d16609d84201a409f83640e4000010e23102de9560a0049b2200f686f231f15d095c3ea19309482e80a4000010e1d0b2d215009b447c20f8f006c830214f88d43c417509103100ca000010e16e52de95689fc4a42280fac71832b16109703f419b09a83340d8000 else (if i < 169 then 0x1111eb12f015eca324ba2270fb070a32215e89743e419d09303200ca000011118b52cb94bc99c47220d0f106d030515709143c018408e831c0ca000011112832ec15dca244b622f8fc471232e16989c84121a309f03780d800001110c5f2e09588a104ab2230fa470c32015d09543de18609302f00be000011106502d795209c44862100ef46cc30115208ec3a817408c82e40b4000011100382dc956c9ea4902150f106e031015809283d418809203080c20000110fa262de9584a0e49e2290fa470032015a89543e819509283080b60000110f40f2d715389cc4842140f206ca2ff152891c3e018d095030c0be0000110ee182c994d499c4692078ec46aa2f914e08f03b617b08b82d40ca0000110e7cd2f61614a324b52268fb4716327160095c3fa19a0a003500cc0000110e1cc2d395089c847f20f0ef46b830315589403e019009403280da0000110dbb62db95709ea49b21c8f186c830414c08fc3a817608e82e40aa0000110d5b92cc94f09b047620c8f146d630715889283d417c09003080d20000110cfb92d595409d448e21a8f386d630815509103c418208f83040c60000110c98f2e39598a144a12220f986fe31215a09603f419609e03440c40000110c3942ca14c49b24872158f406cc30315989483e419809983340cc0000110bd762e895cca2c4b12260fdc71832116409743fc18f09603240c20000110b76d2d094c89b046e2000e9867e2dd14088c83b617308902ec0b80000110b1612d795389e048020d0edc6a42f514f88f83a817c09483140c80000110ab0e2fc962ca4e4bd2290f706f831c161897040a19509a034c0ce0000110a4e32e29598a104a721e0f786e631415a89203d818709503080b400001109e9d2f415f8a3c4b822d900c72633316489883f019509283180d0000011098a32cf95149a44732098ee86b22e914588bc39817a08c02d00ba000011092792e21588a024a721f0f946ea31015489443ee19009603440d400001108c5e2e395a8a1c4bc22d8fd873233116509a040818e09883380ce000011086312e89588a064982200f7c70632015509083d418708f03180c2000011080402c394c89b047420c0f006c830815209083d618608f82e00ae000011079ff2ec15bca264ba22e0fe871032515d89703e618509583100b2000011073e12e095809d64852120f586ec30b15b09243c017808f02ec0b200001106dd62d815289cc48b2118eec6b02f914988e439a16f08c03180cc0000110678e2ef15e8a264c02278fb46fc31e15c09a03f019c0a083280c20000110615e2e6159ca244b22258f906f631a15a89183dc18b09302f40be00001105b502d695289f04962208f5c6fc32215e89283c218709203100d0000011055102ec95e8a304ba22a8fb872c32f16289943fe19409483380e000001104f062d515249d048a2110f106b42fd14a88d83ba18309403000ca000011048f12de95409d24942158ef46be30315289083c018009282f00be000011042b82ef15b8a124a621d0f5c70a32a15e89503e218508d02f80d000001103ca62df157c9fc49f21e8f4c6d83151628974400192099032c0be0000110364c2fa9618a504cc2318ff872a32516409703e818c094831c0ce0000110303a2dd9570a0849f2210f746fc31615609343ce18808d83080c400001102a332d814e89c44872108edc6bc2fe15089283ba18509283200b80000110241f2dc95489da49121b0f486da30815309283dc18709403140ce00001101ddf2ee95eca104aa2240fac70432616209903f619b09903140c2000011017df2d395149c04832138f246ca2f414d08f43ae18d09402fc0ba000011011ad2ee95f0a2a4b62288fe073c33716789ac3fe1a309a83540ce00001100ba72d415189e048f2198f186c830c15409203d618408e02e00b2000011005ad2ce94fc9b647d20d8ee06b62f714408fc3da18b09002fc0bc000010fff7a2e815bca024992180f186c230b15989503f018909403180bc000010ff97d2cf94f89ba4802110f1c6ce305156092c3e418a09703380ca000010ff3532e895a49fa49521a0f2c6de30915209403e618809183040b0000010fed332db15349e64882180f146d02fe14e09183cc17e091030c0be000010fe7162e09594a1a4b522a8fa470e323159891c3bc18108f82c80b8000010fe1002e095749f248a2120eec6c830415609603ea19809a03500e4000010fdb022d614f09c247920d8eec6ba2f814b09003be17a08f83200c2000010fd5052cc14cc9b04782088ed46b62f114308b03b417d08f830c0c6000010fced72de957c9e648f2178f446d230715989343f418f09583300d0000010fc8722fd1658a5a4c822d0ff474233416e09a84181a909d032c0ce000010fc28c2c0947897c4551fb0e406682d813e887c38416108482c40a6000010fbc672e015809ec49a21f0f8470231615a091c3b617c08c83180b6000010fb6672ca94e09ba4832120f1c6d831815e89783ee19509403280d0000010fb01b2ef95c8a204af22a0fd471232616389983fa19509903500d8000010faa1a2d7953c9e24882138f4c6e6318155091c3d618e08e83040c6000010fa3f02e695a09f449a21e8f506c42fd15409003d417b08e02f40b8000010f9df42cd94e89ac47820a8edc6b030414a08f03be17b08f02e80b6000 else 0x112a63e2d9153c9ea4812100f146c630015308f43c018108b02dc0b00000112a0422cf94e89a64692098ea06a62fa14c88f83ae17b08c02e80a800001129a382d195149c448420e0ef86c230215509083ce18609183180cc000011294102e415a4a064a72220f746fe31c15b09403bc18008f83300dc00001128df72df158c9f449521f0f746e630f15309103c818108f82fc0ce000011288052c994ac9b447420f0ed86b42f514b88b039c17308b02f40ba000011281f02dc15589f44a22270fbc714323162899441219c09803580e800001127ba62f41620a4a4c0232101074e33e16589a44181a109903200d6000011275ba2c914d899a46920a0ec869a2e714308bc3a016d08b02d40b000001126f8e2e895949e248920f0f286c430214e88ec3b818609583240d40000112694a2e995d8a2c4b622a0fc470e32315c09503e818509503280ce0000112634e2ce94dc9b847d2118ef86ca30b15789683e018e09883200cc00001125d452d294f899c47320d8f086cc30015188f03be186094030c0c2000011257102e7158ca0449f2200f7c6f830b15209143bc18408f02f40b4000011250d32ea158ca0048f2150f686e831015388f03d218709482f80c000001124ac42da15609ea4852140f086ba2f514b08e839e17308b02e00cc000011244a22da95609f24992150f186d630c155892c3dc19109383180c000001123e752e3956c9e849421b0f486e630e15689603e418a09183080c8000011238252f81604a324b922f0fac6f631515389083ba18109002cc0be0000112320a2d895489dc48e2130f346d830615b09343be18508e82e80ba00001122c002d515109c848120e8ecc6b42fe15109243d819109602e80ba000011225cd2e6159ca244b121f8f7c6de31b15a09383da18f09603240ce00001121fc42d515049d44892150f546ca2fc15609143d618109303180d8000011219af2df156c9d848a2148f586da31515a89583d218d09783400d4000011213982dc15749fc4af2290f946e830c15609103b017808c02f00a200001120d9e2cd95009ac4772098ef46b02ff14a89043ca18b09883300ca000011207a72cb15109bc48120e0ef86be30a15409003bc18409283180c8000011201be2ca14c49a646f2090e8868e2e214608e03be17c08b02f40c00000111fb952e215a8a184a72210f746fe312151890c3cc18a08d02d40ae0000111f5982d495289e24932148f286e830f15509243dc185093833c0c60000111ef782dd95349cc4842128f0c6a62ee14c08dc3b217308782dc09c0000111e9442e4156c9f249321d0f806f031a159893c3c618209383380d20000111e30f2ea95c0a2e4aa2248fb471632415d89703fe197098036c0d20000111dce02ea15e0a324b322a8f9c6fc314163097c3f219209a03280b60000111d6cd2d815209d64922120f106bc30614d89083c417e08e03080b60000111d09f2e495989fe4a221c0f9071031d15989283b818008c02e00c00000111ca942d1150c9c647720c0f086cc30815389043c017608f03080da0000111c4972cb14dc9d848d2168f3c6d82fe14a88f03d218209402f80ba0000111be5c2eb15b4a164a52208f80710328164097c3f018d09b83600e40000111b84e2d595349d648520e8f046ae2f714a09043cc19009383140da0000111b2562cc14c89aa47720b8eec6b030814f09043c417e08c02cc0c40000111ac282e315749fa4902170f246d030b15009083bc18008f02ec0ca0000111a6072e0154c9f249f21a0f4c6f031a15689443da190098831c0c000001119fdc2e815dca184ac2290fa070c31a15a89383cc17c08e83100ca000011199ac2e29588a0a4a221f8f7c6e831a15889643d019109603040ba000011193702ee15f4a284b22200f8c6fa31215a89303ce19609903400d600001118d6f2cc14fc9a04692078ec86ac2f114808e03a617608f03000bc000011187402e49584a0649e21a8f786f631a15a09483f219409903480cc000011181052ee15e4a344aa2220fa871e32916109b43f4193096031c0cc00001117adf2e2159ca064a92258f9870030c14f08d43b618308f82e80ba000011174992f01600a2e4bc2260f786f031815f09543ee19709583100d800001116e7e2d915509dc4852138ef86b030215109043c817909103100ca000011168652de9578a104b42298fc070231515909483e819709a83280d40000111621b2f495fca324b322d0fdc72c32515c09683f2197096832c0dc00001115c002df9574a0e4aa2228fa071232a15e89583f218d08e03040b8000011155d82df9584a084a621a0f506de30b154891c3e018909583340c400001114fbe2da154c9e048c2168f1c6c62fb14f08e43c017f09083000c0000011149b12d715449e04872140f006d8312156090c3ca18209103100c2000011143732f215f0a364ba2298f9c70c33216689c840019a09903140c800001113d482e41594a004972208f606fa31915d096c3e019009082fc0ba0000111371e2e695c4a024a321b0f8c70e32115b096c3f8193096031c0ce000011131052df15549f649b21d0f946f831a16109743e818e097031c0de00001112b162c614c49b44862150f246d030315309283d218e09603280ce000011124f42e01570a064a32200f986ec31615a093c3b818609303040c6000))) else (if i < 173 then (if i < 171 then 0x1142dd42e715b4a1a4a821f8f786e0311157092c3d618508e02f40b00000114279e2ed95e4a324b32278fb871c32815989703dc18809283300c40000114216c2ee95d4a284a52218f9c70a32115c89583f619f09b836c0dc00001141b392eb15e0a244b72278fc871a328163099c4001a609b832c0cc000011414f02f615eca204bb232901873e34117189a44001a409b034c0c600001140ef72d495109c048020c0ee06c42fc14b88dc3b817608e03100c4000011408ee2d315389d848a2188f686ea30815509143d218908e82d80bc000011402ce2e315909fc4a42230fb070630e15c09303c418709a83340d60000113fcc12dc15609fa49521a8f386e430915809503cc18008b82f40c00000113f6ce2cb14e49ac47320c8f086d231015289283d419409183100bc0000113f0a02e29590a0c4982158f246cc30215108f03b617f09283000b80000113ea8a2dd95589e64892168f306dc30915089383f219209b03180c80000113e4552e59588a044a22210f9c6fe31115909343c617f09103040c20000113de6a2c5149497846d2090ed06ac2f514a88ec3d018908f83140ce0000113d85f2d615089ca4802120ebc6b62fd15008e43b217e09002fc0b20000113d2502d895409f049421d8f7c70632416689883ee19209603240c00000113cc292df95849f84a42250fa870c32315809343d419109b83300c60000113c6282cf94e09bc47d20e8ee069e2fe14b08b439416f08b02f40be0000113c0022e395cca1a4ad21f0f4c6d6304151891c3b817408d03200d00000113ba082cb14cc9b447920c0ed86a82f714888f43a817008c82ec0cc0000113b3ef2d995509ea48b2198f406dc31415809443da18508e03100c00000113adba2e9159c9ee49821e0f746f831d15e09883de18f094832c0c60000113a7c22d094f49c248b2168f206d631115509183ce18008d83000b20000113a1df2c314a49bc47b20d8ed86c42ff14f88f43be17d08d82f00a600001139bc82dd955c9f649321d8f606fc31e15e89703f419609502e40b40000113958d2e495aca264ad2250fc071a32916789b44061a109f83200c800001138f492ed95e0a3a4be2270f846ee31315b09443c817c08802f00ce000011389302d895409f249e2220f646f031115889283cc18e09683480c6000011382fd2e995949f64972170f506e030b15609083c618408c82e40ca00001137cd62e6958c9fe49b21e8f706f431415989283ce18208b03040c0000011376bf2d915409ea48b2188f506e631815a89283b617c08b02b80b6000011370ba2d495209c64822168f546e62ff14c08b039c16d08802c00b800001136a892e995cca344b522b8fb470832315f095c3f419e09383140c00000113645c2e895b0a084a221a0f606f631415a893c3d218808e03000b800001135e2f2e395849e049621d0f346e231b160096c3ee19709e03600ce0000113580d2e01594a0a4a12240f9870632415c895c3c017d093031c0bc0000113520b2cf152c9d649221a0f186c830515689383e618c095833c0d200001134bd62e895d8a424ae2250f806f231715a894c3c017808a82e80ac0000113459c2eb95949f249b21c0f6c6fe32315809303ec19609a032c0d200001133f8b2db155c9f048e2150f406d630d15589203cc17808b82d80b40000113397b2d294d89be47d2120ef86b42fe15108f03ce18908f82f80b6000011333532e0958ca084a121f0f846ee31f161098440419409683380ca00001132d312de95889f449721a8f506fe31815a89403e818a09783280cc000011326ef2ec9620a4c4c022b8fc070c32015a89403d818c09303080ce000011320a82fb163ca564c9233100c73233016989c440e19b09b03340c600001131a9e2d495149c24872180f686fc32715b09883e419a09903700d2000011314a62cb94e89b847a20c8ed46b42f615008f83b418609483480d400001130e6a2ef15d4a2e4b422d0fa46fc32815c099440419c09e83100c0000011308282e895cca2a4b422a0f9c70031a15b09503d018609103080bc000011302222d115189ca47a20e8f086b630415108f43d217e09483440da0000112fc162dc15549e648a2108f046b02f014988bc3bc18b09082d80ca0000112f5df2e995cca1a49f21b0f5c6f231d15e89503ca17c09083240d80000112efac2e9159ca004a52238fa470831e15d093c3e218e09c832c0c20000112e9842e215aca1c4a32220f806e431815889383e618e09503200cc0000112e3812d014e89ac47c20c8ebc6ba2f814a89183bc17c08602ac0aa0000112dd732d495209ce47e20c8ed46962f3147089039617308f82e40b40000112d7512e115589d047d20d8f0c6cc30214d88dc3b017d09383240cc0000112d1232e995bca064a72230fa070a31d15f897c3ee19009d033c0ce0000112caec2e695bca0c4a12210f7870c32716089603ec19409b83380d80000112c4d32dc15549e64952208f906f831a15f89743fe19e09f836c0d40000112bed32d495489da48c2140f146c230214c88e83a817a08e82f009a0000112b8b12dd95609f849c2190f6c6f631415b89303dc190096831c0d40000112b28f2de95509f249821f0fa070e32115b89543c817b09002f40b80000112ac562e69598a124a92250fb070832616489883e819509883440cc000 else (if i < 172 then 0x115b47d2d014f09b647920d8f086da30514f891c3d018808d83180c40000115ae682e0157c9f64812118efc6ae2fb14d09003b018209182f80b60000115a8202f495d8a1e4ab2218f706f831a15a89203da18609302f80cc0000115a2062df15409d849a2180f246c630c14f88e83d6186096032c0ca00001159be42e0959ca1c4a82250fcc70c32816189703f218c08c830c0c6000011595fc2c2949497845a2008e9868a2e113f88a839a17d08b82c80a400001158fd52e795cca264ab2278f94710329163896c3fc1ad0a103600c2000011589ac2e795c8a2e4b72288f786e231415a89483dc18f09483000c4000011583b12d015009cc47a2068eb46b22f314a88d83a416f08d82e00ac00001157da82d415149c24832190f406e831315e899c41819c09903500d8000011577722f71600a3a4bc22b0fe871833016389903fe1a609b83440d20000115712d2f215eca304b12278fd072032415b09403ca19109b83480d200001156b342c894f09ba47a20c8f086d830e15309283c6182091030c0c40000115650e2e215989fe4a321e0f806fa31815f89703ea18909383080c200001155efc2d815349d448e2180f406da31015709543ee190093031c0d0000011558eb2d895349d848220f0f186e031315809443e818b09283480d4000011553092c2946c98246a20b8ed068c2db144889c39617508982e40b200001154cf82db15349e44952130f246ca30515389243d618409202ec0b2000011546c02ea95e4a084ae2250fcc72231f15989343d218609403200ca0000115408d2e5959c9f049321d8f7c6f431915689243e018d09382fc0c000001153a6b2e2157c9f44952180f486da2ff15108f03ac17c08d02e00b40000115344d2dd1574a024952168f1c6c230415709383ba186091830c0c400001152e372de156ca004a021c8f8c6fe31615b89803ee18b09783040bc000011528362d495349c64852130f006c030415008e43bc176092834c0c4000011521fa2ee95f8a364ba22c0ff072432816409703d617808982f80b400001151bea2d795189d84872178f146b42f214b88d03a817308502b40be000011515bf2e915b4a1c4a22228f8c6f631615e09443e418d09283180a600001150fc52c995009b44892148f3c6d430915b09383f619209f03700e4000011509b02e21564a084a92258f886f231816089503fa19d09683300cc0000115039a2d515049ce47f2180f106b82fd14a09143be17a08e82f40be0000114fd932d5952c9c847b2098ee06b22ee14a08e03a216c08c02d00c40000114f7602e995fca204b42278f886e830d157091c3dc18308f02cc0c00000114f10a2f91650a4a4bb22d0fd072a33216789b041419f09d83340b80000114eaf22dd15349cc48320e0ef86c630615089343ee19c09c03380d40000114e4cc2e29570a044972198f406c22fc14d08f43b217808c02f40c60000114de902e69584a004a92208f886f030d15a094c3de18b09503140c80000114d8822d915689ec49521f0f446e430a15288f03ce18908f02f00a80000114d2632da95189c247a2098ecc6ae2f314d08c439616908782d00b40000114cc482de956c9f649921b0f386ea31a15c09343d018b098030c0b40000114c63a2d895489d448420e8ef86be2fa14b88dc3c017b08e031c0ba0000114c04b2cb14fc9b847a20b8ed86b630014d08bc38a16107e82ac0a60000114ba2a2e115909fa4972198f546da30e158893c3d018809903240d40000114b4212d415149c848020f0f046a22eb14208a838a16708282c80a40000114adf72df95909f249221d8f7470e32215d09103d819509a032c0c80000114a7d32e315a0a0a4a92200f346de30b15408f43ba17e09803340c20000114a1cc2d214f89b648220d0f1c6d62ff14d88d83b418308e030c0c400001149b992eb15d8a244b32270fa071e32416409843f418b09703340d40000114957f2db95709e84862198f606ea31c15d09783ea18909703480d200001148f992c394b09944622038eb068e2f214688d03c417f09182dc09e000011489592eb95b8a324b22278fb8708326159892c3ce18b09002fc0c60000114833e2dd95c09f449921c0f646cc2fe14e88f83b818008d02f80c400001147cfc2f195fca424b42270f9870c32115c09303ce18709483180d8000011476ed2d5155ca0c49921e0f646f831815308f03ce18809483280c8000011471032c814a89824672020ec869e2e7141088838416008182c80ae00001146ae22df158ca184a12210f906fe31d15b09543ee18b09183080c4000011464a82e59598a0e4a62278f9070a31415e89783f419b09703100c400001145e7b2e895989fe4a221f8f746f431c15609403dc18009583240ba000011458732d4951c9d649521d0f4c6da30715188f43d418208e83040ba0000114525f2d7954c9e649321d8f8c6fa325157093c3d017b08903100c000001144c582d4151c9e248d2140f206e431215509003b617f08f03040c40000114466a2ce94d09ac47d2100eec6c230114f892c3dc18a09803100c40000114402a2f21608a2e4b12238f446de30c15288d83a017208b82e00aa00001143a092e495949fc49f2200f406f831d15b094c3e418b09683300c4000011434082cb94d89a247720b8ec469a2f514808c439a17c08b02ec0b8000 else 0x1173bc02e915b4a244af2258fa870431315809703ec18809383240c6000011735872f115fca4e4b62278fbc70e32315b09843fc19009883340c000001172f412f29618a3c4bb22a8fe073433c166898c41019b09c03340ce000011729112e515c0a184a42240fac70432016009583e818b095031c0ce000011723162cc94bc98c47520c0ef46c4304150891c3cc17e08d03000b400001171d022d7154c9e64902188f4c6e231715809203ca19108e03080c0000011716e42dd95649e64882120ef06ca30215289183d818609883080b8000011710bf2e015589e449721f8f686fe31015809243e819009583340cc00001170ab02d495209da4912188f646de30f15a89343c618108f83080b4000011704882e015609e449321a8f3c6e830c15789103e618408f82dc0ae0000116fe5c2e495a4a144ae2260f7c6f031315589243be19109683280c20000116f8322e4159ca164b92290f7c6fc31a15d89843ec19409903280c20000116f2312cd95109c44862150f146aa2f515308e83b8183097033c0dc0000116ebed2f095d8a2a4ab2228f7470a33116189683f21a609a83500dc0000116e5c92e2157c9ec49c21d8f406dc31315409283d018608e02dc0b60000116dfc22d7155c9d84892188f706f0317159094c3d8188098834c0d80000116d99f2e515a0a024a32230fa470832416609703ea19009903280d00000116d3792e115b0a0649f2240fa471231b15c09383c618408f02f80b00000116cd792d395509fa4932198f546d630215289303d018409103200d00000116c75e2de95489fa49821d0f646e431015d09383dc18308c82dc0c40000116c14b2da95689f849921c8f7070431e156095c3d218008e02e00cc0000116bb1b2e615889f449d2230fa46fa31b159894c3f619609a034c0da0000116b5112d315149de49821d0f2c6c6306150890c3ba17608802e80ba0000116aef22e095789d448a2160f486d630a153092c3dc18c09583280c20000116a8f22d294f09c248c2160f506f4318158094c3e8189095832c0d00000116a2dd2d995609ee4922178f306cc30a14f09103ce18109103100c200001169cb52e295849e24902188f4c6da30415289083ba17e08b82c80b60000116968f2db153c9e448f2160f286e430d15488fc3a617408902c00ae0000116909b2d315509e648c2198f286c4305153890c3d0189093031c0c000001168a982ce95149ba47a20f0f446e231015688f43bc17408c82f40ba000011684662ed95e4a1a4ab2288fa070232e16809b44101a009983340cc00001167e562d81574a024ab2218f846f632015f098c3f818c09403240c0000011678272ea15d4a3c4b62268fc072e33416c09c84101a2099034c0d0000011672152d715249d448d21a8f3c6ce30915b89443c818808b82dc0a600001166c102d1950c9dc48f2170f506e431415c89403d818709383080ca000011665e72de9584a0c49c2188f4c6ee31a15e09883fa18d09583100c400001165fbc2e295849ea4942190f346e8308154891c3c818309703280d20000116598f2e515889fe4a02290fa0708329162899441219a099834c0d0000011653702e315b4a0449b21f0f4c6ee31415d09483d418108f02f80bc00001164d762d415189ce48b2168f3c6d02ff14f09103da18a097030c0da000011647342f115e8a184ae2288fa070031715b09603de17e08d02f00b0000011641082e615a0a264b32250fb070432c16609a840019d09c034c0ca00001163aaa2fe9668a5a4bb2288fd872032116489a43fc19e09d03480d80000116349a2dc95289e24912190f1c6dc30615108e83b017d09403440c600001162e742e7158ca064a92250f8470031815a09483e8188092030c0d0000011628642d415209d649921a0f446e630b15609343ca18109702fc0b8000011622402e095889fc4932150f146ce30815089003c818508f82e00a400001161c352d7952c9e848e21a8f406c2306156890c3c618708f02f40da0000116161b2db95349e448e2148f2c6e2313158094c3fe19a09703380c00000116102c2c794bc9b447a20b8ed86a82ef14a08b83ae17007f82a00ae000011609e62ee95c4a2c4bf2318fe871c32515f89703f618f09a831c0c6000011603dd2d595289d84882158f486ee31415c89543e618c094830c0bc0000115fdb62e315809f249a21c0f406e031715289443f418c09382fc0c60000115f79f2d915249ce4802118f286d030815689443f419d09f03400ce0000115f1822da15589d448c2180f406f231c15a09543de19509803240cc0000115eb632df15409f249d21d8f306d2304151090c3c217f08f02fc0d00000115e54f2dd156c9d648d2170f346d430b15709043ce17e08e83040b20000115df212e39588a0049b2210f686ea30515a093c3f018b093832c0c40000115d8fd2e015849f449921e8fa06fa32015709243d218708b82cc0c00000115d2fa2cf151c9d84932198f786de31315909303b817a08c82d40ba0000115ccd02e4959c9fa49621c0f446cc30515088fc3ce181094831c0ce0000115c6982eb15d8a144ad2250f9871032c16209583fa19609983580d00000115c0a32cc14e89b44782098efc6b22f814a08f03cc18309403180ac0000115ba842e415d4a1849921f8f9070831615a09443e819209503380d6000)) else (if i < 174 then 0x118c3352d9955c9ea49721f0f6c6fa31115a89183b217708982ec0c20000118bd082e395609ee49f2170f2c6ce30c15a090c3be17e08e82dc0b20000118b6e92dd15509de4832110f0c6c62ff15209443be18b09603200bc0000118b0d12df95889fe4a82240fa070633016209583e418f091031c0c80000118aabd2da95509e048e20c8ee46a62ee14b08c03c017f08f830c0b40000118a49e2dc95449d04832168f5c6e631915d09643d619009782fc0c200001189e612ed15cca144af2278fac718328161896c3d818209383200dc000011898672ca94ec9c047a20e8ec46a42f914d08d039416d08702f00ae0000118923e2e395c0a224b62238f9070632715e895c3f219309883240c800001188c232e01578a064a621f8f9c70e319161096c3e218e092832c0c6000011885fc2ea159ca124aa2278fd472432b165098c40419b09703340cc00001187fee2e09584a0049c21e0f586ee31b160095c3d818309803480d0000011879f12cf14d09ac47220a8eec6b02f814a889c39616f08782c40a6000011873b42ec95b8a2e4a72228f486d62fd14e88e83b418308c03040c000001186dc82c994a497a4542000e6c67e2dd14008ac38c17308b83040b8000011867a02e415b0a1449c21a0f746f8323161897c40e19709e032c0c6000011861992d295249ca4822150f246ca30815609483d017c09283080be00001185b602f095e8a544cc2300fdc72232816509b03f6198097830c0b8000011855232ed15c8a284ab2298f9470631115809383da18008f82fc0b200001184f062de15549dc4882140f146ce2f914a88c03b618309283200c6000011848d12e515689ee4932158f1c6da30b15389183dc18f09003140c20000118429a2ea15b4a384b622d0fe471e32616309b43fe19809703300dc00001183c5e2ec15bca264ae2240f8c70e323164899c3ee193098031c0c2000011836422dc15489da4912180f306ea30115109083ae17a08c02e40ac0000118303e2d4954c9e44962158f246c830115489143d217f09182ec0c000001182a192de95689ee4892178f646ea30e157890c3c818609402f40be0000118240a2d815409dc49121a0f306da30e15b09503ea19a09903540d000001181ded2df1570a0c4a321a0f446e231315d89603f618b095030c0d0000011817d62d995389ce4782108f246ca30815288e03ac17308802e40c0000011811c42d915189e04932180f1c6c22f614a88c03c618608d82e00b800001180bb32d695009c24812130ee06ae2f514a08f43b617909002f40c80000118059c2d715349ee49921a0f446e030f15909343d018a09302ec0ac0000117ffab2c994f89d448a2170f406e231115389343de18e09803340c00000117f9822df959c9fc49a2168f486da30514c88e43ba17b08e02d80ac0000117f37a2da15549e448e21b0f546ec31515c897c3fc19909503340ce0000117ed472e795b4a144ad2270fb4702323160096c3f419f09c83440ba0000117e7162ea9598a184a92220f6c70431d15d09443ca18208b02ec0b20000117e0f02e415a09fe49721e0f9470232715c898040c19809e833c0d40000117dac62e01598a184a521f8f6c70a31315e09603fa19109082f40d00000117d4a92dc15349e04882158f146b42fb14c08e03ba177091831c0e00000117ceb02cb94ec9b448020c0ee06962e214688bc3a816a08c02d00aa0000117c8852e895bca304b122b8fc471632115f89303c817b09083200ce0000117c27b2d795409d44912188f386d630715309303d618509103180cc0000117bc632db15589f44982170f146ce30415388dc3b417408b82f00a80000117b61d2f21638a404b32278fc871432a15f899840819709f03300d60000117afea2e915e4a324b52270f8c6fe31615689243be18a09402fc0b40000117aa182bb14a099e4592000eb06a42f114d08dc3ba17309303100c60000117a3e52ea15fca344bd22e8fcc72632c16909943f219409683100ca00001179db02e915eca3c4b92288fac6f431815d89743e418309203380d20000117979d2de15149c247820b0ef06b82fe14c88f43a416d08382e80c6000011791762e195649fa49d2178f106e030e15689143ac17609183000b400001178b762d395349c448420c8ed86be2f614b88e03b818009103180ca000011785862c714ac9824702060ec869e2ee146889839817f08f832c0ba00001177f512e7159ca024a821f0f646ec31115889183d418409202e00be000011779062f39600a1e4a62238fe073432e16889783f219a09a83540d0000011772e42e3159ca0c4a421e0f846f031d160096c3f618f09303080b400001176cdf2d81574a084a22210f9070032015b89483d418309082f40b8000011766c12e415c0a1649e21e8f586d631015a895c3e0188091830c0b8000011760922e51588a124ac2248f9470231a15809303c818909b83400cc00001175a582ea15e4a1449f2238fb070e31f15709303e019509a83380d60000117545f2c1948498e46d20b8ed06cc30614f08ec3b218009403040c400001174e312e015449e047f2108f0c6c630015208f03c418b09a03180b60000117482c2d4953c9d048320c8ee46ae2fa14808f03b817d08b82b00a8000011741f12e895b8a064a02200fa46fa31515e09643e6198099035c0d4000 else (if i < 175 then 0x11a49cf2d995289de4802108ef06b22f514a88ec3b017909002f00be000011a43c22d115049c448320b0ef86ae30415389043be18709202f40ca000011a3dcd2c914d09aa46f2078ec86aa2f214808cc3bc18608f83040c2000011a37a72e815aca1a4a221e0f9471032215e09503e4191096031c0b8000011a31ac2cd94d09a446b20b0ebc6902f014988dc3be17a08a82dc0b8000011a2baa2d295489e249021e8f4c6da313154093c3ce18008a82b8098000011a25ad2d294e499e4712050ed069e2f1145889c39216f08a82d80b6000011a1fa02d6151c9be4842108f1c6c230c15489083b017b092830c0b8000011a19542f61614a444b62268f9871031e15e894c3f819409983180c0000011a130a2f51608a404bb22b0fd871c33716609943f019609683240d4000011a0cd62e715d8a104a52208fb070a32416209843fe18c08d02f00a4000011a06b22db9588a084a12208f8470c32116189683f8190096832c0cc000011a00bd2cc94ec9b247a20b0ed86c02fe14b88fc3d618208f03140da0000119faa42d815109cc4912100f0c6c630114e08dc3ba18a09203080d20000119f4622f115e0a204b22238f6c6dc30e15789743dc19209703240d60000119ee3c2e095889de48a2150f4c6e230f14e89003ce18209403240c80000119e82d2d495349d648a20f0f006ce2f814b08ec3ba17808a82dc0aa0000119e1df2f81610a404b922a8fc472432716309883ec18a09503140c80000119dba12e895809ea49c2258f9870031815e89703ec198098830c0c00000119d5c02c494989784642008e746922eb145889839816f08d02dc0b80000119cf6c2f71608a404b42228f646ea30b15609003e018809583200cc0000119c96a2d014c89a847a2110f1c6b82f614a09043c418f09383180ca0000119c3442e2156c9f449421b0f486fc31d15a89443e419309283380be0000119bd5c2c5949c98c46b20b8ed86a42f714708ec3c817708b02fc0e80000119b75b2d015049b64782078ec06942f714b88e03a417108c02f40b60000119b12d2e595c0a224ab2208f8c6fa31915b093c3f619209b03200d60000119ab102dc95689fa4a02248fac70831b15389403cc18808d03000d00000119a4ed2e0959ca124ab2200f586e230e156092c3e219309b03500d000001199ea42f99660a7e4d9240104873e33016289603ec19b09d033c0d6000011998832df9594a0e4ab2240fcc71432716309c440219609b83500e0000011992622e515449de4922168f346d431115909403da193097832c0de00001198c2a2ea95bca124a121e0f886f031b15f097c3f819a09d83780ea000011986282d8952c9ce4892150f346e431415709283d618f094032c0d6000011980362cd14d49a647920c0f086da30f15389043c6188092830c0d6000011979e82f315fca3a4c122c0fe873632815e09543ee19309d83580d4000011973d42d8951c9d448a2168f306bc30215208fc3d018b09202f00c600001196dba2de15a4a004942200f7c706318155891c3e218d09203180c0000011967a82d7952c9ce4892120f186bc2fb15289183c017908f031c0be000011961932d995349dc4922130f0c6ae2fa14a08f43c818a09282f80b000001195b782df15389fa4a121e0f5c6fc32916189583d619009103140d2000011955732d6152c9c44872160f246c430e15288dc3b817409083040c800001194f602d695209ce48d2188f2c6d830f15509243d417c08a82e00be000011949262ef1614a524b92288fd471a32d16909c840a1a409a031c0da000011943422c4149898045a2030eac6b22fa14a88d439816f08102c00c200001193d172e11584a004ac2260fb071232916189943fa19b09903200c4000011936f12dd15649e648e2130f286d431015209103cc18309102f00ba000011930d22e195849f449621f0f686d830e15588e03a016a08883000c800001192ac42d795249da48520d0ef06b42e9144089438616908402c40b2000011924b62d7152c9ec4922148edc6962fd14e08f83c017a08f03280d200001191ed72c1945097c4672050eac6922ec140888439416e08702b40b2000011918c32d8157c9f84962190f3c6da30d15008dc3c417508702e40b80000119129d2e1159ca0249821a0f646f831815d89303c4186093830c0c000001190c882da15889f649521b8f3c6e431015009143d017d09003040ca000011906872d015189e048721a8f446de31d15a896c3ea18e09583040b20000119005a2e9157c9f84942150f206e030914e09103c218409083380d00000118fa082f39618a3c4ce238102074633e16d09d441419d09783240d00000118f43f2b8142094e44b1f80e206502cf137884035415c08282b00a80000118ee1f2e195649e248e2170f086b22f014988c83aa17508f82e40ae0000118e7da2ee15e8a364ac2290fdc73e32e16689683f419409403340c20000118e1bc2e195649f24972178f586dc30c15289083b217708b82e40ba0000118dbb32d394dc9a647220a0ed46a42f614d89043d418e09202e40a60000118d5842e715a0a104a521d0f906fc30e159097c3f019209503000c20000118cf4f2eb15f8a1c4ab2220f706f4310156892c3d419209303240ca0000118c9472d095189ca47b2108f306c830515088f83b817e09502f00be000 else 0x11b07690000000000000000000000031815e094c3ce18e09603340e2000011b016a2d014e49aa47820e0f146d631a157090c3be17a091031c0be000011afb452eb15e4a424bb22a8fbc714329163897840019609683140ca000011af4ff2ef95c8a024a121b8f7c70a31115589083c217a08e82e80b8000011aeedf2e5159ca084a72258fa871a32316109883fe19009d03500d8000011ae8ed2c994f89b44822100ee86aa2f814688ac3a817d08d83200c4000011ae2ea2d795249d048a2170f386de31315f099c3f819109783340e4000011adcc72dc95449e648d20f8ee06b42f314a88c439c16c08c02d00be000011ad6b62d215049c647e20f8ef06aa2f014508b43a016e08202ac0a2000011ad0aa2d215049c247b20d8f0c6c230814e08fc3c418208e02d40bc000011aca912dd15649ee4a221c0f706f230d15b096c3f419f09c03440d2000011ac46f2e395809fc49921b8f4c6d62f8152890c3ce18509303140c6000011abe682d995689e448f2178f206dc30b15109343be18809583300d2000011ab8472e295c4a324a821b0f306e431615c09483f419309403140d6000011ab2282df1574a0049a21b0f706fa31d15889203cc17b09782f80c2000011aabdf2f115c8a124a221d8f7070432315d89403e219909802fc0c2000011aa5bc2e315c8a2e4b52278fb871a32716509803f218e09203040ae000011a9fe12c1145c94e4441f70e2c6582d213d083c37216c085829c0a4000011a99e22cd95209ce4862130f386d630215288e83ae17808e82fc0c0000011a93cb2dd15649f64992190f3c6ce30a15789543e219209883300c4000011a8daa2e6957c9fc49e21d8f546f631a15d89743f619b09883300da000011a878a2e095849ee4902168f406dc314158892c3da18d09803280d6000011a813b2f115eca284bb22c8fe872a33216889ac3fc19909c83200c6000011a7b0a2e795809f24972200f886e631715b89343de18e09603000b0000011a74d32e815bca1e4b32270fb471c31b15c09603fa19e09d83700ea000011a6ea82e495d8a1e4aa2218f846f6316158894c3e8194095830c0be000011a68872e295809f049821d0f1c6d630015108f83b818a09402fc0c2000011a62442ed9630a404c12308ff072231f15b096c3ec191096830c0d0000011a5c352d695409d84932160f106ce2fd15009183b618209103080c2000011a560a2e595909fc4a52230f8470231415989543e818f09c034c0dc000011a4fe52e695cca1a4a32228fb46f431415989603ec18d093032c0d0000))))))))

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



private theorem b166614 : covered 166614 166702 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166702 : covered 166702 166789 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166789 : covered 166789 166877 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166877 : covered 166877 166965 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b166965 : covered 166965 167053 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167053 : covered 167053 167140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167140 : covered 167140 167228 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167228 : covered 167228 167316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167316 : covered 167316 167404 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167404 : covered 167404 167491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167491 : covered 167491 167579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167579 : covered 167579 167667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167667 : covered 167667 167755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167755 : covered 167755 167842 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167842 : covered 167842 167930 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b167930 : covered 167930 168018 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168018 : covered 168018 168106 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168106 : covered 168106 168193 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168193 : covered 168193 168281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168281 : covered 168281 168369 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168369 : covered 168369 168457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168457 : covered 168457 168544 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168544 : covered 168544 168632 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168632 : covered 168632 168719 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168719 : covered 168719 168807 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168807 : covered 168807 168894 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168894 : covered 168894 168982 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b168982 : covered 168982 169070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169070 : covered 169070 169158 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169158 : covered 169158 169245 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169245 : covered 169245 169333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169333 : covered 169333 169421 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169421 : covered 169421 169509 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169509 : covered 169509 169596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169596 : covered 169596 169684 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169684 : covered 169684 169772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169772 : covered 169772 169860 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169860 : covered 169860 169947 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b169947 : covered 169947 170035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170035 : covered 170035 170123 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170123 : covered 170123 170211 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170211 : covered 170211 170298 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170298 : covered 170298 170386 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170386 : covered 170386 170474 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170474 : covered 170474 170562 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170562 : covered 170562 170649 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170649 : covered 170649 170737 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170737 : covered 170737 170825 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170825 : covered 170825 170913 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b170913 : covered 170913 171000 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171000 : covered 171000 171088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171088 : covered 171088 171176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171176 : covered 171176 171264 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171264 : covered 171264 171351 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171351 : covered 171351 171439 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171439 : covered 171439 171527 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171527 : covered 171527 171615 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171615 : covered 171615 171702 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171702 : covered 171702 171790 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171790 : covered 171790 171878 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171878 : covered 171878 171966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b171966 : covered 171966 172053 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172053 : covered 172053 172141 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172141 : covered 172141 172229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172229 : covered 172229 172317 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172317 : covered 172317 172404 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172404 : covered 172404 172492 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172492 : covered 172492 172580 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172580 : covered 172580 172668 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172668 : covered 172668 172755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172755 : covered 172755 172843 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172843 : covered 172843 172931 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b172931 : covered 172931 173019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173019 : covered 173019 173106 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173106 : covered 173106 173194 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173194 : covered 173194 173282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173282 : covered 173282 173370 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173370 : covered 173370 173457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173457 : covered 173457 173545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173545 : covered 173545 173633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173633 : covered 173633 173721 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173721 : covered 173721 173808 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173808 : covered 173808 173896 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173896 : covered 173896 173984 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b173984 : covered 173984 174072 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174072 : covered 174072 174159 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174159 : covered 174159 174247 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174247 : covered 174247 174335 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174335 : covered 174335 174423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174423 : covered 174423 174510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174510 : covered 174510 174598 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174598 : covered 174598 174686 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174686 : covered 174686 174774 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174774 : covered 174774 174861 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174861 : covered 174861 174949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b174949 : covered 174949 175037 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175037 : covered 175037 175125 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175125 : covered 175125 175212 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175212 : covered 175212 175300 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175300 : covered 175300 175388 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175388 : covered 175388 175476 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175476 : covered 175476 175563 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175563 : covered 175563 175651 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175651 : covered 175651 175739 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175739 : covered 175739 175827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175827 : covered 175827 175914 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b175914 : covered 175914 176002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176002 : covered 176002 176090 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176090 : covered 176090 176178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176178 : covered 176178 176265 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176265 : covered 176265 176353 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176353 : covered 176353 176441 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176441 : covered 176441 176529 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176529 : covered 176529 176616 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176616 : covered 176616 176704 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176704 : covered 176704 176792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176792 : covered 176792 176880 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176880 : covered 176880 176967 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b176967 : covered 176967 177055 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177055 : covered 177055 177143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177143 : covered 177143 177231 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177231 : covered 177231 177318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177318 : covered 177318 177406 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177406 : covered 177406 177494 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177494 : covered 177494 177582 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177582 : covered 177582 177669 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177669 : covered 177669 177757 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177757 : covered 177757 177845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177845 : covered 177845 177933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b177933 : covered 177933 178020 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178020 : covered 178020 178108 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178108 : covered 178108 178196 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178196 : covered 178196 178284 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178284 : covered 178284 178371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178371 : covered 178371 178459 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178459 : covered 178459 178547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178547 : covered 178547 178635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178635 : covered 178635 178722 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178722 : covered 178722 178810 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178810 : covered 178810 178898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178898 : covered 178898 178986 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b178986 : covered 178986 179073 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179073 : covered 179073 179161 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179161 : covered 179161 179249 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179249 : covered 179249 179337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179337 : covered 179337 179424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179424 : covered 179424 179512 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179512 : covered 179512 179600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179600 : covered 179600 179688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 166614 179688 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b166614 b166702) (joinCoverage b166789 b166877)) (joinCoverage (joinCoverage b166965 b167053) (joinCoverage b167140 (joinCoverage b167228 b167316)))) (joinCoverage (joinCoverage (joinCoverage b167404 b167491) (joinCoverage b167579 b167667)) (joinCoverage (joinCoverage b167755 b167842) (joinCoverage b167930 (joinCoverage b168018 b168106))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b168193 b168281) (joinCoverage b168369 b168457)) (joinCoverage (joinCoverage b168544 b168632) (joinCoverage b168719 (joinCoverage b168807 b168894)))) (joinCoverage (joinCoverage (joinCoverage b168982 b169070) (joinCoverage b169158 (joinCoverage b169245 b169333))) (joinCoverage (joinCoverage b169421 b169509) (joinCoverage b169596 (joinCoverage b169684 b169772)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b169860 b169947) (joinCoverage b170035 b170123)) (joinCoverage (joinCoverage b170211 b170298) (joinCoverage b170386 (joinCoverage b170474 b170562)))) (joinCoverage (joinCoverage (joinCoverage b170649 b170737) (joinCoverage b170825 b170913)) (joinCoverage (joinCoverage b171000 b171088) (joinCoverage b171176 (joinCoverage b171264 b171351))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b171439 b171527) (joinCoverage b171615 b171702)) (joinCoverage (joinCoverage b171790 b171878) (joinCoverage b171966 (joinCoverage b172053 b172141)))) (joinCoverage (joinCoverage (joinCoverage b172229 b172317) (joinCoverage b172404 (joinCoverage b172492 b172580))) (joinCoverage (joinCoverage b172668 b172755) (joinCoverage b172843 (joinCoverage b172931 b173019))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b173106 b173194) (joinCoverage b173282 b173370)) (joinCoverage (joinCoverage b173457 b173545) (joinCoverage b173633 (joinCoverage b173721 b173808)))) (joinCoverage (joinCoverage (joinCoverage b173896 b173984) (joinCoverage b174072 b174159)) (joinCoverage (joinCoverage b174247 b174335) (joinCoverage b174423 (joinCoverage b174510 b174598))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b174686 b174774) (joinCoverage b174861 b174949)) (joinCoverage (joinCoverage b175037 b175125) (joinCoverage b175212 (joinCoverage b175300 b175388)))) (joinCoverage (joinCoverage (joinCoverage b175476 b175563) (joinCoverage b175651 (joinCoverage b175739 b175827))) (joinCoverage (joinCoverage b175914 b176002) (joinCoverage b176090 (joinCoverage b176178 b176265)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b176353 b176441) (joinCoverage b176529 b176616)) (joinCoverage (joinCoverage b176704 b176792) (joinCoverage b176880 (joinCoverage b176967 b177055)))) (joinCoverage (joinCoverage (joinCoverage b177143 b177231) (joinCoverage b177318 (joinCoverage b177406 b177494))) (joinCoverage (joinCoverage b177582 b177669) (joinCoverage b177757 (joinCoverage b177845 b177933))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b178020 b178108) (joinCoverage b178196 b178284)) (joinCoverage (joinCoverage b178371 b178459) (joinCoverage b178547 (joinCoverage b178635 b178722)))) (joinCoverage (joinCoverage (joinCoverage b178810 b178898) (joinCoverage b178986 (joinCoverage b179073 b179161))) (joinCoverage (joinCoverage b179249 b179337) (joinCoverage b179424 (joinCoverage b179512 b179600))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 166614 ≤ index 320000000/512 := by decide +kernel
private theorem starting_value : fast 320000000=17275206 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 320000000=17275206) (n : ℕ) (low : 320000000≤n) (bound : n≤345000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=320000000
    · rw [first,anchor]
      exact starting_value
    · have past : 320000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤345000000 by omega)
        have within : index n / 512 < 179688 := by omega
        have lower : index 320000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤345000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ320000000To345000000
