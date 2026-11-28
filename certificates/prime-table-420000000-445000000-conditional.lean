import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ420000000To445000000

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




private def radical : ℕ := 0x5e7c67a379b8918faeb9a7970cb240bb0a51753d9f2119e91de10d0f968e30df987d4b5cf4cdb24889be60804d526079ff394ed74e8965b01cb0f5aa5aa7927ae5162a2b4c2b075ad5a76231203ccc28d652e6ab47dc884fb7a05ab633af4020f690a45da90a0415a108053179c61bbdbc6045014b99e0137586064ffeb43f97d3c13568e66fc28dd78bab7cd9b1fef01f451faa4ddfe8b2b63610c6d2bfbe9211e3033ca430ad1e4da152220eac21de00712a963b4fef9edb75108ff48e935dbce0f71a69c01a52cfa783dd2ba3640553f8d347b9b13c9fbb23432177b2fd75ba73669ccc1602d423194009cccd94ac90c524db7c31adbbd70a6f5146ac2cf06170ba61aec734b5eda884df320b5cded9ec3d764da2d8ea303ea1a5c16f880363171df179ad24966f16c7355c2705e67380304172e5f151efe290207179d2c40f330be6662ab7c9b22880d73d79b09b7882f000ca19b9182f32bc441033156d4f48581bdb54bc976bc57df423e191dd6c730a04c2d29d26627313a388bec955142cb1c256bb7c2ee53745cf1f55e3490917e1171f2366f5ca604e8a10d7f16f10df720643a8345b0673f181866d8648a72a0066ac2af5be4a1405a5ab878bc6f25d5142bbc5cfe707f4656936885e6b2c06efed4a516bb5183de0900e74008453fd9b59b633ad1cb4d4436f9ef88a8663d207bc679c648904027b027ad1572843caed1927744498fb5b36598b5a781c1ab21dce9a7afefdd632e2e8ba12a06bcf8998b3eb36eb193b0a1e2fdcdc6acd96d6eb048200e4ffd137adc7a2c184ac18257479fcea84116dafc8e0657e73cc2dd8c97c21e0c4b7352ee81cfa013492e6bf0938ed9eecb72c419af1597a2d664bb7d47d14b517433fcc99abef74cf76311e48dfc64df9d3b7e969d842fe7bc261bdf8036dbc8d736f4e03f13d656a7dc928eaaca120d8006e2027bdb7d9aff33bc4b76324fd8ebef63e945ad42388204fc934f68a14ad33930594d99037906bd26a34deddcee5e8c7d06c25356123dedcf73a30f003fa3e3636bbad820ad89086af0d207f1ed24ac6a20f112bfa9c08b097455e65d63874406bd42def41cf1f7c62b0ebdd35e2d44e733319087d078fd7885b7354feaf3c3129e46319a66153d75cfefba8a815590eb46df9cbe3f7558aa25e8b90e45ce38e099e5ff0ded651ff8ffcc13baa0ae2d47c86ab380eb7252f0d95ad6a84f5571ed4df6f9a69b59d549b1c5d0e800397451d7adcba0463b43661c77f5b47cc1842a89cfd27a633db4aab024daf13cc2b3d35557d094aa242272335cf29cc8603803bd632ad63fdcef44c6ef2b57ca36dc5f1755f64220465c964c5b187e4203ec8fde31a06e7ae6bdac77f9aa8f31547ef1cf2f6712c05c296ba1d48d6bb24c4789fb9747a2be0afe327a5732d8f8da01240687f1e33f7f1aca04b111382e160217b3d3da1dab6c3d1e66e520d8176f5dbe455127a1d267e31c103a470ac9d98eb30f910650b0023ae444e4d9c6e5a0d269db693672005ac95b922064485c88db25fa28c33555fc21f338619760597d188cac0166671ed09f7a6bcccda9022e28f7e7571591778864a04a6a7209a4701b6c4f0a3f5927bd7cd1242aed33bcfd12e7b359320fbf70efab97b22db19ed21684aeb03a9249c01a44e766683cd98fb20a7779f3ba0cd49e10f1ae69e1a85f53cb5f80cea3e6b75003e265f07f5ae0d84c0bd41919f5df5302f1f7c5c901ecbfd8a7bb71c0028d286d5292fd9ab366cf54bb7dfdbc65bd7c34c8bd322ea460511570bca23ea8c541147614523c638bcba863bf9b041bf86dd2951983d21d9d3cafad25ca27acf1bb1228d62aa0e34d24fb5ecb5add7b735b162017b15ed82f73c2838c51b1839e564bee3ff1e82548dfdb81de75bff798e1a47f082b40ee08e760d1278c9ea130fb1692b2b9d9c91ce949482983cf1c6ff13eb8ee005e2fc72e8416d4cb3c3820ff56cb68e87e7d79d1a9fac7c32ec93e2be686be19fef62df2d821e8e1ae9539316dac25b0e80c0c25244db78772255f57df9e14efb57dca05270653f8cf9e50b66f4c0dc9fb5556dc64e447015c01ce6aaa82f8b0c4235a8887e267d9a59b342ca3580cbc8e6f65b36dfdfef0692cda7d96d46b2d455e41260dbe54603fb31fba67f1547572480e2c204bebb8c9aa47503f583c9ac84e31e4ee60fcce6c5504392cdec70b6fed36d91d91c733c45a9500cee3096754867a477f4323c84dec1c284764da86614d7b2d56c663c54621c17e057e52ffb25fbf1f016c92c5c52a3bc366c5d0fa31f3a79a68056ba090b9be9beec09a04919acf71583d50612ee9a55ec1a2f6dfefcfce8b1da46ad8e1367b34d90a1c6f0d9cfd612ca1dc58c1b4f19d5f65d4e71b596f5d510ad48b8027bbb081058cdb4373a7b25cbf746858815136f88164362c481b6b64132836c3091e39976fde1a84ff7e055dfd384ee64b3af369c6cd246123b8d97b55da936a1efbd93d2369ca692582fae87b3b942585dbb14c64b66739e0564972b87a590929b231b576790caf9db3e9d0f31cd7ac5cf533e79f9e4e04e88f5dd41f64ffd620bf626c828515b2c8dda59976d589b297245892c7aa8ec8258c771b5cb8cb5303b1c8cbe39c4e839338f529727593d86d462e5a6391c512db85a94c2df56036f8464c71f50307441b86d072f2930bd6115b1f127def867361b622a2e2949caf736ce89f2ace26cc90f9faba3eb8e7e23950518255a496ee5a124b0bbe3400d1523464b1ed296c8eebee36c15a5c829e34c8930b545ca49f51293c5579b76f318e93fca660a77a7478c79622b76e1a05540e457d05771671b7a0b3e2fe38ff8d23383fdd417fc594d7c96925ba5e5b1133fecedb5001a9f6f1ff60ec17672c26c2b39a102083674acbab0e336bd9993c494a72ff5148c2073369a2f0748cc9d3cbaaa67c269c6c70f5ba3e164c4447a4b625c7d08a00330db492dfaabf2c6057945b382fbb4ebb7160396d815bb88ce8b39c148cd169d7cc2063da4144a2209e69694cdd7ebd049a6636261dcc210f3d834b2431c7daadd7e32dedd681f0c820480fb3f0c33b61f8996511f4a66ac989ac00c808d1d819db4f8d4501eccc91d6b3aad80c68fb25cffadfea916aacc03e740602fac9725566866439818a7cd037a86a268683ab912a8a0f67e7ba268f58b6fa50ed7059d5736777602052cc31ac5bc5d6047b1914848295069fc050af06df9748faca6a04ab6e63e07fcf1bd7eb59d5e542d9dd3013e20fa5ae7980744fb2b6a94c213b16e787ce0a4d782f0ec882615543f7c0f844e44bf16337f12622925c138d090ed03393d97e75e2ef7070b9c9640096e6a82d8c7bb8749813b6f8352595e570b7f54d9291eda3a1b5d84d6e4473b9b6c2a57cbf7543a21c7f693414db995b882df19161b8b9ebbbdc7e562b5f71dd51b761956287208fadf6603ab9c1ac7c5a6f683ef92c499796e154f292a488c7c8775a54ac8c2fe902c9f0b680892f3ea04b397741a8c33cfd4aea3af568f0450e00d4fc78c9f05688dfd3755fb2a21c5f2ac81c13e6018511bef8ff777164c729d2e3cd4fb3ce0fd9c3a5c4cdd61f65107272bfd48adc2ebde9949a6a521314e8c9e3baf6eb5007348a48ba0835957ccd48968dea84047a3fc5fbb3eb3531925ebbce20203262da48ef5c9494d2255737052e338fe78f864e871e8050e0e4d94dac57d120db7a4baea3c971c8239ee74f42c4b0c3645ff107ddd60205d280576ef34edffa8468782fb779f89b1e4a116eb40b5fb97bde19ee4e1f4b9570fc7d464b31e9bb149e40b8127a077e64f7035dcb9f77c00773db3103a589de74c70c4d0ac0019d6baf5d2cc7246f9a716b0cd9ad90eabbe85cffb6edae09880542c99b926e9618eab4ab8bf97e0a1a28e7bb1ba23918e85ee4062eefe8703c621b958848cf84c14ad51926798f67e0b4d60e4a88e7911732b8db75f5c53c9017aec779a1eb22cd2713fe706a17d3ff53d509c71a665b6045f6f2b55372d133929485b0140a0dacf047857c3f7cdebd2c68b124ba741e844ad727ca7447856fc91f6af79583d2b79d0a0177c39a76682177435ef6fef62cbd48b7aa51b746b0a94ae8dfb6d612903dc3f2331fc4eed98428291c5b99a0dc570bb60bb73340e2619908316a14b28d8799e9ca8c05f4425999e65a281b149a9cc8a468062002ee3f62c4a9354ada5198c7863f13c0df5dbd42d76e70e95c5dbacfefe710802af96012db3e213e02e60daa60e62ededa12f70411d8a5e1eed34bf72d10a54c44aebac53d5b3d990b0fd5a0e7a614e4f8691f09c780de0576e35b5938c506f110675df00cb1bbf02a1eebc2a3f771efe800900aaf244739e690b827f4d4b6090ced78ff78bcdd2ec3fc06b3f5e4c47a5ef8f9de6792033c2f7277c3e4ab06f77dd3e8e2ad2e75443f4b7a9acd0ea4df8a80716c58805f0115cac1765521fd527a87034f48493cff53e6b058ee5e0c04dc1f01e3ac06d29c2bca59476483cd8960d5ec4aa1ed67018404b23c9549d61718b0385d49d010eb2bd66e205f7f50d79cc4af4996bcb14f240847c91a1a0c674b36fe86499fa659beacb2615ffe863021f1dda3c91d90438eef62a89c85c9adc3cc249856179374387a541af18c9ad5756c3c36914eb9bcc41d298d2729585c9c98a9f1a1b35b464cea260313d03b4c91c382bee75171d25242340a3703661350e612197a43452ae695c23b97caf4152099486f2985d11c069b991e9993cd147479f7b67854bbfad4cf29ffecbd80121bff1075b92698f05ebc0994efec1272ee25b8eeb7f501ac5f11779898a100435558d50408f51c763421e33e12cedcd3d819b706fed078ae61acbf75002b56ce2d5a81d99864a98326e60e8f428e12278516fdfacc781631896b6bff73745d208d796559badd4e001229ba8b6c0deca6ee1b8ac80595935114ea3827821c1109f58fc912d498dafff557d36ede59b7473b2e08e370e248a5c947d15c2bb8ee2e7469184405eea3638c4a97c95ab5795a9bb32088eff4c1c096ee1b93e351b8165e5afc6a4ff55f2718a72267dfd09c08d3fa155e97a8f61d5fa233273c45201bcafcfdf2324e7c524db20386e5d37a523f1fa559356f3bac56b3f26f74f5d5880cc54aea4dd66a25d8d1d341361773e740fecbe6845337a26e4f89eb88b6f76f17e2924f9d1b925f74e9c936fd35b31740e3f2c8ea05a9b31603102b2ef79ea210fdbaecce74fe61aaaf8f54360e1754f9ceb3bcc6357e60318470c6c303d205d7eaa51004dcbad0798b6

private def light (n : ℕ) : Bool :=
  if n≤145 then decide n.Prime else n.gcd 804792605747199194484902925779806277109997439007500616344745281047115412373646521410850481879839649227439298230298915019813108221651663659572441609408556917739149315905992811411866635786075524601835815642793302504243200000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤21095) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 145 = 804792605747199194484902925779806277109997439007500616344745281047115412373646521410850481879839649227439298230298915019813108221651663659572441609408556917739149315905992811411866635786075524601835815642793302504243200000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 145 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤21095 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 41 := by unfold smallValid; decide +kernel

private theorem sp41 : smallValid 41 41 := by unfold smallValid; decide +kernel

private theorem sp82 : smallValid 82 41 := by unfold smallValid; decide +kernel

private theorem sp123 : smallValid 123 41 := by unfold smallValid; decide +kernel

private theorem sp164 : smallValid 164 41 := by unfold smallValid; decide +kernel

private theorem sp205 : smallValid 205 41 := by unfold smallValid; decide +kernel

private theorem sp246 : smallValid 246 41 := by unfold smallValid; decide +kernel

private theorem sp287 : smallValid 287 42 := by unfold smallValid; decide +kernel

private theorem sp329 : smallValid 329 41 := by unfold smallValid; decide +kernel

private theorem sp370 : smallValid 370 41 := by unfold smallValid; decide +kernel

private theorem sp411 : smallValid 411 41 := by unfold smallValid; decide +kernel

private theorem sp452 : smallValid 452 42 := by unfold smallValid; decide +kernel

private theorem sp494 : smallValid 494 41 := by unfold smallValid; decide +kernel

private theorem sp535 : smallValid 535 41 := by unfold smallValid; decide +kernel

private theorem sp576 : smallValid 576 41 := by unfold smallValid; decide +kernel

private theorem sp617 : smallValid 617 42 := by unfold smallValid; decide +kernel

private theorem sp659 : smallValid 659 41 := by unfold smallValid; decide +kernel

private theorem sp700 : smallValid 700 41 := by unfold smallValid; decide +kernel

private theorem sp741 : smallValid 741 41 := by unfold smallValid; decide +kernel

private theorem sp782 : smallValid 782 41 := by unfold smallValid; decide +kernel

private theorem sp823 : smallValid 823 41 := by unfold smallValid; decide +kernel

private theorem sp864 : smallValid 864 41 := by unfold smallValid; decide +kernel

private theorem sp905 : smallValid 905 41 := by unfold smallValid; decide +kernel

private theorem sp946 : smallValid 946 42 := by unfold smallValid; decide +kernel

private theorem sp988 : smallValid 988 41 := by unfold smallValid; decide +kernel

private theorem sp1029 : smallValid 1029 41 := by unfold smallValid; decide +kernel

private theorem sp1070 : smallValid 1070 41 := by unfold smallValid; decide +kernel

private theorem sp1111 : smallValid 1111 42 := by unfold smallValid; decide +kernel

private theorem sp1153 : smallValid 1153 41 := by unfold smallValid; decide +kernel

private theorem sp1194 : smallValid 1194 41 := by unfold smallValid; decide +kernel

private theorem sp1235 : smallValid 1235 41 := by unfold smallValid; decide +kernel

private theorem sp1276 : smallValid 1276 42 := by unfold smallValid; decide +kernel

private theorem sp1318 : smallValid 1318 41 := by unfold smallValid; decide +kernel

private theorem sp1359 : smallValid 1359 41 := by unfold smallValid; decide +kernel

private theorem sp1400 : smallValid 1400 41 := by unfold smallValid; decide +kernel

private theorem sp1441 : smallValid 1441 41 := by unfold smallValid; decide +kernel

private theorem sp1482 : smallValid 1482 41 := by unfold smallValid; decide +kernel

private theorem sp1523 : smallValid 1523 41 := by unfold smallValid; decide +kernel

private theorem sp1564 : smallValid 1564 41 := by unfold smallValid; decide +kernel

private theorem sp1605 : smallValid 1605 42 := by unfold smallValid; decide +kernel

private theorem sp1647 : smallValid 1647 41 := by unfold smallValid; decide +kernel

private theorem sp1688 : smallValid 1688 41 := by unfold smallValid; decide +kernel

private theorem sp1729 : smallValid 1729 41 := by unfold smallValid; decide +kernel

private theorem sp1770 : smallValid 1770 42 := by unfold smallValid; decide +kernel

private theorem sp1812 : smallValid 1812 41 := by unfold smallValid; decide +kernel

private theorem sp1853 : smallValid 1853 41 := by unfold smallValid; decide +kernel

private theorem sp1894 : smallValid 1894 41 := by unfold smallValid; decide +kernel

private theorem sp1935 : smallValid 1935 42 := by unfold smallValid; decide +kernel

private theorem sp1977 : smallValid 1977 41 := by unfold smallValid; decide +kernel

private theorem sp2018 : smallValid 2018 41 := by unfold smallValid; decide +kernel

private theorem sp2059 : smallValid 2059 41 := by unfold smallValid; decide +kernel

private theorem sp2100 : smallValid 2100 42 := by unfold smallValid; decide +kernel

private theorem sp2142 : smallValid 2142 41 := by unfold smallValid; decide +kernel

private theorem sp2183 : smallValid 2183 41 := by unfold smallValid; decide +kernel

private theorem sp2224 : smallValid 2224 41 := by unfold smallValid; decide +kernel

private theorem sp2265 : smallValid 2265 42 := by unfold smallValid; decide +kernel

private theorem sp2307 : smallValid 2307 41 := by unfold smallValid; decide +kernel

private theorem sp2348 : smallValid 2348 41 := by unfold smallValid; decide +kernel

private theorem sp2389 : smallValid 2389 41 := by unfold smallValid; decide +kernel

private theorem sp2430 : smallValid 2430 42 := by unfold smallValid; decide +kernel

private theorem sp2472 : smallValid 2472 41 := by unfold smallValid; decide +kernel

private theorem sp2513 : smallValid 2513 41 := by unfold smallValid; decide +kernel

private theorem sp2554 : smallValid 2554 41 := by unfold smallValid; decide +kernel

private theorem sp2595 : smallValid 2595 42 := by unfold smallValid; decide +kernel

private theorem sp2637 : smallValid 2637 41 := by unfold smallValid; decide +kernel

private theorem sp2678 : smallValid 2678 41 := by unfold smallValid; decide +kernel

private theorem sp2719 : smallValid 2719 41 := by unfold smallValid; decide +kernel

private theorem sp2760 : smallValid 2760 41 := by unfold smallValid; decide +kernel

private theorem sp2801 : smallValid 2801 41 := by unfold smallValid; decide +kernel

private theorem sp2842 : smallValid 2842 41 := by unfold smallValid; decide +kernel

private theorem sp2883 : smallValid 2883 41 := by unfold smallValid; decide +kernel

private theorem sp2924 : smallValid 2924 42 := by unfold smallValid; decide +kernel

private theorem sp2966 : smallValid 2966 41 := by unfold smallValid; decide +kernel

private theorem sp3007 : smallValid 3007 41 := by unfold smallValid; decide +kernel

private theorem sp3048 : smallValid 3048 41 := by unfold smallValid; decide +kernel

private theorem sp3089 : smallValid 3089 42 := by unfold smallValid; decide +kernel

private theorem sp3131 : smallValid 3131 41 := by unfold smallValid; decide +kernel

private theorem sp3172 : smallValid 3172 41 := by unfold smallValid; decide +kernel

private theorem sp3213 : smallValid 3213 41 := by unfold smallValid; decide +kernel

private theorem sp3254 : smallValid 3254 42 := by unfold smallValid; decide +kernel

private theorem sp3296 : smallValid 3296 41 := by unfold smallValid; decide +kernel

private theorem sp3337 : smallValid 3337 41 := by unfold smallValid; decide +kernel

private theorem sp3378 : smallValid 3378 41 := by unfold smallValid; decide +kernel

private theorem sp3419 : smallValid 3419 41 := by unfold smallValid; decide +kernel

private theorem sp3460 : smallValid 3460 41 := by unfold smallValid; decide +kernel

private theorem sp3501 : smallValid 3501 41 := by unfold smallValid; decide +kernel

private theorem sp3542 : smallValid 3542 41 := by unfold smallValid; decide +kernel

private theorem sp3583 : smallValid 3583 42 := by unfold smallValid; decide +kernel

private theorem sp3625 : smallValid 3625 41 := by unfold smallValid; decide +kernel

private theorem sp3666 : smallValid 3666 41 := by unfold smallValid; decide +kernel

private theorem sp3707 : smallValid 3707 41 := by unfold smallValid; decide +kernel

private theorem sp3748 : smallValid 3748 42 := by unfold smallValid; decide +kernel

private theorem sp3790 : smallValid 3790 41 := by unfold smallValid; decide +kernel

private theorem sp3831 : smallValid 3831 41 := by unfold smallValid; decide +kernel

private theorem sp3872 : smallValid 3872 41 := by unfold smallValid; decide +kernel

private theorem sp3913 : smallValid 3913 42 := by unfold smallValid; decide +kernel

private theorem sp3955 : smallValid 3955 41 := by unfold smallValid; decide +kernel

private theorem sp3996 : smallValid 3996 41 := by unfold smallValid; decide +kernel

private theorem sp4037 : smallValid 4037 41 := by unfold smallValid; decide +kernel

private theorem sp4078 : smallValid 4078 41 := by unfold smallValid; decide +kernel

private theorem sp4119 : smallValid 4119 41 := by unfold smallValid; decide +kernel

private theorem sp4160 : smallValid 4160 41 := by unfold smallValid; decide +kernel

private theorem sp4201 : smallValid 4201 41 := by unfold smallValid; decide +kernel

private theorem sp4242 : smallValid 4242 42 := by unfold smallValid; decide +kernel

private theorem sp4284 : smallValid 4284 41 := by unfold smallValid; decide +kernel

private theorem sp4325 : smallValid 4325 41 := by unfold smallValid; decide +kernel

private theorem sp4366 : smallValid 4366 41 := by unfold smallValid; decide +kernel

private theorem sp4407 : smallValid 4407 42 := by unfold smallValid; decide +kernel

private theorem sp4449 : smallValid 4449 41 := by unfold smallValid; decide +kernel

private theorem sp4490 : smallValid 4490 41 := by unfold smallValid; decide +kernel

private theorem sp4531 : smallValid 4531 41 := by unfold smallValid; decide +kernel

private theorem sp4572 : smallValid 4572 42 := by unfold smallValid; decide +kernel

private theorem sp4614 : smallValid 4614 41 := by unfold smallValid; decide +kernel

private theorem sp4655 : smallValid 4655 41 := by unfold smallValid; decide +kernel

private theorem sp4696 : smallValid 4696 41 := by unfold smallValid; decide +kernel

private theorem sp4737 : smallValid 4737 42 := by unfold smallValid; decide +kernel

private theorem sp4779 : smallValid 4779 41 := by unfold smallValid; decide +kernel

private theorem sp4820 : smallValid 4820 41 := by unfold smallValid; decide +kernel

private theorem sp4861 : smallValid 4861 41 := by unfold smallValid; decide +kernel

private theorem sp4902 : smallValid 4902 42 := by unfold smallValid; decide +kernel

private theorem sp4944 : smallValid 4944 41 := by unfold smallValid; decide +kernel

private theorem sp4985 : smallValid 4985 41 := by unfold smallValid; decide +kernel

private theorem sp5026 : smallValid 5026 41 := by unfold smallValid; decide +kernel

private theorem sp5067 : smallValid 5067 42 := by unfold smallValid; decide +kernel

private theorem sp5109 : smallValid 5109 41 := by unfold smallValid; decide +kernel

private theorem sp5150 : smallValid 5150 41 := by unfold smallValid; decide +kernel

private theorem sp5191 : smallValid 5191 41 := by unfold smallValid; decide +kernel

private theorem sp5232 : smallValid 5232 42 := by unfold smallValid; decide +kernel

private theorem sp5274 : smallValid 5274 41 := by unfold smallValid; decide +kernel

private theorem sp5315 : smallValid 5315 41 := by unfold smallValid; decide +kernel

private theorem sp5356 : smallValid 5356 41 := by unfold smallValid; decide +kernel

private theorem sp5397 : smallValid 5397 41 := by unfold smallValid; decide +kernel

private theorem sp5438 : smallValid 5438 41 := by unfold smallValid; decide +kernel

private theorem sp5479 : smallValid 5479 41 := by unfold smallValid; decide +kernel

private theorem sp5520 : smallValid 5520 41 := by unfold smallValid; decide +kernel

private theorem sp5561 : smallValid 5561 42 := by unfold smallValid; decide +kernel

private theorem sp5603 : smallValid 5603 41 := by unfold smallValid; decide +kernel

private theorem sp5644 : smallValid 5644 41 := by unfold smallValid; decide +kernel

private theorem sp5685 : smallValid 5685 41 := by unfold smallValid; decide +kernel

private theorem sp5726 : smallValid 5726 42 := by unfold smallValid; decide +kernel

private theorem sp5768 : smallValid 5768 41 := by unfold smallValid; decide +kernel

private theorem sp5809 : smallValid 5809 41 := by unfold smallValid; decide +kernel

private theorem sp5850 : smallValid 5850 41 := by unfold smallValid; decide +kernel

private theorem sp5891 : smallValid 5891 42 := by unfold smallValid; decide +kernel

private theorem sp5933 : smallValid 5933 41 := by unfold smallValid; decide +kernel

private theorem sp5974 : smallValid 5974 41 := by unfold smallValid; decide +kernel

private theorem sp6015 : smallValid 6015 41 := by unfold smallValid; decide +kernel

private theorem sp6056 : smallValid 6056 41 := by unfold smallValid; decide +kernel

private theorem sp6097 : smallValid 6097 41 := by unfold smallValid; decide +kernel

private theorem sp6138 : smallValid 6138 41 := by unfold smallValid; decide +kernel

private theorem sp6179 : smallValid 6179 41 := by unfold smallValid; decide +kernel

private theorem sp6220 : smallValid 6220 42 := by unfold smallValid; decide +kernel

private theorem sp6262 : smallValid 6262 41 := by unfold smallValid; decide +kernel

private theorem sp6303 : smallValid 6303 41 := by unfold smallValid; decide +kernel

private theorem sp6344 : smallValid 6344 41 := by unfold smallValid; decide +kernel

private theorem sp6385 : smallValid 6385 42 := by unfold smallValid; decide +kernel

private theorem sp6427 : smallValid 6427 41 := by unfold smallValid; decide +kernel

private theorem sp6468 : smallValid 6468 41 := by unfold smallValid; decide +kernel

private theorem sp6509 : smallValid 6509 41 := by unfold smallValid; decide +kernel

private theorem sp6550 : smallValid 6550 42 := by unfold smallValid; decide +kernel

private theorem sp6592 : smallValid 6592 41 := by unfold smallValid; decide +kernel

private theorem sp6633 : smallValid 6633 41 := by unfold smallValid; decide +kernel

private theorem sp6674 : smallValid 6674 41 := by unfold smallValid; decide +kernel

private theorem sp6715 : smallValid 6715 41 := by unfold smallValid; decide +kernel

private theorem sp6756 : smallValid 6756 41 := by unfold smallValid; decide +kernel

private theorem sp6797 : smallValid 6797 41 := by unfold smallValid; decide +kernel

private theorem sp6838 : smallValid 6838 41 := by unfold smallValid; decide +kernel

private theorem sp6879 : smallValid 6879 42 := by unfold smallValid; decide +kernel

private theorem sp6921 : smallValid 6921 41 := by unfold smallValid; decide +kernel

private theorem sp6962 : smallValid 6962 41 := by unfold smallValid; decide +kernel

private theorem sp7003 : smallValid 7003 41 := by unfold smallValid; decide +kernel

private theorem sp7044 : smallValid 7044 42 := by unfold smallValid; decide +kernel

private theorem sp7086 : smallValid 7086 41 := by unfold smallValid; decide +kernel

private theorem sp7127 : smallValid 7127 41 := by unfold smallValid; decide +kernel

private theorem sp7168 : smallValid 7168 41 := by unfold smallValid; decide +kernel

private theorem sp7209 : smallValid 7209 42 := by unfold smallValid; decide +kernel

private theorem sp7251 : smallValid 7251 41 := by unfold smallValid; decide +kernel

private theorem sp7292 : smallValid 7292 41 := by unfold smallValid; decide +kernel

private theorem sp7333 : smallValid 7333 41 := by unfold smallValid; decide +kernel

private theorem sp7374 : smallValid 7374 42 := by unfold smallValid; decide +kernel

private theorem sp7416 : smallValid 7416 41 := by unfold smallValid; decide +kernel

private theorem sp7457 : smallValid 7457 41 := by unfold smallValid; decide +kernel

private theorem sp7498 : smallValid 7498 41 := by unfold smallValid; decide +kernel

private theorem sp7539 : smallValid 7539 42 := by unfold smallValid; decide +kernel

private theorem sp7581 : smallValid 7581 41 := by unfold smallValid; decide +kernel

private theorem sp7622 : smallValid 7622 41 := by unfold smallValid; decide +kernel

private theorem sp7663 : smallValid 7663 41 := by unfold smallValid; decide +kernel

private theorem sp7704 : smallValid 7704 42 := by unfold smallValid; decide +kernel

private theorem sp7746 : smallValid 7746 41 := by unfold smallValid; decide +kernel

private theorem sp7787 : smallValid 7787 41 := by unfold smallValid; decide +kernel

private theorem sp7828 : smallValid 7828 41 := by unfold smallValid; decide +kernel

private theorem sp7869 : smallValid 7869 42 := by unfold smallValid; decide +kernel

private theorem sp7911 : smallValid 7911 41 := by unfold smallValid; decide +kernel

private theorem sp7952 : smallValid 7952 41 := by unfold smallValid; decide +kernel

private theorem sp7993 : smallValid 7993 41 := by unfold smallValid; decide +kernel

private theorem sp8034 : smallValid 8034 41 := by unfold smallValid; decide +kernel

private theorem sp8075 : smallValid 8075 41 := by unfold smallValid; decide +kernel

private theorem sp8116 : smallValid 8116 41 := by unfold smallValid; decide +kernel

private theorem sp8157 : smallValid 8157 41 := by unfold smallValid; decide +kernel

private theorem sp8198 : smallValid 8198 42 := by unfold smallValid; decide +kernel

private theorem sp8240 : smallValid 8240 41 := by unfold smallValid; decide +kernel

private theorem sp8281 : smallValid 8281 41 := by unfold smallValid; decide +kernel

private theorem sp8322 : smallValid 8322 41 := by unfold smallValid; decide +kernel

private theorem sp8363 : smallValid 8363 42 := by unfold smallValid; decide +kernel

private theorem sp8405 : smallValid 8405 41 := by unfold smallValid; decide +kernel

private theorem sp8446 : smallValid 8446 41 := by unfold smallValid; decide +kernel

private theorem sp8487 : smallValid 8487 41 := by unfold smallValid; decide +kernel

private theorem sp8528 : smallValid 8528 42 := by unfold smallValid; decide +kernel

private theorem sp8570 : smallValid 8570 41 := by unfold smallValid; decide +kernel

private theorem sp8611 : smallValid 8611 41 := by unfold smallValid; decide +kernel

private theorem sp8652 : smallValid 8652 41 := by unfold smallValid; decide +kernel

private theorem sp8693 : smallValid 8693 41 := by unfold smallValid; decide +kernel

private theorem sp8734 : smallValid 8734 41 := by unfold smallValid; decide +kernel

private theorem sp8775 : smallValid 8775 41 := by unfold smallValid; decide +kernel

private theorem sp8816 : smallValid 8816 41 := by unfold smallValid; decide +kernel

private theorem sp8857 : smallValid 8857 42 := by unfold smallValid; decide +kernel

private theorem sp8899 : smallValid 8899 41 := by unfold smallValid; decide +kernel

private theorem sp8940 : smallValid 8940 41 := by unfold smallValid; decide +kernel

private theorem sp8981 : smallValid 8981 41 := by unfold smallValid; decide +kernel

private theorem sp9022 : smallValid 9022 42 := by unfold smallValid; decide +kernel

private theorem sp9064 : smallValid 9064 41 := by unfold smallValid; decide +kernel

private theorem sp9105 : smallValid 9105 41 := by unfold smallValid; decide +kernel

private theorem sp9146 : smallValid 9146 41 := by unfold smallValid; decide +kernel

private theorem sp9187 : smallValid 9187 42 := by unfold smallValid; decide +kernel

private theorem sp9229 : smallValid 9229 41 := by unfold smallValid; decide +kernel

private theorem sp9270 : smallValid 9270 41 := by unfold smallValid; decide +kernel

private theorem sp9311 : smallValid 9311 41 := by unfold smallValid; decide +kernel

private theorem sp9352 : smallValid 9352 41 := by unfold smallValid; decide +kernel

private theorem sp9393 : smallValid 9393 41 := by unfold smallValid; decide +kernel

private theorem sp9434 : smallValid 9434 41 := by unfold smallValid; decide +kernel

private theorem sp9475 : smallValid 9475 41 := by unfold smallValid; decide +kernel

private theorem sp9516 : smallValid 9516 42 := by unfold smallValid; decide +kernel

private theorem sp9558 : smallValid 9558 41 := by unfold smallValid; decide +kernel

private theorem sp9599 : smallValid 9599 41 := by unfold smallValid; decide +kernel

private theorem sp9640 : smallValid 9640 41 := by unfold smallValid; decide +kernel

private theorem sp9681 : smallValid 9681 42 := by unfold smallValid; decide +kernel

private theorem sp9723 : smallValid 9723 41 := by unfold smallValid; decide +kernel

private theorem sp9764 : smallValid 9764 41 := by unfold smallValid; decide +kernel

private theorem sp9805 : smallValid 9805 41 := by unfold smallValid; decide +kernel

private theorem sp9846 : smallValid 9846 42 := by unfold smallValid; decide +kernel

private theorem sp9888 : smallValid 9888 41 := by unfold smallValid; decide +kernel

private theorem sp9929 : smallValid 9929 41 := by unfold smallValid; decide +kernel

private theorem sp9970 : smallValid 9970 41 := by unfold smallValid; decide +kernel

private theorem sp10011 : smallValid 10011 42 := by unfold smallValid; decide +kernel

private theorem sp10053 : smallValid 10053 41 := by unfold smallValid; decide +kernel

private theorem sp10094 : smallValid 10094 41 := by unfold smallValid; decide +kernel

private theorem sp10135 : smallValid 10135 41 := by unfold smallValid; decide +kernel

private theorem sp10176 : smallValid 10176 42 := by unfold smallValid; decide +kernel

private theorem sp10218 : smallValid 10218 41 := by unfold smallValid; decide +kernel

private theorem sp10259 : smallValid 10259 41 := by unfold smallValid; decide +kernel

private theorem sp10300 : smallValid 10300 41 := by unfold smallValid; decide +kernel

private theorem sp10341 : smallValid 10341 42 := by unfold smallValid; decide +kernel

private theorem sp10383 : smallValid 10383 41 := by unfold smallValid; decide +kernel

private theorem sp10424 : smallValid 10424 41 := by unfold smallValid; decide +kernel

private theorem sp10465 : smallValid 10465 41 := by unfold smallValid; decide +kernel

private theorem sp10506 : smallValid 10506 42 := by unfold smallValid; decide +kernel

private theorem sp10548 : smallValid 10548 41 := by unfold smallValid; decide +kernel

private theorem sp10589 : smallValid 10589 41 := by unfold smallValid; decide +kernel

private theorem sp10630 : smallValid 10630 41 := by unfold smallValid; decide +kernel

private theorem sp10671 : smallValid 10671 41 := by unfold smallValid; decide +kernel

private theorem sp10712 : smallValid 10712 41 := by unfold smallValid; decide +kernel

private theorem sp10753 : smallValid 10753 41 := by unfold smallValid; decide +kernel

private theorem sp10794 : smallValid 10794 41 := by unfold smallValid; decide +kernel

private theorem sp10835 : smallValid 10835 42 := by unfold smallValid; decide +kernel

private theorem sp10877 : smallValid 10877 41 := by unfold smallValid; decide +kernel

private theorem sp10918 : smallValid 10918 41 := by unfold smallValid; decide +kernel

private theorem sp10959 : smallValid 10959 41 := by unfold smallValid; decide +kernel

private theorem sp11000 : smallValid 11000 42 := by unfold smallValid; decide +kernel

private theorem sp11042 : smallValid 11042 41 := by unfold smallValid; decide +kernel

private theorem sp11083 : smallValid 11083 41 := by unfold smallValid; decide +kernel

private theorem sp11124 : smallValid 11124 41 := by unfold smallValid; decide +kernel

private theorem sp11165 : smallValid 11165 42 := by unfold smallValid; decide +kernel

private theorem sp11207 : smallValid 11207 41 := by unfold smallValid; decide +kernel

private theorem sp11248 : smallValid 11248 41 := by unfold smallValid; decide +kernel

private theorem sp11289 : smallValid 11289 41 := by unfold smallValid; decide +kernel

private theorem sp11330 : smallValid 11330 41 := by unfold smallValid; decide +kernel

private theorem sp11371 : smallValid 11371 41 := by unfold smallValid; decide +kernel

private theorem sp11412 : smallValid 11412 41 := by unfold smallValid; decide +kernel

private theorem sp11453 : smallValid 11453 41 := by unfold smallValid; decide +kernel

private theorem sp11494 : smallValid 11494 42 := by unfold smallValid; decide +kernel

private theorem sp11536 : smallValid 11536 41 := by unfold smallValid; decide +kernel

private theorem sp11577 : smallValid 11577 41 := by unfold smallValid; decide +kernel

private theorem sp11618 : smallValid 11618 41 := by unfold smallValid; decide +kernel

private theorem sp11659 : smallValid 11659 42 := by unfold smallValid; decide +kernel

private theorem sp11701 : smallValid 11701 41 := by unfold smallValid; decide +kernel

private theorem sp11742 : smallValid 11742 41 := by unfold smallValid; decide +kernel

private theorem sp11783 : smallValid 11783 41 := by unfold smallValid; decide +kernel

private theorem sp11824 : smallValid 11824 42 := by unfold smallValid; decide +kernel

private theorem sp11866 : smallValid 11866 41 := by unfold smallValid; decide +kernel

private theorem sp11907 : smallValid 11907 41 := by unfold smallValid; decide +kernel

private theorem sp11948 : smallValid 11948 41 := by unfold smallValid; decide +kernel

private theorem sp11989 : smallValid 11989 41 := by unfold smallValid; decide +kernel

private theorem sp12030 : smallValid 12030 41 := by unfold smallValid; decide +kernel

private theorem sp12071 : smallValid 12071 41 := by unfold smallValid; decide +kernel

private theorem sp12112 : smallValid 12112 41 := by unfold smallValid; decide +kernel

private theorem sp12153 : smallValid 12153 42 := by unfold smallValid; decide +kernel

private theorem sp12195 : smallValid 12195 41 := by unfold smallValid; decide +kernel

private theorem sp12236 : smallValid 12236 41 := by unfold smallValid; decide +kernel

private theorem sp12277 : smallValid 12277 41 := by unfold smallValid; decide +kernel

private theorem sp12318 : smallValid 12318 42 := by unfold smallValid; decide +kernel

private theorem sp12360 : smallValid 12360 41 := by unfold smallValid; decide +kernel

private theorem sp12401 : smallValid 12401 41 := by unfold smallValid; decide +kernel

private theorem sp12442 : smallValid 12442 41 := by unfold smallValid; decide +kernel

private theorem sp12483 : smallValid 12483 42 := by unfold smallValid; decide +kernel

private theorem sp12525 : smallValid 12525 41 := by unfold smallValid; decide +kernel

private theorem sp12566 : smallValid 12566 41 := by unfold smallValid; decide +kernel

private theorem sp12607 : smallValid 12607 41 := by unfold smallValid; decide +kernel

private theorem sp12648 : smallValid 12648 42 := by unfold smallValid; decide +kernel

private theorem sp12690 : smallValid 12690 41 := by unfold smallValid; decide +kernel

private theorem sp12731 : smallValid 12731 41 := by unfold smallValid; decide +kernel

private theorem sp12772 : smallValid 12772 41 := by unfold smallValid; decide +kernel

private theorem sp12813 : smallValid 12813 42 := by unfold smallValid; decide +kernel

private theorem sp12855 : smallValid 12855 41 := by unfold smallValid; decide +kernel

private theorem sp12896 : smallValid 12896 41 := by unfold smallValid; decide +kernel

private theorem sp12937 : smallValid 12937 41 := by unfold smallValid; decide +kernel

private theorem sp12978 : smallValid 12978 42 := by unfold smallValid; decide +kernel

private theorem sp13020 : smallValid 13020 41 := by unfold smallValid; decide +kernel

private theorem sp13061 : smallValid 13061 41 := by unfold smallValid; decide +kernel

private theorem sp13102 : smallValid 13102 41 := by unfold smallValid; decide +kernel

private theorem sp13143 : smallValid 13143 42 := by unfold smallValid; decide +kernel

private theorem sp13185 : smallValid 13185 41 := by unfold smallValid; decide +kernel

private theorem sp13226 : smallValid 13226 41 := by unfold smallValid; decide +kernel

private theorem sp13267 : smallValid 13267 41 := by unfold smallValid; decide +kernel

private theorem sp13308 : smallValid 13308 41 := by unfold smallValid; decide +kernel

private theorem sp13349 : smallValid 13349 41 := by unfold smallValid; decide +kernel

private theorem sp13390 : smallValid 13390 41 := by unfold smallValid; decide +kernel

private theorem sp13431 : smallValid 13431 41 := by unfold smallValid; decide +kernel

private theorem sp13472 : smallValid 13472 42 := by unfold smallValid; decide +kernel

private theorem sp13514 : smallValid 13514 41 := by unfold smallValid; decide +kernel

private theorem sp13555 : smallValid 13555 41 := by unfold smallValid; decide +kernel

private theorem sp13596 : smallValid 13596 41 := by unfold smallValid; decide +kernel

private theorem sp13637 : smallValid 13637 42 := by unfold smallValid; decide +kernel

private theorem sp13679 : smallValid 13679 41 := by unfold smallValid; decide +kernel

private theorem sp13720 : smallValid 13720 41 := by unfold smallValid; decide +kernel

private theorem sp13761 : smallValid 13761 41 := by unfold smallValid; decide +kernel

private theorem sp13802 : smallValid 13802 42 := by unfold smallValid; decide +kernel

private theorem sp13844 : smallValid 13844 41 := by unfold smallValid; decide +kernel

private theorem sp13885 : smallValid 13885 41 := by unfold smallValid; decide +kernel

private theorem sp13926 : smallValid 13926 41 := by unfold smallValid; decide +kernel

private theorem sp13967 : smallValid 13967 41 := by unfold smallValid; decide +kernel

private theorem sp14008 : smallValid 14008 41 := by unfold smallValid; decide +kernel

private theorem sp14049 : smallValid 14049 41 := by unfold smallValid; decide +kernel

private theorem sp14090 : smallValid 14090 41 := by unfold smallValid; decide +kernel

private theorem sp14131 : smallValid 14131 42 := by unfold smallValid; decide +kernel

private theorem sp14173 : smallValid 14173 41 := by unfold smallValid; decide +kernel

private theorem sp14214 : smallValid 14214 41 := by unfold smallValid; decide +kernel

private theorem sp14255 : smallValid 14255 41 := by unfold smallValid; decide +kernel

private theorem sp14296 : smallValid 14296 42 := by unfold smallValid; decide +kernel

private theorem sp14338 : smallValid 14338 41 := by unfold smallValid; decide +kernel

private theorem sp14379 : smallValid 14379 41 := by unfold smallValid; decide +kernel

private theorem sp14420 : smallValid 14420 41 := by unfold smallValid; decide +kernel

private theorem sp14461 : smallValid 14461 42 := by unfold smallValid; decide +kernel

private theorem sp14503 : smallValid 14503 41 := by unfold smallValid; decide +kernel

private theorem sp14544 : smallValid 14544 41 := by unfold smallValid; decide +kernel

private theorem sp14585 : smallValid 14585 41 := by unfold smallValid; decide +kernel

private theorem sp14626 : smallValid 14626 41 := by unfold smallValid; decide +kernel

private theorem sp14667 : smallValid 14667 41 := by unfold smallValid; decide +kernel

private theorem sp14708 : smallValid 14708 41 := by unfold smallValid; decide +kernel

private theorem sp14749 : smallValid 14749 41 := by unfold smallValid; decide +kernel

private theorem sp14790 : smallValid 14790 42 := by unfold smallValid; decide +kernel

private theorem sp14832 : smallValid 14832 41 := by unfold smallValid; decide +kernel

private theorem sp14873 : smallValid 14873 41 := by unfold smallValid; decide +kernel

private theorem sp14914 : smallValid 14914 41 := by unfold smallValid; decide +kernel

private theorem sp14955 : smallValid 14955 42 := by unfold smallValid; decide +kernel

private theorem sp14997 : smallValid 14997 41 := by unfold smallValid; decide +kernel

private theorem sp15038 : smallValid 15038 41 := by unfold smallValid; decide +kernel

private theorem sp15079 : smallValid 15079 41 := by unfold smallValid; decide +kernel

private theorem sp15120 : smallValid 15120 42 := by unfold smallValid; decide +kernel

private theorem sp15162 : smallValid 15162 41 := by unfold smallValid; decide +kernel

private theorem sp15203 : smallValid 15203 41 := by unfold smallValid; decide +kernel

private theorem sp15244 : smallValid 15244 41 := by unfold smallValid; decide +kernel

private theorem sp15285 : smallValid 15285 42 := by unfold smallValid; decide +kernel

private theorem sp15327 : smallValid 15327 41 := by unfold smallValid; decide +kernel

private theorem sp15368 : smallValid 15368 41 := by unfold smallValid; decide +kernel

private theorem sp15409 : smallValid 15409 41 := by unfold smallValid; decide +kernel

private theorem sp15450 : smallValid 15450 42 := by unfold smallValid; decide +kernel

private theorem sp15492 : smallValid 15492 41 := by unfold smallValid; decide +kernel

private theorem sp15533 : smallValid 15533 41 := by unfold smallValid; decide +kernel

private theorem sp15574 : smallValid 15574 41 := by unfold smallValid; decide +kernel

private theorem sp15615 : smallValid 15615 42 := by unfold smallValid; decide +kernel

private theorem sp15657 : smallValid 15657 41 := by unfold smallValid; decide +kernel

private theorem sp15698 : smallValid 15698 41 := by unfold smallValid; decide +kernel

private theorem sp15739 : smallValid 15739 41 := by unfold smallValid; decide +kernel

private theorem sp15780 : smallValid 15780 42 := by unfold smallValid; decide +kernel

private theorem sp15822 : smallValid 15822 41 := by unfold smallValid; decide +kernel

private theorem sp15863 : smallValid 15863 41 := by unfold smallValid; decide +kernel

private theorem sp15904 : smallValid 15904 41 := by unfold smallValid; decide +kernel

private theorem sp15945 : smallValid 15945 41 := by unfold smallValid; decide +kernel

private theorem sp15986 : smallValid 15986 41 := by unfold smallValid; decide +kernel

private theorem sp16027 : smallValid 16027 41 := by unfold smallValid; decide +kernel

private theorem sp16068 : smallValid 16068 41 := by unfold smallValid; decide +kernel

private theorem sp16109 : smallValid 16109 42 := by unfold smallValid; decide +kernel

private theorem sp16151 : smallValid 16151 41 := by unfold smallValid; decide +kernel

private theorem sp16192 : smallValid 16192 41 := by unfold smallValid; decide +kernel

private theorem sp16233 : smallValid 16233 41 := by unfold smallValid; decide +kernel

private theorem sp16274 : smallValid 16274 42 := by unfold smallValid; decide +kernel

private theorem sp16316 : smallValid 16316 41 := by unfold smallValid; decide +kernel

private theorem sp16357 : smallValid 16357 41 := by unfold smallValid; decide +kernel

private theorem sp16398 : smallValid 16398 41 := by unfold smallValid; decide +kernel

private theorem sp16439 : smallValid 16439 42 := by unfold smallValid; decide +kernel

private theorem sp16481 : smallValid 16481 41 := by unfold smallValid; decide +kernel

private theorem sp16522 : smallValid 16522 41 := by unfold smallValid; decide +kernel

private theorem sp16563 : smallValid 16563 41 := by unfold smallValid; decide +kernel

private theorem sp16604 : smallValid 16604 41 := by unfold smallValid; decide +kernel

private theorem sp16645 : smallValid 16645 41 := by unfold smallValid; decide +kernel

private theorem sp16686 : smallValid 16686 41 := by unfold smallValid; decide +kernel

private theorem sp16727 : smallValid 16727 41 := by unfold smallValid; decide +kernel

private theorem sp16768 : smallValid 16768 42 := by unfold smallValid; decide +kernel

private theorem sp16810 : smallValid 16810 41 := by unfold smallValid; decide +kernel

private theorem sp16851 : smallValid 16851 41 := by unfold smallValid; decide +kernel

private theorem sp16892 : smallValid 16892 41 := by unfold smallValid; decide +kernel

private theorem sp16933 : smallValid 16933 42 := by unfold smallValid; decide +kernel

private theorem sp16975 : smallValid 16975 41 := by unfold smallValid; decide +kernel

private theorem sp17016 : smallValid 17016 41 := by unfold smallValid; decide +kernel

private theorem sp17057 : smallValid 17057 41 := by unfold smallValid; decide +kernel

private theorem sp17098 : smallValid 17098 42 := by unfold smallValid; decide +kernel

private theorem sp17140 : smallValid 17140 41 := by unfold smallValid; decide +kernel

private theorem sp17181 : smallValid 17181 41 := by unfold smallValid; decide +kernel

private theorem sp17222 : smallValid 17222 41 := by unfold smallValid; decide +kernel

private theorem sp17263 : smallValid 17263 41 := by unfold smallValid; decide +kernel

private theorem sp17304 : smallValid 17304 41 := by unfold smallValid; decide +kernel

private theorem sp17345 : smallValid 17345 41 := by unfold smallValid; decide +kernel

private theorem sp17386 : smallValid 17386 41 := by unfold smallValid; decide +kernel

private theorem sp17427 : smallValid 17427 42 := by unfold smallValid; decide +kernel

private theorem sp17469 : smallValid 17469 41 := by unfold smallValid; decide +kernel

private theorem sp17510 : smallValid 17510 41 := by unfold smallValid; decide +kernel

private theorem sp17551 : smallValid 17551 41 := by unfold smallValid; decide +kernel

private theorem sp17592 : smallValid 17592 42 := by unfold smallValid; decide +kernel

private theorem sp17634 : smallValid 17634 41 := by unfold smallValid; decide +kernel

private theorem sp17675 : smallValid 17675 41 := by unfold smallValid; decide +kernel

private theorem sp17716 : smallValid 17716 41 := by unfold smallValid; decide +kernel

private theorem sp17757 : smallValid 17757 42 := by unfold smallValid; decide +kernel

private theorem sp17799 : smallValid 17799 41 := by unfold smallValid; decide +kernel

private theorem sp17840 : smallValid 17840 41 := by unfold smallValid; decide +kernel

private theorem sp17881 : smallValid 17881 41 := by unfold smallValid; decide +kernel

private theorem sp17922 : smallValid 17922 42 := by unfold smallValid; decide +kernel

private theorem sp17964 : smallValid 17964 41 := by unfold smallValid; decide +kernel

private theorem sp18005 : smallValid 18005 41 := by unfold smallValid; decide +kernel

private theorem sp18046 : smallValid 18046 41 := by unfold smallValid; decide +kernel

private theorem sp18087 : smallValid 18087 42 := by unfold smallValid; decide +kernel

private theorem sp18129 : smallValid 18129 41 := by unfold smallValid; decide +kernel

private theorem sp18170 : smallValid 18170 41 := by unfold smallValid; decide +kernel

private theorem sp18211 : smallValid 18211 41 := by unfold smallValid; decide +kernel

private theorem sp18252 : smallValid 18252 42 := by unfold smallValid; decide +kernel

private theorem sp18294 : smallValid 18294 41 := by unfold smallValid; decide +kernel

private theorem sp18335 : smallValid 18335 41 := by unfold smallValid; decide +kernel

private theorem sp18376 : smallValid 18376 41 := by unfold smallValid; decide +kernel

private theorem sp18417 : smallValid 18417 42 := by unfold smallValid; decide +kernel

private theorem sp18459 : smallValid 18459 41 := by unfold smallValid; decide +kernel

private theorem sp18500 : smallValid 18500 41 := by unfold smallValid; decide +kernel

private theorem sp18541 : smallValid 18541 41 := by unfold smallValid; decide +kernel

private theorem sp18582 : smallValid 18582 41 := by unfold smallValid; decide +kernel

private theorem sp18623 : smallValid 18623 41 := by unfold smallValid; decide +kernel

private theorem sp18664 : smallValid 18664 41 := by unfold smallValid; decide +kernel

private theorem sp18705 : smallValid 18705 41 := by unfold smallValid; decide +kernel

private theorem sp18746 : smallValid 18746 42 := by unfold smallValid; decide +kernel

private theorem sp18788 : smallValid 18788 41 := by unfold smallValid; decide +kernel

private theorem sp18829 : smallValid 18829 41 := by unfold smallValid; decide +kernel

private theorem sp18870 : smallValid 18870 41 := by unfold smallValid; decide +kernel

private theorem sp18911 : smallValid 18911 42 := by unfold smallValid; decide +kernel

private theorem sp18953 : smallValid 18953 41 := by unfold smallValid; decide +kernel

private theorem sp18994 : smallValid 18994 41 := by unfold smallValid; decide +kernel

private theorem sp19035 : smallValid 19035 41 := by unfold smallValid; decide +kernel

private theorem sp19076 : smallValid 19076 42 := by unfold smallValid; decide +kernel

private theorem sp19118 : smallValid 19118 41 := by unfold smallValid; decide +kernel

private theorem sp19159 : smallValid 19159 41 := by unfold smallValid; decide +kernel

private theorem sp19200 : smallValid 19200 41 := by unfold smallValid; decide +kernel

private theorem sp19241 : smallValid 19241 41 := by unfold smallValid; decide +kernel

private theorem sp19282 : smallValid 19282 41 := by unfold smallValid; decide +kernel

private theorem sp19323 : smallValid 19323 41 := by unfold smallValid; decide +kernel

private theorem sp19364 : smallValid 19364 41 := by unfold smallValid; decide +kernel

private theorem sp19405 : smallValid 19405 42 := by unfold smallValid; decide +kernel

private theorem sp19447 : smallValid 19447 41 := by unfold smallValid; decide +kernel

private theorem sp19488 : smallValid 19488 41 := by unfold smallValid; decide +kernel

private theorem sp19529 : smallValid 19529 41 := by unfold smallValid; decide +kernel

private theorem sp19570 : smallValid 19570 42 := by unfold smallValid; decide +kernel

private theorem sp19612 : smallValid 19612 41 := by unfold smallValid; decide +kernel

private theorem sp19653 : smallValid 19653 41 := by unfold smallValid; decide +kernel

private theorem sp19694 : smallValid 19694 41 := by unfold smallValid; decide +kernel

private theorem sp19735 : smallValid 19735 42 := by unfold smallValid; decide +kernel

private theorem sp19777 : smallValid 19777 41 := by unfold smallValid; decide +kernel

private theorem sp19818 : smallValid 19818 41 := by unfold smallValid; decide +kernel

private theorem sp19859 : smallValid 19859 41 := by unfold smallValid; decide +kernel

private theorem sp19900 : smallValid 19900 41 := by unfold smallValid; decide +kernel

private theorem sp19941 : smallValid 19941 41 := by unfold smallValid; decide +kernel

private theorem sp19982 : smallValid 19982 41 := by unfold smallValid; decide +kernel

private theorem sp20023 : smallValid 20023 41 := by unfold smallValid; decide +kernel

private theorem sp20064 : smallValid 20064 42 := by unfold smallValid; decide +kernel

private theorem sp20106 : smallValid 20106 41 := by unfold smallValid; decide +kernel

private theorem sp20147 : smallValid 20147 41 := by unfold smallValid; decide +kernel

private theorem sp20188 : smallValid 20188 41 := by unfold smallValid; decide +kernel

private theorem sp20229 : smallValid 20229 42 := by unfold smallValid; decide +kernel

private theorem sp20271 : smallValid 20271 41 := by unfold smallValid; decide +kernel

private theorem sp20312 : smallValid 20312 41 := by unfold smallValid; decide +kernel

private theorem sp20353 : smallValid 20353 41 := by unfold smallValid; decide +kernel

private theorem sp20394 : smallValid 20394 42 := by unfold smallValid; decide +kernel

private theorem sp20436 : smallValid 20436 41 := by unfold smallValid; decide +kernel

private theorem sp20477 : smallValid 20477 41 := by unfold smallValid; decide +kernel

private theorem sp20518 : smallValid 20518 41 := by unfold smallValid; decide +kernel

private theorem sp20559 : smallValid 20559 42 := by unfold smallValid; decide +kernel

private theorem sp20601 : smallValid 20601 41 := by unfold smallValid; decide +kernel

private theorem sp20642 : smallValid 20642 41 := by unfold smallValid; decide +kernel

private theorem sp20683 : smallValid 20683 41 := by unfold smallValid; decide +kernel

private theorem sp20724 : smallValid 20724 42 := by unfold smallValid; decide +kernel

private theorem sp20766 : smallValid 20766 41 := by unfold smallValid; decide +kernel

private theorem sp20807 : smallValid 20807 41 := by unfold smallValid; decide +kernel

private theorem sp20848 : smallValid 20848 41 := by unfold smallValid; decide +kernel

private theorem sp20889 : smallValid 20889 42 := by unfold smallValid; decide +kernel

private theorem sp20931 : smallValid 20931 41 := by unfold smallValid; decide +kernel

private theorem sp20972 : smallValid 20972 41 := by unfold smallValid; decide +kernel

private theorem sp21013 : smallValid 21013 41 := by unfold smallValid; decide +kernel

private theorem sp21054 : smallValid 21054 42 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤21095) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 21096 := (joinSmall (lo:=0) (a:=10548) (b:=10548) (joinSmall (lo:=0) (a:=5274) (b:=5274) (joinSmall (lo:=0) (a:=2637) (b:=2637) (joinSmall (lo:=0) (a:=1318) (b:=1319) (joinSmall (lo:=0) (a:=659) (b:=659) (joinSmall (lo:=0) (a:=329) (b:=330) (joinSmall (lo:=0) (a:=164) (b:=165) (joinSmall (lo:=0) (a:=82) (b:=82) (joinSmall (lo:=0) (a:=41) (b:=41) sp0 sp41) (joinSmall (lo:=82) (a:=41) (b:=41) sp82 sp123)) (joinSmall (lo:=164) (a:=82) (b:=83) (joinSmall (lo:=164) (a:=41) (b:=41) sp164 sp205) (joinSmall (lo:=246) (a:=41) (b:=42) sp246 sp287))) (joinSmall (lo:=329) (a:=165) (b:=165) (joinSmall (lo:=329) (a:=82) (b:=83) (joinSmall (lo:=329) (a:=41) (b:=41) sp329 sp370) (joinSmall (lo:=411) (a:=41) (b:=42) sp411 sp452)) (joinSmall (lo:=494) (a:=82) (b:=83) (joinSmall (lo:=494) (a:=41) (b:=41) sp494 sp535) (joinSmall (lo:=576) (a:=41) (b:=42) sp576 sp617)))) (joinSmall (lo:=659) (a:=329) (b:=330) (joinSmall (lo:=659) (a:=164) (b:=165) (joinSmall (lo:=659) (a:=82) (b:=82) (joinSmall (lo:=659) (a:=41) (b:=41) sp659 sp700) (joinSmall (lo:=741) (a:=41) (b:=41) sp741 sp782)) (joinSmall (lo:=823) (a:=82) (b:=83) (joinSmall (lo:=823) (a:=41) (b:=41) sp823 sp864) (joinSmall (lo:=905) (a:=41) (b:=42) sp905 sp946))) (joinSmall (lo:=988) (a:=165) (b:=165) (joinSmall (lo:=988) (a:=82) (b:=83) (joinSmall (lo:=988) (a:=41) (b:=41) sp988 sp1029) (joinSmall (lo:=1070) (a:=41) (b:=42) sp1070 sp1111)) (joinSmall (lo:=1153) (a:=82) (b:=83) (joinSmall (lo:=1153) (a:=41) (b:=41) sp1153 sp1194) (joinSmall (lo:=1235) (a:=41) (b:=42) sp1235 sp1276))))) (joinSmall (lo:=1318) (a:=659) (b:=660) (joinSmall (lo:=1318) (a:=329) (b:=330) (joinSmall (lo:=1318) (a:=164) (b:=165) (joinSmall (lo:=1318) (a:=82) (b:=82) (joinSmall (lo:=1318) (a:=41) (b:=41) sp1318 sp1359) (joinSmall (lo:=1400) (a:=41) (b:=41) sp1400 sp1441)) (joinSmall (lo:=1482) (a:=82) (b:=83) (joinSmall (lo:=1482) (a:=41) (b:=41) sp1482 sp1523) (joinSmall (lo:=1564) (a:=41) (b:=42) sp1564 sp1605))) (joinSmall (lo:=1647) (a:=165) (b:=165) (joinSmall (lo:=1647) (a:=82) (b:=83) (joinSmall (lo:=1647) (a:=41) (b:=41) sp1647 sp1688) (joinSmall (lo:=1729) (a:=41) (b:=42) sp1729 sp1770)) (joinSmall (lo:=1812) (a:=82) (b:=83) (joinSmall (lo:=1812) (a:=41) (b:=41) sp1812 sp1853) (joinSmall (lo:=1894) (a:=41) (b:=42) sp1894 sp1935)))) (joinSmall (lo:=1977) (a:=330) (b:=330) (joinSmall (lo:=1977) (a:=165) (b:=165) (joinSmall (lo:=1977) (a:=82) (b:=83) (joinSmall (lo:=1977) (a:=41) (b:=41) sp1977 sp2018) (joinSmall (lo:=2059) (a:=41) (b:=42) sp2059 sp2100)) (joinSmall (lo:=2142) (a:=82) (b:=83) (joinSmall (lo:=2142) (a:=41) (b:=41) sp2142 sp2183) (joinSmall (lo:=2224) (a:=41) (b:=42) sp2224 sp2265))) (joinSmall (lo:=2307) (a:=165) (b:=165) (joinSmall (lo:=2307) (a:=82) (b:=83) (joinSmall (lo:=2307) (a:=41) (b:=41) sp2307 sp2348) (joinSmall (lo:=2389) (a:=41) (b:=42) sp2389 sp2430)) (joinSmall (lo:=2472) (a:=82) (b:=83) (joinSmall (lo:=2472) (a:=41) (b:=41) sp2472 sp2513) (joinSmall (lo:=2554) (a:=41) (b:=42) sp2554 sp2595)))))) (joinSmall (lo:=2637) (a:=1318) (b:=1319) (joinSmall (lo:=2637) (a:=659) (b:=659) (joinSmall (lo:=2637) (a:=329) (b:=330) (joinSmall (lo:=2637) (a:=164) (b:=165) (joinSmall (lo:=2637) (a:=82) (b:=82) (joinSmall (lo:=2637) (a:=41) (b:=41) sp2637 sp2678) (joinSmall (lo:=2719) (a:=41) (b:=41) sp2719 sp2760)) (joinSmall (lo:=2801) (a:=82) (b:=83) (joinSmall (lo:=2801) (a:=41) (b:=41) sp2801 sp2842) (joinSmall (lo:=2883) (a:=41) (b:=42) sp2883 sp2924))) (joinSmall (lo:=2966) (a:=165) (b:=165) (joinSmall (lo:=2966) (a:=82) (b:=83) (joinSmall (lo:=2966) (a:=41) (b:=41) sp2966 sp3007) (joinSmall (lo:=3048) (a:=41) (b:=42) sp3048 sp3089)) (joinSmall (lo:=3131) (a:=82) (b:=83) (joinSmall (lo:=3131) (a:=41) (b:=41) sp3131 sp3172) (joinSmall (lo:=3213) (a:=41) (b:=42) sp3213 sp3254)))) (joinSmall (lo:=3296) (a:=329) (b:=330) (joinSmall (lo:=3296) (a:=164) (b:=165) (joinSmall (lo:=3296) (a:=82) (b:=82) (joinSmall (lo:=3296) (a:=41) (b:=41) sp3296 sp3337) (joinSmall (lo:=3378) (a:=41) (b:=41) sp3378 sp3419)) (joinSmall (lo:=3460) (a:=82) (b:=83) (joinSmall (lo:=3460) (a:=41) (b:=41) sp3460 sp3501) (joinSmall (lo:=3542) (a:=41) (b:=42) sp3542 sp3583))) (joinSmall (lo:=3625) (a:=165) (b:=165) (joinSmall (lo:=3625) (a:=82) (b:=83) (joinSmall (lo:=3625) (a:=41) (b:=41) sp3625 sp3666) (joinSmall (lo:=3707) (a:=41) (b:=42) sp3707 sp3748)) (joinSmall (lo:=3790) (a:=82) (b:=83) (joinSmall (lo:=3790) (a:=41) (b:=41) sp3790 sp3831) (joinSmall (lo:=3872) (a:=41) (b:=42) sp3872 sp3913))))) (joinSmall (lo:=3955) (a:=659) (b:=660) (joinSmall (lo:=3955) (a:=329) (b:=330) (joinSmall (lo:=3955) (a:=164) (b:=165) (joinSmall (lo:=3955) (a:=82) (b:=82) (joinSmall (lo:=3955) (a:=41) (b:=41) sp3955 sp3996) (joinSmall (lo:=4037) (a:=41) (b:=41) sp4037 sp4078)) (joinSmall (lo:=4119) (a:=82) (b:=83) (joinSmall (lo:=4119) (a:=41) (b:=41) sp4119 sp4160) (joinSmall (lo:=4201) (a:=41) (b:=42) sp4201 sp4242))) (joinSmall (lo:=4284) (a:=165) (b:=165) (joinSmall (lo:=4284) (a:=82) (b:=83) (joinSmall (lo:=4284) (a:=41) (b:=41) sp4284 sp4325) (joinSmall (lo:=4366) (a:=41) (b:=42) sp4366 sp4407)) (joinSmall (lo:=4449) (a:=82) (b:=83) (joinSmall (lo:=4449) (a:=41) (b:=41) sp4449 sp4490) (joinSmall (lo:=4531) (a:=41) (b:=42) sp4531 sp4572)))) (joinSmall (lo:=4614) (a:=330) (b:=330) (joinSmall (lo:=4614) (a:=165) (b:=165) (joinSmall (lo:=4614) (a:=82) (b:=83) (joinSmall (lo:=4614) (a:=41) (b:=41) sp4614 sp4655) (joinSmall (lo:=4696) (a:=41) (b:=42) sp4696 sp4737)) (joinSmall (lo:=4779) (a:=82) (b:=83) (joinSmall (lo:=4779) (a:=41) (b:=41) sp4779 sp4820) (joinSmall (lo:=4861) (a:=41) (b:=42) sp4861 sp4902))) (joinSmall (lo:=4944) (a:=165) (b:=165) (joinSmall (lo:=4944) (a:=82) (b:=83) (joinSmall (lo:=4944) (a:=41) (b:=41) sp4944 sp4985) (joinSmall (lo:=5026) (a:=41) (b:=42) sp5026 sp5067)) (joinSmall (lo:=5109) (a:=82) (b:=83) (joinSmall (lo:=5109) (a:=41) (b:=41) sp5109 sp5150) (joinSmall (lo:=5191) (a:=41) (b:=42) sp5191 sp5232))))))) (joinSmall (lo:=5274) (a:=2637) (b:=2637) (joinSmall (lo:=5274) (a:=1318) (b:=1319) (joinSmall (lo:=5274) (a:=659) (b:=659) (joinSmall (lo:=5274) (a:=329) (b:=330) (joinSmall (lo:=5274) (a:=164) (b:=165) (joinSmall (lo:=5274) (a:=82) (b:=82) (joinSmall (lo:=5274) (a:=41) (b:=41) sp5274 sp5315) (joinSmall (lo:=5356) (a:=41) (b:=41) sp5356 sp5397)) (joinSmall (lo:=5438) (a:=82) (b:=83) (joinSmall (lo:=5438) (a:=41) (b:=41) sp5438 sp5479) (joinSmall (lo:=5520) (a:=41) (b:=42) sp5520 sp5561))) (joinSmall (lo:=5603) (a:=165) (b:=165) (joinSmall (lo:=5603) (a:=82) (b:=83) (joinSmall (lo:=5603) (a:=41) (b:=41) sp5603 sp5644) (joinSmall (lo:=5685) (a:=41) (b:=42) sp5685 sp5726)) (joinSmall (lo:=5768) (a:=82) (b:=83) (joinSmall (lo:=5768) (a:=41) (b:=41) sp5768 sp5809) (joinSmall (lo:=5850) (a:=41) (b:=42) sp5850 sp5891)))) (joinSmall (lo:=5933) (a:=329) (b:=330) (joinSmall (lo:=5933) (a:=164) (b:=165) (joinSmall (lo:=5933) (a:=82) (b:=82) (joinSmall (lo:=5933) (a:=41) (b:=41) sp5933 sp5974) (joinSmall (lo:=6015) (a:=41) (b:=41) sp6015 sp6056)) (joinSmall (lo:=6097) (a:=82) (b:=83) (joinSmall (lo:=6097) (a:=41) (b:=41) sp6097 sp6138) (joinSmall (lo:=6179) (a:=41) (b:=42) sp6179 sp6220))) (joinSmall (lo:=6262) (a:=165) (b:=165) (joinSmall (lo:=6262) (a:=82) (b:=83) (joinSmall (lo:=6262) (a:=41) (b:=41) sp6262 sp6303) (joinSmall (lo:=6344) (a:=41) (b:=42) sp6344 sp6385)) (joinSmall (lo:=6427) (a:=82) (b:=83) (joinSmall (lo:=6427) (a:=41) (b:=41) sp6427 sp6468) (joinSmall (lo:=6509) (a:=41) (b:=42) sp6509 sp6550))))) (joinSmall (lo:=6592) (a:=659) (b:=660) (joinSmall (lo:=6592) (a:=329) (b:=330) (joinSmall (lo:=6592) (a:=164) (b:=165) (joinSmall (lo:=6592) (a:=82) (b:=82) (joinSmall (lo:=6592) (a:=41) (b:=41) sp6592 sp6633) (joinSmall (lo:=6674) (a:=41) (b:=41) sp6674 sp6715)) (joinSmall (lo:=6756) (a:=82) (b:=83) (joinSmall (lo:=6756) (a:=41) (b:=41) sp6756 sp6797) (joinSmall (lo:=6838) (a:=41) (b:=42) sp6838 sp6879))) (joinSmall (lo:=6921) (a:=165) (b:=165) (joinSmall (lo:=6921) (a:=82) (b:=83) (joinSmall (lo:=6921) (a:=41) (b:=41) sp6921 sp6962) (joinSmall (lo:=7003) (a:=41) (b:=42) sp7003 sp7044)) (joinSmall (lo:=7086) (a:=82) (b:=83) (joinSmall (lo:=7086) (a:=41) (b:=41) sp7086 sp7127) (joinSmall (lo:=7168) (a:=41) (b:=42) sp7168 sp7209)))) (joinSmall (lo:=7251) (a:=330) (b:=330) (joinSmall (lo:=7251) (a:=165) (b:=165) (joinSmall (lo:=7251) (a:=82) (b:=83) (joinSmall (lo:=7251) (a:=41) (b:=41) sp7251 sp7292) (joinSmall (lo:=7333) (a:=41) (b:=42) sp7333 sp7374)) (joinSmall (lo:=7416) (a:=82) (b:=83) (joinSmall (lo:=7416) (a:=41) (b:=41) sp7416 sp7457) (joinSmall (lo:=7498) (a:=41) (b:=42) sp7498 sp7539))) (joinSmall (lo:=7581) (a:=165) (b:=165) (joinSmall (lo:=7581) (a:=82) (b:=83) (joinSmall (lo:=7581) (a:=41) (b:=41) sp7581 sp7622) (joinSmall (lo:=7663) (a:=41) (b:=42) sp7663 sp7704)) (joinSmall (lo:=7746) (a:=82) (b:=83) (joinSmall (lo:=7746) (a:=41) (b:=41) sp7746 sp7787) (joinSmall (lo:=7828) (a:=41) (b:=42) sp7828 sp7869)))))) (joinSmall (lo:=7911) (a:=1318) (b:=1319) (joinSmall (lo:=7911) (a:=659) (b:=659) (joinSmall (lo:=7911) (a:=329) (b:=330) (joinSmall (lo:=7911) (a:=164) (b:=165) (joinSmall (lo:=7911) (a:=82) (b:=82) (joinSmall (lo:=7911) (a:=41) (b:=41) sp7911 sp7952) (joinSmall (lo:=7993) (a:=41) (b:=41) sp7993 sp8034)) (joinSmall (lo:=8075) (a:=82) (b:=83) (joinSmall (lo:=8075) (a:=41) (b:=41) sp8075 sp8116) (joinSmall (lo:=8157) (a:=41) (b:=42) sp8157 sp8198))) (joinSmall (lo:=8240) (a:=165) (b:=165) (joinSmall (lo:=8240) (a:=82) (b:=83) (joinSmall (lo:=8240) (a:=41) (b:=41) sp8240 sp8281) (joinSmall (lo:=8322) (a:=41) (b:=42) sp8322 sp8363)) (joinSmall (lo:=8405) (a:=82) (b:=83) (joinSmall (lo:=8405) (a:=41) (b:=41) sp8405 sp8446) (joinSmall (lo:=8487) (a:=41) (b:=42) sp8487 sp8528)))) (joinSmall (lo:=8570) (a:=329) (b:=330) (joinSmall (lo:=8570) (a:=164) (b:=165) (joinSmall (lo:=8570) (a:=82) (b:=82) (joinSmall (lo:=8570) (a:=41) (b:=41) sp8570 sp8611) (joinSmall (lo:=8652) (a:=41) (b:=41) sp8652 sp8693)) (joinSmall (lo:=8734) (a:=82) (b:=83) (joinSmall (lo:=8734) (a:=41) (b:=41) sp8734 sp8775) (joinSmall (lo:=8816) (a:=41) (b:=42) sp8816 sp8857))) (joinSmall (lo:=8899) (a:=165) (b:=165) (joinSmall (lo:=8899) (a:=82) (b:=83) (joinSmall (lo:=8899) (a:=41) (b:=41) sp8899 sp8940) (joinSmall (lo:=8981) (a:=41) (b:=42) sp8981 sp9022)) (joinSmall (lo:=9064) (a:=82) (b:=83) (joinSmall (lo:=9064) (a:=41) (b:=41) sp9064 sp9105) (joinSmall (lo:=9146) (a:=41) (b:=42) sp9146 sp9187))))) (joinSmall (lo:=9229) (a:=659) (b:=660) (joinSmall (lo:=9229) (a:=329) (b:=330) (joinSmall (lo:=9229) (a:=164) (b:=165) (joinSmall (lo:=9229) (a:=82) (b:=82) (joinSmall (lo:=9229) (a:=41) (b:=41) sp9229 sp9270) (joinSmall (lo:=9311) (a:=41) (b:=41) sp9311 sp9352)) (joinSmall (lo:=9393) (a:=82) (b:=83) (joinSmall (lo:=9393) (a:=41) (b:=41) sp9393 sp9434) (joinSmall (lo:=9475) (a:=41) (b:=42) sp9475 sp9516))) (joinSmall (lo:=9558) (a:=165) (b:=165) (joinSmall (lo:=9558) (a:=82) (b:=83) (joinSmall (lo:=9558) (a:=41) (b:=41) sp9558 sp9599) (joinSmall (lo:=9640) (a:=41) (b:=42) sp9640 sp9681)) (joinSmall (lo:=9723) (a:=82) (b:=83) (joinSmall (lo:=9723) (a:=41) (b:=41) sp9723 sp9764) (joinSmall (lo:=9805) (a:=41) (b:=42) sp9805 sp9846)))) (joinSmall (lo:=9888) (a:=330) (b:=330) (joinSmall (lo:=9888) (a:=165) (b:=165) (joinSmall (lo:=9888) (a:=82) (b:=83) (joinSmall (lo:=9888) (a:=41) (b:=41) sp9888 sp9929) (joinSmall (lo:=9970) (a:=41) (b:=42) sp9970 sp10011)) (joinSmall (lo:=10053) (a:=82) (b:=83) (joinSmall (lo:=10053) (a:=41) (b:=41) sp10053 sp10094) (joinSmall (lo:=10135) (a:=41) (b:=42) sp10135 sp10176))) (joinSmall (lo:=10218) (a:=165) (b:=165) (joinSmall (lo:=10218) (a:=82) (b:=83) (joinSmall (lo:=10218) (a:=41) (b:=41) sp10218 sp10259) (joinSmall (lo:=10300) (a:=41) (b:=42) sp10300 sp10341)) (joinSmall (lo:=10383) (a:=82) (b:=83) (joinSmall (lo:=10383) (a:=41) (b:=41) sp10383 sp10424) (joinSmall (lo:=10465) (a:=41) (b:=42) sp10465 sp10506)))))))) (joinSmall (lo:=10548) (a:=5274) (b:=5274) (joinSmall (lo:=10548) (a:=2637) (b:=2637) (joinSmall (lo:=10548) (a:=1318) (b:=1319) (joinSmall (lo:=10548) (a:=659) (b:=659) (joinSmall (lo:=10548) (a:=329) (b:=330) (joinSmall (lo:=10548) (a:=164) (b:=165) (joinSmall (lo:=10548) (a:=82) (b:=82) (joinSmall (lo:=10548) (a:=41) (b:=41) sp10548 sp10589) (joinSmall (lo:=10630) (a:=41) (b:=41) sp10630 sp10671)) (joinSmall (lo:=10712) (a:=82) (b:=83) (joinSmall (lo:=10712) (a:=41) (b:=41) sp10712 sp10753) (joinSmall (lo:=10794) (a:=41) (b:=42) sp10794 sp10835))) (joinSmall (lo:=10877) (a:=165) (b:=165) (joinSmall (lo:=10877) (a:=82) (b:=83) (joinSmall (lo:=10877) (a:=41) (b:=41) sp10877 sp10918) (joinSmall (lo:=10959) (a:=41) (b:=42) sp10959 sp11000)) (joinSmall (lo:=11042) (a:=82) (b:=83) (joinSmall (lo:=11042) (a:=41) (b:=41) sp11042 sp11083) (joinSmall (lo:=11124) (a:=41) (b:=42) sp11124 sp11165)))) (joinSmall (lo:=11207) (a:=329) (b:=330) (joinSmall (lo:=11207) (a:=164) (b:=165) (joinSmall (lo:=11207) (a:=82) (b:=82) (joinSmall (lo:=11207) (a:=41) (b:=41) sp11207 sp11248) (joinSmall (lo:=11289) (a:=41) (b:=41) sp11289 sp11330)) (joinSmall (lo:=11371) (a:=82) (b:=83) (joinSmall (lo:=11371) (a:=41) (b:=41) sp11371 sp11412) (joinSmall (lo:=11453) (a:=41) (b:=42) sp11453 sp11494))) (joinSmall (lo:=11536) (a:=165) (b:=165) (joinSmall (lo:=11536) (a:=82) (b:=83) (joinSmall (lo:=11536) (a:=41) (b:=41) sp11536 sp11577) (joinSmall (lo:=11618) (a:=41) (b:=42) sp11618 sp11659)) (joinSmall (lo:=11701) (a:=82) (b:=83) (joinSmall (lo:=11701) (a:=41) (b:=41) sp11701 sp11742) (joinSmall (lo:=11783) (a:=41) (b:=42) sp11783 sp11824))))) (joinSmall (lo:=11866) (a:=659) (b:=660) (joinSmall (lo:=11866) (a:=329) (b:=330) (joinSmall (lo:=11866) (a:=164) (b:=165) (joinSmall (lo:=11866) (a:=82) (b:=82) (joinSmall (lo:=11866) (a:=41) (b:=41) sp11866 sp11907) (joinSmall (lo:=11948) (a:=41) (b:=41) sp11948 sp11989)) (joinSmall (lo:=12030) (a:=82) (b:=83) (joinSmall (lo:=12030) (a:=41) (b:=41) sp12030 sp12071) (joinSmall (lo:=12112) (a:=41) (b:=42) sp12112 sp12153))) (joinSmall (lo:=12195) (a:=165) (b:=165) (joinSmall (lo:=12195) (a:=82) (b:=83) (joinSmall (lo:=12195) (a:=41) (b:=41) sp12195 sp12236) (joinSmall (lo:=12277) (a:=41) (b:=42) sp12277 sp12318)) (joinSmall (lo:=12360) (a:=82) (b:=83) (joinSmall (lo:=12360) (a:=41) (b:=41) sp12360 sp12401) (joinSmall (lo:=12442) (a:=41) (b:=42) sp12442 sp12483)))) (joinSmall (lo:=12525) (a:=330) (b:=330) (joinSmall (lo:=12525) (a:=165) (b:=165) (joinSmall (lo:=12525) (a:=82) (b:=83) (joinSmall (lo:=12525) (a:=41) (b:=41) sp12525 sp12566) (joinSmall (lo:=12607) (a:=41) (b:=42) sp12607 sp12648)) (joinSmall (lo:=12690) (a:=82) (b:=83) (joinSmall (lo:=12690) (a:=41) (b:=41) sp12690 sp12731) (joinSmall (lo:=12772) (a:=41) (b:=42) sp12772 sp12813))) (joinSmall (lo:=12855) (a:=165) (b:=165) (joinSmall (lo:=12855) (a:=82) (b:=83) (joinSmall (lo:=12855) (a:=41) (b:=41) sp12855 sp12896) (joinSmall (lo:=12937) (a:=41) (b:=42) sp12937 sp12978)) (joinSmall (lo:=13020) (a:=82) (b:=83) (joinSmall (lo:=13020) (a:=41) (b:=41) sp13020 sp13061) (joinSmall (lo:=13102) (a:=41) (b:=42) sp13102 sp13143)))))) (joinSmall (lo:=13185) (a:=1318) (b:=1319) (joinSmall (lo:=13185) (a:=659) (b:=659) (joinSmall (lo:=13185) (a:=329) (b:=330) (joinSmall (lo:=13185) (a:=164) (b:=165) (joinSmall (lo:=13185) (a:=82) (b:=82) (joinSmall (lo:=13185) (a:=41) (b:=41) sp13185 sp13226) (joinSmall (lo:=13267) (a:=41) (b:=41) sp13267 sp13308)) (joinSmall (lo:=13349) (a:=82) (b:=83) (joinSmall (lo:=13349) (a:=41) (b:=41) sp13349 sp13390) (joinSmall (lo:=13431) (a:=41) (b:=42) sp13431 sp13472))) (joinSmall (lo:=13514) (a:=165) (b:=165) (joinSmall (lo:=13514) (a:=82) (b:=83) (joinSmall (lo:=13514) (a:=41) (b:=41) sp13514 sp13555) (joinSmall (lo:=13596) (a:=41) (b:=42) sp13596 sp13637)) (joinSmall (lo:=13679) (a:=82) (b:=83) (joinSmall (lo:=13679) (a:=41) (b:=41) sp13679 sp13720) (joinSmall (lo:=13761) (a:=41) (b:=42) sp13761 sp13802)))) (joinSmall (lo:=13844) (a:=329) (b:=330) (joinSmall (lo:=13844) (a:=164) (b:=165) (joinSmall (lo:=13844) (a:=82) (b:=82) (joinSmall (lo:=13844) (a:=41) (b:=41) sp13844 sp13885) (joinSmall (lo:=13926) (a:=41) (b:=41) sp13926 sp13967)) (joinSmall (lo:=14008) (a:=82) (b:=83) (joinSmall (lo:=14008) (a:=41) (b:=41) sp14008 sp14049) (joinSmall (lo:=14090) (a:=41) (b:=42) sp14090 sp14131))) (joinSmall (lo:=14173) (a:=165) (b:=165) (joinSmall (lo:=14173) (a:=82) (b:=83) (joinSmall (lo:=14173) (a:=41) (b:=41) sp14173 sp14214) (joinSmall (lo:=14255) (a:=41) (b:=42) sp14255 sp14296)) (joinSmall (lo:=14338) (a:=82) (b:=83) (joinSmall (lo:=14338) (a:=41) (b:=41) sp14338 sp14379) (joinSmall (lo:=14420) (a:=41) (b:=42) sp14420 sp14461))))) (joinSmall (lo:=14503) (a:=659) (b:=660) (joinSmall (lo:=14503) (a:=329) (b:=330) (joinSmall (lo:=14503) (a:=164) (b:=165) (joinSmall (lo:=14503) (a:=82) (b:=82) (joinSmall (lo:=14503) (a:=41) (b:=41) sp14503 sp14544) (joinSmall (lo:=14585) (a:=41) (b:=41) sp14585 sp14626)) (joinSmall (lo:=14667) (a:=82) (b:=83) (joinSmall (lo:=14667) (a:=41) (b:=41) sp14667 sp14708) (joinSmall (lo:=14749) (a:=41) (b:=42) sp14749 sp14790))) (joinSmall (lo:=14832) (a:=165) (b:=165) (joinSmall (lo:=14832) (a:=82) (b:=83) (joinSmall (lo:=14832) (a:=41) (b:=41) sp14832 sp14873) (joinSmall (lo:=14914) (a:=41) (b:=42) sp14914 sp14955)) (joinSmall (lo:=14997) (a:=82) (b:=83) (joinSmall (lo:=14997) (a:=41) (b:=41) sp14997 sp15038) (joinSmall (lo:=15079) (a:=41) (b:=42) sp15079 sp15120)))) (joinSmall (lo:=15162) (a:=330) (b:=330) (joinSmall (lo:=15162) (a:=165) (b:=165) (joinSmall (lo:=15162) (a:=82) (b:=83) (joinSmall (lo:=15162) (a:=41) (b:=41) sp15162 sp15203) (joinSmall (lo:=15244) (a:=41) (b:=42) sp15244 sp15285)) (joinSmall (lo:=15327) (a:=82) (b:=83) (joinSmall (lo:=15327) (a:=41) (b:=41) sp15327 sp15368) (joinSmall (lo:=15409) (a:=41) (b:=42) sp15409 sp15450))) (joinSmall (lo:=15492) (a:=165) (b:=165) (joinSmall (lo:=15492) (a:=82) (b:=83) (joinSmall (lo:=15492) (a:=41) (b:=41) sp15492 sp15533) (joinSmall (lo:=15574) (a:=41) (b:=42) sp15574 sp15615)) (joinSmall (lo:=15657) (a:=82) (b:=83) (joinSmall (lo:=15657) (a:=41) (b:=41) sp15657 sp15698) (joinSmall (lo:=15739) (a:=41) (b:=42) sp15739 sp15780))))))) (joinSmall (lo:=15822) (a:=2637) (b:=2637) (joinSmall (lo:=15822) (a:=1318) (b:=1319) (joinSmall (lo:=15822) (a:=659) (b:=659) (joinSmall (lo:=15822) (a:=329) (b:=330) (joinSmall (lo:=15822) (a:=164) (b:=165) (joinSmall (lo:=15822) (a:=82) (b:=82) (joinSmall (lo:=15822) (a:=41) (b:=41) sp15822 sp15863) (joinSmall (lo:=15904) (a:=41) (b:=41) sp15904 sp15945)) (joinSmall (lo:=15986) (a:=82) (b:=83) (joinSmall (lo:=15986) (a:=41) (b:=41) sp15986 sp16027) (joinSmall (lo:=16068) (a:=41) (b:=42) sp16068 sp16109))) (joinSmall (lo:=16151) (a:=165) (b:=165) (joinSmall (lo:=16151) (a:=82) (b:=83) (joinSmall (lo:=16151) (a:=41) (b:=41) sp16151 sp16192) (joinSmall (lo:=16233) (a:=41) (b:=42) sp16233 sp16274)) (joinSmall (lo:=16316) (a:=82) (b:=83) (joinSmall (lo:=16316) (a:=41) (b:=41) sp16316 sp16357) (joinSmall (lo:=16398) (a:=41) (b:=42) sp16398 sp16439)))) (joinSmall (lo:=16481) (a:=329) (b:=330) (joinSmall (lo:=16481) (a:=164) (b:=165) (joinSmall (lo:=16481) (a:=82) (b:=82) (joinSmall (lo:=16481) (a:=41) (b:=41) sp16481 sp16522) (joinSmall (lo:=16563) (a:=41) (b:=41) sp16563 sp16604)) (joinSmall (lo:=16645) (a:=82) (b:=83) (joinSmall (lo:=16645) (a:=41) (b:=41) sp16645 sp16686) (joinSmall (lo:=16727) (a:=41) (b:=42) sp16727 sp16768))) (joinSmall (lo:=16810) (a:=165) (b:=165) (joinSmall (lo:=16810) (a:=82) (b:=83) (joinSmall (lo:=16810) (a:=41) (b:=41) sp16810 sp16851) (joinSmall (lo:=16892) (a:=41) (b:=42) sp16892 sp16933)) (joinSmall (lo:=16975) (a:=82) (b:=83) (joinSmall (lo:=16975) (a:=41) (b:=41) sp16975 sp17016) (joinSmall (lo:=17057) (a:=41) (b:=42) sp17057 sp17098))))) (joinSmall (lo:=17140) (a:=659) (b:=660) (joinSmall (lo:=17140) (a:=329) (b:=330) (joinSmall (lo:=17140) (a:=164) (b:=165) (joinSmall (lo:=17140) (a:=82) (b:=82) (joinSmall (lo:=17140) (a:=41) (b:=41) sp17140 sp17181) (joinSmall (lo:=17222) (a:=41) (b:=41) sp17222 sp17263)) (joinSmall (lo:=17304) (a:=82) (b:=83) (joinSmall (lo:=17304) (a:=41) (b:=41) sp17304 sp17345) (joinSmall (lo:=17386) (a:=41) (b:=42) sp17386 sp17427))) (joinSmall (lo:=17469) (a:=165) (b:=165) (joinSmall (lo:=17469) (a:=82) (b:=83) (joinSmall (lo:=17469) (a:=41) (b:=41) sp17469 sp17510) (joinSmall (lo:=17551) (a:=41) (b:=42) sp17551 sp17592)) (joinSmall (lo:=17634) (a:=82) (b:=83) (joinSmall (lo:=17634) (a:=41) (b:=41) sp17634 sp17675) (joinSmall (lo:=17716) (a:=41) (b:=42) sp17716 sp17757)))) (joinSmall (lo:=17799) (a:=330) (b:=330) (joinSmall (lo:=17799) (a:=165) (b:=165) (joinSmall (lo:=17799) (a:=82) (b:=83) (joinSmall (lo:=17799) (a:=41) (b:=41) sp17799 sp17840) (joinSmall (lo:=17881) (a:=41) (b:=42) sp17881 sp17922)) (joinSmall (lo:=17964) (a:=82) (b:=83) (joinSmall (lo:=17964) (a:=41) (b:=41) sp17964 sp18005) (joinSmall (lo:=18046) (a:=41) (b:=42) sp18046 sp18087))) (joinSmall (lo:=18129) (a:=165) (b:=165) (joinSmall (lo:=18129) (a:=82) (b:=83) (joinSmall (lo:=18129) (a:=41) (b:=41) sp18129 sp18170) (joinSmall (lo:=18211) (a:=41) (b:=42) sp18211 sp18252)) (joinSmall (lo:=18294) (a:=82) (b:=83) (joinSmall (lo:=18294) (a:=41) (b:=41) sp18294 sp18335) (joinSmall (lo:=18376) (a:=41) (b:=42) sp18376 sp18417)))))) (joinSmall (lo:=18459) (a:=1318) (b:=1319) (joinSmall (lo:=18459) (a:=659) (b:=659) (joinSmall (lo:=18459) (a:=329) (b:=330) (joinSmall (lo:=18459) (a:=164) (b:=165) (joinSmall (lo:=18459) (a:=82) (b:=82) (joinSmall (lo:=18459) (a:=41) (b:=41) sp18459 sp18500) (joinSmall (lo:=18541) (a:=41) (b:=41) sp18541 sp18582)) (joinSmall (lo:=18623) (a:=82) (b:=83) (joinSmall (lo:=18623) (a:=41) (b:=41) sp18623 sp18664) (joinSmall (lo:=18705) (a:=41) (b:=42) sp18705 sp18746))) (joinSmall (lo:=18788) (a:=165) (b:=165) (joinSmall (lo:=18788) (a:=82) (b:=83) (joinSmall (lo:=18788) (a:=41) (b:=41) sp18788 sp18829) (joinSmall (lo:=18870) (a:=41) (b:=42) sp18870 sp18911)) (joinSmall (lo:=18953) (a:=82) (b:=83) (joinSmall (lo:=18953) (a:=41) (b:=41) sp18953 sp18994) (joinSmall (lo:=19035) (a:=41) (b:=42) sp19035 sp19076)))) (joinSmall (lo:=19118) (a:=329) (b:=330) (joinSmall (lo:=19118) (a:=164) (b:=165) (joinSmall (lo:=19118) (a:=82) (b:=82) (joinSmall (lo:=19118) (a:=41) (b:=41) sp19118 sp19159) (joinSmall (lo:=19200) (a:=41) (b:=41) sp19200 sp19241)) (joinSmall (lo:=19282) (a:=82) (b:=83) (joinSmall (lo:=19282) (a:=41) (b:=41) sp19282 sp19323) (joinSmall (lo:=19364) (a:=41) (b:=42) sp19364 sp19405))) (joinSmall (lo:=19447) (a:=165) (b:=165) (joinSmall (lo:=19447) (a:=82) (b:=83) (joinSmall (lo:=19447) (a:=41) (b:=41) sp19447 sp19488) (joinSmall (lo:=19529) (a:=41) (b:=42) sp19529 sp19570)) (joinSmall (lo:=19612) (a:=82) (b:=83) (joinSmall (lo:=19612) (a:=41) (b:=41) sp19612 sp19653) (joinSmall (lo:=19694) (a:=41) (b:=42) sp19694 sp19735))))) (joinSmall (lo:=19777) (a:=659) (b:=660) (joinSmall (lo:=19777) (a:=329) (b:=330) (joinSmall (lo:=19777) (a:=164) (b:=165) (joinSmall (lo:=19777) (a:=82) (b:=82) (joinSmall (lo:=19777) (a:=41) (b:=41) sp19777 sp19818) (joinSmall (lo:=19859) (a:=41) (b:=41) sp19859 sp19900)) (joinSmall (lo:=19941) (a:=82) (b:=83) (joinSmall (lo:=19941) (a:=41) (b:=41) sp19941 sp19982) (joinSmall (lo:=20023) (a:=41) (b:=42) sp20023 sp20064))) (joinSmall (lo:=20106) (a:=165) (b:=165) (joinSmall (lo:=20106) (a:=82) (b:=83) (joinSmall (lo:=20106) (a:=41) (b:=41) sp20106 sp20147) (joinSmall (lo:=20188) (a:=41) (b:=42) sp20188 sp20229)) (joinSmall (lo:=20271) (a:=82) (b:=83) (joinSmall (lo:=20271) (a:=41) (b:=41) sp20271 sp20312) (joinSmall (lo:=20353) (a:=41) (b:=42) sp20353 sp20394)))) (joinSmall (lo:=20436) (a:=330) (b:=330) (joinSmall (lo:=20436) (a:=165) (b:=165) (joinSmall (lo:=20436) (a:=82) (b:=83) (joinSmall (lo:=20436) (a:=41) (b:=41) sp20436 sp20477) (joinSmall (lo:=20518) (a:=41) (b:=42) sp20518 sp20559)) (joinSmall (lo:=20601) (a:=82) (b:=83) (joinSmall (lo:=20601) (a:=41) (b:=41) sp20601 sp20642) (joinSmall (lo:=20683) (a:=41) (b:=42) sp20683 sp20724))) (joinSmall (lo:=20766) (a:=165) (b:=165) (joinSmall (lo:=20766) (a:=82) (b:=83) (joinSmall (lo:=20766) (a:=41) (b:=41) sp20766 sp20807) (joinSmall (lo:=20848) (a:=41) (b:=42) sp20848 sp20889)) (joinSmall (lo:=20931) (a:=82) (b:=83) (joinSmall (lo:=20931) (a:=41) (b:=41) sp20931 sp20972) (joinSmall (lo:=21013) (a:=41) (b:=42) sp21013 sp21054)))))))))
  have good : (List.range 21096).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 445000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 21095 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 21095 := by
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


private def packet (i : ℕ) : ℕ := (if i < 113 then (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 10 then (if i < 8 then 0 else (if i < 9 then 0 else 0)) else (if i < 12 then (if i < 11 then 0 else 0) else (if i < 13 then 0 else 0)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0 else (if i < 16 then 0 else 0)) else (if i < 19 then (if i < 18 then 0 else 0) else (if i < 20 then 0 else 0))) else (if i < 24 then (if i < 22 then 0 else (if i < 23 then 0 else 0)) else (if i < 26 then (if i < 25 then 0 else 0) else (if i < 27 then 0 else 0))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then 0 else (if i < 30 then 0 else 0)) else (if i < 33 then (if i < 32 then 0 else 0) else (if i < 34 then 0 else 0))) else (if i < 38 then (if i < 36 then 0 else (if i < 37 then 0 else 0)) else (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0)))) else (if i < 49 then (if i < 45 then (if i < 43 then 0 else (if i < 44 then 0 else 0)) else (if i < 47 then (if i < 46 then 0 else 0) else (if i < 48 then 0 else 0))) else (if i < 52 then (if i < 50 then 0 else (if i < 51 then 0 else 0)) else (if i < 54 then (if i < 53 then 0 else 0) else (if i < 55 then 0 else 0)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then 0 else (if i < 58 then 0 else 0)) else (if i < 61 then (if i < 60 then 0 else 0) else (if i < 62 then 0 else 0))) else (if i < 66 then (if i < 64 then 0 else (if i < 65 then 0 else 0)) else (if i < 68 then (if i < 67 then 0 else 0) else (if i < 69 then 0 else 0)))) else (if i < 77 then (if i < 73 then (if i < 71 then 0 else (if i < 72 then 0 else 0)) else (if i < 75 then (if i < 74 then 0 else 0) else (if i < 76 then 0 else 0))) else (if i < 80 then (if i < 78 then 0 else (if i < 79 then 0 else 0)) else (if i < 82 then (if i < 81 then 0 else 0) else (if i < 83 then 0 else 0))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then 0 else (if i < 86 then 0 else 0)) else (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else 0))) else (if i < 94 then (if i < 92 then 0 else (if i < 93 then 0 else 0)) else (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else 0)))) else (if i < 105 then (if i < 101 then (if i < 99 then 0 else (if i < 100 then 0 else 0)) else (if i < 103 then (if i < 102 then 0 else 0) else (if i < 104 then 0 else 0))) else (if i < 109 then (if i < 107 then (if i < 106 then 0 else 0) else (if i < 108 then 0 else 0)) else (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else 0))))))) else (if i < 170 then (if i < 141 then (if i < 127 then (if i < 120 then (if i < 116 then (if i < 114 then 0 else (if i < 115 then 0 else 0)) else (if i < 118 then (if i < 117 then 0 else 0) else (if i < 119 then 0 else 0))) else (if i < 123 then (if i < 121 then 0 else (if i < 122 then 0 else 0)) else (if i < 125 then (if i < 124 then 0 else 0) else (if i < 126 then 0 else 0)))) else (if i < 134 then (if i < 130 then (if i < 128 then 0 else (if i < 129 then 0 else 0)) else (if i < 132 then (if i < 131 then 0 else 0) else (if i < 133 then 0 else 0))) else (if i < 137 then (if i < 135 then 0 else (if i < 136 then 0 else 0)) else (if i < 139 then (if i < 138 then 0 else 0) else (if i < 140 then 0 else 0))))) else (if i < 155 then (if i < 148 then (if i < 144 then (if i < 142 then 0 else (if i < 143 then 0 else 0)) else (if i < 146 then (if i < 145 then 0 else 0) else (if i < 147 then 0 else 0))) else (if i < 151 then (if i < 149 then 0 else (if i < 150 then 0 else 0)) else (if i < 153 then (if i < 152 then 0 else 0) else (if i < 154 then 0 else 0)))) else (if i < 162 then (if i < 158 then (if i < 156 then 0 else (if i < 157 then 0 else 0)) else (if i < 160 then (if i < 159 then 0 else 0) else (if i < 161 then 0 else 0))) else (if i < 166 then (if i < 164 then (if i < 163 then 0 else 0) else (if i < 165 then 0 else 0)) else (if i < 168 then (if i < 167 then 0 else 0) else (if i < 169 then 0 else 0)))))) else (if i < 198 then (if i < 184 then (if i < 177 then (if i < 173 then (if i < 171 then 0 else (if i < 172 then 0 else 0)) else (if i < 175 then (if i < 174 then 0 else 0) else (if i < 176 then 0 else 0))) else (if i < 180 then (if i < 178 then 0 else (if i < 179 then 0 else 0)) else (if i < 182 then (if i < 181 then 0 else 0) else (if i < 183 then 0 else 0)))) else (if i < 191 then (if i < 187 then (if i < 185 then 0 else (if i < 186 then 0 else 0)) else (if i < 189 then (if i < 188 then 0 else 0) else (if i < 190 then 0 else 0))) else (if i < 194 then (if i < 192 then 0 else (if i < 193 then 0 else 0)) else (if i < 196 then (if i < 195 then 0 else 0) else (if i < 197 then 0 else 0))))) else (if i < 212 then (if i < 205 then (if i < 201 then (if i < 199 then 0 else (if i < 200 then 0 else 0)) else (if i < 203 then (if i < 202 then 0 else 0) else (if i < 204 then 0 else 0))) else (if i < 208 then (if i < 206 then 0 else (if i < 207 then 0 else 0)) else (if i < 210 then (if i < 209 then 0 else 0) else (if i < 211 then 0 else 0)))) else (if i < 219 then (if i < 215 then (if i < 213 then 0 else (if i < 214 then 0x1557f0b2e99590a0a4a32280fe872033116909a44061a40a203580e6000015579092d515209d048721e0f786ec31715a89283c417f09383040b4000015572f72cd14d899e46c20b0eb46be30014b88dc3b417c08b82d80a200001556cd62e515749f849921c0f546ec31215989403ee18e09983380c8000015566ab2e315eca204bc22f0fe072232615a893c3d418709283040bc000015560b62c814c89a847520c0ec86962ec14f08e43b218109003000be00001555a922df95789fc49b2178f106be304154891c3d018108f82ec0be0000155547a2d415289d648e2198f446e431215409443e218e09002c00a800001554e5b2e0954c9da48a21a8f686fe31815889203c617d08c03100cc000015548562d915449f64912198f606f430e152091c3c217a09002fc0d6000015542522d015209e84912188f586f030215388fc3ce18709702f80b400001553c372df15849f249e21d0f7070232115709403d218e099032c0be000015536392ce95149d64862140f186d030015289283b817b08f830c0be0000155301d2d815549ec49e21c8f606fa323160095c3e418b09503140d400001552a1f2d015189c648720e8f046c630b15309143c418909483100a6000015524022dc1574a1e4a221b8f446e631816209883ee19709e033c0d800001551e0e2cb95049b848420e0ef06ba2ed14908b43b017408d82f80c8000015518022d415309ce4832110f246c230415288f83ca18b09103100b8000015511f92d394dc99e4792088eb46982e7144089438e17308882c00ac00001550bed2da95489de4942130eec6b82ee14588ac3b217b08f830c0cc000015506092bf14889844642058eb46a42ef143888439e17508d83000c60000154ffba2f49608a2c4ad22a0f9871632716089984161a20a183600cc0000154f9cf2ca94c498c4662058ed869c2e914788bc39217108b03080d00000154f3e72c794d09aa46d2058e846942ee14f88f03a817708f02dc0b60000154edf52c5949c9944672088eb46a02f214788ec3c618708b82f40be0000154e80a2c294a49b447320c0edc6a82f315109043ba16f08882d40b60000154e1fe2da157c9ea4912190f006c831115d893c3e819809983400e00000154dc3d2b7145496e4571fc0e4866a2d8142087c37016808782cc0b00000154d6442c794a899c46f2088eec6a62ee14988d43b817608c82f00c20000154d0422d314f89aa47720b0ed069c2e914508a039816708382bc0aa0000154ca0b2ea95b0a0049f2210f6c6ee31515609043f218d096033c0cc0000154c3df2e315709fa4a021d0f6c6f031a15e89743f018f09303080d60000154bdd32d515389e049a2178f146d030d154893c3f018b09b03200c40000154b7dd2c794dc99c46d20c8ecc6b62fe15008cc3b817c093831c0d20000154b1c42dd95549f44932198f3c6e430715209243e218609783180ba0000154abb52d695149cc4882110f206c82f7152090c3ac17e08f03300be0000154a5952e015749f249521b8f186ca308151090c3b817b09003080c800001549f8d2d895449e649321a0f286ca304151891c3c818409083140ba0000154999a2c514b49ac47e20c8f186e430f14f08cc3a417208f030c0b4000015493a22cb94f89b847620b0edc6c630114e89183bc18208f02e80b800001548d822e015709ee49821b8f6470631815a89503da18f09883300ba000015487ab2bb947096844d1fa8e8c6842df141888839216907e82c009e000015481752e915cca144a72258f9470c31a15e094c3f219109583180be00001547b6a2d6954c9dc4872158f006b030115709403f619f09c03340bc000015475722ce94e49984611ff8ea869a2e814588b43ae18c09503240cc00001546f752cd14c899246e2088ed86b02f914b88c83a217008782fc0b8000015469772cc14d89ca4832138f0c6b62fc14e88e83ac17f09283040cc0000154636f2d395089ce48d21b0f506de30d157091c3c418a09483180c800001545d6d2cc94b097846e20a0ef86cc306158892c3d417c08d82fc0b00000154575b2da152c9d44912160f246c630214b88d03ac17d09182ec0c6000015451412e21578a0c4a42228f786e6311159093c3e219109583300dc00001544b3e2d595189e449321c8f406d830614f08e03c018d09483180b8000015445372d995409fa4a12240f8871231c16009643e618609003100c400001543f4b2c594c09aa47820b8ec46ae2ec14408c83b217b08f82e80ae0000154394c2d095109d247e20b0edc6be2fa14908c03b418008e83100ba000015433602c514b898c45b1ff8e7867a2e314688e439e17808d03040c600001542d4c2d215549ee4992188f546dc31315789203d218809403200c8000015427352d715349da49821c0f6c70231f15c89583ea19209682e80ae000015421342cf14cc9ac4732088ef46ca307157093c3e618909583480cc00001541b462c094ac9a64822150f586dc30f15608ec3c017808c82f00b4000015415262dc95489d248120d0ef86ae2f814b88f43c218009203240be00001540f452c294609744642048eb868a2ee14708b03a216b08a82f40c20000154092e2de956c9c84842160f386dc31415e898840219209503000c2000015403052e4156c9f849d2220f786e6319157093c3ce18509483340ca000 else 0x15701a92dd154c9e649721d8f686ec31315b09543da18308e03100c40000156fb8c2df15449e248f2130f186c630114c08f43ba18108f82d80b20000156f5722d595009c44832120f106ca300152091c3ca18408f83040cc0000156efb72aa14289604642050ea069c2f014988e83c218409303180d00000156e9982de156ca064a22210f986fa31015a896440019d098832c0c80000156e37f2db156c9f84972168f4c6d230315188d83ba18109283380b60000156dd8b2cc14e89ae48020b0f186de30114b88e03ca18609083100ac0000156d7762e195a89e249821a8f406d630714f88e03ba17f08d03040b60000156d13f2e695d8a2c4b121e0f506ec31615609203b617908b02f80b60000156cb4b2cb14b89964692088ebc6a42f814d89043d618a09303080ce0000156c54d2cb15089d048220c8ebc6942f514d08cc3b018108b02c40a80000156bf3d2d7957c9ea48b2148f586ca30014f88f03d018f09883280c40000156b9492cb14c49a44692070ebc6ae2fb14c88f83cc180095830c0dc0000156b35d2c694b89984652050ed06ba2ed14608c43a817208c030c0c80000156ad7e2bf946c9684571ff0e9067e2ea14488b43a416808502c80b60000156a77e2ce14c09a846d2078ed86a82fd15109003c618a08f83240ca0000156a1ac2b694589804691fc0e6c6922de14888ec3c218f09883240cc00001569b7a2e41584a0449821a0f486e431515889083ce18a08e82e80b80000156956d2dc15449d248a2198f4c6e231015a89543e418f093034c0c200001568f5f2d395109bc4862148f106ce31615909243c218a09383100b80000156894a2d715289cc4872178f246c830a15489543ea19209803240c60000156831e2e715d0a284b622c8fec72632f16409ac41c19e0a083840d600001567d1a2d615449ce4882150f2c6e231b15389303c418209302fc0b4000015677072db15389d448b20d0ee06c230615089183d818709803240ce000015670f12db9568a0049f2220f8c70832315589383ca18b091031c0b400001566ad12e095789e04932190f2c6c62fe14e88e03b6181095832c0ce000015664f02be147499847120a0edc6aa2f215089043c618a09783400dc00001565ed02df9578a0e4a22248fa471a33416989803f4197098032c0ce000015658b82da15449d84892130f186e431315a89543d218909783300c4000015652a92d214fc9be47d20c0edc6be2f114b88d03b218208b02bc0c200001564c652f195e0a1e4ac2258f806ee31415789103c017e08d02fc0cc000015646742c994a898446d2038ed86ba30614f08cc39817808802bc0ba000015640782cb15089b447620e8ef86b02f214708d83a617108482b40b600001563a6f2cf95209e04892178f2c6ca30315188e83d618009103100ba000015634512d615249e64962158f186ca30214908dc3b817e09383100d600001562e612c414a89844692020eb069a2ee149089c38c16a08482c80c4000015628632c894b89904662048e986982f014488d03bc17d092833c0ca0000156222d2ed15e4a2a4b42290fa470c32115a09443dc18109282dc0a200001561c482c7149498c46a2038e7c6982eb14488b43a017208d02f40c6000015616462ca14d09a246d20d0ef46b030114c08dc39a17508c02e40cc00001560ffe2ef15eca3e4b32240f606f030c154893c3dc18b09603440d8000015609f52cf151c9be47320a0f006c830715189303d617f08e03000c0000015603dc2dc15389e849121d0f4c6c02fe15189043b217609082e40ca0000155fddd2d494f49ca4812118f306cc30e15589483ec19409702f00ba0000155f7c92d515649fc4a42228f846f031615689083b417808d02d40c80000155f1c22ca15009ce4872150f446d030415609443e618b08e02f00aa0000155ebe22bc145c9724602040e986a82f814e08fc3b617808e02ec0ae0000155e5d32d595309c248420f0ef86c0306151090c3c218208e82e40c60000155dfcd2d815249ca4822140f306ea30c15288ec3b817608c02d40bc0000155d9ab2e29584a124a82278f686fa32215e89843f019909a03300c00000155d3972d995289cc48b2120eec6b230715809303d618409283080ca0000155cd922d915389e248e2188f446dc30a15108fc3c016a08302a00ae0000155c78f2d115389c648120e8ef86c430214f88f03b617808c82c80c00000155c17c2d495009da4902190f1c6d030715789503de18009082f40d20000155bb5d2da15349de4932110f086ba30015009103c818609083080c20000155b53d2e1958c9f649521f0fa871a32916009703e819109703180c40000155af5a2c214d49b64782098edc6b42f714a89083ae16c08802c80a80000155a94b2d8954c9ec49621c8f6c6f232616489ac4141ac09783300c60000155a34e2d295109c84902178f286c430415008ec3bc17a08782d00b400001559d4e2cf94f89c64882120f006c02f815108f03b817909082ec0be0000155975e2ca94f89d048b2140f206d030c15308dc39817108a02fc0c6000015591732c594d89b647e20e8f186c631315b89483e219609983200bc00001558b5c2dc955c9f049c2190f406d430c15008d43aa17a08c82dc0a80000155852f2df15b8a0a4982200f5c6ec31816089903fe19809003000ce000)) else (if i < 217 then (if i < 216 then 0x15885622d094f099c4672000e646722e2142088439816508682b809000001587f3e2e7159ca084aa2260f786e631115589003ba17908702e80b2000015878f42ed15eca2e4b122d8fd872232415b09403da18f09303280c4000015872dd2d594fc9c64842100eec6982ea14988b83a217808982e80c600001586cb32dd157c9fe4972140f006c02f214608bc39416d08c02f40c4000015866d12ba145095e4531fa8e7467e2e214108b83b016f08b82f40c4000015860b82d595209ee4862118eec6b42fc14c08f43b617d09082f40c000001585ab02d515309d448320e0eec6a22f314a08d83a817a090830c0c40000158543e2ff9678a744ca2350fd073233516689b03fa19c09383140c800001584e442d015409d048f2148f506e0305152092c3b418208f030c0be000015848422cc94e49b447a20c8f286c631515e09783f4195096031c0c2000015842432d395209d44872128f046b630614e08e43ba18a09403300ca00001583c362d995689f449a21c0f6870231d15b892c3e218e09783500ce0000158363d2c8149098447120b8f006ac2f714988e03be17608f03040b0000015830282dc156c9ea48e2178f246d630f158892c3c617908802f40be00001582a182da15549e449421a0f346d630715389443d018609102fc0be000015823d32f71618a464af2290fa470c323162898c3ea18c09c834c0d000001581dd42d094d49a446f2060ec06a02ef14808e03c417908982c00bc000015817f52c414e49a046a2050eb86902e814688c43a817008c82fc0b8000015811dd2dd1578a0049e2198f446de30115008f03c018009482fc0c800001580bc42db15749f049e21f8f6c6e430914f89143de18909083000c8000015805e72c1948499a4692020ed069e2f714c08dc3b218108c830c0b00000157ffec2cc14bc99446a2070e806782d913c886837216508f03140c60000157f9e92d3151c9d448b2120f106aa2f514e88d43a617c08c82f00b60000157f3c72e515a4a104a921d8f646fa31f15789503e819309683400cc0000157ed9e2dd95609fa49921f0f9870831415a89503de18609503100c00000157e77e2e015a0a0249721c8f606e230b15a89443c817d091833c0d00000157e18b2c3147c9904692050ec069a2f615109183c618308f82f00c40000157db792da154c9ee4962198f386dc304153893c3c418609383080d80000157d56d2d595409d84842170f246e430d158096440619e09a03480d20000157cf682d114ec9c447f20b0ed46b02fe15289143c017a08e02ec0ba0000157c9622d294dc9a647620a0ed86b62f614e09003c217e08e83000c00000157c3612d015089ca4852128efc6ca30615589143bc17d09003280c40000157bd772c1947c96a45b2050ec06a82f114a08b43ac17508b02e00c20000157b7712d595589ea4982188f0c6ca30515389343da18009503000b40000157b18e2b9943c97045a1fc8e5c6622d513e08b839616307f02a40b60000157ab542e095789fc49c21c8f446da31415889644001a509c030c0c40000157a5582ce14c09a447c20c0ecc6b62f814a08e03bc17508a82d80a200001579f4c2d3153c9d64892100f086c230415909543d418609483180c40000157991b2e095689e04862130f286c830215088fc3ce18209183040b0000015792df2e595a4a064a12168f206e030b15209383e21a009d03540dc00001578cd22d895409d64852180f2c6cc2f514788d03b017908a82f40b8000015786cb2d8952c9ca4762108ee86cc306150090c3b017a08b82f40c4000015780b82d2955c9d048e2148f086ce2f915288f83b817c08d030c0ca00001577ab72ce952c9da48c2150f2c6c430415089183c218609003100ca000015774b92d114f09cc48220f8eb46b82fe15009083c017b08b82ec0aa00001576ecb2be94b89b04772108edc6b02ec14408c039c17508782bc0b2000015768c82d094f89aa47d2088ed86a42f615409303e018f090030c0c8000015762a52db95609f04a721c8f5c6f230415489243bc17a08702d00ac00001575cbb2c714bc9a048120c8eec6ac2f514708dc3ae18109082f00bc0000157568c2e5958ca164992120f646fe32416089743da17d08f030c0cc0000157505b2e815aca184ac2200f446d630a15209103ba18509403080c200001574a662d014f49d048320e0f2c6c630315388ec3aa17308a02d80a0000015744302e795b0a0a49821a0f546e831015909443ce18809403200bc00001573e2f2cf14fc9cc4942178f346d231315909443da18708d03200bc0000157381e2dc15249c248c20f0edc6c030915389083c018208f03080c6000015731ee2e315849f049a21c0f806f631415e89543d618608c02d40c000001572bed2d395409e64902158f346de30915409243c217f08d83000c0000015725d12d995249e249921b8f446d231415d09683e219709c03300c400001571fbc2da95409d84852118f1c6dc31615589483dc18f09683240c2000015719b42d195089c647820e0f186d0306156091c3b416b08482ac0ae000015713e92b4142097845e1fa8e186582cc136083835615007f82b80b600001570df22cb94d89a24772118ef06bc2fb15289303bc18108e03000c0000015707d62db154c9dc4932168f206d030c152090c3c618909302f80c2000 else 0x15a08022ce94e09c648a2160f046aa2f214988f03c618109503140c0000015a01ec2d7952c9b848520e8ee46be2f714b08c039c17408602b00a60000159fbd02d515209c848c2190f886f831715709243de18908d02e00b20000159f5d22ca14b09984742078ee06b42fb14888cc3b817d08d02ec0b20000159efdf2cb14d09ae47720a0ee86b82fc14988c43b818208e03000cc0000159e9cd2d094e89d048820f8f046b830314e08e83a817608a830c0bc0000159e3d72cb14d09a447520c8f106d030615008f03b617d09382e40cc0000159ddd92d095009ae47f2108efc6a62fa14a88dc3a618309583240d00000159d7c02db9588a024a721d0f386e231915d093c3d018d09382f00b00000159d1a12da95489f24a32240f7870e31f15889143d218d09603300d80000159cbb02ca14b099245b2000e986902eb14508a43a217308b82e80b00000159c5b72cb94cc9ae47320a8ed86aa2fe14f09103d218108f030c0be0000159bfbb2cf950c9ba47b2128f446e230c15709303d219809803440c40000159b9ad2d795749d048f2178f646fa31615489143c817b08e82f80b80000159b37b2e595aca084a52200f6470431a15b09503d618b08f82e80bc0000159ad6e2d615189ce4832158f286e831916389703fe19a09903440ce0000159a7582db15449e449521a0f386e431915b894c3d0183090032c0ce0000159a16d2c1949c9944742130f186c830d15a89343c217f08f02b80ae00001599b6c2d214e89b446e20a8ed869e2fc15389243d819109c83240c80000159955e2d615449dc48e2150eec6c430115008fc3b417908d82f80b800001598f652cb94d49b247d2150f346e0315158095c3f019309983140ba0000159896a2d194c89a847b20d0f046b82fb14c09003b816f08683080ca0000159833f2e815949f649e21d8fa0704329162899040619609a03400ca00001597d2f2d8952c9c44872108f046b82f514808c43bc18309103080ce000015977402c614c099c4642090eb06a62f814c08f43c418409603080ae000015971242db156c9f04912190f586ec30d15809503e418d09483200c800001596b212cc95189cc4842158f486da30f157093c3d619109183000c40000159651d2d315409de4902148f246ea31c15b09703f819d097831c0c800001595f402bd946498c46920a0e9c6a42f014608b43b2188091831c0c8000015959362d795389cc4822140ee46c62f815289003be17908d82d40ae000015953182e015849e849921b8f1c6ca2fc15008f03ae17508a82d80be00001594d0c2d7154c9e24912198f106d430515508f03ac17208f03180c0000015946e52e015a4a244ac21e8f846fe31c15989243d018a09102f40b2000015940df2d394e89c24722078ed46b82fc14c08f03d218909483200d000001593aba2e315b8a1c4a72260fb070e32215689303de188093031c0b8000015934542fd963ca2c4bc2280fb070c31b15589583ee18d09182d80ac00001592e6b2c294b09a647620c8efc6bc2fd14a88e83be17808983040a6000015928762cd94e49be47a2118ef86b630514f08ec3d219309a83280c80000159229b2bf949c9a047320b8edc6c630415389003cc18c092030809e00001591c602e895a89f649521d0f306da30815389103c818209783400d0000015916432e015809f249721f0f586e230e157893c3da18f09a03480d20000159101e2e515aca144a12250f9070432816209503e619a09683480da00001590a1a2ce15209b847020b0ed06ba2fd14e091c3c618409883380cc000015904132d395289f04922188f206d8311152091c3d219909c83400d40000158fe1a2cf94ec9b447120b0eec6b22ee14c88f03c217108e02f40ba0000158f8082d6955c9d448d21a0f706ea31415d09703de19409a83580e20000158f20d2c994bc9b447e2110ef06a62f514909043cc18a09403040d20000158ec092d7951c9c64812120ef46b02ff15708f03b817d091030c0ce0000158e5e82e395889f249e21e0f746f631415489183d018408902d40c40000158dfdf2d595249d448b2140f486ea31f15d097c3e418a09403140c40000158d9e62cf95049b24822108ef06b82fc15189383c817b09102f00be0000158d3c52dc95549d047d2118f086ce30c14e09143ca19009783280d60000158cde92b8943496644a1f90e586722d9139087037a16c08002900a00000158c7b52e215bca1e4a321f8f486f231015609203cc18109103040bc0000158c1b52d295189c847b20a8ee06b030114d88f83ce18109083200ca0000158bbb72cc94d89b24742098eec6ba30215589003b817108e03100bc0000158b5c22c994ac9a84722068eb46822e214408c43a816708682c00b00000158afd42be146497e45d2018e7c68a2e1141088439016f08202a40a20000158a9b82e015a0a2c4b022b0fc071a32115e096c3f419b09a833c0de0000158a3a12d595309d048a2140f146b62f414988f83a617409082e80ba00001589da12d115009c648020c8ed86b82f715008fc3b817008d02e40ac000015897a42d1152c9d44822108efc6c630814e08d43c018909583200b8000015891832de95749ea48c2150f3c6d630815208e43b617909003200b800001588b662dc15349d44892158f0c6c230015309103b817d08c82dc0c4000) else (if i < 218 then 0x15b8a972cd94ec9be48120c8ef86c42fb14e08f43b217e08982ec0c2000015b84872d995509ea4922178f486d630214e890c3da18b09603200d6000015b7e8e2c994dc9ae47c20e0f146d030415689103ba18508f82d40b2000015b785d2e895b0a0849e21f8f8071033216509a440219a09d833c0c4000015b724b2d6153c9d247e20b8ef06b42fb14f88d03aa17e08982e40b2000015b6c242df95749ec4a021f8f7c70231315a89343dc18e09383280dc000015b66062db95589f649d21e8f6871032215c096c3e419009983340c6000015b602a2c0947498a4692088ee06a42f714688bc3a217808b83140cc000015b59f22f79604a2e4a52228f806f031815a09583d0189094831c0d2000015b53c42e715b8a104a92238f9472232416589883f819909b83340ea000015b4db52dd95609ee49721f0f6070231a15a89683ec18d09083040c2000015b47a22dc15249c047620e8ef46aa2f214e89083cc18409482e00c4000015b417c2de95709f649a21c0f4c6de30c14c89083bc17909083100c2000015b3b752d8150c9d24882158f2c6dc30e15789303d818b09403240d8000015b35722d114f09be48120f0f106c630915309443e818c09583180cc000015b2f812c794a89864611fb0ea468e2f414b88f03c818108b82d80be000015b29782d6953c9e849d2210f606ea314154892c3ca18109103140cc000015b23592dd156c9e848b2128f186dc2fd14d09043a417208882f40b8000015b1d4a2d7953c9d449721b8f5c6ea31615d89843ee198097831c0ce000015b17412d714f89d04852108efc6bc2fd15009003c418508d02e40b0000015b11492cc95009be4812128f046ae2f614b08e839617908a82f80c4000015b0b3e2da154c9da4852140f086ce307151091c3b417808c82f00ba000015b05302d095189d84902170f0c6e631515589183bc18809103140ba000015aff4a2c814d099a46e2078ec06b82fc14e09183d618608b82e40be000015af9352e0159ca0a4a82220f5c6e831415d09583cc18a097032c0ce000015af31f2d995489f04a42220f806fc32416389483e018409182f40c8000015aed0f2d815489ca48d2148f246ce30415509003cc18e09683200d8000015ae7232ca14c89a047120a8eec6b82fb14b88dc3aa17a08e82f00d2000015ae11a2cf14c89ac46d2098ef46c0303158892c3d618908f82c80b2000015adac82f39630a564c72320fb072033316409703fc19209803340d4000015ad4c02d115149ca4882128f186c82ff14a08c83b618109482fc0c8000015aceb42d5152c9ca49121b8f486d430e15589203da18008c02e40ba000015ac8c82bf14809884612030eb069a2f214988c439c17208802dc0a6000015ac2ca2d014f09ac47420e0ef46ae30214d89103ce17f08a830c0c4000015abca72df955c9da48220e0f046c62ff14f89083ac17a08d82fc0ba000015ab6972dd95809de4912180f406e031a15e09543f019509803300c6000015ab0892de158c9f649921a8f406e8313154090c3e418908d02c00ac000015aaa832d314b09a84782068e9067e2e4142888439016508202cc0a8000015aa4932c814bc9a847420b8ef06c430114f88f43ba18109583200b8000015a9e882d315389c64882140ee46a42f814988ac39a17808d02ec0c2000015a98692df15689f049a2180f286c630514e89083b818009683040c4000015a92462e09584a044a02260fa471232516689a840e19709883200ca000015a8c692c114a099e4722068ed06ba30615309183c218609182d80b6000015a865e2cb94cc9aa4772088ec06a82f814588a038a16c08382ac0a2000015a805e2cd14f49c44772100ee06a42fb14b08d03a417708882b00ae000015a7a2a2e9157c9fc4a62260fc46fc31a15d09483de19609783340c8000015a744a2c3149c98a46a2058e9468a2ec14a89103c2186090031c0ba000015a6e5d2c694c49ac47f2140ec869c2f614e091c3b217208a82c809e000015a68342db1558a084a62228f8c70431b15f898c40619c09603280d4000015a62112de15509ea4902190f286e6311154891c3c6182097832c0c2000015a5c1e2cd94f89b647f2168f1c6d630f15309443ce18309283100b2000015a56112dc15609ee4872168f306d630114d89003d8184092830c0d6000015a50152d395109c047b2118ef06b22f814d88f43b618608f02e40b4000015a4a072d214f49b247520f0edc6b22fb151890c3c418209102d80c0000015a43e42df1588a064a62290fbc70e31e157094c3e018f09803400e4000015a3dde2ce94e49c84882130f206d431115889343ca19309a83400dc000015a37f02c494d09a647320a0eec6b62f314608a43b016808882ec0a4000015a320e2c414d09a247220a8ecc6aa2f814f88ec3c618509483240c8000015a2c062d715389c849221a8f506d630415289443d818a08f03100be000015a263b2b9145c98046b2078edc6a22f314d08b43a217b08e82d00a4000015a201e2e615849f249b21e8f7c6ee312157894c3e419b099031c0ce000015a1a042d915649ec4982180f3c6e430f153091c3c017d09102f80be000015a14072c914ec9b046e20a0ecc6c8303155091c3d018c08b83280da000015a0e042d615509d64872160f186d030315089083c018309403200bc000 else 0x15d0c2e2e495b8a1c4ae2200f946f630b15209203d218308e82b40b0000015d06252d1152c9ca4862190f386f431b15b093c3f619109682f40c0000015d00252d214f89b247820a8ed46a82ed14488d83ae17208d03100c6000015cfa372c514809764631ff8e806882e514788ac3bc185090831c0c6000015cf4242de15749f449821d8f8c70e32c16209883ee18d09182d00b2000015cee092dc153c9d848b2180f5c6f231515d09443da18d09282fc0d2000015ce8422b494089504471fa8e6067e2e114308d43ca17908b83080be000015ce22c2da152c9c84872138f2c6d630315289203d418008c02d80c4000015cdc572bb147897e4682038e806902f314c89083b217708f02ec0b6000015cd6422dc95689ea4a121c0f5870231a15789443f019909a03180c4000015cd0652c695109c04822170f386e6311156091c3b818709883240c6000015cca3e2e0158ca264a021f0f486f030f15989183d819909783240d0000015cc40b2eb95d0a164a32230f9870832115d097840019e09803280d0000015cbdfb2d915209d648f2180f446e830f15889303d218509503300ce000015cb7db2de956c9fe4a221e0f646e830d15589103d418a09382ec0b8000015cb1f62c814a89884692010e846a02f014b08e03a617608f82e40c6000015cac0b2c794d099c47120c0ed86ae2f614b08c83b217208982f00b4000015ca5f32de15589f249721c8f686ce303156891c3c418809603000cc000015c9fd52df95849fc48b2128f006ae2fa14c88f03c218e09c83440b8000015c99c02dd15549f04932188f006b62fb14a08e43a816f08b82d80c2000015c939f2df15309dc49221c0f646e631a15a09043ae17a08d03240c6000015c8d8c2d815609fe49e21b0f246dc30f15609203d418b09502f80c6000015c879a2c414989a647920f0eec6b82f813f088c39217509182fc0ae000015c81932d215009cc4892148f386e831b15a09543d618f091830c0c8000015c7b632e51588a164a321c8f406dc31715d89743fa19509c83540d2000015c757e2c214c09ac47e2128f346de31c15d096c3ea19f09e035c0c8000015c6f7a2d715449da4932140f406d831515a89403d418309203180d2000015c69822cd14e49be47b20c8ee06ce30b15188f03ca18108e82fc0da000015c63872cd94d09b447620d0ed46ba2ff14c89003d018209383000d4000015c5d842d495449c84812148f106ba2fc14c08f83ca182092030c0be000015c57772d915309e64892090ec46ae2e814508bc39e16d08a82cc0b4000015c514f2dc95589f849a21e0f786e4317160896c3dc19109a03100b6000015c4b232e715d8a2a4ad2280fa870633016389743ea18c09282f00ba000015c452c2cd14f09a847720a0ed468a2d7137886038816208602b40a6000015c3f062e3155c9e249821a8f5c6e030a150891c3d6186095831c0ca000015c39052cc14d49ba4822138ee86ce30515609143ba17b09082fc0bc000015c33062d1950c9c847d2150f106c830915088f43b818108c82e80c2000015c2cf42d5153c9e248b2130f146c030c15208fc3ca17c08c02e80aa000015c26ec2d195249d64842108efc6d230e15409483dc18a09183200c6000015c20e82d515249cc4872158ef46be30015008dc3ae17e08e02e40b4000015c1ad02dd9578a084a22208f7470032615f89503be18809483180d0000015c14e62c6949097a4571fe8e846a42ee14708b43a617708d83040b8000015c0eec2d215309e648f2150f086be30115189303cc18809402f40c2000015c08fa2c694d899e47b20d0ef06b42f314988ac38c16d08c02c00b2000015c02ed2dc15709fa48f2170f686ec30f15609203d418609282f80c4000015bfd0c2c214a098e4621ff8ee46b02fa15189043d018609583300ce000015bf7072ce15149c447f2110f046b82fe15588f83b417e08f82e40a0000015bf0f92d415109b047920b8f1c6ba30715789303c218b09683100c2000015beaf32d015049da47f2138f406b630015109043be17b09083140c2000015be50c2c414b89a046c2068ec86be30215489243dc18809083080c0000015bdecb2ee95e8a284b52240f746f231c15f896440019a09a832c0d6000015bd8bd2d595249b04792110f106b030815589403ca17d09103180cc000015bd2bc2d015109b646d2070eac6922e313e089839416b08902dc0b2000015bccc32ce14d49c84802098edc6a62f814e09043ba17408602d80c6000015bc6c22cd94cc9b847a20b8ee86ac2f614b08ec3ae18209183000ba000015bc0c32d095049b246d2040ecc6a230215609243b817908e02ec0b2000015bbad22c414e89b647220a8ebc69c2e914608a03a217108c03000c0000015bb4c62cf14b897e46b2078edc6a02f514d89003a817d08e83200d8000015baebe2d315189c84892150f146de30e15789443ca182095031c0c6000015ba8aa2db95589ec48e2120f206cc30b15989683e218909003040c2000015ba29a2d895209d04862198f346e030615409203c218709683240ce000015b9ca02cb14f89ba4772080eb46a62fc15309143ce17e08f82f80ce000015b96972d815489ec4892148f086b62ef14988a83b017b09103100d8000015b908b2d1150c9cc4942158f086c630d15109183c817f08b82e80b4000))) else (if i < 223 then (if i < 221 then (if i < 220 then 0x15e8e4d2ce94c899846f2080ec469c2f314688a43aa17f09103240c4000015e88332df15749fe49e21d8f546f230a15789243ba17408d82d80ba000015e82052ea15aca0a4a221e8f446e030b15809283d417d09282fc0c8000015e7c002d1950c9da48220d8efc6bc2fc14d08c43b418609503300d0000015e75fd2d495289c64912198f546cc30114c08f43ba17d08e82fc0ba000015e6fe42da95249d448d2150f106c22f815209243ce18408e831c0c2000015e69e22cf15149b847820e8ed46b22ff158090c3ca18609883340e0000015e63eb2cf15089be48220e0f006d630815889543c0187092831c0ce000015e5dd42d795289e048820e8ed86b02fa14a88d43b017608c02dc0b0000015e57d62cb94cc9b648320c8ef06ae2f714f89003c217908b82fc0c0000015e51c02d5955c9f84912188f3c6cc30814f08fc3b817908e02dc0bc000015e4bbb2d595089dc48921c0f2c6d230a154091c3ca191096032c0d6000015e45fb2ae14289624541fa0e5c6862ed14d88e03b417f08b82ec0c0000015e3fe02da95649f448e2160f106ca30514e08d83a016408682a80b4000015e39fd2be949099c47120a8ed46a42eb14988e43ba17508702c40a6000015e33d42e715d0a0c49f2238f9c70a31915589543dc18909003140ce000015e2dec2c714b09a647c20d0f0c6ba2ec148087839816c08382d00b0000015e27a82f01604a464c522e8fa871c31c16089b441e19b09c83500da000015e21b62c814d899e46f20a8ec46882f214888cc3ae18009183200ce000015e1bd72c294bc9ae47b20c0ef46b02fd14d89083c418a09403240ce000015e15d82d294f49c648b21c8f506e630e15589303d218a09002f00c4000015e0fe42cb14e09a046c2070ebc6b02f414989203e018e098831c0c4000015e09ea2cd14f49d04822168f6c70030d157892c3e619309803300be000015e03d12d815049d24862120f046d230114d88dc3be17e09283280c2000015dfdd02d215349bc4852110f046be31015b09543f419609783140ca000015df7af2de15749f04922168f046ce30015609503d817908a830c0c4000015df19a2d795209da48d20c8ea46722dc14008a039017208982dc0b4000015deb7e2df15509e248720f0edc6a82f714e88f03ae18508d02f80c0000015de5572e51598a1a4b22240f9c6f630e15389303ca17e09382e80aa000015ddf5b2cd94cc9a24692020e8c6782e614488b43a817808c02dc0b4000015dd96b2ca14e09a24722070ebc6be2fe14c88d439a16e08a82d00c2000015dd3652d595349d648b21a0f686fa31e16189983ea18609282fc0b8000015dcd6c2cb14e09b24792100f0c6ce31315509343e018309203080c2000015dc75e2d515309d24862160f346dc30f15989583e018808a82cc0b2000015dc1512d915409d448c21a8f3c6d630b14d88dc3ae18008c82f40ac000015dbb412da95509ee49521d0f5870031c15e89403ea19709c03340bc000015db5532cb94d09a447820d8f086de31815989683d619009983440d6000015daf512d315109ca47c20e8f0c6dc30915608fc3d218909503140c0000015da95b2cb14ec9aa4722060ed86ac2fc14c89083c418809803300cc000015da3742c514989a046f20c0ef06ac2fd15209003c417b08c82f00d0000015d9d732d715289ea49a21d8f8071231b15a096c3e018208d83040b8000015d975f2d915389e24922168f346c830e15489183c018608c82e00b6000015d91522d8154c9e84892150f146be30514f08e83ca17c08d02d00c0000015d8b4c2d294f09bc47e2140f006c82fd14d88dc3b217d08d82e40c0000015d854f2cc14d89c04822108ef86b82f314388ac39e16f08a82bc0b8000015d7f3e2d595189da48720b0f086c430214f891c3d618709603440ce000015d79322d395049b847e20b8edc6c22fa15188f03a618108f02e40be000015d733e2c514d09a046b2040ea46962f314a89103ce189093834c0ce000015d6d332d7154c9ea4852148f2c6ca2f514c88f03c0185098831c0c8000015d67042e79590a044a72210f9470031315889503f61aa0a283380d8000015d60ee2d995309c648d2140f1c6ce31315809583f218c09503280c0000015d5af52d195309cc48a2128ec86c430415289183e018509183240b4000015d54e72d795389d448b21c0f746f431915a89503d818109082fc0c6000015d4eb42ee15c8a2449e2200f886f831615709643dc19309d03480ca000015d48912dc15509e448220f0f106c030515088d43c0185093030c0b4000015d429b2ca14d89ae47b20d8eec6c230b14e89043b417308b02d00bc000015d3c9d2d395149cc48120d8ef06a62fa14c08d83b017808c02f80b4000015d367e2d915549fc4a32210f806f432516489b44101a009c834c0e0000015d30662de95549f24a62218f846fc32516209783f819309a83200da000015d2a3f2e09580a244b222c8fb0716326161899040819f09983200c2000015d24402cd94e49ba4832108efc6ca30715308f83c017f092031c0c0000015d1e512c714b097c4622000e886802e113f888c39e16e08d83100cc000015d18352dc95689ea48520f8edc6be30415189243a416b08c82dc0c2000015d125c2c294b499646d2050ebc6a82f614988b839c16308402dc0b0000 else 0x16010682e6158c9ee4922170f386ca30815089143dc18f08f031c0d000001600a592d895409da4892198f5c6e831315a89703f4195096831c0c2000016004322e315a0a084a321a0f546f031315288f43c818509183440ce000015ffe062e495b4a0649d2210f706fa315159895c3fa19a09a83480da000015ff7fa2d8950c9ce4892178f3c6da30115089143c218508d82e40b6000015ff21b2c2947898a46c2018eb06a42ec14488c83a817308d02f00c0000015fec092e2957ca084a62210f9c71a329164897840619009983580d4000015fe5e92dc95949ea49721a0f446d02fb15309183b617f08d02dc0be000015fdfd32e2157c9de48c2140f286dc30615209183cc19409503300c8000015fd9d52d194f49ae47b20c8edc6cc30a15689003a217f08d82e00b8000015fd3b62e0155c9e44982188f2c6d631515488ec3a416c08902e80b4000015fcdb42cc95249c84762080ee46b830415489203e218e09a03380d2000015fc7972db15609e64902180f3c6dc30414c88e43b817e08c83000ba000015fc18c2d395449ea49e21e8f506ea31515889243be17b09103080be000015fbb952c494b49a847a20f0ee46bc2fe15108d03aa17b08902dc0b6000015fb5632e695b0a024992190f606dc30a15688fc3c818409603580d8000015faf4f2d715309ea48c2160f4c6d431115909583ee18c09903340d4000015fa9562cb94d49ae47c2088ec46ae2f914788b439a16d08682c40b4000015fa3872bd94589724561fc0e746822ed14688b03ae178090831c0cc000015f9d8d2cb94dc9aa4742098ef06ac2ea14a89003c217d08c82f00d6000015f97742dc15549e648c2138f246c22fc14d08d83a617508c02d80ce000015f915f2dc15689fc49f21f8f406e231615889103ce18709183380c6000015f8b372e015849fc49921c8f3c6c830414b89043cc182092030c0c8000015f85272d915749f249421c8f546e031515d894c3e418409082e80c0000015f7f172dc95289f04962120f1c6c230114c08f83a817f08d82fc0ba000015f78ff2da15549ec49c2178f706e430b15889183e619509603180c8000015f72c52eb959ca144b52248f806f231815d09703ee18c09683100c8000015f6cca2d194f89bc47b2080ecc69a2f114e08fc3ac17508f02e00b8000015f66be2d415249da49121b8f386e2311158893c3c419309603080ca000015f60b32dc95609e64902188f346d830e15b095c3e81a4099832c0d2000015f5ad52c014ac99847020e0ee86ba2fc14c88fc3a617209003100ca000015f54d32d114f89a847020c0f006da30f156090c3aa17c08f83040b6000015f4edc2c414ac99446920a0ee46bc2f014408b83b017608d83200d2000015f48d22d4954c9e648a2160f246d430515488e83c8190095830c0ba000015f43002bb945095244f1f58e086502ca138087438617108a02b009e000015f3d042d195089ce47920e0f046b62f314d88f83bc18609483040be000015f36f72d615189c647a2098eb069e2f014808e83aa17908f832c0ce000015f30f42d2152c9b847d2130f246bc30815409403c8187093031c0c0000015f2af72d215409da49121b8f406d431515709143ae17008a02cc0aa000015f24c02eb15c8a1c4ae2290fe072e33316609a040819e098031c0cc000015f1eeb2bd94a499a4702070ed46982f114d89003a417908f030c0bc000015f18cc2dd95749fa4a42220f8870c322162099c41219209282ec0c2000015f12b42dd155c9fe4a62260fb871a32415d89543de18d09103180c2000015f0ca42d615209dc48a2140f186c830615489203c217908983040b0000015f06a52d1951c9da4912140f086c630c15509243cc18d09783080ca000015f008b2d795289d848f2170f286c42fb15209343ca18709082e00ac000015efac32b6143895e44f1fc0e786702e114688a039817008d82dc0ae000015ef4be2d795009d24832128f006c430315489183c017f09383300c0000015eeeac2d6951c9c648820e0efc6b630215109043c018409403200d0000015ee8ad2cf14f49d248a2178f2c6e831015609503de18209283200cc000015ee2a62d9153c9d64842128f186b42ff15189243bc18009603300ce000015edcae2c694949864641fb0ea86922f514708b439617508902dc0ba000015ed6b62ce950c9d449721a8f546ec30a15289243c218209183180dc000015ed08d2de15b0a1649d2260fc870e323160899040219809a83240dc000015eca812d515409ee48f2180f506f232115f09543e618409203180ca000015ec4852cf14f89d047b20e0ed86b62f915108e03b017608803000be000015ebe712dd15609ec4982190f146d630214f09203c217e09583400d6000015eb86f2d194f49ca48120a8ecc6aa2f914c88c03aa17508782c40a4000015eb2872c494b89864632030eb06aa30314a08e83b817308e02f40be000015eac852d215209bc4872158f3c6ea31315009183e419109282f80aa000015ea66a2dd95449d64922220fb070631a15e89843fe19509383300c8000015ea0662d3950c9b647d2098ed86a42f414c08d03b017908e03040b2000015e9a402e295a0a2c4ae2200f706f630e15789383c217c08f82e80b6000015e94472ce94f49ba47a2128f006ca31015c092c3ce18709403380d8000) else (if i < 222 then 0x161927c2d214dc9ba47620c8ef06ba30515488fc3ac18309183140c200001618c632d8952c9d84872140f146d030415109043d018709383100c4000016186712ca14fc9ea4902160f386ce2f414e08f43ca18708c02f80b4000016180532db95589da48e2150f506c62f814d09143c218008d83280c000001617a452dd95789e648f2188f506f231d15c89443c818108a82dc0b8000016174072ec95e8a344c322a0ff872a32e16709b03f218509402fc0c800001616deb2db95509e04902150f4070432216009944081a409f03600d2000016167cf2d815349e448e2120f046ba30f15689583e819c09b03340d0000016161d22ce15049b647c20c0ed46a42f814b08a839c17208802e40ae00001615bd62c994cc9a847f20d0efc6c6310159893c3cc17c08c82f80ba000016155e22c914bc99646b2068e986962f515089043a417b08b83000ba00001614fd82dc15449d44852100f1c6b230015108f43b017c09083340cc000016149d72d295049bc47e20e0f006a42ff15489203d818809083040c6000016143d92d0151c9c04792078e9469c2fc15189183c618509103080c400001613e0f2b9944c97c4691fd8e906862ea13e08b03a416e08882d009c000016137ec2e29594a204a32240f7c6fc31e15a09243ce18e09803340ce000016131cb2dd956c9f649f21c8f646f631f161096c3d418808c82dc0c600001612bd92cc14f89b848a2148f2c6e430415609203ea19509183080c0000016125b62e29590a144a22220f7c70232415b094c3dc18808982e40be00001611f822e295609ee49021c0f586da30815209083be18209103080aa0000161198c2c5949c9944672020ec86902e514708b83a817708802c80b0000016113ac2bf947497e4632010e9868e2f014808ec3bc17a08d02dc0b600001610db42cf95189d44862128f146ce31515989583dc19109783440d4000016107bc2d094fc9dc47f2148f106ec31115289043c017a08d82ec0d00000161019f2de15509ea49221b8f7070431615909203c217b09283100b80000160fb992d315309d24982178f4c6e431114f88f43b617b08b82fc0bc0000160f5822dc155c9d24912200f94714323160098841219309d83540d80000160ef672dc95589e648e2180f546dc30f15b89383da18909703400bc0000160e95c2d495589d44832138f286e631115309203d018508d82e80ac0000160e3522d595189bc47c20d0ee06b02f414c09003c018809703200d20000160dd2e2da9570a064a621a0f406d230c15689403d417e08a82f80c40000160d7352c994d09a647620a0ed46a02fa15289303de18009002f00be0000160d0f82e91598a0c49a21a0f206e230b15409583e819509a83140b80000160cb042c6948c9a646c20a8ee06b62fa15008ec3b017f09702fc0c60000160c51c2c894e09a446c20a0ef06ac30214e09043c819209203100be0000160bf312c2148c97445e1ff8ea066e2d513f088839616d08602d00be0000160b9252dc15609e248e2160f406ea312158894c3e819909b03140ca0000160b3112dc9588a084a82248f846f631515b896c3de18d09583100c40000160ad102d015449dc47c20a0ec86a42f214888f83bc18509202f40b20000160a71d2cb14e89b04762120f3c6d831415e095c3da18408e82fc0c40000160a10d2de15509f049e2198f386ce30a155891c3c218c09103240c000001609b1d2c294d89aa4742108f146b42f714d08cc3bc18a09c03140ca000016095172d6952c9ce48d2188f106c42fc15089043c0188092030c0cc00001608f0a2d915409d648f21b8f6471632015909483d619609983380de000016089192cc950c9c647a20d8f106ba30015389483e0187093031c0dc0000160833a2c394a097e4642020eb86b62fb14e88e43b818208c82d40b800001607d462c394909964612098ed86ae2f414a88ec3c418408e82bc0bc0000160773a2d795049c44842120ef86ba302152890c3bc18709383000c2000016071162dd9584a084a721f0f906f831115589303ce18b097031c0de00001606b1e2c714c49a84742068e986ac2ec14c09103d219009a03380d6000016064ec2e415c4a364c02260fac70c31c15b89583e218508b02e40c000001605ee92d395489c44802110ee06bc30315689683f2190095830c0b8000016058fc2c394a499c47b20f8eec6bc30214e08a43a617208c82ec0bc000016052d92de15649ee49721b8f386c630815308fc3b817108f032c0cc00001604ce52cb14c899c4772098ed86a62fa14888d03b417508702c40aa000016046c32e495d0a1e4af2220f746de30d155091c3b618308e82c40ae000016040c32d194fc9b04842148f3c6d6300152893c3e819508f83040ca00001603ab62d115009e048f2178f206d431215609703e418f09a83380d0000016034da2c014a89b047920f0ec86902e714408b83a216608b02f00c400001602ef12c2948c99245f2028ea06962f714e88d03be18008c02fc0be000016028d72db95649f449721a0f6c6ea315159892c3e0197098835c0d4000016022cd2d795389ec4912160f2c6e230215489183be17708d02d00b600001601cb12dd95649fe4ac2240f886fc31315889383e819209903480d20000160169c2da95709fe4ad2258f7c6d231915d094c3d618209303240c2000 else 0x163144f2c194809624541f98e4c66e2dd14288a439817208802ac0b000001630e3e2d795289c247c20f8f146c42fd14d09003a017808a83080cc000016308382d094e89be47d2120f306ec31b155093c3c618209182dc0bc000016301f62ed95e4a1a4a92288fa86fe31f15c896840419d09e832c0d40000162fc052c814ec9b447e2090ef86b02ff15109043d218a09283200d40000162f6242bc944097c4581fc8e886782d913d089c3a217b08a82d40b00000162f0142d2951c9ca48020d0efc6d430615409143b618309283180bc0000162ea1c2c494b09ac4792090ed46b02fd14b08e83b818208d83100ba0000162e3f72e595649e849a2198f206e030115789303ce18008c82e00c00000162de0d2c514c09a447c20f0ed46902e714888a839417208b02d00a80000162d7e52e015609de48c2148f0c6d230815888fc3ce188093834c0d00000162d1c72e395aca0a4a421d0f606d830c14f08c83a817708902bc0b40000162cbaf2dd15689ec49121b8f646f431b16189783ea19709a03080c20000162c5e02bb14709644471f28e2866e2e314d88fc3ce18608f03000b80000162bfcd2d195089c84802100f006ce2fe15409043b416e08502d40b40000162b9b72db954c9ee4992198f506e631815f09403d8191095831c0be0000162b3b62cf94e49b247d2118efc69e2f314708cc3a817708e82fc0c80000162adb12ce95109b847e20d0ecc6bc30215409243b017208d82fc0b40000162a7ab2d114e09a44742078ee46a82f114888ac3b017e08a02f00c80000162a1c12c614a49aa47620b8ecc6b02fd14d88f83bc17f08f03140d600001629beb2ba144898046f20b8ef06ba30315088e83b617208e83240ce000016295ae2ea9588a244b62288fc86fa31815e89483b617e08f82ec0c400001628f7a2ee1604a4c4bf22e0ffc73e33d16409903f019209683400c0000016289672dc15409d44962168f386d230e15689143d019609082f00ae000016283582d715509ce4892158f1c6b62f515089003c617708702e80b200001627d412d395289be47620d0ecc6be302156091c3d419709403000da0000162773f2d8153c9d84882160f3c6d431615c09743e419409803080ce000016271352cf94c89ac47820b0ee06c230514f08e43ba18208f82e00b400001626b352d095009c248e2110f046b02fd15088f43ac16f08b03080c80000162654f2c394a499446d20c8ee06ac2fb14888cc3b217a08802f80c800001625f5a2cc14c49b24772118f206be2fd153091c3cc18109483080bc0000162594d2d7955c9f449a21d8f5c6d030a15389003be17b08e82ec0ba0000162533d2d595349e249c2178f546c030114a08f83c417c09303200d000001624d4b2cd14d09ba4862178f2c6da31c15809183c018109083340c80000162473d2d1950c9d64842110edc6a22f114a88ec3b418309103280d80000162412e2d695109d048f2140ef86b42fb152093c3fa19109283000b400001623b092e195789ea48921b8f306d830615789483d018809303100d2000016234f62d395309be4862138ef46bc2f814d08e83bc18709403140b600001622ee22d915309d84872148f586e631615d89a43e417e08e03140ca000016229002bb94949a24662020e8c6922ea14288b039417308c02e80b4000016222da2e39598a004972190f386d030115108e43d217d09103200bc00001621ce22d195089be47420f0ed86be2ff151892c3be17908b02ec0c0000016216d52d5150c9d64952178f146e030615209243cc17f09182ec0b4000016210ec2c2149097e45d2028e8467c2db13f08943aa17608e82f00cc00001620af02cc94f89c84832110f086c430014e88f83c617f08d02e40b0000016204c62e415c4a384a72250fac6fe324165096c3e418b08f02e80c00000161fec92d314f89c44872108f146d431015809243da18c09583040be0000161f8da2c614b09984742090ed06922ea14988c83a017308e02d80c00000161f2e52ce150c9d84872188f506fa31615c89743f419a09802fc0ce0000161ecdc2d8155c9be4732080eb06b230614c88d43a217808d831c0d40000161e7082bd946c98046e2090ed86a62e9147089439817208982d00aa0000161e1052d095289bc4862160f406d830014d88d43bc17908d02f00b80000161dade2e11590a0c49221b0f446d630f157893c3e219309d03380c40000161d4cd2d315189be48420b8eec6b42fb14e08f43c217b08e82f80bc0000161cead2dd95509fc49d2208f906ea30f15689483da19009a83580d60000161c8a72cf95089b24752090eec6b4302154890c3e019509483240bc0000161c2ac2cd14e49b647c20f8f146c430c15589583f018708e03100b60000161bc912de956c9ec49f21d8f806f4303152090c3cc17a08a02e40ba0000161b6a82cf14fc9b447b20b0ef86a62fd15188e43b017b09102ec0bc0000161b0b82c0949898446a2060ec46ac2fc15208e83bc18b09103200c00000161aaa82d0951c9c848520d8ef46d030315109003ba17d08e02e40b00000161a4b32ca94e49c44822160f2c6d631315108fc3cc18609783300b800001619e932e015809fa4972188f3c6e031615a891c3e818f094830c0bc0000161987c2d8955c9ea49a2180f2c6c830115009083d218d09983440d4000)) else (if i < 225 then (if i < 224 then 0x16495e62d4150c9d848d2120ef86dc30314d89183c417808a830c0ca00001648fc82db153c9de48d2198f686f831615a892c3dc18909783340c4000016489bf2d995709f24a02228f646ce309155890c3d618009082e00b6000016483bf2cb94b49a24682088edc6b42fa15309183c6181097035c0de00001647dda2c914e49b04872158f086c030715309243b618109183140be000016477db2cb95049b847c2110ef86ca30715309283dc19009303240ba000016471d72d0151c9d04902178f346ce30514e08fc3c018709c03380d000001646bcb2d215049b44812150f386da30e15809543d618a09683300bc0000164659f2e2959c9fe4a021f0f746dc31415e096c3f618e09503280b800001645faa2cf14dc9b04822108ed06ae2f014808a039617508982d40a2000016459a92d014dc9b648020d0ee46ae2f614e08f03d018a09203040be000016453842e495b8a304b82280f9071031715a89583e618f09403280d000001644d972c714b49a246f2080ed46b22f615089303d218408d02ec0ca000016447c22be145497a4591fd0e806882e814788f03cc19109983240b8000016441de2bd946097c4571f98e446642dc14188a438217108902cc0b400001643bee2cc14bc9a047120d8ec06ae2ef14a08d03b017708d82c80b4000016435f22ca94e099846e2048ea86942f114988d03a417808f83200d600001642fd52db95749ee4902180f6c6e230615409083c418209603300c6000016429bb2dc15649ee4912138f2c6de30d154095c3d418a09382fc0a4000016423db2c714e49a846f2080e7067c2e214308bc3a617508a02f00bc00001641dbd2da95489e248620d8edc6ba307153891c3be17808d02f40d4000016417cb2ce14e49aa4752038ea869c2f514b08c439e17008982dc0bc000016411c52d395389d047d2138f0c6da30b15589143be17408a02b40a600001640bd62c894a09984662058eb86882ed14788d03ac16a08682c80bc000016405d92cb14d89ae46820a8f086b02fd14e88e03bc18009802fc0ce0000163ffb52e615889ee49f21e8f8c70431d15c89643e6191097030c0c60000163f99e2e4959ca024a821f8f646f231115709703f019609783180ba0000163f35e2ed95eca304bb2270fc471232c16489a44181b009f83500d80000163ed352e495a0a004b12248f8870e32315b09603da18509303280c60000163e7312cf15049ce4872138f2c6b82fc14c88f43a817808d83040ca0000163e1202d395109c647d2128f186c8303153892c3de19a09983300d40000163db202cd94f09c248520d0ebc6c630114e890c3bc17e09102d40a00000163d5182da95609f24922170f286be2fe151090c3d418608f03040c20000163cf372bd14989924632020e8c68e2ed14688dc3ac17508e82fc0cc0000163c9432c714b09aa47120e8ec869e2ea14988f83c218309482d40c20000163c32b2da15349da48a2140f246c230e15709103c418709803080d80000163bd382cb950c9b44732090ec86b02ed14488b839417208d02e40a40000163b7452cd94e499a47220b8eb068e2ec149089c3a017508d82f80aa0000163b1512d094f09c24842188f3c6e631615b094c3ea18e09a031c0c00000163ab602ca14b49a647a2070edc6c02fc14e89003c017b08b02c80b80000163a55c2d5954c9d04852100f006c02fe15209103ca19509d035c0d600001639f572cf95249da49b2168f086d630315489143d218e09502fc0bc0000163995d2cb150c9d848b2160f186d430614f88f43ba17808c82e40be0000163935f2d015149b848220a8ef06c02fe15089283ac17808b02e40ae00001638d2f2e515c0a204ac21f8f7070431c15a89443e419109883340ce000016387322d515209d44932100f386ee30d153895c3de19309a83500d80000163812b2d615309dc4892168f206d030a15689543dc19009a83380d800001637b182d715189bc47920b8ed06aa2f614e88dc3c018309903280c4000016374f72dc157c9d44962150f206ce30614f08e83b017608c02f40b800001636ee72cf14b89aa47a20d8ed86a62f714b88e43cc18909183280d8000016368ec2d095189cc48120d0ef86bc2f814988d43a817708e02fc0b4000016362e92d315509e048b2160f386f231b15f09403e018e09483040cc00001635cd52d815389ea49c2178f386ee31115809303dc19109883180b2000016356bd2d715389e44952180f446ea31915889443da18609302f00c0000016350dd2ba14589644531fb8e546842ef14708c43bc17809403040c600001634acd2d9155c9e649821d0f7c70032316089883f419609a83240b8000016344a22de15789fe49c21b8f486de30b15e09683f218f08f03040c000001633e8e2db95609d848c2170f406d231215b09543e018f09783400cc0000163387a2d715289ca4782120f046be2fd15689443e219209583540d60000163325c2e2157c9f049c21e0f8470030b15c09503d818f09a03440be00001632c412d614e49ca4872120f146ca30615289083d4195096032c0c4000016326302da15549d448d2168f386dc30b15809543e019109482fc0b6000016320272cc950c9d248c2118ed86ba2f114608dc3c817f09002fc0c400001631a302ca14fc9b848c2148f206c42fe14b88dc3c417608c03100cc000 else 0x16618e32e415909fe4a22218fa070e32a167097c40419e09703200ca000016612b32e4959ca104a221a0f50700320162099440e19609803240ae00001660cc12cb94e89ca4802138f246d82fc15709203c617608d030c0c4000016606912e615889f049b21a8f586f031816089983f81a209883200ca0000166007f2d615289d04832130f0c6d02f815589283d218f092832c0bc0000165fa892c694b89b44822148f1c6ca30514a89003c6181094831c0ce0000165f45c2e515789f449e2200f78702318160897c3f218a09383040aa0000165ee622d094f89c44902160f346e030715809543de18709503080d40000165e8722ca94bc9a846b20b0ed06942e714408d03aa17e08c02f40c60000165e2462de1590a0449b2190f3c6e631c15909403ec18b09603200be0000165dc452d5951c9d04832110f046b62fc14b88bc3bc17708a02c00aa0000165d6312d915549f049321d8f606ee316157092c3d018909483140c40000165d00a2e795bc9f849d21d0f6c6d630e15389143bc18209483400ca0000165ca052cf14d49b047b20a8ec46ba2f414888ac3a8183095034c0d60000165c3d72df95909f04962198f386ee31a15c094c3de19009a83180d60000165be072b9145c97e4662060ea06902f114b08e83c818109303100c20000165b7f52d895189b847a2100f086ba30014d88f83d017c08f83040c80000165b1fa2d615609e449c2198f446cc30214f88ec3a017308a82e80c80000165abf32d4151c9c447e20f0f086da30815b89783f219909a83440cc0000165a6022c714789824692028e786762e0141089c39016308502cc0b200001659fe92d795289c648c2170f3c6da30a15088fc3b817608b82d00a2000016599e72ce14e89ac4692008e8c6782d3140888037616408182b40aa000016593e22c914e89a247820d0ee869e2e714488d43c218009283340d600001658dc72e015649fa4a42220f7c6fc32b16689743f419609803440b6000016587b62d615349d448821c8f486ea31a15b89503ea19309603300c4000016581b82cc14d499846d2018e706882e014508ac39417708c03240c400001657bc02cc14e499c4722078ecc6b22fb14f89043d218a092033c0ca000016575cc2cc14e49cc4772118efc6ce30c15608ec3b617608682d00b000001656fdd2cb14d49b04732038e906902ea14488c83ae17708c02d40a4000016569b82dc9558a0649f2218f546ea31415c89543f419b099830c0c2000016563c02ce14d89aa47e2170f386e231115189183c217a08e83100bc00001655d9a2e195b4a224b32288fd471c32815d09683e219509503100d00000165577a2e6158c9fe4a32200fa86ea31615a09403d218808d03080ca0000165517f2c994bc9b84882168f306c630915809443f219509903280ce00001654b7a2d115009cc4832140f2c6d831715809703fe19909403080d40000165455c2de15a4a364b62298fd873433816789c840e1990a003500e200001653f522d695389d849021a0f7c6ee31615b894c3ee19409503600de0000165395d2c794c89a44732108f206d030615309083c218e095032c0c6000016533462e1155c9e64942138f006be30014a08f83b016f08a02f00cc00001652d2b2db9574a0449e2150f506f031e161897c404196094033c0ca0000165272b2d414fc9ac4742050ed069c2f614a88f83c818209402f40cc000016521372c794a899246a2040ee06ae2fe15209043b617508f82c40b600001651b482c694d49ac47020e0ee06b22f314b88c839a17d08c02f80c20000165154e2d114f49c647420a0ef06c830215309283c418108f82fc0c600001650f2f2de95689dc48120c0ef46b42f614f88d83ac17808982b40b2000016509182d3150c9c848020f8ef46c630e15909183ce18b091831c0c60000165031d2cf15189d648d2188f446da30c15509243ce18308d03000be0000164fd262c994bc99845d2008e786922ef14408a039616b08e82d40c00000164f6fe2e095809e448d2120f086c430514d08e03b817a08382b00a40000164f1062ca94b89b44742108ed06a62e614508cc3c218208c82e80a40000164eb002d4952c9d44802118f086c42fe14e89003b418008c82f80b40000164e51e2c3949898c46e2098ec46a02f314889043b818409703200bc0000164ded92f39610a304b12250f9870432515f09643ea19509803100d00000164d8a42e695bca224ae2260fa471432f16009443dc18809383180cc0000164d28d2d695209d048a2128f1c6e831615889503d418909082f00bc0000164cc7b2d894fc9c447d2110f106c630b15388f83b617b08f02e00b20000164c67e2d415309dc4832108ef86a42ff14988a03a016f08882dc0a00000164c0522e015649f44a02218f8470a32115f095c3f019809682f80bc0000164ba502d1951c9e048b2168f1c6dc30515188f43c6187093030c0c80000164b42a2db956c9fa49f21e8f986fe31a15509243d418208d02d00ae0000164ae0e2da95309c64862120f386ea31915a893c3da192099832c0c00000164a8162ce14e89aa47c2108f0c6d830014e08dc3b218109403180d40000164a20b2d8154c9d848e2140f246dc31115a09543ec194096830c0b400001649bf72da15789fc4962180f686d430114d88e43c618709002e00be000) else (if i < 226 then 0x1679a7d2de15709ee49921f8f546fa31615789443ca18209103440ca0000167947c2cc95109c64822128f2c6de30b15889503d8189092832c0d200001678ea42c414ac99c47320a0ed06b830815909383e419709983440ca000016788ad2cd94f49a446e2080ec06c830114f08fc3ba18009103200c2000016782722e915c4a0e4ae2240fb471e31e15989083dc18f09303040c200001677c902c2949499247820a0ecc6a62eb14e89103b818709202f40c8000016776a22c2948897a4632030e9c6982e414a08c839017709383140c2000016770962d795489ea4902120f2c6c82fb14b08f03b016e08703040ac00001676a642e515949fc4a021f8f686f431915c09443f019909503240c00000167647e2c414bc9b44792138f386de31415309103c618409203200ca00001675e822d115149c847d2118f346f0311154092c3c6184096032c0ca000016758832d094ec9ae4762090ec06b62fa15008c039e17608f03280d2000016752652de9584a084a021b8f4c6c630414e08d83b017308782c80b400001674c7d2c194a49a847120e0ee86c430515108e43d818e08f02d40b8000016746722d815289ce47a2098ed46a22f214b88bc39817d08402e40a6000016740822c894ec9b248020f0efc6d030415589143c418808e82f00b000001673a7c2d4955ca044a421d0f846ec31215008ec3c018709082f40b8000016734862ca14bc9964662020ea86a42f114e08f83c417408702d40ae00001672e972cb14e099c4601fd8e806782dd14288c83b618208d02f00cc0000167284b2ed95e0a2a4bd22f8fd472633316409943f818f095032c0ce000016722622c514d099446c2080ee06ae30214d892c3d8188091031c0c200001671c7b2c594b099446e20a0ecc6b62f715108b03a4177090830c0ba000016716882ca14d49ae48020f8ee46b02f214608d039616f08d82e80b40000167108f2cc94f89a647520c8edc6c230915089143de19609683380ce00001670a972d194fc9c84862160f306e630d15a09503de18209783340c6000016704862d295009c848c2180f486ee31e15d89783f819309983300da0000166fea32c014849784521fd8e806782e113f889039217308b82c80b20000166f8792e095909f64a32220f7870a31e15a093c3ca18708f82d40c20000166f2472e815aca104b422a8fe471032a16589943fe19e09b035c0c80000166ec552cf14ec9a846f2078ea06942ed14c08ac3a217308a83100b40000166e63b2d8953c9da49921b0f506d830b158095c3d418e09883340c00000166e01a2e0158ca0a4a121b0f586ee31c160898c40419309403080be0000166da0a2db155c9d848d2140f2c6c630215089043be17d09083100d00000166d4232c414ac99646e2090ec06942f114b08c43b417f08b82d40b40000166cdf52e695a8a044a62228f7c70c32215a894c3d018b09102f80b40000166c7f32d294fc9c648a2190f406dc30f15789303d619009483180be0000166c22b2b814409664592048ebc69a2ea14988d03c817a08c02e40ae0000166bc122d414f89ba47720a0ee86c02fe15189283d218609683200c00000166b6002dc954c9fc4932180f146ba2fe14c08d039e17408882c00a20000166afe22d8950c9b847620e8ef86ba30115209083ca18008f83100b80000166a9d52d9955c9da47c20a8ef06d630814e88e83ba18609483240b40000166a3da2c994d49b047c2108ef06ae2f914988c439a17d08f82d40ac00001669ddd2ca94d89ac4712048e946982ef14588bc39416b08302ac0a2000016697ca2d295049c247b20e8f0c6c42fe14c88d43b217b08782d40a6000016691d32cf15049ca4822108f046c430614f88fc39617008d83100ba00001668bb92dc1558a0449a21f8f786fa31516009883e619609d83540d6000016685922e095909ea48c20f0efc6ce30515689103de18f092830c0be00001667f922d2953c9d648620d8ee86c42fb14c08d03b818709482f00c00000166799b2cc151c9ec4892150f346d630a15909103c017f09183240d0000016673772e4157ca0649d21e8f7c6fe31915c093c3e219409882fc0c200001666d632d795349e44992180f246e630b15a09583ee19509502fc0d6000016667582d195289e248b20f0ec86a22f914d88f43b817b08d02e80ba000016661352db15409e049221d0f506d430215409203ca18709283480f200001665b282da95549ee49e2200f7870231b16289703e019109983480d2000016655132da15609e048d2178ef46b82fd14988bc39a16e08902bc0c200001664f172ce14f09be47c2158f286d431415b89403ca18509783240d6000016649292ce14e49c647f20c8ee06be2ff15708fc3c018b09383180ba0000166430e2de959ca144a721b8f1c6c230514e08b83b217f09003240d600001663cde2e895b4a164aa2200f806e830715088e03b417d09083380d2000016636b32e515989fc49921d8f586ec30a15509083cc18909482ec0ac000016630ce2c194b099a4702038ec869e2ee15009483da18c098832c0be00001662af82bd948897845c1ff8e886982f714b08e43ca18109002dc0c40000166251b2be149098845a2040ebc6aa2f714c08dc3ba17f08f02f80b000001661f072d6150c9b847420e0ee06aa2f814c08d83b217909083280d2000 else 0x1681f5000000000000002198f386ca2fe15109203da18d09003100c0000016819452d5951c9e84942188ef86c22ff14e88d83c218209003100be0000168135c2c694cc99c45c2030ec46882e614a08f43c418209283380b800001680d732c894b498447120a0ec06b22f914808b839617708702f40c20000168077e2cb94bc99c4742088ea869a2f114708cc3ae17c08d02c80a8000016801622e6959ca004a721e8f686de30b15589203ce19509303180dc0000167fb2d2e3959ca164a42248f746e831415789543dc18b094032c0c60000167f5242d795109b64722080ee86a02ed142089438016608b02dc0cc0000167ef202d014c49a447e2108f106d231015989683da18909583180c60000167e92b2cd14e89bc47c20d8f146cc30815b094c3da18f093030c0be0000167e3232d214f89c447620b8ee06b42f814d88e03ba18009402fc0cc0000167dd362c714dc99c4752080e986842eb14308a038416608502d40be0000167d71f2dc95789f84952160ee06c830b15809143d418d09083040ba0000167d11c2ce94e09a047820c8ef46ca2fa14708c03b817408b830c0d00000167cb0c2d515189d449221e0f346d431415b894c3e419109503200b40000167c5372b794489664562030e9c6922e214188b039216908802b409a0000167bef12ed95b4a2a4ad2288fb46f231815d09603e618809703480d00000167b8d82d995409e84982178f506e230915589143d817a09503300c60000167b2b62df15549f049c21e8f446de31315a09303d819b09203280c00000167ac9e2d8952c9cc4922198f086d030915809303d818a09603200d20000167a6752ea15c0a0649e2190f646d430715308ec3c418208e83080b80000167a0952bf947c9804641ff8e7867c2ee14488cc39e177091831c0bc000))))))))

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



private theorem b218642 : covered 218642 218755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218755 : covered 218755 218868 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218868 : covered 218868 218981 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218981 : covered 218981 219095 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b219095 : covered 219095 219208 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b219208 : covered 219208 219321 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b219321 : covered 219321 219434 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b219434 : covered 219434 219547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b219547 : covered 219547 219660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b219660 : covered 219660 219773 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b219773 : covered 219773 219886 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b219886 : covered 219886 220000 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220000 : covered 220000 220113 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220113 : covered 220113 220226 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220226 : covered 220226 220339 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220339 : covered 220339 220453 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220453 : covered 220453 220566 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220566 : covered 220566 220679 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220679 : covered 220679 220792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220792 : covered 220792 220906 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b220906 : covered 220906 221019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221019 : covered 221019 221132 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221132 : covered 221132 221245 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221245 : covered 221245 221358 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221358 : covered 221358 221471 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221471 : covered 221471 221584 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221584 : covered 221584 221697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221697 : covered 221697 221811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221811 : covered 221811 221924 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b221924 : covered 221924 222037 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222037 : covered 222037 222150 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222150 : covered 222150 222264 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222264 : covered 222264 222377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222377 : covered 222377 222490 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222490 : covered 222490 222603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222603 : covered 222603 222717 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222717 : covered 222717 222830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222830 : covered 222830 222943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b222943 : covered 222943 223056 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223056 : covered 223056 223169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223169 : covered 223169 223282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223282 : covered 223282 223395 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223395 : covered 223395 223508 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223508 : covered 223508 223622 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223622 : covered 223622 223735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223735 : covered 223735 223848 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223848 : covered 223848 223961 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b223961 : covered 223961 224075 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224075 : covered 224075 224188 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224188 : covered 224188 224301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224301 : covered 224301 224414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224414 : covered 224414 224528 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224528 : covered 224528 224641 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224641 : covered 224641 224754 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224754 : covered 224754 224867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224867 : covered 224867 224980 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b224980 : covered 224980 225093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225093 : covered 225093 225206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225206 : covered 225206 225319 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225319 : covered 225319 225433 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225433 : covered 225433 225546 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225546 : covered 225546 225659 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225659 : covered 225659 225772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225772 : covered 225772 225885 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225885 : covered 225885 225998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b225998 : covered 225998 226111 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b226111 : covered 226111 226224 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b226224 : covered 226224 226338 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b226338 : covered 226338 226451 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b226451 : covered 226451 226564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b226564 : covered 226564 226677 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b226677 : covered 226677 226790 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b226790 : covered 226790 226903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b226903 : covered 226903 227016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227016 : covered 227016 227129 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227129 : covered 227129 227243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227243 : covered 227243 227356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227356 : covered 227356 227469 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227469 : covered 227469 227582 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227582 : covered 227582 227696 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227696 : covered 227696 227809 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227809 : covered 227809 227922 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b227922 : covered 227922 228035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228035 : covered 228035 228149 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228149 : covered 228149 228262 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228262 : covered 228262 228375 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228375 : covered 228375 228488 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228488 : covered 228488 228601 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228601 : covered 228601 228714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228714 : covered 228714 228827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228827 : covered 228827 228940 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b228940 : covered 228940 229054 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229054 : covered 229054 229167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229167 : covered 229167 229280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229280 : covered 229280 229393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229393 : covered 229393 229507 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229507 : covered 229507 229620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229620 : covered 229620 229733 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229733 : covered 229733 229846 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229846 : covered 229846 229960 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b229960 : covered 229960 230073 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230073 : covered 230073 230186 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230186 : covered 230186 230299 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230299 : covered 230299 230412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230412 : covered 230412 230525 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230525 : covered 230525 230638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230638 : covered 230638 230751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230751 : covered 230751 230865 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230865 : covered 230865 230978 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b230978 : covered 230978 231091 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b231091 : covered 231091 231204 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b231204 : covered 231204 231318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b231318 : covered 231318 231431 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b231431 : covered 231431 231544 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b231544 : covered 231544 231657 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b231657 : covered 231657 231771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 218642 231771 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b218642 (joinCoverage b218755 b218868)) (joinCoverage (joinCoverage b218981 b219095) (joinCoverage b219208 b219321))) (joinCoverage (joinCoverage b219434 (joinCoverage b219547 b219660)) (joinCoverage (joinCoverage b219773 b219886) (joinCoverage b220000 b220113)))) (joinCoverage (joinCoverage (joinCoverage b220226 (joinCoverage b220339 b220453)) (joinCoverage (joinCoverage b220566 b220679) (joinCoverage b220792 b220906))) (joinCoverage (joinCoverage (joinCoverage b221019 b221132) (joinCoverage b221245 b221358)) (joinCoverage (joinCoverage b221471 b221584) (joinCoverage b221697 b221811))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b221924 (joinCoverage b222037 b222150)) (joinCoverage (joinCoverage b222264 b222377) (joinCoverage b222490 b222603))) (joinCoverage (joinCoverage b222717 (joinCoverage b222830 b222943)) (joinCoverage (joinCoverage b223056 b223169) (joinCoverage b223282 b223395)))) (joinCoverage (joinCoverage (joinCoverage b223508 (joinCoverage b223622 b223735)) (joinCoverage (joinCoverage b223848 b223961) (joinCoverage b224075 b224188))) (joinCoverage (joinCoverage (joinCoverage b224301 b224414) (joinCoverage b224528 b224641)) (joinCoverage (joinCoverage b224754 b224867) (joinCoverage b224980 b225093)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b225206 (joinCoverage b225319 b225433)) (joinCoverage (joinCoverage b225546 b225659) (joinCoverage b225772 b225885))) (joinCoverage (joinCoverage b225998 (joinCoverage b226111 b226224)) (joinCoverage (joinCoverage b226338 b226451) (joinCoverage b226564 b226677)))) (joinCoverage (joinCoverage (joinCoverage b226790 (joinCoverage b226903 b227016)) (joinCoverage (joinCoverage b227129 b227243) (joinCoverage b227356 b227469))) (joinCoverage (joinCoverage (joinCoverage b227582 b227696) (joinCoverage b227809 b227922)) (joinCoverage (joinCoverage b228035 b228149) (joinCoverage b228262 b228375))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b228488 (joinCoverage b228601 b228714)) (joinCoverage (joinCoverage b228827 b228940) (joinCoverage b229054 b229167))) (joinCoverage (joinCoverage b229280 (joinCoverage b229393 b229507)) (joinCoverage (joinCoverage b229620 b229733) (joinCoverage b229846 b229960)))) (joinCoverage (joinCoverage (joinCoverage b230073 (joinCoverage b230186 b230299)) (joinCoverage (joinCoverage b230412 b230525) (joinCoverage b230638 b230751))) (joinCoverage (joinCoverage (joinCoverage b230865 b230978) (joinCoverage b231091 b231204)) (joinCoverage (joinCoverage b231318 b231431) (joinCoverage b231544 b231657)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 218642 ≤ index 420000000/512 := by decide +kernel
private theorem starting_value : fast 420000000=22344479 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 420000000=22344479) (n : ℕ) (low : 420000000≤n) (bound : n≤445000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=420000000
    · rw [first,anchor]
      exact starting_value
    · have past : 420000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤445000000 by omega)
        have within : index n / 512 < 231771 := by omega
        have lower : index 420000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤445000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ420000000To445000000
