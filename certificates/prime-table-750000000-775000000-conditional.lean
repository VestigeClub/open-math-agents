import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ750000000To775000000

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




private def radical : ℕ := 0x791f5f39c3a88db1f600eec6d968a6b413f5ad64a1a4421b5d80568dd95800c04d019e9a863780daac4c8f05c97d1179fe3fe1a7914a40190f817a186ad10246a8e62be414f70156ac6c92ea6cc14fff484013c19ee09422009fb4d33107eed2c47c56f8891d75ce485a2bc71f34e399aafb2934f93f8d1d815d2510cbd99a5b6896f5ed3e933d226d869d0ca6195ccd436d2cfb119540b5e820bb191576c55e49210c566afbf1e7539305d69cd5f55178914140a29893a136498717b830af3af12d883faabb57ce53d499e24be1d0367908dea1754889110c78e6d59952e1feafcb26f81ef647e6b3b164ecb5b99c819a80440d8431bc2095d63a06cecbaae3d2e4432bb878c3036508ddd7328a4e56e4dbb7451ba4b289f2e70b011019aa9aa09196bb720f194fe7ac42a1d44c7aec922b84c5a4131ec4e0ebed2373905e4a6ca3117ef626b1115e9f1942a31b4e08aff8c0b819e26b57ccd2b5311c0839ed1ecd8a9853965d87625a46d9b5bfe33337ca088d74428a6af2fdf35a5672bb3dc7c7135be9eaa2fbe1a23724b61e4524158e8680db0d111f6ba61c00b90c706cc4b21ed0a508e5736f82dce7c0238e726c6475d66f4b3df1a341f333cd004319fe3cf5dd130804937a7d3d716db303281fceb2f3c6fcf1357072d4bf69cf356d18a692a20464b2944afbad567d7dd1e3ba5b2f29ef28866ae1bbfbe9be143a474ec154ac9d609d02181cdb81d294f7e00c57ace12630e12eeb3d4c4143b5e023985e87d58e8dfbbaad1a2f24e26267e51037d493f18dcca956468349a8a7ed5b63760bb67d3ae0bf82b732c48ba02b8ae0035f37bbae7ac34c9eb4a30d2f9c067b95ed790dce14dec4c31cf0ab5fb95a93e8be1ea3943016d4096e1fdd6cd492e41621130bcf4e51d892cfdb0c45381aa9f986e092d04cba476bfd9c2466ffc20f6ac64e499ae0459ee7955d73ff8ccfcc2b19587dbc2f5944f7c3953f2d3f9910ee886c91c24de8c39f2af0f81a22ea03f5b3c04e31eed3b99484b904bf9a899b9563df6211ab04ec0c8754ae5e89237f44ae67e58898c32005c3b3210ede9d1965c63287ee512bcac1e1928c9ebeecd577f26019024e877864583afc8d7cdf86a12dde9851b2bfafe690a262e79a7c0da747a064d04a6bbeab2730bb3624df20ac397e3d0539470a90bbd9ad9ffb86071ebca5048d1135bedcf499663b1134b0d8cfe6a57028e313328705261f2718c230bd174dcf7b464549dbfc65f75fa0d41fa1624304434488d33c971838dcb53cb948f8c0b7186a114ad07200e8e08eba29b2f4728af4223ef3e6903515542db6584b72bcfeae07f69b40b7fec69aa0b310c483775c13a448c710e3f5d747c0d099daa70ebebfdf5c9bd26314b971e341077b7676f30ef98644479df11b8102fb59394d119e88364a3f0cbc2e4feb624e5473b76ee125f2679ef0f8f5a20811261236148aa9e5883cdd62ef2d5c85355768fac3d865f03e63e87c44f46844d0c15ed2a612e838fcc584127d4aade7276eb7079ad0d88257d331cd33819f21a721a64212d6e891ebba7ba16942b3ebbeba7ab19c3949cc5f39bf4b8bbef318ad9ca1b252d9e9472b988b322277c23b3f171e72a36af6e2bb3d63d68fad123ecdb8b3454be485ec1b33dfe1c9ac307fde2d64bba9fb09f69ef9c5c52fa4b762daf720ff67da26aad78946e2ce50cfbc80e5d145d09165c03c6b46e2e9cad46132ff49949c6bc1cf2d89cf04341557c51d1533bf8c09e0dc5a9341bd23b966bcfea09f77116b6d116464881b09b011f188640d389f5027d09174e93a11a9a46cfc07e4062e3e51e94c1d7f305a44f173e71f529add78b1e09b644d78bc4b9e5be967ec010e0eddb8aa2d759ed88b127fb783412d4d19c16c92fbd3f7bf79e6afa6a35fa2c33c906ac9fc219849a120651c713e0f224daceefffbec8d9631c791784195a5d717ff0223ff718780e1810203c9232d5f476e1fa59055a67e0b2502664f2ca7f1d473101b19326517e0a486d682ae5f10cf96f6ebfbd22fef0be0e117cb1265f42357659074a5faff37d31e09315fd6fdd06f000a6f28e0490022035042d67357b9724d4788401a04044d834f34a48807386e20ff3e780ea99ce89198fe8bdfc78a8eb6e8a2fc044068057c63a4d6be75bc7ccd7174ee14ea2002799fa205ebc7524e66dbc70222c70a917bb0ec284d44ccef74d3ebe364e39f196b86e2d3525b5c0dd470ac7ee97afa1f67f8145465d57fa0ee96915f583b4a3b832ede1ef0cb01786c1cb8e0fef51b830a7542a8e1e8d19b4ec9efa50c0096e5584bcd94a7f1a8f83ff0206657b28275c0c7db99442debece17006cdb081e9783c01cc78f72e4b277a1d4717596c36be2e74af14684864d95ff98ca3642b8b1dceb821ea7c56c5905bfa8d43e0769fcbcada5bdb7b698feae8924045ea35ee03a18ecdf6dab765e5b3cc86842ce297f4402695916af8700820410679025cc371ece11cff181d0b494b6102d0150e552e94b81d2faacadb00daac98d990f5742188293334c5555c7c689f092d9963fd92653cba989513f71e4d27d37d4aac3291a46e2966597e5b0c1d8a27f90f84201caaa6e29150b38dbadb3d7232c99bd244da9448c6024482e40fa664c41f2b73b5ef248f47a43beaf3da493a6c76afe3842ee05fab2e244eb47484f3621a88461f886f2c954c1c37c0e717e73730a06be5a0bbda7d7df700697a3bc3cd295b3e18c459dc508d217ff6f7350bad0a4e69d24af24a5b0c4456af820e6770e37420166f03885097630de64b2965806c29ea94749418b2a4dadea4449c8a2f1aaa73dc4de06f5f00cac901bb0a80d9345d16f3179486c9c67be41deeaa05becd0e7f53f08215b6e8ae948dd52955b6c4b1fb1a456bfd1a1eff0734d49769d37dd79d52a2a6a290e78eec13ec782ccd493f6b9959cea5079a29f9a08485253afab724b1a2918cf0a5b6b9bb86ea854e9865ac25b0cb8fbde88e5e4277978eea543f2b06e0002c00846b34e7ba9ed3c510fc47e0f095fa6161a7c7051ab089e76f8847638d4b3abab36b77b76a1056f007029cf998fc3ea367c3ec9f734f57647bdd9e8e34f0ddb9719cb8c830f64aa6a1fd5b3429a0c827348b0dd3116d1bbd0e807fe468ef820b355373bb6375dede280dc91727b7459b8f6d856e591a7e2b458e70f28b030a72ca3255bb8a29a68ec4ec0496c5d28b3bb6229c9e03d77cb1b8fb83641c55367f024d2321930c5b23d18137347c3f3c97c1b604159c7f45864c54704bf6033425ba5f3452c7ad660b7b3e53cba6de2697af2a7cde1909e5055ccf3ca41f135ce219ab05ec46c3ffeaf3387d2100ba0d1e3dce1656897ff656ac124e75e45b980053a75098782a56e624cbbd528b703d30058c3202988e33fc648268136356615b4ad16d05d16ba774e34318382af5d0328036e6f1f26b869c29792738b35f7ddbd872d065dc7d220dd41ec18d261a2c5c2b1c07a7ff6d8815c4d545ec53ec874762612ad49d4006714cae9da6381cc43a4f52b5ec1f4c179904fe469d1888b9bfe42e9e32a32c471faaa43b9205a0d3e018860027e8a2966f454207b3f05d0ee68e5777998d14dc07cb0a643fc4515d1d0fcb2dc3053d2474e2eb2e61b8f2e2c54d0976fb7d6e3efacc9982fbdbc78645d415a183f831e9b9309f330f8f648fa531de13a97399507942c8447672a73c07097a0cd62fb115acf9acdb63e7facf4b50801f39f966b2432de94220deaa2c265378fa8adb37050bd668fa189ba18a3edddddcb6d8f01b645a70a00917f2d5e6a4aa6dac7b55f56eab42f5f26e93f8dd95e368156e8cafb779f800c68973c9d3d16919f58a1b86410c71bb9dd40746b43d63dda6e9e0b0bab68e05bf8fa3104d31aae5049155ea2838d8e61146dbd661df545bcd34de837f51cfbd52653c4e94fdbf9d6b1ee3f2897b3356e792c1bf96b8749d09944838e8691cdb149334d944274a1a5fdaf4c28ffe441914e7fe157716cd122bbec70dd81262f8bc4c154e532194fcf3587e73c8feac2e48c67b0212cd9c1551de0f47b528fc627c8508d4b7d337c0a42db443fe9f3356292b812e18fb29126dc1574765a2f1654e0c823d7414a21c3c9d6881d529d18e1c7c7173acb4efad36a0ae2b8c04433630458a335283535577fe4c68070d5c0cb048163676b74c26d19795369f1a1967e7f2b8054b62483170c34e6186d2b2d80ab350399de7bdd063869c896d96c762d3af88525069c28ee2e3eee0464342d5f174381970a8f059206e3bbf4d9f3853707617ad94a8aae7edd1d081c52f8fe075d8a93ecfa9223acf1a12d27158ee4e7d77df8fcd62d533b3c396a5b7fb9f7e36774ac3ad72acd1ac3c13196b0c96833a45996705f289bc3b09a59189c7891dcfc52e8c714009f2d074cab5225364c4f644125f5d02919ba000fea60c491511b1dfd021401971f86e16f2a66f056c1d93e25bcb7826f77987bfe7a0b0e876cc1cbeb97b2ca98293d2489d2ac4a5d4a07799d24045f9269e49ba5433dcc23c10f71d8a21ac522a729a2fef93c25ab02edb2e51f2ae7363281ea378612899870aaf590c307212cdd88836161c2f205fdce1b9cd3b77b2dfd97d806e3bb8c9078aabb5dc01679373ec37406b1f13eccb98445ac399a4d73bbfc4d7fce89bc665112f557d52f0eb7b2e558d6698cf8b3cd513de23c42cdc9d40b904090190b08a7795128b0a1703e33a6270e7e89fa4abb6c7d45fd44d085261c2e7025a7b0999019aa11ebc451f7ddc7f50cb1aae2bd4bbb9583ca224164bb6ffcf6b94bc7677972ba10cce4c353d0423dbf23dba292580ee0c42b75c8dff0ee4856c88b61a5a40572c9eb49460cfd500fedf8a233ee5f39d19014aaf89590bbfb9b9314175f8d7ea357a4c15ae256cb5c24a36e3ccb24a79db349c2f786bb62063e195387529017e97ce6e7df5f2b6f6d09bc67a6bdf01ac9bc6253769a3f5040691b2857667e3cbfd0e5d05c6c4c85e670892e63c20e02459ad7b8029b9a611b8bd0c370823c23b987650ee86dd57a64cbee350a5efebaefb65f5b25c0b862e8301b02d0111bc6444db10f4d7c338872204d2c999f75a19ea2c8445e43067e11c1dbf986dc79b8577db76acbb1cd7853fd7eeea589355e6fce6d834a71efc68292240f6baefd732102e0311d24b13d17d9914c6115b7191c426c0031c5987fb97cb68fa928e811a5e4cd9256a73dc4f69e578539bcb357445116d5021b2d91837b4e14b8a192e9a646a6e49225c87d376f34dac34598c726b0c31cdbde717f2ea07e31e060cf01d5310660ffafc66c73cc1dfffaf742cdb39b5d5505d21d9f5d35a8dc46fccb02a48f1b13773265b6bea2c0cbd113c081fe88a220abe6238942b3ad3faec76c7ecd3f67aaebd21dedbd858a1754956ea26061a3bac6fcdf78b8cede1f5ed2ea1a023f797adb25366ce08a0297bdc21fd200b4bc55d3d7a64c146ca4f429eed81ab5e5890f290ab7b2e8c6da616be190f759b26eded5a2db2385f1bebc08ee556d76729978cca458823961ba955d7b4ffbbf8e966b57b1dd0b8a1adbf3934953b356388203a8a9dc397d32496cc702cf37e52d246118549aefbb0b46732a0b581a0d393a5a4fbef398c802f31c349a8e813d5960b1d1ed38f3dc01f0d8b323fe4e3ea3fdeb89aee604ce9bc8a819214b93150db19c6940814fc3e3b45fded0e1081d637a5de36c9e3be870c94a8eb2418d45a1fc21a370a469acb27394ebd4735b7c9324c3d28e1193fb348eeb8e36f7c8a879c36e66a43c80993af8599266fed83fb4a81608f10e4f1556e486700a448f58a2753ec23f9c202f429510e82e1e45befd515eae310d2632fc124d4c386520ff35f9400e763547989fc9acaee0fbacdc0ec009b1234e3fbb86e6f204ff7dc64d8b8137526fb5c57230a18d065b9a774e3e08deae67f96bf439820197b15b79e6069fd0b3bbc4137d491621bf757170ef4a3fea1282e184cba7b12788af3f241e994aa01e37d49f71b85a079f994f69dcb733812ac456722f96a8f705f6738c98b50179e235fd321c48cf9fbe6970dfad25ea9148a1109e41643aa6b1aaa32cf3dfc6341c42cec70861c367ec5c4878b379c7d37560a5503cb4b5907f7b43966c322120fe435d56df461c530c8bc89978b1dbbff7f4178f43edab23d3c4a07ee732bb897f19a98a7e04f4815aec11ea004c275fbcf2c591ac99160f1ad55db5795f685f9d3f1b05b6cfb983fdf5d6aa7b99918be4aefbec71eca0d8a6e17fdc15ee455de355de868b6f1e627864cc017235eead5ebb18c491d7a7428a011a92231621a9e03344b8cd62b66da807621ccefe07757637f4eb3b7044b36f5399e88816b2071e22f1fff6afce64113deb7aa0926be771d03aaf7cf6fa4bc27514fb3e31428cf193e2537f283ae85448774d8636c47a8aabfe0b45a0a8b58d97755fc708a8d8df47f6d2465e85f5133e89fb4788629e38cc353437f5d56042b1ad43e294bd8b0e12f203b4bd8b6d4286e416d5e90ba4d32aa866ef5ac0af587ef250c07857bff6d407bf667b0d18f17070ec070b8ff8eb692082a47396336edeae5098b4fdcdd138cfa26056024f80cd0e0fec4965867d12dba84882014664a87a4153e4ac14fc216928389e84eaae65fe391982725abb62b3c7486496ebe9d9dfcec47113a9df2168d1823a18e76fcfe3dbfe4e480cbda17d0c9ea38b578d378e08d59766b85d480a541ce3b5d700e77a33cb973dd1cc2fdc482337d37a11b5df6583e03b1f926ee4c21dc3ec3032c5df8d48c92b670885f070785e23a0ac9b9a3561de9419b81c3d8eedb0b084bd09e438627602fa6d47b9a4f93e6e42385a254179528a4201cb1abfdf936e8a6b8a76a74d1b4100beba29386235e0542f9d8539800330d8e66c7827c53d84a3fee4e79ad321e52a7f4819fabb94578851653c95fe21c3beb0529cd3e347b09e120e3f45d00b7ece98caabd13cfbede579674819ceb1005398991b333f1a0582

private def light (n : ℕ) : Bool :=
  if n≤166 then decide n.Prime else n.gcd 9003691705778437366474261723593317460743809582982673924866166675773511208652391102946946281027792581898371958829393225850851653767501982045219020431127589808697991466793298694201538496844331704050700119151048217216603057946772526930136930660543663874569666560000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤27838) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 166 = 9003691705778437366474261723593317460743809582982673924866166675773511208652391102946946281027792581898371958829393225850851653767501982045219020431127589808697991466793298694201538496844331704050700119151048217216603057946772526930136930660543663874569666560000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 166 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤27838 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 54 := by unfold smallValid; decide +kernel

private theorem sp54 : smallValid 54 54 := by unfold smallValid; decide +kernel

private theorem sp108 : smallValid 108 54 := by unfold smallValid; decide +kernel

private theorem sp162 : smallValid 162 55 := by unfold smallValid; decide +kernel

private theorem sp217 : smallValid 217 54 := by unfold smallValid; decide +kernel

private theorem sp271 : smallValid 271 54 := by unfold smallValid; decide +kernel

private theorem sp325 : smallValid 325 54 := by unfold smallValid; decide +kernel

private theorem sp379 : smallValid 379 55 := by unfold smallValid; decide +kernel

private theorem sp434 : smallValid 434 54 := by unfold smallValid; decide +kernel

private theorem sp488 : smallValid 488 54 := by unfold smallValid; decide +kernel

private theorem sp542 : smallValid 542 54 := by unfold smallValid; decide +kernel

private theorem sp596 : smallValid 596 55 := by unfold smallValid; decide +kernel

private theorem sp651 : smallValid 651 54 := by unfold smallValid; decide +kernel

private theorem sp705 : smallValid 705 55 := by unfold smallValid; decide +kernel

private theorem sp760 : smallValid 760 54 := by unfold smallValid; decide +kernel

private theorem sp814 : smallValid 814 55 := by unfold smallValid; decide +kernel

private theorem sp869 : smallValid 869 54 := by unfold smallValid; decide +kernel

private theorem sp923 : smallValid 923 54 := by unfold smallValid; decide +kernel

private theorem sp977 : smallValid 977 54 := by unfold smallValid; decide +kernel

private theorem sp1031 : smallValid 1031 55 := by unfold smallValid; decide +kernel

private theorem sp1086 : smallValid 1086 54 := by unfold smallValid; decide +kernel

private theorem sp1140 : smallValid 1140 55 := by unfold smallValid; decide +kernel

private theorem sp1195 : smallValid 1195 54 := by unfold smallValid; decide +kernel

private theorem sp1249 : smallValid 1249 55 := by unfold smallValid; decide +kernel

private theorem sp1304 : smallValid 1304 54 := by unfold smallValid; decide +kernel

private theorem sp1358 : smallValid 1358 54 := by unfold smallValid; decide +kernel

private theorem sp1412 : smallValid 1412 54 := by unfold smallValid; decide +kernel

private theorem sp1466 : smallValid 1466 55 := by unfold smallValid; decide +kernel

private theorem sp1521 : smallValid 1521 54 := by unfold smallValid; decide +kernel

private theorem sp1575 : smallValid 1575 55 := by unfold smallValid; decide +kernel

private theorem sp1630 : smallValid 1630 54 := by unfold smallValid; decide +kernel

private theorem sp1684 : smallValid 1684 55 := by unfold smallValid; decide +kernel

private theorem sp1739 : smallValid 1739 54 := by unfold smallValid; decide +kernel

private theorem sp1793 : smallValid 1793 54 := by unfold smallValid; decide +kernel

private theorem sp1847 : smallValid 1847 54 := by unfold smallValid; decide +kernel

private theorem sp1901 : smallValid 1901 55 := by unfold smallValid; decide +kernel

private theorem sp1956 : smallValid 1956 54 := by unfold smallValid; decide +kernel

private theorem sp2010 : smallValid 2010 55 := by unfold smallValid; decide +kernel

private theorem sp2065 : smallValid 2065 54 := by unfold smallValid; decide +kernel

private theorem sp2119 : smallValid 2119 55 := by unfold smallValid; decide +kernel

private theorem sp2174 : smallValid 2174 54 := by unfold smallValid; decide +kernel

private theorem sp2228 : smallValid 2228 54 := by unfold smallValid; decide +kernel

private theorem sp2282 : smallValid 2282 54 := by unfold smallValid; decide +kernel

private theorem sp2336 : smallValid 2336 55 := by unfold smallValid; decide +kernel

private theorem sp2391 : smallValid 2391 54 := by unfold smallValid; decide +kernel

private theorem sp2445 : smallValid 2445 55 := by unfold smallValid; decide +kernel

private theorem sp2500 : smallValid 2500 54 := by unfold smallValid; decide +kernel

private theorem sp2554 : smallValid 2554 55 := by unfold smallValid; decide +kernel

private theorem sp2609 : smallValid 2609 54 := by unfold smallValid; decide +kernel

private theorem sp2663 : smallValid 2663 54 := by unfold smallValid; decide +kernel

private theorem sp2717 : smallValid 2717 54 := by unfold smallValid; decide +kernel

private theorem sp2771 : smallValid 2771 55 := by unfold smallValid; decide +kernel

private theorem sp2826 : smallValid 2826 54 := by unfold smallValid; decide +kernel

private theorem sp2880 : smallValid 2880 55 := by unfold smallValid; decide +kernel

private theorem sp2935 : smallValid 2935 54 := by unfold smallValid; decide +kernel

private theorem sp2989 : smallValid 2989 55 := by unfold smallValid; decide +kernel

private theorem sp3044 : smallValid 3044 54 := by unfold smallValid; decide +kernel

private theorem sp3098 : smallValid 3098 54 := by unfold smallValid; decide +kernel

private theorem sp3152 : smallValid 3152 54 := by unfold smallValid; decide +kernel

private theorem sp3206 : smallValid 3206 55 := by unfold smallValid; decide +kernel

private theorem sp3261 : smallValid 3261 54 := by unfold smallValid; decide +kernel

private theorem sp3315 : smallValid 3315 55 := by unfold smallValid; decide +kernel

private theorem sp3370 : smallValid 3370 54 := by unfold smallValid; decide +kernel

private theorem sp3424 : smallValid 3424 55 := by unfold smallValid; decide +kernel

private theorem sp3479 : smallValid 3479 54 := by unfold smallValid; decide +kernel

private theorem sp3533 : smallValid 3533 54 := by unfold smallValid; decide +kernel

private theorem sp3587 : smallValid 3587 54 := by unfold smallValid; decide +kernel

private theorem sp3641 : smallValid 3641 55 := by unfold smallValid; decide +kernel

private theorem sp3696 : smallValid 3696 54 := by unfold smallValid; decide +kernel

private theorem sp3750 : smallValid 3750 55 := by unfold smallValid; decide +kernel

private theorem sp3805 : smallValid 3805 54 := by unfold smallValid; decide +kernel

private theorem sp3859 : smallValid 3859 55 := by unfold smallValid; decide +kernel

private theorem sp3914 : smallValid 3914 54 := by unfold smallValid; decide +kernel

private theorem sp3968 : smallValid 3968 54 := by unfold smallValid; decide +kernel

private theorem sp4022 : smallValid 4022 54 := by unfold smallValid; decide +kernel

private theorem sp4076 : smallValid 4076 55 := by unfold smallValid; decide +kernel

private theorem sp4131 : smallValid 4131 54 := by unfold smallValid; decide +kernel

private theorem sp4185 : smallValid 4185 55 := by unfold smallValid; decide +kernel

private theorem sp4240 : smallValid 4240 54 := by unfold smallValid; decide +kernel

private theorem sp4294 : smallValid 4294 55 := by unfold smallValid; decide +kernel

private theorem sp4349 : smallValid 4349 54 := by unfold smallValid; decide +kernel

private theorem sp4403 : smallValid 4403 54 := by unfold smallValid; decide +kernel

private theorem sp4457 : smallValid 4457 54 := by unfold smallValid; decide +kernel

private theorem sp4511 : smallValid 4511 55 := by unfold smallValid; decide +kernel

private theorem sp4566 : smallValid 4566 54 := by unfold smallValid; decide +kernel

private theorem sp4620 : smallValid 4620 55 := by unfold smallValid; decide +kernel

private theorem sp4675 : smallValid 4675 54 := by unfold smallValid; decide +kernel

private theorem sp4729 : smallValid 4729 55 := by unfold smallValid; decide +kernel

private theorem sp4784 : smallValid 4784 54 := by unfold smallValid; decide +kernel

private theorem sp4838 : smallValid 4838 54 := by unfold smallValid; decide +kernel

private theorem sp4892 : smallValid 4892 54 := by unfold smallValid; decide +kernel

private theorem sp4946 : smallValid 4946 55 := by unfold smallValid; decide +kernel

private theorem sp5001 : smallValid 5001 54 := by unfold smallValid; decide +kernel

private theorem sp5055 : smallValid 5055 55 := by unfold smallValid; decide +kernel

private theorem sp5110 : smallValid 5110 54 := by unfold smallValid; decide +kernel

private theorem sp5164 : smallValid 5164 55 := by unfold smallValid; decide +kernel

private theorem sp5219 : smallValid 5219 54 := by unfold smallValid; decide +kernel

private theorem sp5273 : smallValid 5273 54 := by unfold smallValid; decide +kernel

private theorem sp5327 : smallValid 5327 54 := by unfold smallValid; decide +kernel

private theorem sp5381 : smallValid 5381 55 := by unfold smallValid; decide +kernel

private theorem sp5436 : smallValid 5436 54 := by unfold smallValid; decide +kernel

private theorem sp5490 : smallValid 5490 55 := by unfold smallValid; decide +kernel

private theorem sp5545 : smallValid 5545 54 := by unfold smallValid; decide +kernel

private theorem sp5599 : smallValid 5599 55 := by unfold smallValid; decide +kernel

private theorem sp5654 : smallValid 5654 54 := by unfold smallValid; decide +kernel

private theorem sp5708 : smallValid 5708 54 := by unfold smallValid; decide +kernel

private theorem sp5762 : smallValid 5762 54 := by unfold smallValid; decide +kernel

private theorem sp5816 : smallValid 5816 55 := by unfold smallValid; decide +kernel

private theorem sp5871 : smallValid 5871 54 := by unfold smallValid; decide +kernel

private theorem sp5925 : smallValid 5925 55 := by unfold smallValid; decide +kernel

private theorem sp5980 : smallValid 5980 54 := by unfold smallValid; decide +kernel

private theorem sp6034 : smallValid 6034 55 := by unfold smallValid; decide +kernel

private theorem sp6089 : smallValid 6089 54 := by unfold smallValid; decide +kernel

private theorem sp6143 : smallValid 6143 54 := by unfold smallValid; decide +kernel

private theorem sp6197 : smallValid 6197 54 := by unfold smallValid; decide +kernel

private theorem sp6251 : smallValid 6251 55 := by unfold smallValid; decide +kernel

private theorem sp6306 : smallValid 6306 54 := by unfold smallValid; decide +kernel

private theorem sp6360 : smallValid 6360 55 := by unfold smallValid; decide +kernel

private theorem sp6415 : smallValid 6415 54 := by unfold smallValid; decide +kernel

private theorem sp6469 : smallValid 6469 55 := by unfold smallValid; decide +kernel

private theorem sp6524 : smallValid 6524 54 := by unfold smallValid; decide +kernel

private theorem sp6578 : smallValid 6578 54 := by unfold smallValid; decide +kernel

private theorem sp6632 : smallValid 6632 54 := by unfold smallValid; decide +kernel

private theorem sp6686 : smallValid 6686 55 := by unfold smallValid; decide +kernel

private theorem sp6741 : smallValid 6741 54 := by unfold smallValid; decide +kernel

private theorem sp6795 : smallValid 6795 55 := by unfold smallValid; decide +kernel

private theorem sp6850 : smallValid 6850 54 := by unfold smallValid; decide +kernel

private theorem sp6904 : smallValid 6904 55 := by unfold smallValid; decide +kernel

private theorem sp6959 : smallValid 6959 54 := by unfold smallValid; decide +kernel

private theorem sp7013 : smallValid 7013 54 := by unfold smallValid; decide +kernel

private theorem sp7067 : smallValid 7067 54 := by unfold smallValid; decide +kernel

private theorem sp7121 : smallValid 7121 55 := by unfold smallValid; decide +kernel

private theorem sp7176 : smallValid 7176 54 := by unfold smallValid; decide +kernel

private theorem sp7230 : smallValid 7230 55 := by unfold smallValid; decide +kernel

private theorem sp7285 : smallValid 7285 54 := by unfold smallValid; decide +kernel

private theorem sp7339 : smallValid 7339 55 := by unfold smallValid; decide +kernel

private theorem sp7394 : smallValid 7394 54 := by unfold smallValid; decide +kernel

private theorem sp7448 : smallValid 7448 54 := by unfold smallValid; decide +kernel

private theorem sp7502 : smallValid 7502 54 := by unfold smallValid; decide +kernel

private theorem sp7556 : smallValid 7556 55 := by unfold smallValid; decide +kernel

private theorem sp7611 : smallValid 7611 54 := by unfold smallValid; decide +kernel

private theorem sp7665 : smallValid 7665 55 := by unfold smallValid; decide +kernel

private theorem sp7720 : smallValid 7720 54 := by unfold smallValid; decide +kernel

private theorem sp7774 : smallValid 7774 55 := by unfold smallValid; decide +kernel

private theorem sp7829 : smallValid 7829 54 := by unfold smallValid; decide +kernel

private theorem sp7883 : smallValid 7883 54 := by unfold smallValid; decide +kernel

private theorem sp7937 : smallValid 7937 54 := by unfold smallValid; decide +kernel

private theorem sp7991 : smallValid 7991 55 := by unfold smallValid; decide +kernel

private theorem sp8046 : smallValid 8046 54 := by unfold smallValid; decide +kernel

private theorem sp8100 : smallValid 8100 55 := by unfold smallValid; decide +kernel

private theorem sp8155 : smallValid 8155 54 := by unfold smallValid; decide +kernel

private theorem sp8209 : smallValid 8209 55 := by unfold smallValid; decide +kernel

private theorem sp8264 : smallValid 8264 54 := by unfold smallValid; decide +kernel

private theorem sp8318 : smallValid 8318 54 := by unfold smallValid; decide +kernel

private theorem sp8372 : smallValid 8372 54 := by unfold smallValid; decide +kernel

private theorem sp8426 : smallValid 8426 55 := by unfold smallValid; decide +kernel

private theorem sp8481 : smallValid 8481 54 := by unfold smallValid; decide +kernel

private theorem sp8535 : smallValid 8535 55 := by unfold smallValid; decide +kernel

private theorem sp8590 : smallValid 8590 54 := by unfold smallValid; decide +kernel

private theorem sp8644 : smallValid 8644 55 := by unfold smallValid; decide +kernel

private theorem sp8699 : smallValid 8699 54 := by unfold smallValid; decide +kernel

private theorem sp8753 : smallValid 8753 54 := by unfold smallValid; decide +kernel

private theorem sp8807 : smallValid 8807 54 := by unfold smallValid; decide +kernel

private theorem sp8861 : smallValid 8861 55 := by unfold smallValid; decide +kernel

private theorem sp8916 : smallValid 8916 54 := by unfold smallValid; decide +kernel

private theorem sp8970 : smallValid 8970 55 := by unfold smallValid; decide +kernel

private theorem sp9025 : smallValid 9025 54 := by unfold smallValid; decide +kernel

private theorem sp9079 : smallValid 9079 55 := by unfold smallValid; decide +kernel

private theorem sp9134 : smallValid 9134 54 := by unfold smallValid; decide +kernel

private theorem sp9188 : smallValid 9188 54 := by unfold smallValid; decide +kernel

private theorem sp9242 : smallValid 9242 54 := by unfold smallValid; decide +kernel

private theorem sp9296 : smallValid 9296 55 := by unfold smallValid; decide +kernel

private theorem sp9351 : smallValid 9351 54 := by unfold smallValid; decide +kernel

private theorem sp9405 : smallValid 9405 55 := by unfold smallValid; decide +kernel

private theorem sp9460 : smallValid 9460 54 := by unfold smallValid; decide +kernel

private theorem sp9514 : smallValid 9514 55 := by unfold smallValid; decide +kernel

private theorem sp9569 : smallValid 9569 54 := by unfold smallValid; decide +kernel

private theorem sp9623 : smallValid 9623 54 := by unfold smallValid; decide +kernel

private theorem sp9677 : smallValid 9677 54 := by unfold smallValid; decide +kernel

private theorem sp9731 : smallValid 9731 55 := by unfold smallValid; decide +kernel

private theorem sp9786 : smallValid 9786 54 := by unfold smallValid; decide +kernel

private theorem sp9840 : smallValid 9840 55 := by unfold smallValid; decide +kernel

private theorem sp9895 : smallValid 9895 54 := by unfold smallValid; decide +kernel

private theorem sp9949 : smallValid 9949 55 := by unfold smallValid; decide +kernel

private theorem sp10004 : smallValid 10004 54 := by unfold smallValid; decide +kernel

private theorem sp10058 : smallValid 10058 54 := by unfold smallValid; decide +kernel

private theorem sp10112 : smallValid 10112 54 := by unfold smallValid; decide +kernel

private theorem sp10166 : smallValid 10166 55 := by unfold smallValid; decide +kernel

private theorem sp10221 : smallValid 10221 54 := by unfold smallValid; decide +kernel

private theorem sp10275 : smallValid 10275 55 := by unfold smallValid; decide +kernel

private theorem sp10330 : smallValid 10330 54 := by unfold smallValid; decide +kernel

private theorem sp10384 : smallValid 10384 55 := by unfold smallValid; decide +kernel

private theorem sp10439 : smallValid 10439 54 := by unfold smallValid; decide +kernel

private theorem sp10493 : smallValid 10493 54 := by unfold smallValid; decide +kernel

private theorem sp10547 : smallValid 10547 54 := by unfold smallValid; decide +kernel

private theorem sp10601 : smallValid 10601 55 := by unfold smallValid; decide +kernel

private theorem sp10656 : smallValid 10656 54 := by unfold smallValid; decide +kernel

private theorem sp10710 : smallValid 10710 55 := by unfold smallValid; decide +kernel

private theorem sp10765 : smallValid 10765 54 := by unfold smallValid; decide +kernel

private theorem sp10819 : smallValid 10819 55 := by unfold smallValid; decide +kernel

private theorem sp10874 : smallValid 10874 54 := by unfold smallValid; decide +kernel

private theorem sp10928 : smallValid 10928 54 := by unfold smallValid; decide +kernel

private theorem sp10982 : smallValid 10982 54 := by unfold smallValid; decide +kernel

private theorem sp11036 : smallValid 11036 55 := by unfold smallValid; decide +kernel

private theorem sp11091 : smallValid 11091 54 := by unfold smallValid; decide +kernel

private theorem sp11145 : smallValid 11145 55 := by unfold smallValid; decide +kernel

private theorem sp11200 : smallValid 11200 54 := by unfold smallValid; decide +kernel

private theorem sp11254 : smallValid 11254 55 := by unfold smallValid; decide +kernel

private theorem sp11309 : smallValid 11309 54 := by unfold smallValid; decide +kernel

private theorem sp11363 : smallValid 11363 54 := by unfold smallValid; decide +kernel

private theorem sp11417 : smallValid 11417 54 := by unfold smallValid; decide +kernel

private theorem sp11471 : smallValid 11471 55 := by unfold smallValid; decide +kernel

private theorem sp11526 : smallValid 11526 54 := by unfold smallValid; decide +kernel

private theorem sp11580 : smallValid 11580 55 := by unfold smallValid; decide +kernel

private theorem sp11635 : smallValid 11635 54 := by unfold smallValid; decide +kernel

private theorem sp11689 : smallValid 11689 55 := by unfold smallValid; decide +kernel

private theorem sp11744 : smallValid 11744 54 := by unfold smallValid; decide +kernel

private theorem sp11798 : smallValid 11798 54 := by unfold smallValid; decide +kernel

private theorem sp11852 : smallValid 11852 54 := by unfold smallValid; decide +kernel

private theorem sp11906 : smallValid 11906 55 := by unfold smallValid; decide +kernel

private theorem sp11961 : smallValid 11961 54 := by unfold smallValid; decide +kernel

private theorem sp12015 : smallValid 12015 55 := by unfold smallValid; decide +kernel

private theorem sp12070 : smallValid 12070 54 := by unfold smallValid; decide +kernel

private theorem sp12124 : smallValid 12124 55 := by unfold smallValid; decide +kernel

private theorem sp12179 : smallValid 12179 54 := by unfold smallValid; decide +kernel

private theorem sp12233 : smallValid 12233 54 := by unfold smallValid; decide +kernel

private theorem sp12287 : smallValid 12287 54 := by unfold smallValid; decide +kernel

private theorem sp12341 : smallValid 12341 55 := by unfold smallValid; decide +kernel

private theorem sp12396 : smallValid 12396 54 := by unfold smallValid; decide +kernel

private theorem sp12450 : smallValid 12450 55 := by unfold smallValid; decide +kernel

private theorem sp12505 : smallValid 12505 54 := by unfold smallValid; decide +kernel

private theorem sp12559 : smallValid 12559 55 := by unfold smallValid; decide +kernel

private theorem sp12614 : smallValid 12614 54 := by unfold smallValid; decide +kernel

private theorem sp12668 : smallValid 12668 54 := by unfold smallValid; decide +kernel

private theorem sp12722 : smallValid 12722 54 := by unfold smallValid; decide +kernel

private theorem sp12776 : smallValid 12776 55 := by unfold smallValid; decide +kernel

private theorem sp12831 : smallValid 12831 54 := by unfold smallValid; decide +kernel

private theorem sp12885 : smallValid 12885 55 := by unfold smallValid; decide +kernel

private theorem sp12940 : smallValid 12940 54 := by unfold smallValid; decide +kernel

private theorem sp12994 : smallValid 12994 55 := by unfold smallValid; decide +kernel

private theorem sp13049 : smallValid 13049 54 := by unfold smallValid; decide +kernel

private theorem sp13103 : smallValid 13103 54 := by unfold smallValid; decide +kernel

private theorem sp13157 : smallValid 13157 54 := by unfold smallValid; decide +kernel

private theorem sp13211 : smallValid 13211 55 := by unfold smallValid; decide +kernel

private theorem sp13266 : smallValid 13266 54 := by unfold smallValid; decide +kernel

private theorem sp13320 : smallValid 13320 55 := by unfold smallValid; decide +kernel

private theorem sp13375 : smallValid 13375 54 := by unfold smallValid; decide +kernel

private theorem sp13429 : smallValid 13429 55 := by unfold smallValid; decide +kernel

private theorem sp13484 : smallValid 13484 54 := by unfold smallValid; decide +kernel

private theorem sp13538 : smallValid 13538 54 := by unfold smallValid; decide +kernel

private theorem sp13592 : smallValid 13592 54 := by unfold smallValid; decide +kernel

private theorem sp13646 : smallValid 13646 55 := by unfold smallValid; decide +kernel

private theorem sp13701 : smallValid 13701 54 := by unfold smallValid; decide +kernel

private theorem sp13755 : smallValid 13755 55 := by unfold smallValid; decide +kernel

private theorem sp13810 : smallValid 13810 54 := by unfold smallValid; decide +kernel

private theorem sp13864 : smallValid 13864 55 := by unfold smallValid; decide +kernel

private theorem sp13919 : smallValid 13919 54 := by unfold smallValid; decide +kernel

private theorem sp13973 : smallValid 13973 54 := by unfold smallValid; decide +kernel

private theorem sp14027 : smallValid 14027 54 := by unfold smallValid; decide +kernel

private theorem sp14081 : smallValid 14081 55 := by unfold smallValid; decide +kernel

private theorem sp14136 : smallValid 14136 54 := by unfold smallValid; decide +kernel

private theorem sp14190 : smallValid 14190 55 := by unfold smallValid; decide +kernel

private theorem sp14245 : smallValid 14245 54 := by unfold smallValid; decide +kernel

private theorem sp14299 : smallValid 14299 55 := by unfold smallValid; decide +kernel

private theorem sp14354 : smallValid 14354 54 := by unfold smallValid; decide +kernel

private theorem sp14408 : smallValid 14408 54 := by unfold smallValid; decide +kernel

private theorem sp14462 : smallValid 14462 54 := by unfold smallValid; decide +kernel

private theorem sp14516 : smallValid 14516 55 := by unfold smallValid; decide +kernel

private theorem sp14571 : smallValid 14571 54 := by unfold smallValid; decide +kernel

private theorem sp14625 : smallValid 14625 55 := by unfold smallValid; decide +kernel

private theorem sp14680 : smallValid 14680 54 := by unfold smallValid; decide +kernel

private theorem sp14734 : smallValid 14734 55 := by unfold smallValid; decide +kernel

private theorem sp14789 : smallValid 14789 54 := by unfold smallValid; decide +kernel

private theorem sp14843 : smallValid 14843 54 := by unfold smallValid; decide +kernel

private theorem sp14897 : smallValid 14897 54 := by unfold smallValid; decide +kernel

private theorem sp14951 : smallValid 14951 55 := by unfold smallValid; decide +kernel

private theorem sp15006 : smallValid 15006 54 := by unfold smallValid; decide +kernel

private theorem sp15060 : smallValid 15060 55 := by unfold smallValid; decide +kernel

private theorem sp15115 : smallValid 15115 54 := by unfold smallValid; decide +kernel

private theorem sp15169 : smallValid 15169 55 := by unfold smallValid; decide +kernel

private theorem sp15224 : smallValid 15224 54 := by unfold smallValid; decide +kernel

private theorem sp15278 : smallValid 15278 54 := by unfold smallValid; decide +kernel

private theorem sp15332 : smallValid 15332 54 := by unfold smallValid; decide +kernel

private theorem sp15386 : smallValid 15386 55 := by unfold smallValid; decide +kernel

private theorem sp15441 : smallValid 15441 54 := by unfold smallValid; decide +kernel

private theorem sp15495 : smallValid 15495 55 := by unfold smallValid; decide +kernel

private theorem sp15550 : smallValid 15550 54 := by unfold smallValid; decide +kernel

private theorem sp15604 : smallValid 15604 55 := by unfold smallValid; decide +kernel

private theorem sp15659 : smallValid 15659 54 := by unfold smallValid; decide +kernel

private theorem sp15713 : smallValid 15713 54 := by unfold smallValid; decide +kernel

private theorem sp15767 : smallValid 15767 54 := by unfold smallValid; decide +kernel

private theorem sp15821 : smallValid 15821 55 := by unfold smallValid; decide +kernel

private theorem sp15876 : smallValid 15876 54 := by unfold smallValid; decide +kernel

private theorem sp15930 : smallValid 15930 55 := by unfold smallValid; decide +kernel

private theorem sp15985 : smallValid 15985 54 := by unfold smallValid; decide +kernel

private theorem sp16039 : smallValid 16039 55 := by unfold smallValid; decide +kernel

private theorem sp16094 : smallValid 16094 54 := by unfold smallValid; decide +kernel

private theorem sp16148 : smallValid 16148 54 := by unfold smallValid; decide +kernel

private theorem sp16202 : smallValid 16202 54 := by unfold smallValid; decide +kernel

private theorem sp16256 : smallValid 16256 55 := by unfold smallValid; decide +kernel

private theorem sp16311 : smallValid 16311 54 := by unfold smallValid; decide +kernel

private theorem sp16365 : smallValid 16365 55 := by unfold smallValid; decide +kernel

private theorem sp16420 : smallValid 16420 54 := by unfold smallValid; decide +kernel

private theorem sp16474 : smallValid 16474 55 := by unfold smallValid; decide +kernel

private theorem sp16529 : smallValid 16529 54 := by unfold smallValid; decide +kernel

private theorem sp16583 : smallValid 16583 54 := by unfold smallValid; decide +kernel

private theorem sp16637 : smallValid 16637 54 := by unfold smallValid; decide +kernel

private theorem sp16691 : smallValid 16691 55 := by unfold smallValid; decide +kernel

private theorem sp16746 : smallValid 16746 54 := by unfold smallValid; decide +kernel

private theorem sp16800 : smallValid 16800 55 := by unfold smallValid; decide +kernel

private theorem sp16855 : smallValid 16855 54 := by unfold smallValid; decide +kernel

private theorem sp16909 : smallValid 16909 55 := by unfold smallValid; decide +kernel

private theorem sp16964 : smallValid 16964 54 := by unfold smallValid; decide +kernel

private theorem sp17018 : smallValid 17018 54 := by unfold smallValid; decide +kernel

private theorem sp17072 : smallValid 17072 54 := by unfold smallValid; decide +kernel

private theorem sp17126 : smallValid 17126 55 := by unfold smallValid; decide +kernel

private theorem sp17181 : smallValid 17181 54 := by unfold smallValid; decide +kernel

private theorem sp17235 : smallValid 17235 55 := by unfold smallValid; decide +kernel

private theorem sp17290 : smallValid 17290 54 := by unfold smallValid; decide +kernel

private theorem sp17344 : smallValid 17344 55 := by unfold smallValid; decide +kernel

private theorem sp17399 : smallValid 17399 54 := by unfold smallValid; decide +kernel

private theorem sp17453 : smallValid 17453 54 := by unfold smallValid; decide +kernel

private theorem sp17507 : smallValid 17507 54 := by unfold smallValid; decide +kernel

private theorem sp17561 : smallValid 17561 55 := by unfold smallValid; decide +kernel

private theorem sp17616 : smallValid 17616 54 := by unfold smallValid; decide +kernel

private theorem sp17670 : smallValid 17670 55 := by unfold smallValid; decide +kernel

private theorem sp17725 : smallValid 17725 54 := by unfold smallValid; decide +kernel

private theorem sp17779 : smallValid 17779 55 := by unfold smallValid; decide +kernel

private theorem sp17834 : smallValid 17834 54 := by unfold smallValid; decide +kernel

private theorem sp17888 : smallValid 17888 54 := by unfold smallValid; decide +kernel

private theorem sp17942 : smallValid 17942 54 := by unfold smallValid; decide +kernel

private theorem sp17996 : smallValid 17996 55 := by unfold smallValid; decide +kernel

private theorem sp18051 : smallValid 18051 54 := by unfold smallValid; decide +kernel

private theorem sp18105 : smallValid 18105 55 := by unfold smallValid; decide +kernel

private theorem sp18160 : smallValid 18160 54 := by unfold smallValid; decide +kernel

private theorem sp18214 : smallValid 18214 55 := by unfold smallValid; decide +kernel

private theorem sp18269 : smallValid 18269 54 := by unfold smallValid; decide +kernel

private theorem sp18323 : smallValid 18323 54 := by unfold smallValid; decide +kernel

private theorem sp18377 : smallValid 18377 54 := by unfold smallValid; decide +kernel

private theorem sp18431 : smallValid 18431 55 := by unfold smallValid; decide +kernel

private theorem sp18486 : smallValid 18486 54 := by unfold smallValid; decide +kernel

private theorem sp18540 : smallValid 18540 55 := by unfold smallValid; decide +kernel

private theorem sp18595 : smallValid 18595 54 := by unfold smallValid; decide +kernel

private theorem sp18649 : smallValid 18649 55 := by unfold smallValid; decide +kernel

private theorem sp18704 : smallValid 18704 54 := by unfold smallValid; decide +kernel

private theorem sp18758 : smallValid 18758 54 := by unfold smallValid; decide +kernel

private theorem sp18812 : smallValid 18812 54 := by unfold smallValid; decide +kernel

private theorem sp18866 : smallValid 18866 55 := by unfold smallValid; decide +kernel

private theorem sp18921 : smallValid 18921 54 := by unfold smallValid; decide +kernel

private theorem sp18975 : smallValid 18975 55 := by unfold smallValid; decide +kernel

private theorem sp19030 : smallValid 19030 54 := by unfold smallValid; decide +kernel

private theorem sp19084 : smallValid 19084 55 := by unfold smallValid; decide +kernel

private theorem sp19139 : smallValid 19139 54 := by unfold smallValid; decide +kernel

private theorem sp19193 : smallValid 19193 54 := by unfold smallValid; decide +kernel

private theorem sp19247 : smallValid 19247 54 := by unfold smallValid; decide +kernel

private theorem sp19301 : smallValid 19301 55 := by unfold smallValid; decide +kernel

private theorem sp19356 : smallValid 19356 54 := by unfold smallValid; decide +kernel

private theorem sp19410 : smallValid 19410 55 := by unfold smallValid; decide +kernel

private theorem sp19465 : smallValid 19465 54 := by unfold smallValid; decide +kernel

private theorem sp19519 : smallValid 19519 55 := by unfold smallValid; decide +kernel

private theorem sp19574 : smallValid 19574 54 := by unfold smallValid; decide +kernel

private theorem sp19628 : smallValid 19628 54 := by unfold smallValid; decide +kernel

private theorem sp19682 : smallValid 19682 54 := by unfold smallValid; decide +kernel

private theorem sp19736 : smallValid 19736 55 := by unfold smallValid; decide +kernel

private theorem sp19791 : smallValid 19791 54 := by unfold smallValid; decide +kernel

private theorem sp19845 : smallValid 19845 55 := by unfold smallValid; decide +kernel

private theorem sp19900 : smallValid 19900 54 := by unfold smallValid; decide +kernel

private theorem sp19954 : smallValid 19954 55 := by unfold smallValid; decide +kernel

private theorem sp20009 : smallValid 20009 54 := by unfold smallValid; decide +kernel

private theorem sp20063 : smallValid 20063 54 := by unfold smallValid; decide +kernel

private theorem sp20117 : smallValid 20117 54 := by unfold smallValid; decide +kernel

private theorem sp20171 : smallValid 20171 55 := by unfold smallValid; decide +kernel

private theorem sp20226 : smallValid 20226 54 := by unfold smallValid; decide +kernel

private theorem sp20280 : smallValid 20280 55 := by unfold smallValid; decide +kernel

private theorem sp20335 : smallValid 20335 54 := by unfold smallValid; decide +kernel

private theorem sp20389 : smallValid 20389 55 := by unfold smallValid; decide +kernel

private theorem sp20444 : smallValid 20444 54 := by unfold smallValid; decide +kernel

private theorem sp20498 : smallValid 20498 54 := by unfold smallValid; decide +kernel

private theorem sp20552 : smallValid 20552 54 := by unfold smallValid; decide +kernel

private theorem sp20606 : smallValid 20606 55 := by unfold smallValid; decide +kernel

private theorem sp20661 : smallValid 20661 54 := by unfold smallValid; decide +kernel

private theorem sp20715 : smallValid 20715 55 := by unfold smallValid; decide +kernel

private theorem sp20770 : smallValid 20770 54 := by unfold smallValid; decide +kernel

private theorem sp20824 : smallValid 20824 55 := by unfold smallValid; decide +kernel

private theorem sp20879 : smallValid 20879 54 := by unfold smallValid; decide +kernel

private theorem sp20933 : smallValid 20933 54 := by unfold smallValid; decide +kernel

private theorem sp20987 : smallValid 20987 54 := by unfold smallValid; decide +kernel

private theorem sp21041 : smallValid 21041 55 := by unfold smallValid; decide +kernel

private theorem sp21096 : smallValid 21096 54 := by unfold smallValid; decide +kernel

private theorem sp21150 : smallValid 21150 55 := by unfold smallValid; decide +kernel

private theorem sp21205 : smallValid 21205 54 := by unfold smallValid; decide +kernel

private theorem sp21259 : smallValid 21259 55 := by unfold smallValid; decide +kernel

private theorem sp21314 : smallValid 21314 54 := by unfold smallValid; decide +kernel

private theorem sp21368 : smallValid 21368 54 := by unfold smallValid; decide +kernel

private theorem sp21422 : smallValid 21422 54 := by unfold smallValid; decide +kernel

private theorem sp21476 : smallValid 21476 55 := by unfold smallValid; decide +kernel

private theorem sp21531 : smallValid 21531 54 := by unfold smallValid; decide +kernel

private theorem sp21585 : smallValid 21585 55 := by unfold smallValid; decide +kernel

private theorem sp21640 : smallValid 21640 54 := by unfold smallValid; decide +kernel

private theorem sp21694 : smallValid 21694 55 := by unfold smallValid; decide +kernel

private theorem sp21749 : smallValid 21749 54 := by unfold smallValid; decide +kernel

private theorem sp21803 : smallValid 21803 54 := by unfold smallValid; decide +kernel

private theorem sp21857 : smallValid 21857 54 := by unfold smallValid; decide +kernel

private theorem sp21911 : smallValid 21911 55 := by unfold smallValid; decide +kernel

private theorem sp21966 : smallValid 21966 54 := by unfold smallValid; decide +kernel

private theorem sp22020 : smallValid 22020 55 := by unfold smallValid; decide +kernel

private theorem sp22075 : smallValid 22075 54 := by unfold smallValid; decide +kernel

private theorem sp22129 : smallValid 22129 55 := by unfold smallValid; decide +kernel

private theorem sp22184 : smallValid 22184 54 := by unfold smallValid; decide +kernel

private theorem sp22238 : smallValid 22238 54 := by unfold smallValid; decide +kernel

private theorem sp22292 : smallValid 22292 54 := by unfold smallValid; decide +kernel

private theorem sp22346 : smallValid 22346 55 := by unfold smallValid; decide +kernel

private theorem sp22401 : smallValid 22401 54 := by unfold smallValid; decide +kernel

private theorem sp22455 : smallValid 22455 55 := by unfold smallValid; decide +kernel

private theorem sp22510 : smallValid 22510 54 := by unfold smallValid; decide +kernel

private theorem sp22564 : smallValid 22564 55 := by unfold smallValid; decide +kernel

private theorem sp22619 : smallValid 22619 54 := by unfold smallValid; decide +kernel

private theorem sp22673 : smallValid 22673 54 := by unfold smallValid; decide +kernel

private theorem sp22727 : smallValid 22727 54 := by unfold smallValid; decide +kernel

private theorem sp22781 : smallValid 22781 55 := by unfold smallValid; decide +kernel

private theorem sp22836 : smallValid 22836 54 := by unfold smallValid; decide +kernel

private theorem sp22890 : smallValid 22890 55 := by unfold smallValid; decide +kernel

private theorem sp22945 : smallValid 22945 54 := by unfold smallValid; decide +kernel

private theorem sp22999 : smallValid 22999 55 := by unfold smallValid; decide +kernel

private theorem sp23054 : smallValid 23054 54 := by unfold smallValid; decide +kernel

private theorem sp23108 : smallValid 23108 54 := by unfold smallValid; decide +kernel

private theorem sp23162 : smallValid 23162 54 := by unfold smallValid; decide +kernel

private theorem sp23216 : smallValid 23216 55 := by unfold smallValid; decide +kernel

private theorem sp23271 : smallValid 23271 54 := by unfold smallValid; decide +kernel

private theorem sp23325 : smallValid 23325 55 := by unfold smallValid; decide +kernel

private theorem sp23380 : smallValid 23380 54 := by unfold smallValid; decide +kernel

private theorem sp23434 : smallValid 23434 55 := by unfold smallValid; decide +kernel

private theorem sp23489 : smallValid 23489 54 := by unfold smallValid; decide +kernel

private theorem sp23543 : smallValid 23543 54 := by unfold smallValid; decide +kernel

private theorem sp23597 : smallValid 23597 54 := by unfold smallValid; decide +kernel

private theorem sp23651 : smallValid 23651 55 := by unfold smallValid; decide +kernel

private theorem sp23706 : smallValid 23706 54 := by unfold smallValid; decide +kernel

private theorem sp23760 : smallValid 23760 55 := by unfold smallValid; decide +kernel

private theorem sp23815 : smallValid 23815 54 := by unfold smallValid; decide +kernel

private theorem sp23869 : smallValid 23869 55 := by unfold smallValid; decide +kernel

private theorem sp23924 : smallValid 23924 54 := by unfold smallValid; decide +kernel

private theorem sp23978 : smallValid 23978 54 := by unfold smallValid; decide +kernel

private theorem sp24032 : smallValid 24032 54 := by unfold smallValid; decide +kernel

private theorem sp24086 : smallValid 24086 55 := by unfold smallValid; decide +kernel

private theorem sp24141 : smallValid 24141 54 := by unfold smallValid; decide +kernel

private theorem sp24195 : smallValid 24195 55 := by unfold smallValid; decide +kernel

private theorem sp24250 : smallValid 24250 54 := by unfold smallValid; decide +kernel

private theorem sp24304 : smallValid 24304 55 := by unfold smallValid; decide +kernel

private theorem sp24359 : smallValid 24359 54 := by unfold smallValid; decide +kernel

private theorem sp24413 : smallValid 24413 54 := by unfold smallValid; decide +kernel

private theorem sp24467 : smallValid 24467 54 := by unfold smallValid; decide +kernel

private theorem sp24521 : smallValid 24521 55 := by unfold smallValid; decide +kernel

private theorem sp24576 : smallValid 24576 54 := by unfold smallValid; decide +kernel

private theorem sp24630 : smallValid 24630 55 := by unfold smallValid; decide +kernel

private theorem sp24685 : smallValid 24685 54 := by unfold smallValid; decide +kernel

private theorem sp24739 : smallValid 24739 55 := by unfold smallValid; decide +kernel

private theorem sp24794 : smallValid 24794 54 := by unfold smallValid; decide +kernel

private theorem sp24848 : smallValid 24848 54 := by unfold smallValid; decide +kernel

private theorem sp24902 : smallValid 24902 54 := by unfold smallValid; decide +kernel

private theorem sp24956 : smallValid 24956 55 := by unfold smallValid; decide +kernel

private theorem sp25011 : smallValid 25011 54 := by unfold smallValid; decide +kernel

private theorem sp25065 : smallValid 25065 55 := by unfold smallValid; decide +kernel

private theorem sp25120 : smallValid 25120 54 := by unfold smallValid; decide +kernel

private theorem sp25174 : smallValid 25174 55 := by unfold smallValid; decide +kernel

private theorem sp25229 : smallValid 25229 54 := by unfold smallValid; decide +kernel

private theorem sp25283 : smallValid 25283 54 := by unfold smallValid; decide +kernel

private theorem sp25337 : smallValid 25337 54 := by unfold smallValid; decide +kernel

private theorem sp25391 : smallValid 25391 55 := by unfold smallValid; decide +kernel

private theorem sp25446 : smallValid 25446 54 := by unfold smallValid; decide +kernel

private theorem sp25500 : smallValid 25500 55 := by unfold smallValid; decide +kernel

private theorem sp25555 : smallValid 25555 54 := by unfold smallValid; decide +kernel

private theorem sp25609 : smallValid 25609 55 := by unfold smallValid; decide +kernel

private theorem sp25664 : smallValid 25664 54 := by unfold smallValid; decide +kernel

private theorem sp25718 : smallValid 25718 54 := by unfold smallValid; decide +kernel

private theorem sp25772 : smallValid 25772 54 := by unfold smallValid; decide +kernel

private theorem sp25826 : smallValid 25826 55 := by unfold smallValid; decide +kernel

private theorem sp25881 : smallValid 25881 54 := by unfold smallValid; decide +kernel

private theorem sp25935 : smallValid 25935 55 := by unfold smallValid; decide +kernel

private theorem sp25990 : smallValid 25990 54 := by unfold smallValid; decide +kernel

private theorem sp26044 : smallValid 26044 55 := by unfold smallValid; decide +kernel

private theorem sp26099 : smallValid 26099 54 := by unfold smallValid; decide +kernel

private theorem sp26153 : smallValid 26153 54 := by unfold smallValid; decide +kernel

private theorem sp26207 : smallValid 26207 54 := by unfold smallValid; decide +kernel

private theorem sp26261 : smallValid 26261 55 := by unfold smallValid; decide +kernel

private theorem sp26316 : smallValid 26316 54 := by unfold smallValid; decide +kernel

private theorem sp26370 : smallValid 26370 55 := by unfold smallValid; decide +kernel

private theorem sp26425 : smallValid 26425 54 := by unfold smallValid; decide +kernel

private theorem sp26479 : smallValid 26479 55 := by unfold smallValid; decide +kernel

private theorem sp26534 : smallValid 26534 54 := by unfold smallValid; decide +kernel

private theorem sp26588 : smallValid 26588 54 := by unfold smallValid; decide +kernel

private theorem sp26642 : smallValid 26642 54 := by unfold smallValid; decide +kernel

private theorem sp26696 : smallValid 26696 55 := by unfold smallValid; decide +kernel

private theorem sp26751 : smallValid 26751 54 := by unfold smallValid; decide +kernel

private theorem sp26805 : smallValid 26805 55 := by unfold smallValid; decide +kernel

private theorem sp26860 : smallValid 26860 54 := by unfold smallValid; decide +kernel

private theorem sp26914 : smallValid 26914 55 := by unfold smallValid; decide +kernel

private theorem sp26969 : smallValid 26969 54 := by unfold smallValid; decide +kernel

private theorem sp27023 : smallValid 27023 54 := by unfold smallValid; decide +kernel

private theorem sp27077 : smallValid 27077 54 := by unfold smallValid; decide +kernel

private theorem sp27131 : smallValid 27131 55 := by unfold smallValid; decide +kernel

private theorem sp27186 : smallValid 27186 54 := by unfold smallValid; decide +kernel

private theorem sp27240 : smallValid 27240 55 := by unfold smallValid; decide +kernel

private theorem sp27295 : smallValid 27295 54 := by unfold smallValid; decide +kernel

private theorem sp27349 : smallValid 27349 55 := by unfold smallValid; decide +kernel

private theorem sp27404 : smallValid 27404 54 := by unfold smallValid; decide +kernel

private theorem sp27458 : smallValid 27458 54 := by unfold smallValid; decide +kernel

private theorem sp27512 : smallValid 27512 54 := by unfold smallValid; decide +kernel

private theorem sp27566 : smallValid 27566 55 := by unfold smallValid; decide +kernel

private theorem sp27621 : smallValid 27621 54 := by unfold smallValid; decide +kernel

private theorem sp27675 : smallValid 27675 55 := by unfold smallValid; decide +kernel

private theorem sp27730 : smallValid 27730 54 := by unfold smallValid; decide +kernel

private theorem sp27784 : smallValid 27784 55 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤27838) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 27839 := (joinSmall (lo:=0) (a:=13919) (b:=13920) (joinSmall (lo:=0) (a:=6959) (b:=6960) (joinSmall (lo:=0) (a:=3479) (b:=3480) (joinSmall (lo:=0) (a:=1739) (b:=1740) (joinSmall (lo:=0) (a:=869) (b:=870) (joinSmall (lo:=0) (a:=434) (b:=435) (joinSmall (lo:=0) (a:=217) (b:=217) (joinSmall (lo:=0) (a:=108) (b:=109) (joinSmall (lo:=0) (a:=54) (b:=54) sp0 sp54) (joinSmall (lo:=108) (a:=54) (b:=55) sp108 sp162)) (joinSmall (lo:=217) (a:=108) (b:=109) (joinSmall (lo:=217) (a:=54) (b:=54) sp217 sp271) (joinSmall (lo:=325) (a:=54) (b:=55) sp325 sp379))) (joinSmall (lo:=434) (a:=217) (b:=218) (joinSmall (lo:=434) (a:=108) (b:=109) (joinSmall (lo:=434) (a:=54) (b:=54) sp434 sp488) (joinSmall (lo:=542) (a:=54) (b:=55) sp542 sp596)) (joinSmall (lo:=651) (a:=109) (b:=109) (joinSmall (lo:=651) (a:=54) (b:=55) sp651 sp705) (joinSmall (lo:=760) (a:=54) (b:=55) sp760 sp814)))) (joinSmall (lo:=869) (a:=435) (b:=435) (joinSmall (lo:=869) (a:=217) (b:=218) (joinSmall (lo:=869) (a:=108) (b:=109) (joinSmall (lo:=869) (a:=54) (b:=54) sp869 sp923) (joinSmall (lo:=977) (a:=54) (b:=55) sp977 sp1031)) (joinSmall (lo:=1086) (a:=109) (b:=109) (joinSmall (lo:=1086) (a:=54) (b:=55) sp1086 sp1140) (joinSmall (lo:=1195) (a:=54) (b:=55) sp1195 sp1249))) (joinSmall (lo:=1304) (a:=217) (b:=218) (joinSmall (lo:=1304) (a:=108) (b:=109) (joinSmall (lo:=1304) (a:=54) (b:=54) sp1304 sp1358) (joinSmall (lo:=1412) (a:=54) (b:=55) sp1412 sp1466)) (joinSmall (lo:=1521) (a:=109) (b:=109) (joinSmall (lo:=1521) (a:=54) (b:=55) sp1521 sp1575) (joinSmall (lo:=1630) (a:=54) (b:=55) sp1630 sp1684))))) (joinSmall (lo:=1739) (a:=870) (b:=870) (joinSmall (lo:=1739) (a:=435) (b:=435) (joinSmall (lo:=1739) (a:=217) (b:=218) (joinSmall (lo:=1739) (a:=108) (b:=109) (joinSmall (lo:=1739) (a:=54) (b:=54) sp1739 sp1793) (joinSmall (lo:=1847) (a:=54) (b:=55) sp1847 sp1901)) (joinSmall (lo:=1956) (a:=109) (b:=109) (joinSmall (lo:=1956) (a:=54) (b:=55) sp1956 sp2010) (joinSmall (lo:=2065) (a:=54) (b:=55) sp2065 sp2119))) (joinSmall (lo:=2174) (a:=217) (b:=218) (joinSmall (lo:=2174) (a:=108) (b:=109) (joinSmall (lo:=2174) (a:=54) (b:=54) sp2174 sp2228) (joinSmall (lo:=2282) (a:=54) (b:=55) sp2282 sp2336)) (joinSmall (lo:=2391) (a:=109) (b:=109) (joinSmall (lo:=2391) (a:=54) (b:=55) sp2391 sp2445) (joinSmall (lo:=2500) (a:=54) (b:=55) sp2500 sp2554)))) (joinSmall (lo:=2609) (a:=435) (b:=435) (joinSmall (lo:=2609) (a:=217) (b:=218) (joinSmall (lo:=2609) (a:=108) (b:=109) (joinSmall (lo:=2609) (a:=54) (b:=54) sp2609 sp2663) (joinSmall (lo:=2717) (a:=54) (b:=55) sp2717 sp2771)) (joinSmall (lo:=2826) (a:=109) (b:=109) (joinSmall (lo:=2826) (a:=54) (b:=55) sp2826 sp2880) (joinSmall (lo:=2935) (a:=54) (b:=55) sp2935 sp2989))) (joinSmall (lo:=3044) (a:=217) (b:=218) (joinSmall (lo:=3044) (a:=108) (b:=109) (joinSmall (lo:=3044) (a:=54) (b:=54) sp3044 sp3098) (joinSmall (lo:=3152) (a:=54) (b:=55) sp3152 sp3206)) (joinSmall (lo:=3261) (a:=109) (b:=109) (joinSmall (lo:=3261) (a:=54) (b:=55) sp3261 sp3315) (joinSmall (lo:=3370) (a:=54) (b:=55) sp3370 sp3424)))))) (joinSmall (lo:=3479) (a:=1740) (b:=1740) (joinSmall (lo:=3479) (a:=870) (b:=870) (joinSmall (lo:=3479) (a:=435) (b:=435) (joinSmall (lo:=3479) (a:=217) (b:=218) (joinSmall (lo:=3479) (a:=108) (b:=109) (joinSmall (lo:=3479) (a:=54) (b:=54) sp3479 sp3533) (joinSmall (lo:=3587) (a:=54) (b:=55) sp3587 sp3641)) (joinSmall (lo:=3696) (a:=109) (b:=109) (joinSmall (lo:=3696) (a:=54) (b:=55) sp3696 sp3750) (joinSmall (lo:=3805) (a:=54) (b:=55) sp3805 sp3859))) (joinSmall (lo:=3914) (a:=217) (b:=218) (joinSmall (lo:=3914) (a:=108) (b:=109) (joinSmall (lo:=3914) (a:=54) (b:=54) sp3914 sp3968) (joinSmall (lo:=4022) (a:=54) (b:=55) sp4022 sp4076)) (joinSmall (lo:=4131) (a:=109) (b:=109) (joinSmall (lo:=4131) (a:=54) (b:=55) sp4131 sp4185) (joinSmall (lo:=4240) (a:=54) (b:=55) sp4240 sp4294)))) (joinSmall (lo:=4349) (a:=435) (b:=435) (joinSmall (lo:=4349) (a:=217) (b:=218) (joinSmall (lo:=4349) (a:=108) (b:=109) (joinSmall (lo:=4349) (a:=54) (b:=54) sp4349 sp4403) (joinSmall (lo:=4457) (a:=54) (b:=55) sp4457 sp4511)) (joinSmall (lo:=4566) (a:=109) (b:=109) (joinSmall (lo:=4566) (a:=54) (b:=55) sp4566 sp4620) (joinSmall (lo:=4675) (a:=54) (b:=55) sp4675 sp4729))) (joinSmall (lo:=4784) (a:=217) (b:=218) (joinSmall (lo:=4784) (a:=108) (b:=109) (joinSmall (lo:=4784) (a:=54) (b:=54) sp4784 sp4838) (joinSmall (lo:=4892) (a:=54) (b:=55) sp4892 sp4946)) (joinSmall (lo:=5001) (a:=109) (b:=109) (joinSmall (lo:=5001) (a:=54) (b:=55) sp5001 sp5055) (joinSmall (lo:=5110) (a:=54) (b:=55) sp5110 sp5164))))) (joinSmall (lo:=5219) (a:=870) (b:=870) (joinSmall (lo:=5219) (a:=435) (b:=435) (joinSmall (lo:=5219) (a:=217) (b:=218) (joinSmall (lo:=5219) (a:=108) (b:=109) (joinSmall (lo:=5219) (a:=54) (b:=54) sp5219 sp5273) (joinSmall (lo:=5327) (a:=54) (b:=55) sp5327 sp5381)) (joinSmall (lo:=5436) (a:=109) (b:=109) (joinSmall (lo:=5436) (a:=54) (b:=55) sp5436 sp5490) (joinSmall (lo:=5545) (a:=54) (b:=55) sp5545 sp5599))) (joinSmall (lo:=5654) (a:=217) (b:=218) (joinSmall (lo:=5654) (a:=108) (b:=109) (joinSmall (lo:=5654) (a:=54) (b:=54) sp5654 sp5708) (joinSmall (lo:=5762) (a:=54) (b:=55) sp5762 sp5816)) (joinSmall (lo:=5871) (a:=109) (b:=109) (joinSmall (lo:=5871) (a:=54) (b:=55) sp5871 sp5925) (joinSmall (lo:=5980) (a:=54) (b:=55) sp5980 sp6034)))) (joinSmall (lo:=6089) (a:=435) (b:=435) (joinSmall (lo:=6089) (a:=217) (b:=218) (joinSmall (lo:=6089) (a:=108) (b:=109) (joinSmall (lo:=6089) (a:=54) (b:=54) sp6089 sp6143) (joinSmall (lo:=6197) (a:=54) (b:=55) sp6197 sp6251)) (joinSmall (lo:=6306) (a:=109) (b:=109) (joinSmall (lo:=6306) (a:=54) (b:=55) sp6306 sp6360) (joinSmall (lo:=6415) (a:=54) (b:=55) sp6415 sp6469))) (joinSmall (lo:=6524) (a:=217) (b:=218) (joinSmall (lo:=6524) (a:=108) (b:=109) (joinSmall (lo:=6524) (a:=54) (b:=54) sp6524 sp6578) (joinSmall (lo:=6632) (a:=54) (b:=55) sp6632 sp6686)) (joinSmall (lo:=6741) (a:=109) (b:=109) (joinSmall (lo:=6741) (a:=54) (b:=55) sp6741 sp6795) (joinSmall (lo:=6850) (a:=54) (b:=55) sp6850 sp6904))))))) (joinSmall (lo:=6959) (a:=3480) (b:=3480) (joinSmall (lo:=6959) (a:=1740) (b:=1740) (joinSmall (lo:=6959) (a:=870) (b:=870) (joinSmall (lo:=6959) (a:=435) (b:=435) (joinSmall (lo:=6959) (a:=217) (b:=218) (joinSmall (lo:=6959) (a:=108) (b:=109) (joinSmall (lo:=6959) (a:=54) (b:=54) sp6959 sp7013) (joinSmall (lo:=7067) (a:=54) (b:=55) sp7067 sp7121)) (joinSmall (lo:=7176) (a:=109) (b:=109) (joinSmall (lo:=7176) (a:=54) (b:=55) sp7176 sp7230) (joinSmall (lo:=7285) (a:=54) (b:=55) sp7285 sp7339))) (joinSmall (lo:=7394) (a:=217) (b:=218) (joinSmall (lo:=7394) (a:=108) (b:=109) (joinSmall (lo:=7394) (a:=54) (b:=54) sp7394 sp7448) (joinSmall (lo:=7502) (a:=54) (b:=55) sp7502 sp7556)) (joinSmall (lo:=7611) (a:=109) (b:=109) (joinSmall (lo:=7611) (a:=54) (b:=55) sp7611 sp7665) (joinSmall (lo:=7720) (a:=54) (b:=55) sp7720 sp7774)))) (joinSmall (lo:=7829) (a:=435) (b:=435) (joinSmall (lo:=7829) (a:=217) (b:=218) (joinSmall (lo:=7829) (a:=108) (b:=109) (joinSmall (lo:=7829) (a:=54) (b:=54) sp7829 sp7883) (joinSmall (lo:=7937) (a:=54) (b:=55) sp7937 sp7991)) (joinSmall (lo:=8046) (a:=109) (b:=109) (joinSmall (lo:=8046) (a:=54) (b:=55) sp8046 sp8100) (joinSmall (lo:=8155) (a:=54) (b:=55) sp8155 sp8209))) (joinSmall (lo:=8264) (a:=217) (b:=218) (joinSmall (lo:=8264) (a:=108) (b:=109) (joinSmall (lo:=8264) (a:=54) (b:=54) sp8264 sp8318) (joinSmall (lo:=8372) (a:=54) (b:=55) sp8372 sp8426)) (joinSmall (lo:=8481) (a:=109) (b:=109) (joinSmall (lo:=8481) (a:=54) (b:=55) sp8481 sp8535) (joinSmall (lo:=8590) (a:=54) (b:=55) sp8590 sp8644))))) (joinSmall (lo:=8699) (a:=870) (b:=870) (joinSmall (lo:=8699) (a:=435) (b:=435) (joinSmall (lo:=8699) (a:=217) (b:=218) (joinSmall (lo:=8699) (a:=108) (b:=109) (joinSmall (lo:=8699) (a:=54) (b:=54) sp8699 sp8753) (joinSmall (lo:=8807) (a:=54) (b:=55) sp8807 sp8861)) (joinSmall (lo:=8916) (a:=109) (b:=109) (joinSmall (lo:=8916) (a:=54) (b:=55) sp8916 sp8970) (joinSmall (lo:=9025) (a:=54) (b:=55) sp9025 sp9079))) (joinSmall (lo:=9134) (a:=217) (b:=218) (joinSmall (lo:=9134) (a:=108) (b:=109) (joinSmall (lo:=9134) (a:=54) (b:=54) sp9134 sp9188) (joinSmall (lo:=9242) (a:=54) (b:=55) sp9242 sp9296)) (joinSmall (lo:=9351) (a:=109) (b:=109) (joinSmall (lo:=9351) (a:=54) (b:=55) sp9351 sp9405) (joinSmall (lo:=9460) (a:=54) (b:=55) sp9460 sp9514)))) (joinSmall (lo:=9569) (a:=435) (b:=435) (joinSmall (lo:=9569) (a:=217) (b:=218) (joinSmall (lo:=9569) (a:=108) (b:=109) (joinSmall (lo:=9569) (a:=54) (b:=54) sp9569 sp9623) (joinSmall (lo:=9677) (a:=54) (b:=55) sp9677 sp9731)) (joinSmall (lo:=9786) (a:=109) (b:=109) (joinSmall (lo:=9786) (a:=54) (b:=55) sp9786 sp9840) (joinSmall (lo:=9895) (a:=54) (b:=55) sp9895 sp9949))) (joinSmall (lo:=10004) (a:=217) (b:=218) (joinSmall (lo:=10004) (a:=108) (b:=109) (joinSmall (lo:=10004) (a:=54) (b:=54) sp10004 sp10058) (joinSmall (lo:=10112) (a:=54) (b:=55) sp10112 sp10166)) (joinSmall (lo:=10221) (a:=109) (b:=109) (joinSmall (lo:=10221) (a:=54) (b:=55) sp10221 sp10275) (joinSmall (lo:=10330) (a:=54) (b:=55) sp10330 sp10384)))))) (joinSmall (lo:=10439) (a:=1740) (b:=1740) (joinSmall (lo:=10439) (a:=870) (b:=870) (joinSmall (lo:=10439) (a:=435) (b:=435) (joinSmall (lo:=10439) (a:=217) (b:=218) (joinSmall (lo:=10439) (a:=108) (b:=109) (joinSmall (lo:=10439) (a:=54) (b:=54) sp10439 sp10493) (joinSmall (lo:=10547) (a:=54) (b:=55) sp10547 sp10601)) (joinSmall (lo:=10656) (a:=109) (b:=109) (joinSmall (lo:=10656) (a:=54) (b:=55) sp10656 sp10710) (joinSmall (lo:=10765) (a:=54) (b:=55) sp10765 sp10819))) (joinSmall (lo:=10874) (a:=217) (b:=218) (joinSmall (lo:=10874) (a:=108) (b:=109) (joinSmall (lo:=10874) (a:=54) (b:=54) sp10874 sp10928) (joinSmall (lo:=10982) (a:=54) (b:=55) sp10982 sp11036)) (joinSmall (lo:=11091) (a:=109) (b:=109) (joinSmall (lo:=11091) (a:=54) (b:=55) sp11091 sp11145) (joinSmall (lo:=11200) (a:=54) (b:=55) sp11200 sp11254)))) (joinSmall (lo:=11309) (a:=435) (b:=435) (joinSmall (lo:=11309) (a:=217) (b:=218) (joinSmall (lo:=11309) (a:=108) (b:=109) (joinSmall (lo:=11309) (a:=54) (b:=54) sp11309 sp11363) (joinSmall (lo:=11417) (a:=54) (b:=55) sp11417 sp11471)) (joinSmall (lo:=11526) (a:=109) (b:=109) (joinSmall (lo:=11526) (a:=54) (b:=55) sp11526 sp11580) (joinSmall (lo:=11635) (a:=54) (b:=55) sp11635 sp11689))) (joinSmall (lo:=11744) (a:=217) (b:=218) (joinSmall (lo:=11744) (a:=108) (b:=109) (joinSmall (lo:=11744) (a:=54) (b:=54) sp11744 sp11798) (joinSmall (lo:=11852) (a:=54) (b:=55) sp11852 sp11906)) (joinSmall (lo:=11961) (a:=109) (b:=109) (joinSmall (lo:=11961) (a:=54) (b:=55) sp11961 sp12015) (joinSmall (lo:=12070) (a:=54) (b:=55) sp12070 sp12124))))) (joinSmall (lo:=12179) (a:=870) (b:=870) (joinSmall (lo:=12179) (a:=435) (b:=435) (joinSmall (lo:=12179) (a:=217) (b:=218) (joinSmall (lo:=12179) (a:=108) (b:=109) (joinSmall (lo:=12179) (a:=54) (b:=54) sp12179 sp12233) (joinSmall (lo:=12287) (a:=54) (b:=55) sp12287 sp12341)) (joinSmall (lo:=12396) (a:=109) (b:=109) (joinSmall (lo:=12396) (a:=54) (b:=55) sp12396 sp12450) (joinSmall (lo:=12505) (a:=54) (b:=55) sp12505 sp12559))) (joinSmall (lo:=12614) (a:=217) (b:=218) (joinSmall (lo:=12614) (a:=108) (b:=109) (joinSmall (lo:=12614) (a:=54) (b:=54) sp12614 sp12668) (joinSmall (lo:=12722) (a:=54) (b:=55) sp12722 sp12776)) (joinSmall (lo:=12831) (a:=109) (b:=109) (joinSmall (lo:=12831) (a:=54) (b:=55) sp12831 sp12885) (joinSmall (lo:=12940) (a:=54) (b:=55) sp12940 sp12994)))) (joinSmall (lo:=13049) (a:=435) (b:=435) (joinSmall (lo:=13049) (a:=217) (b:=218) (joinSmall (lo:=13049) (a:=108) (b:=109) (joinSmall (lo:=13049) (a:=54) (b:=54) sp13049 sp13103) (joinSmall (lo:=13157) (a:=54) (b:=55) sp13157 sp13211)) (joinSmall (lo:=13266) (a:=109) (b:=109) (joinSmall (lo:=13266) (a:=54) (b:=55) sp13266 sp13320) (joinSmall (lo:=13375) (a:=54) (b:=55) sp13375 sp13429))) (joinSmall (lo:=13484) (a:=217) (b:=218) (joinSmall (lo:=13484) (a:=108) (b:=109) (joinSmall (lo:=13484) (a:=54) (b:=54) sp13484 sp13538) (joinSmall (lo:=13592) (a:=54) (b:=55) sp13592 sp13646)) (joinSmall (lo:=13701) (a:=109) (b:=109) (joinSmall (lo:=13701) (a:=54) (b:=55) sp13701 sp13755) (joinSmall (lo:=13810) (a:=54) (b:=55) sp13810 sp13864)))))))) (joinSmall (lo:=13919) (a:=6960) (b:=6960) (joinSmall (lo:=13919) (a:=3480) (b:=3480) (joinSmall (lo:=13919) (a:=1740) (b:=1740) (joinSmall (lo:=13919) (a:=870) (b:=870) (joinSmall (lo:=13919) (a:=435) (b:=435) (joinSmall (lo:=13919) (a:=217) (b:=218) (joinSmall (lo:=13919) (a:=108) (b:=109) (joinSmall (lo:=13919) (a:=54) (b:=54) sp13919 sp13973) (joinSmall (lo:=14027) (a:=54) (b:=55) sp14027 sp14081)) (joinSmall (lo:=14136) (a:=109) (b:=109) (joinSmall (lo:=14136) (a:=54) (b:=55) sp14136 sp14190) (joinSmall (lo:=14245) (a:=54) (b:=55) sp14245 sp14299))) (joinSmall (lo:=14354) (a:=217) (b:=218) (joinSmall (lo:=14354) (a:=108) (b:=109) (joinSmall (lo:=14354) (a:=54) (b:=54) sp14354 sp14408) (joinSmall (lo:=14462) (a:=54) (b:=55) sp14462 sp14516)) (joinSmall (lo:=14571) (a:=109) (b:=109) (joinSmall (lo:=14571) (a:=54) (b:=55) sp14571 sp14625) (joinSmall (lo:=14680) (a:=54) (b:=55) sp14680 sp14734)))) (joinSmall (lo:=14789) (a:=435) (b:=435) (joinSmall (lo:=14789) (a:=217) (b:=218) (joinSmall (lo:=14789) (a:=108) (b:=109) (joinSmall (lo:=14789) (a:=54) (b:=54) sp14789 sp14843) (joinSmall (lo:=14897) (a:=54) (b:=55) sp14897 sp14951)) (joinSmall (lo:=15006) (a:=109) (b:=109) (joinSmall (lo:=15006) (a:=54) (b:=55) sp15006 sp15060) (joinSmall (lo:=15115) (a:=54) (b:=55) sp15115 sp15169))) (joinSmall (lo:=15224) (a:=217) (b:=218) (joinSmall (lo:=15224) (a:=108) (b:=109) (joinSmall (lo:=15224) (a:=54) (b:=54) sp15224 sp15278) (joinSmall (lo:=15332) (a:=54) (b:=55) sp15332 sp15386)) (joinSmall (lo:=15441) (a:=109) (b:=109) (joinSmall (lo:=15441) (a:=54) (b:=55) sp15441 sp15495) (joinSmall (lo:=15550) (a:=54) (b:=55) sp15550 sp15604))))) (joinSmall (lo:=15659) (a:=870) (b:=870) (joinSmall (lo:=15659) (a:=435) (b:=435) (joinSmall (lo:=15659) (a:=217) (b:=218) (joinSmall (lo:=15659) (a:=108) (b:=109) (joinSmall (lo:=15659) (a:=54) (b:=54) sp15659 sp15713) (joinSmall (lo:=15767) (a:=54) (b:=55) sp15767 sp15821)) (joinSmall (lo:=15876) (a:=109) (b:=109) (joinSmall (lo:=15876) (a:=54) (b:=55) sp15876 sp15930) (joinSmall (lo:=15985) (a:=54) (b:=55) sp15985 sp16039))) (joinSmall (lo:=16094) (a:=217) (b:=218) (joinSmall (lo:=16094) (a:=108) (b:=109) (joinSmall (lo:=16094) (a:=54) (b:=54) sp16094 sp16148) (joinSmall (lo:=16202) (a:=54) (b:=55) sp16202 sp16256)) (joinSmall (lo:=16311) (a:=109) (b:=109) (joinSmall (lo:=16311) (a:=54) (b:=55) sp16311 sp16365) (joinSmall (lo:=16420) (a:=54) (b:=55) sp16420 sp16474)))) (joinSmall (lo:=16529) (a:=435) (b:=435) (joinSmall (lo:=16529) (a:=217) (b:=218) (joinSmall (lo:=16529) (a:=108) (b:=109) (joinSmall (lo:=16529) (a:=54) (b:=54) sp16529 sp16583) (joinSmall (lo:=16637) (a:=54) (b:=55) sp16637 sp16691)) (joinSmall (lo:=16746) (a:=109) (b:=109) (joinSmall (lo:=16746) (a:=54) (b:=55) sp16746 sp16800) (joinSmall (lo:=16855) (a:=54) (b:=55) sp16855 sp16909))) (joinSmall (lo:=16964) (a:=217) (b:=218) (joinSmall (lo:=16964) (a:=108) (b:=109) (joinSmall (lo:=16964) (a:=54) (b:=54) sp16964 sp17018) (joinSmall (lo:=17072) (a:=54) (b:=55) sp17072 sp17126)) (joinSmall (lo:=17181) (a:=109) (b:=109) (joinSmall (lo:=17181) (a:=54) (b:=55) sp17181 sp17235) (joinSmall (lo:=17290) (a:=54) (b:=55) sp17290 sp17344)))))) (joinSmall (lo:=17399) (a:=1740) (b:=1740) (joinSmall (lo:=17399) (a:=870) (b:=870) (joinSmall (lo:=17399) (a:=435) (b:=435) (joinSmall (lo:=17399) (a:=217) (b:=218) (joinSmall (lo:=17399) (a:=108) (b:=109) (joinSmall (lo:=17399) (a:=54) (b:=54) sp17399 sp17453) (joinSmall (lo:=17507) (a:=54) (b:=55) sp17507 sp17561)) (joinSmall (lo:=17616) (a:=109) (b:=109) (joinSmall (lo:=17616) (a:=54) (b:=55) sp17616 sp17670) (joinSmall (lo:=17725) (a:=54) (b:=55) sp17725 sp17779))) (joinSmall (lo:=17834) (a:=217) (b:=218) (joinSmall (lo:=17834) (a:=108) (b:=109) (joinSmall (lo:=17834) (a:=54) (b:=54) sp17834 sp17888) (joinSmall (lo:=17942) (a:=54) (b:=55) sp17942 sp17996)) (joinSmall (lo:=18051) (a:=109) (b:=109) (joinSmall (lo:=18051) (a:=54) (b:=55) sp18051 sp18105) (joinSmall (lo:=18160) (a:=54) (b:=55) sp18160 sp18214)))) (joinSmall (lo:=18269) (a:=435) (b:=435) (joinSmall (lo:=18269) (a:=217) (b:=218) (joinSmall (lo:=18269) (a:=108) (b:=109) (joinSmall (lo:=18269) (a:=54) (b:=54) sp18269 sp18323) (joinSmall (lo:=18377) (a:=54) (b:=55) sp18377 sp18431)) (joinSmall (lo:=18486) (a:=109) (b:=109) (joinSmall (lo:=18486) (a:=54) (b:=55) sp18486 sp18540) (joinSmall (lo:=18595) (a:=54) (b:=55) sp18595 sp18649))) (joinSmall (lo:=18704) (a:=217) (b:=218) (joinSmall (lo:=18704) (a:=108) (b:=109) (joinSmall (lo:=18704) (a:=54) (b:=54) sp18704 sp18758) (joinSmall (lo:=18812) (a:=54) (b:=55) sp18812 sp18866)) (joinSmall (lo:=18921) (a:=109) (b:=109) (joinSmall (lo:=18921) (a:=54) (b:=55) sp18921 sp18975) (joinSmall (lo:=19030) (a:=54) (b:=55) sp19030 sp19084))))) (joinSmall (lo:=19139) (a:=870) (b:=870) (joinSmall (lo:=19139) (a:=435) (b:=435) (joinSmall (lo:=19139) (a:=217) (b:=218) (joinSmall (lo:=19139) (a:=108) (b:=109) (joinSmall (lo:=19139) (a:=54) (b:=54) sp19139 sp19193) (joinSmall (lo:=19247) (a:=54) (b:=55) sp19247 sp19301)) (joinSmall (lo:=19356) (a:=109) (b:=109) (joinSmall (lo:=19356) (a:=54) (b:=55) sp19356 sp19410) (joinSmall (lo:=19465) (a:=54) (b:=55) sp19465 sp19519))) (joinSmall (lo:=19574) (a:=217) (b:=218) (joinSmall (lo:=19574) (a:=108) (b:=109) (joinSmall (lo:=19574) (a:=54) (b:=54) sp19574 sp19628) (joinSmall (lo:=19682) (a:=54) (b:=55) sp19682 sp19736)) (joinSmall (lo:=19791) (a:=109) (b:=109) (joinSmall (lo:=19791) (a:=54) (b:=55) sp19791 sp19845) (joinSmall (lo:=19900) (a:=54) (b:=55) sp19900 sp19954)))) (joinSmall (lo:=20009) (a:=435) (b:=435) (joinSmall (lo:=20009) (a:=217) (b:=218) (joinSmall (lo:=20009) (a:=108) (b:=109) (joinSmall (lo:=20009) (a:=54) (b:=54) sp20009 sp20063) (joinSmall (lo:=20117) (a:=54) (b:=55) sp20117 sp20171)) (joinSmall (lo:=20226) (a:=109) (b:=109) (joinSmall (lo:=20226) (a:=54) (b:=55) sp20226 sp20280) (joinSmall (lo:=20335) (a:=54) (b:=55) sp20335 sp20389))) (joinSmall (lo:=20444) (a:=217) (b:=218) (joinSmall (lo:=20444) (a:=108) (b:=109) (joinSmall (lo:=20444) (a:=54) (b:=54) sp20444 sp20498) (joinSmall (lo:=20552) (a:=54) (b:=55) sp20552 sp20606)) (joinSmall (lo:=20661) (a:=109) (b:=109) (joinSmall (lo:=20661) (a:=54) (b:=55) sp20661 sp20715) (joinSmall (lo:=20770) (a:=54) (b:=55) sp20770 sp20824))))))) (joinSmall (lo:=20879) (a:=3480) (b:=3480) (joinSmall (lo:=20879) (a:=1740) (b:=1740) (joinSmall (lo:=20879) (a:=870) (b:=870) (joinSmall (lo:=20879) (a:=435) (b:=435) (joinSmall (lo:=20879) (a:=217) (b:=218) (joinSmall (lo:=20879) (a:=108) (b:=109) (joinSmall (lo:=20879) (a:=54) (b:=54) sp20879 sp20933) (joinSmall (lo:=20987) (a:=54) (b:=55) sp20987 sp21041)) (joinSmall (lo:=21096) (a:=109) (b:=109) (joinSmall (lo:=21096) (a:=54) (b:=55) sp21096 sp21150) (joinSmall (lo:=21205) (a:=54) (b:=55) sp21205 sp21259))) (joinSmall (lo:=21314) (a:=217) (b:=218) (joinSmall (lo:=21314) (a:=108) (b:=109) (joinSmall (lo:=21314) (a:=54) (b:=54) sp21314 sp21368) (joinSmall (lo:=21422) (a:=54) (b:=55) sp21422 sp21476)) (joinSmall (lo:=21531) (a:=109) (b:=109) (joinSmall (lo:=21531) (a:=54) (b:=55) sp21531 sp21585) (joinSmall (lo:=21640) (a:=54) (b:=55) sp21640 sp21694)))) (joinSmall (lo:=21749) (a:=435) (b:=435) (joinSmall (lo:=21749) (a:=217) (b:=218) (joinSmall (lo:=21749) (a:=108) (b:=109) (joinSmall (lo:=21749) (a:=54) (b:=54) sp21749 sp21803) (joinSmall (lo:=21857) (a:=54) (b:=55) sp21857 sp21911)) (joinSmall (lo:=21966) (a:=109) (b:=109) (joinSmall (lo:=21966) (a:=54) (b:=55) sp21966 sp22020) (joinSmall (lo:=22075) (a:=54) (b:=55) sp22075 sp22129))) (joinSmall (lo:=22184) (a:=217) (b:=218) (joinSmall (lo:=22184) (a:=108) (b:=109) (joinSmall (lo:=22184) (a:=54) (b:=54) sp22184 sp22238) (joinSmall (lo:=22292) (a:=54) (b:=55) sp22292 sp22346)) (joinSmall (lo:=22401) (a:=109) (b:=109) (joinSmall (lo:=22401) (a:=54) (b:=55) sp22401 sp22455) (joinSmall (lo:=22510) (a:=54) (b:=55) sp22510 sp22564))))) (joinSmall (lo:=22619) (a:=870) (b:=870) (joinSmall (lo:=22619) (a:=435) (b:=435) (joinSmall (lo:=22619) (a:=217) (b:=218) (joinSmall (lo:=22619) (a:=108) (b:=109) (joinSmall (lo:=22619) (a:=54) (b:=54) sp22619 sp22673) (joinSmall (lo:=22727) (a:=54) (b:=55) sp22727 sp22781)) (joinSmall (lo:=22836) (a:=109) (b:=109) (joinSmall (lo:=22836) (a:=54) (b:=55) sp22836 sp22890) (joinSmall (lo:=22945) (a:=54) (b:=55) sp22945 sp22999))) (joinSmall (lo:=23054) (a:=217) (b:=218) (joinSmall (lo:=23054) (a:=108) (b:=109) (joinSmall (lo:=23054) (a:=54) (b:=54) sp23054 sp23108) (joinSmall (lo:=23162) (a:=54) (b:=55) sp23162 sp23216)) (joinSmall (lo:=23271) (a:=109) (b:=109) (joinSmall (lo:=23271) (a:=54) (b:=55) sp23271 sp23325) (joinSmall (lo:=23380) (a:=54) (b:=55) sp23380 sp23434)))) (joinSmall (lo:=23489) (a:=435) (b:=435) (joinSmall (lo:=23489) (a:=217) (b:=218) (joinSmall (lo:=23489) (a:=108) (b:=109) (joinSmall (lo:=23489) (a:=54) (b:=54) sp23489 sp23543) (joinSmall (lo:=23597) (a:=54) (b:=55) sp23597 sp23651)) (joinSmall (lo:=23706) (a:=109) (b:=109) (joinSmall (lo:=23706) (a:=54) (b:=55) sp23706 sp23760) (joinSmall (lo:=23815) (a:=54) (b:=55) sp23815 sp23869))) (joinSmall (lo:=23924) (a:=217) (b:=218) (joinSmall (lo:=23924) (a:=108) (b:=109) (joinSmall (lo:=23924) (a:=54) (b:=54) sp23924 sp23978) (joinSmall (lo:=24032) (a:=54) (b:=55) sp24032 sp24086)) (joinSmall (lo:=24141) (a:=109) (b:=109) (joinSmall (lo:=24141) (a:=54) (b:=55) sp24141 sp24195) (joinSmall (lo:=24250) (a:=54) (b:=55) sp24250 sp24304)))))) (joinSmall (lo:=24359) (a:=1740) (b:=1740) (joinSmall (lo:=24359) (a:=870) (b:=870) (joinSmall (lo:=24359) (a:=435) (b:=435) (joinSmall (lo:=24359) (a:=217) (b:=218) (joinSmall (lo:=24359) (a:=108) (b:=109) (joinSmall (lo:=24359) (a:=54) (b:=54) sp24359 sp24413) (joinSmall (lo:=24467) (a:=54) (b:=55) sp24467 sp24521)) (joinSmall (lo:=24576) (a:=109) (b:=109) (joinSmall (lo:=24576) (a:=54) (b:=55) sp24576 sp24630) (joinSmall (lo:=24685) (a:=54) (b:=55) sp24685 sp24739))) (joinSmall (lo:=24794) (a:=217) (b:=218) (joinSmall (lo:=24794) (a:=108) (b:=109) (joinSmall (lo:=24794) (a:=54) (b:=54) sp24794 sp24848) (joinSmall (lo:=24902) (a:=54) (b:=55) sp24902 sp24956)) (joinSmall (lo:=25011) (a:=109) (b:=109) (joinSmall (lo:=25011) (a:=54) (b:=55) sp25011 sp25065) (joinSmall (lo:=25120) (a:=54) (b:=55) sp25120 sp25174)))) (joinSmall (lo:=25229) (a:=435) (b:=435) (joinSmall (lo:=25229) (a:=217) (b:=218) (joinSmall (lo:=25229) (a:=108) (b:=109) (joinSmall (lo:=25229) (a:=54) (b:=54) sp25229 sp25283) (joinSmall (lo:=25337) (a:=54) (b:=55) sp25337 sp25391)) (joinSmall (lo:=25446) (a:=109) (b:=109) (joinSmall (lo:=25446) (a:=54) (b:=55) sp25446 sp25500) (joinSmall (lo:=25555) (a:=54) (b:=55) sp25555 sp25609))) (joinSmall (lo:=25664) (a:=217) (b:=218) (joinSmall (lo:=25664) (a:=108) (b:=109) (joinSmall (lo:=25664) (a:=54) (b:=54) sp25664 sp25718) (joinSmall (lo:=25772) (a:=54) (b:=55) sp25772 sp25826)) (joinSmall (lo:=25881) (a:=109) (b:=109) (joinSmall (lo:=25881) (a:=54) (b:=55) sp25881 sp25935) (joinSmall (lo:=25990) (a:=54) (b:=55) sp25990 sp26044))))) (joinSmall (lo:=26099) (a:=870) (b:=870) (joinSmall (lo:=26099) (a:=435) (b:=435) (joinSmall (lo:=26099) (a:=217) (b:=218) (joinSmall (lo:=26099) (a:=108) (b:=109) (joinSmall (lo:=26099) (a:=54) (b:=54) sp26099 sp26153) (joinSmall (lo:=26207) (a:=54) (b:=55) sp26207 sp26261)) (joinSmall (lo:=26316) (a:=109) (b:=109) (joinSmall (lo:=26316) (a:=54) (b:=55) sp26316 sp26370) (joinSmall (lo:=26425) (a:=54) (b:=55) sp26425 sp26479))) (joinSmall (lo:=26534) (a:=217) (b:=218) (joinSmall (lo:=26534) (a:=108) (b:=109) (joinSmall (lo:=26534) (a:=54) (b:=54) sp26534 sp26588) (joinSmall (lo:=26642) (a:=54) (b:=55) sp26642 sp26696)) (joinSmall (lo:=26751) (a:=109) (b:=109) (joinSmall (lo:=26751) (a:=54) (b:=55) sp26751 sp26805) (joinSmall (lo:=26860) (a:=54) (b:=55) sp26860 sp26914)))) (joinSmall (lo:=26969) (a:=435) (b:=435) (joinSmall (lo:=26969) (a:=217) (b:=218) (joinSmall (lo:=26969) (a:=108) (b:=109) (joinSmall (lo:=26969) (a:=54) (b:=54) sp26969 sp27023) (joinSmall (lo:=27077) (a:=54) (b:=55) sp27077 sp27131)) (joinSmall (lo:=27186) (a:=109) (b:=109) (joinSmall (lo:=27186) (a:=54) (b:=55) sp27186 sp27240) (joinSmall (lo:=27295) (a:=54) (b:=55) sp27295 sp27349))) (joinSmall (lo:=27404) (a:=217) (b:=218) (joinSmall (lo:=27404) (a:=108) (b:=109) (joinSmall (lo:=27404) (a:=54) (b:=54) sp27404 sp27458) (joinSmall (lo:=27512) (a:=54) (b:=55) sp27512 sp27566)) (joinSmall (lo:=27621) (a:=109) (b:=109) (joinSmall (lo:=27621) (a:=54) (b:=55) sp27621 sp27675) (joinSmall (lo:=27730) (a:=54) (b:=55) sp27730 sp27784)))))))))
  have good : (List.range 27839).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 775000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 27838 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 27838 := by
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


private def packet (i : ℕ) : ℕ := (if i < 197 then (if i < 98 then (if i < 49 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 10 then 0 else (if i < 11 then 0 else 0)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0 else (if i < 14 then 0 else 0)) else (if i < 16 then 0 else (if i < 17 then 0 else 0))) else (if i < 21 then (if i < 19 then 0 else (if i < 20 then 0 else 0)) else (if i < 22 then 0 else (if i < 23 then 0 else 0))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0 else (if i < 26 then 0 else 0)) else (if i < 28 then 0 else (if i < 29 then 0 else 0))) else (if i < 33 then (if i < 31 then 0 else (if i < 32 then 0 else 0)) else (if i < 34 then 0 else (if i < 35 then 0 else 0)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0 else (if i < 38 then 0 else 0)) else (if i < 40 then 0 else (if i < 41 then 0 else 0))) else (if i < 45 then (if i < 43 then 0 else (if i < 44 then 0 else 0)) else (if i < 47 then (if i < 46 then 0 else 0) else (if i < 48 then 0 else 0)))))) else (if i < 73 then (if i < 61 then (if i < 55 then (if i < 52 then (if i < 50 then 0 else (if i < 51 then 0 else 0)) else (if i < 53 then 0 else (if i < 54 then 0 else 0))) else (if i < 58 then (if i < 56 then 0 else (if i < 57 then 0 else 0)) else (if i < 59 then 0 else (if i < 60 then 0 else 0)))) else (if i < 67 then (if i < 64 then (if i < 62 then 0 else (if i < 63 then 0 else 0)) else (if i < 65 then 0 else (if i < 66 then 0 else 0))) else (if i < 70 then (if i < 68 then 0 else (if i < 69 then 0 else 0)) else (if i < 71 then 0 else (if i < 72 then 0 else 0))))) else (if i < 85 then (if i < 79 then (if i < 76 then (if i < 74 then 0 else (if i < 75 then 0 else 0)) else (if i < 77 then 0 else (if i < 78 then 0 else 0))) else (if i < 82 then (if i < 80 then 0 else (if i < 81 then 0 else 0)) else (if i < 83 then 0 else (if i < 84 then 0 else 0)))) else (if i < 91 then (if i < 88 then (if i < 86 then 0 else (if i < 87 then 0 else 0)) else (if i < 89 then 0 else (if i < 90 then 0 else 0))) else (if i < 94 then (if i < 92 then 0 else (if i < 93 then 0 else 0)) else (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else 0))))))) else (if i < 147 then (if i < 122 then (if i < 110 then (if i < 104 then (if i < 101 then (if i < 99 then 0 else (if i < 100 then 0 else 0)) else (if i < 102 then 0 else (if i < 103 then 0 else 0))) else (if i < 107 then (if i < 105 then 0 else (if i < 106 then 0 else 0)) else (if i < 108 then 0 else (if i < 109 then 0 else 0)))) else (if i < 116 then (if i < 113 then (if i < 111 then 0 else (if i < 112 then 0 else 0)) else (if i < 114 then 0 else (if i < 115 then 0 else 0))) else (if i < 119 then (if i < 117 then 0 else (if i < 118 then 0 else 0)) else (if i < 120 then 0 else (if i < 121 then 0 else 0))))) else (if i < 134 then (if i < 128 then (if i < 125 then (if i < 123 then 0 else (if i < 124 then 0 else 0)) else (if i < 126 then 0 else (if i < 127 then 0 else 0))) else (if i < 131 then (if i < 129 then 0 else (if i < 130 then 0 else 0)) else (if i < 132 then 0 else (if i < 133 then 0 else 0)))) else (if i < 140 then (if i < 137 then (if i < 135 then 0 else (if i < 136 then 0 else 0)) else (if i < 138 then 0 else (if i < 139 then 0 else 0))) else (if i < 143 then (if i < 141 then 0 else (if i < 142 then 0 else 0)) else (if i < 145 then (if i < 144 then 0 else 0) else (if i < 146 then 0 else 0)))))) else (if i < 172 then (if i < 159 then (if i < 153 then (if i < 150 then (if i < 148 then 0 else (if i < 149 then 0 else 0)) else (if i < 151 then 0 else (if i < 152 then 0 else 0))) else (if i < 156 then (if i < 154 then 0 else (if i < 155 then 0 else 0)) else (if i < 157 then 0 else (if i < 158 then 0 else 0)))) else (if i < 165 then (if i < 162 then (if i < 160 then 0 else (if i < 161 then 0 else 0)) else (if i < 163 then 0 else (if i < 164 then 0 else 0))) else (if i < 168 then (if i < 166 then 0 else (if i < 167 then 0 else 0)) else (if i < 170 then (if i < 169 then 0 else 0) else (if i < 171 then 0 else 0))))) else (if i < 184 then (if i < 178 then (if i < 175 then (if i < 173 then 0 else (if i < 174 then 0 else 0)) else (if i < 176 then 0 else (if i < 177 then 0 else 0))) else (if i < 181 then (if i < 179 then 0 else (if i < 180 then 0 else 0)) else (if i < 182 then 0 else (if i < 183 then 0 else 0)))) else (if i < 190 then (if i < 187 then (if i < 185 then 0 else (if i < 186 then 0 else 0)) else (if i < 188 then 0 else (if i < 189 then 0 else 0))) else (if i < 193 then (if i < 191 then 0 else (if i < 192 then 0 else 0)) else (if i < 195 then (if i < 194 then 0 else 0) else (if i < 196 then 0 else 0)))))))) else (if i < 296 then (if i < 246 then (if i < 221 then (if i < 209 then (if i < 203 then (if i < 200 then (if i < 198 then 0 else (if i < 199 then 0 else 0)) else (if i < 201 then 0 else (if i < 202 then 0 else 0))) else (if i < 206 then (if i < 204 then 0 else (if i < 205 then 0 else 0)) else (if i < 207 then 0 else (if i < 208 then 0 else 0)))) else (if i < 215 then (if i < 212 then (if i < 210 then 0 else (if i < 211 then 0 else 0)) else (if i < 213 then 0 else (if i < 214 then 0 else 0))) else (if i < 218 then (if i < 216 then 0 else (if i < 217 then 0 else 0)) else (if i < 219 then 0 else (if i < 220 then 0 else 0))))) else (if i < 233 then (if i < 227 then (if i < 224 then (if i < 222 then 0 else (if i < 223 then 0 else 0)) else (if i < 225 then 0 else (if i < 226 then 0 else 0))) else (if i < 230 then (if i < 228 then 0 else (if i < 229 then 0 else 0)) else (if i < 231 then 0 else (if i < 232 then 0 else 0)))) else (if i < 239 then (if i < 236 then (if i < 234 then 0 else (if i < 235 then 0 else 0)) else (if i < 237 then 0 else (if i < 238 then 0 else 0))) else (if i < 242 then (if i < 240 then 0 else (if i < 241 then 0 else 0)) else (if i < 244 then (if i < 243 then 0 else 0) else (if i < 245 then 0 else 0)))))) else (if i < 271 then (if i < 258 then (if i < 252 then (if i < 249 then (if i < 247 then 0 else (if i < 248 then 0 else 0)) else (if i < 250 then 0 else (if i < 251 then 0 else 0))) else (if i < 255 then (if i < 253 then 0 else (if i < 254 then 0 else 0)) else (if i < 256 then 0 else (if i < 257 then 0 else 0)))) else (if i < 264 then (if i < 261 then (if i < 259 then 0 else (if i < 260 then 0 else 0)) else (if i < 262 then 0 else (if i < 263 then 0 else 0))) else (if i < 267 then (if i < 265 then 0 else (if i < 266 then 0 else 0)) else (if i < 269 then (if i < 268 then 0 else 0) else (if i < 270 then 0 else 0))))) else (if i < 283 then (if i < 277 then (if i < 274 then (if i < 272 then 0 else (if i < 273 then 0 else 0)) else (if i < 275 then 0 else (if i < 276 then 0 else 0))) else (if i < 280 then (if i < 278 then 0 else (if i < 279 then 0 else 0)) else (if i < 281 then 0 else (if i < 282 then 0 else 0)))) else (if i < 289 then (if i < 286 then (if i < 284 then 0 else (if i < 285 then 0 else 0)) else (if i < 287 then 0 else (if i < 288 then 0 else 0))) else (if i < 292 then (if i < 290 then 0 else (if i < 291 then 0 else 0)) else (if i < 294 then (if i < 293 then 0 else 0) else (if i < 295 then 0 else 0))))))) else (if i < 345 then (if i < 320 then (if i < 308 then (if i < 302 then (if i < 299 then (if i < 297 then 0 else (if i < 298 then 0 else 0)) else (if i < 300 then 0 else (if i < 301 then 0 else 0))) else (if i < 305 then (if i < 303 then 0 else (if i < 304 then 0 else 0)) else (if i < 306 then 0 else (if i < 307 then 0 else 0)))) else (if i < 314 then (if i < 311 then (if i < 309 then 0 else (if i < 310 then 0 else 0)) else (if i < 312 then 0 else (if i < 313 then 0 else 0))) else (if i < 317 then (if i < 315 then 0 else (if i < 316 then 0 else 0)) else (if i < 318 then 0 else (if i < 319 then 0 else 0))))) else (if i < 332 then (if i < 326 then (if i < 323 then (if i < 321 then 0 else (if i < 322 then 0 else 0)) else (if i < 324 then 0 else (if i < 325 then 0 else 0))) else (if i < 329 then (if i < 327 then 0 else (if i < 328 then 0 else 0)) else (if i < 330 then 0 else (if i < 331 then 0 else 0)))) else (if i < 338 then (if i < 335 then (if i < 333 then 0 else (if i < 334 then 0 else 0)) else (if i < 336 then 0 else (if i < 337 then 0 else 0))) else (if i < 341 then (if i < 339 then 0 else (if i < 340 then 0 else 0)) else (if i < 343 then (if i < 342 then 0 else 0) else (if i < 344 then 0 else 0)))))) else (if i < 370 then (if i < 357 then (if i < 351 then (if i < 348 then (if i < 346 then 0 else (if i < 347 then 0 else 0)) else (if i < 349 then 0 else (if i < 350 then 0 else 0))) else (if i < 354 then (if i < 352 then 0 else (if i < 353 then 0 else 0)) else (if i < 355 then 0 else (if i < 356 then 0 else 0)))) else (if i < 363 then (if i < 360 then (if i < 358 then 0 else (if i < 359 then 0 else 0)) else (if i < 361 then 0 else (if i < 362 then 0 else 0))) else (if i < 366 then (if i < 364 then 0 else (if i < 365 then 0 else 0)) else (if i < 368 then (if i < 367 then 0 else 0) else (if i < 369 then 0 else 0))))) else (if i < 382 then (if i < 376 then (if i < 373 then (if i < 371 then 0 else (if i < 372 then 0 else 0)) else (if i < 374 then 0 else (if i < 375 then 0 else 0))) else (if i < 379 then (if i < 377 then 0 else (if i < 378 then 0 else 0)) else (if i < 380 then 0 else (if i < 381 then 0 else 0x24f51272cf15109c448520f0ef46c02fc14e08e43a617708b82e80b8000024f4b442bc946498246e20a0ec06962ea14708d039816a08b02f80b8000024f457f2b6144896045a2000ea46802d213f088c38c16108302c00b2000024f3fd02a293ac91e4391ec0e0c65a2d4140889838216408602e00ba000024f3a002b694349484451f28e4c6662de14388b83a417908802980b0000024f34292bb947096e4672070ed06a82f114a88cc3b017d09283300d0000024f2e6d2b614409624531f58e386642d713f087038e16308502ac0b4000024f28582dd15609ec48e2170f386de31115989643e618709303180c0000024f227b2bf144497c4532030e9c6ac2f915089003be18709703200c4000024f1c8e2c514e49bc4862180f346e030b15509183c218509583280da000024f16a72c694e49ba47a2050ea86a22f314d08ec3c418608c02f80b8000024f109b2d895589f249421b0f406e230015509283ba18309403040c4000024f0ac72b9145c9884692060e886902da13b886436c15b08582b80b2000024f05122ae93e893e44e1f40e3c66a2dd138086838016708982ec0c8000024eff5b2b093f093a4431f80e406622ce13b085c38416808682d00b4000024ef9752c914e49c04792108ee06ac2f914e09283dc19209a03140d0000024ef3982bd94789904642038eac6802dd14188ac3a217308f03180d0000024eed892d6950c9ba4812068ee06ba2f014408b43aa18308f82c40b4000024ee7b22bb14649644531ff8e7067c2e214888dc3ba18209283300cc000024ee1f22b2940c94a4421f20e1865a2cf14588b838c17508982cc0c2000024edbf72cf94e89ca4812170f246aa2eb14708cc3a017808e02d80ae000024ed5f12d0951c9ce4882198f386dc31015408fc3aa18208d830c0c0000024ed0212b6144c9744602058ebc6982e214408a838e16708a82d40bc000024eca412bd945c97e45e2020e8867c2dd13d886438017108c82ec0cc000024ec4792b694209624571f88e446542cf13b083837c16a08982a00b4000024ebe8e2bf148898e46c20f8ee06b42f614a890c3be17a08e03180c4000024eb8a12c714b89a647620b8ec86be2ff14b08d03a016d08782b80b4000024eb2d82b7944c9644591fe0e786922dc14408943a417b08e02d00c0000024ead162b3943c9684551f70e4c6882eb14508c83a417008c82ec0bc000024ea7372c1145c9764551f98e5c68e2ef14588ac3a818109583180d0000024ea1632c194d89a84732070ebc69a2f514c08ec3d417708e83080c2000024e9b932b4144c97245a1fb8e9067a2e114308943a617a09002f40c4000024e95c32ba146c97a4601fd8e706682df13f888839017208d02e00bc000024e8ff22b5942c96044f1f60e646822e0142089c3b618109202f80b0000024e8a132bb946898e46f2070ea86ac30114d08ec3b018209283100be000024e84442b9946896a4602008e6467e2df141889039a17108902d00b4000024e7e4e2c814b89984632008e9868c2e113f888038e16908482c009c000024e783a2dd9580a104a221f8f6470031815609283da18d09703180cc000024e72682b714549724531f90e9468e2f014a88c83a217109402fc0b0000024e6c812c814f89b447920e0ef46ce31115609183d218709783240ca000024e66ae2ba144096c45d2038e6c68a2e814488ac3a017508c82ec0b8000024e60e32b5943895e45c1f58e386482cb13a086837816308582b809c000024e5aef2c714cc9aa47520c0efc6b22f814d08f43e2191096035c0cc000024e54e32d595149ca48a2158f1c6d230a15489283d818a09683300c2000024e4f1f2b7943494c4441f38e306662cf13c088038c16b08702dc0ac000024e49242cb94c499c4772080e986882de14488b83b417308982b80b2000024e43402c214e09a847d20c0ee46a42f1148089c39617308582b40ae000024e3d6b2b8145c9604581f88e7069e2f614d08dc3c217e08b02f80c8000024e376e2d194fc9aa47820d8ecc69a2f1142889c38c16f088031c0b8000024e31b32b513fc94244e1f30e3066c2d613e08a839217108902ec0c6000024e2bba2c894e09ce48a20f8f106ac2f414d090c3ce18709782f40b0000024e25e52ba945495c44e1f80e4c6802de13b887437a16c08302c00b0000024e20292af940496245c1fa8e6c65e2cd140086c38216907e829c0ac000024e1a4b2c0948898246820d0f0c6d22fd14e09043d4186095833c0da000024e14722be946496c4571fd0e806822f014808c439616808782b80b0000024e0e8a2c894bc9be47b2108f186c430615088e03b217308a02dc0d0000024e089b2c894849964702070eac6a42f214b88cc3b018a09683500c0000024e02ca2b5144898045f2070edc6ca2f614888b839e16f08e02f80b4000024dfcc62d215289c247e2150f106c430015088ec3b017708e83040a6000024df6f12bf949097845e2028e986962e3140089039e16608382a80b0000024df11e2b9145897c4521fa8e5c65c2d113d087037a16108402b40a0000024deb362c914bc99646c2090edc6a02f214908fc3b818409582f40c2000024de57e2b014049564511fb8e3c66e2d814288ac39616f08402d809c000024ddf812c614dc9aa47f20e8ef46be308155890c3d218609302f80be000)))) else (if i < 388 then (if i < 385 then (if i < 383 then 0x250c9442a993a492442f1ee0e1c6682e114008a839816908982e40b80000250c3722b894349824652048ec06882e313e889838016a07f02b00b20000250bd982bd144096e45a2010e706682de141089437c16808382bc0b00000250b7cd2b8946c9844612030e886802e814308dc3a617108982c40b60000250b1f02c3148499c47120f8eac6862e814b09003d418508f03000c40000250ac1a2bd144496645b1fb8e4465c2ca13a084838a16208902c80b60000250a62d2c494b898847220b0ec86a02f214c88e03c017808d02fc0ae0000250a00f2dc95689f249020f0ed46ac2f514808b839a17108d03040ce00002509a482b394249484511fe0ea068a2e914789083ae18009403140b8000025094862ae13f494a4441f60e306682d214208a038417508b82d00b400002508eb92b9144895e4572028e8869e2f614988f03b818209283000ba000025088d42c1949c97c46f20e0ebc6b6304150890c3d418709583440c2000025082e22c994c899e46e2060ee46b02f514888d83a216e08682d00b800002507d372ad13c09484461f48e606642d213d886837c15f08282d00ba000025077482c714c099a46c1ff0ebc69a2ec148089c38616d08482cc0b4000025071772b7941c96244d1fb8e706882ec14388c839c17308a02f40ca00002506b8c2c4148c98e4752090eb86a42e814808b439816f08a02d80c4000025065cf2b594309744581fc0e886aa2f614788d83bc17f08902e80ae00002505ff22c294b09924662090ef86be30115609483d018509803080c2000025059ed2d515289f049f21d0f686ee31a15809383dc18209103080b6000025053f52c914b499847120d0ee86ce303155893c3d417c08f82e40bc00002504e002c894d09a247c20e0ebc6b62fa14b88e83ae17808e82ec0a8000025048082c694b89aa46d20c8edc6b62fb14f09143c418b09883380d00000250420f2cb94c09ac4712070ec06a82f214e08e83b217708d02d00b000002503c412b3944896e44f1fc8e7c6882e7141889839a16f08982ac0a2000025036752ba145097645a1fd8e8468c2df143888838e16b08782d00be000025030b22b4142095a44d1f98e8c65e2cc13c086436815b08682dc0b600002502a992dd15589e648b2178f586ee30b14f89143ca18c09983200cc000025024b72c4148897a45c1fe0ea869c2f214a88ac3a817708802ac0b000002501ec62ca14b09a047320c8f046c82f614e09003bc17b08902d80b6000025019122a993d893443a1f28e2c65c2d614508c03a817a08e83040be0000250131d2cf95209d047d2098eac67e2ef14688d03b617308982f00ca00002500d2f2ce94e49b847520c8ecc6a22f414b88dc3b017508e02fc0c0000025007482c514a49984722058ed86aa2ff15509143ca187094030c09c000025001662c414b09964782128ef86b62fd15089003c217608f82fc0bc000024ffb952bd94649624551f38e2066c2e9147889c39a17508d82d00ba000024ff5ba2c114849844602058e7c6762dc13e089839017108b02d40b2000024fefe92bb148897e45f2000eac6b22f014d88e43b217208e02f80b4000024fe9f12cf95089ce48c2140f4c6d030b152893c3d219509d036c0d6000024fe40f2c414b49a647a2158f086cc2fb14a09003ba17308c83100d0000024fde1c2cc94c89a047120b0ecc6a42f7152090c3c217d08d02f00c0000024fd83b2c114b49ac4792068eb068c2e814508c03b617308b02c80ac000024fd2352d715449d44792078ed06982ee14688c43ba18309203000b8000024fcc412c714d09964662070eb869a2f214a88f43a616708482bc0ac000024fc6622c414809844611ff0eb068e2f014e08c83ac17b08d82c00b6000024fc0a72af143c96644e1f38e286562d613d885036816208602b80b0000024fbaae2c714949844622050e8868e2e514b08e83b218008b02dc0be000024fb4db2bb147096444e1fd0e6c6962e714288cc3a817a08e03100d0000024faf012ba146c97a4672008e8866e2e814388bc3b217e09083040ba000024fa9172c614c89ae47820d8ee46b02f814788b83a417008882c40ac000024fa3562b4941493643c1ee0e0c65e2d2141088c39416b08b82d00ae000024f9d8c2b7945897245a1fe8e9467c2e214388a83a217108903080c2000024f97ae2c2949c99447320b8ed06b22ff14b89003be18008f02e80b8000024f91d22be946496e45f1fe8eac6a82fa14f090c3b817508e02dc0a8000024f8c142af93f49444531ff8e6468e2ee14808a439a17608802fc0c4000024f85f22e515e4a344b02210fa872032616289803f21a409c03380c4000024f80112c514989884631fd0e946842ed14b88c43ae17208d02e00b4000024f7a382c1148c99645e2080ec86ae2fa14d08f03ba181095031c0c4000024f747a2af943c9464471fc0e686762da141887c39017208802d80c6000024f6e9d2bb945497645b2018ea46a42e313e888038816908a02d80a4000024f68d02b694389604521fd8e5867e2dd142089438a16d088029009a000024f62fd2c1148898c4752080eac69c2eb14c090c3ac17c08e83040be000024f5d022c8146898a4621fd0e706862dd14088d83a217e08a02e40c2000024f57262bd946097c4642058e7c6a22f814c08d83b617708802c00a4000 else (if i < 384 then 0x25240482be945498c4642038e8468a2e614108983a017208882f80b600002523a982b113f092a43c1f10e1465c2c9133882837615e08782d80b80000252349c2ce94e49be47a2140f4c6d4307152892c3ca18a08d82e80b000002522e922d4951c9d64882120f346c630515109143e019009203000ba000025228bd2bb147c98245d1fc8e946822e714488b039e16e08602c80cc000025223012b4143497045e2018ea469c2eb14608bc3a617908d02e40c400002521d1d2c214ac99a4772098eb469e2e814388d83a418409503440d8000025217512b3945496c45e1ff0ea06982f314808dc3a417a08a02e80b8000025211332db954c9e64922180f546e6315159893c3c018909503340d200002520b4c2c294b099c46d2098ebc6aa2e814a88f83be17b09082e40be000025205512d094f49c647820c8f206cc30a15709343ce18c09903080b80000251ffa32a5939890c4321ee0dfc6502ce134884436016108382b80ac0000251f9d22b814389704592008ea86882e414588e43b617a09383040ba0000251f3d52d195189f24a121e0f306e430d14e89283c418409002d00b80000251eddc2cd14e49b647e2100eec6c02fb14b88e43bc18008b82e40b40000251e7f82c3147c9784672028ec46a02f014d08e03bc17e08e82f40c40000251e2432a993dc91e4281ec0e146522c6138883437016108102cc0b80000251dc512c994c899847d20f8f046d430815409203d818509603300da0000251d6502ce94e09a447e2158f146d031115709243e419009303100be0000251d05c2ca95009ca47c20f8eec6b02eb14708c03ac173091830c0c00000251ca952bd146898e4752048ea06942ee14c88f43c017909083180cc0000251c4b72c1148897c46b2080ee46c830b158891c3b617c08b02cc0b20000251bee52be147098846b20a0ef06ce30315088f43ba18809783440d40000251b9052bb94789724602040ea069c2ee14b89243d618808d82e00b00000251b32b2b7145497045d2020eb86922ef14208dc3b818208f82f00d00000251ad532be14909904792088ec06b02fb14d08f43bc181096031c0be0000251a7642c494bc9ba48220f0f2c6d231215709283d017f08a82f00c80000251a1892c0148c9a047020a8ee469c2ee14508cc3aa17a08d82c80aa00002519bab2bf949c98c46d2058ea46942ec14a08d43b617608e02f80c4000025195c62c0948898a45e2000e846982f714888ec3d218208f03340c800002518ffa2b294309464461f78e506822f014a88dc3b618109082f00ba00002518a182c2148c98e4632038eb068c2f014408b839a17a08902ec0b0000025184352bc147097e4622068eb86b42f514f88f03bc18009483180c200002517e692c014c09a647520a8ed86b02f714c08cc3aa18008c02d80aa000025178922bd948097a4571fc8e706802dd13e089039a16e08a02cc0a6000025172c42b314109544561fb0e686842db13c087c3a217908e03340c600002516cf32bd149498e4662070eb86982f114488b839c16808082bc0b8000025167292b1944496c45d2010e986962f215389143b818308f02f40bc000025161522bb946c98846c2058eb46a02f214608b03ac17d08e832c0da00002515b6f2c694c89a247c2108f1c6d631115489203da18c09283180ce000025155862c594a498c47720d0ec86a62ef14408783a617408482dc0b000002514fa52c494909864642080ec46a22f0142087c38c17208d82f00b000002514a1429713389084241e38dc462c2b5133082c37a15a08702f00bc000025144332c1949c99046b20d0ef46aa2f114708b43b017409183080c400002513e532c094bc99645f1fa8e506782e2140888838816908802c80bc0000251387f2be144096e4531fa8e2866c2e0142887c38a16107e82ac0be000025132b22bc949c99446620a8eb46a62f814b08cc3ba18408b82e40c600002512cd72ba145c96e45a1fc8e506862e614008c039416e08e82e40aa000025127192b7944c97445a1fc0e7467a2e114808ac3ac17f08e02fc0c0000025121202cb94c89a246f2078eb86aa2f814d08c43b217909182e80c600002511b642a693b89304331ed8dec63e2b612f881036015008202a80a2000025115622cf15089c047c20c8ecc6ba2ff14b88c83ac17508f82e80a200002510f832c114a49a246c2058ec86b42f414e89083c418209083200d0000025109a12bf947897e4682030ec869a2ef14808d83be18208f03140b8000025103c42bb146897a4602000e746942f814d88ec3b417c08a02d80ae0000250fe0c2ac13cc9384451fa8e6067e2e214388d83b617a08b02ec0c00000250f7fe2d4153c9d048b2168f406c030114e88e03b617c08f02dc0bc0000250f2592a493e89424471f60e3c65a2d213e089839217308b82c40b80000250ec7c2c0148897e4682058e706722e514408e43b017f09082d40b60000250e6712d3152c9d848220b0ed86a62f014a88cc38e15e08102bc0c00000250e09f2b9942c9644561fa0e706802dd140888c37a15f08402c00a60000250da9b2d014ec9b847a2128f206dc31115f09283c618609482f80a40000250d4c52bc949498446a2090efc6d030815509403da18a09603180d00000250cefb2b7941c95e45a1fa0ec06b82ff14a88e83ae17008902f00c6000 else 0x253b9242c514c89aa46b2028e8868a2e814d88e43b017608602d00b00000253b3622b3946498e4612060eac69c2f514988f43ae18208e03000b80000253ad502d895109ba47e2120eec6ba300152092c3d0183094031c0c80000253a7812bd944896a45b1fd0e9868e2e414808d83ac17b09602f40a60000253a1a32bb946899a4722080ef86c230014f092c3ce18309603300c800002539bd62b7945098045d1fa0e4c6962ef14908c039416f08a02e00b6000025396092bb146c9784652098ea46a62f514d08dc3b616f08a82f40da000025390432b914249604581fa8e5867c2da13e089c39a17008a02dc0c200002538a5c2bf948899445b1ff0e7869c2ec14808c43bc17b09183140c00000253849c2b4146c9764612038e906902e1140887837615c08602b80b200002537ea72c994cc9ae47720b8ec06982e714988d03ae16e08802d80ac000025378952d995689f248c2130f106ca2f915009103be18008d83080a6000025372b92b814389664531fc0e6866c2d613b086c38616808382ec0a600002536d162a713e891c4301ee0e1065e2d813c887c3801670840290096000025367332c214c499c4672068ea06822e414388a438c16c08502ec0b6000025361652b6944895a44b1f80e546782e1145889838e16d08882cc0aa00002535b682d094f89ba47920b0edc6b42f915309183c817e09703240c8000025355772cb14d89b447a2090ec069c2f114788c83b6181091031c0bc00002534f992c2147c98645a2020e786742d413f08a839617a08c830c0d0000025349db2b0142097045e2048ec46b02f215089103d418409203000cc000025343ea2cf95009ae47c2128f386de30a15609503d618a09503180d400002533de32d0151c9d44852120f206d630d159092c3e618d095031c0ec000025338232b8945097a4571fc0e706862e114a08c439817208a02c00b2000025332542b7142c9564531fa8e386622e514588b039a17108a02dc0b000002532c7f2ba14649784652078ec86a22f615009303d218709402f40cc0000253268f2c694b09a24712078ea46942ee14488a439216a08903080aa000025320af2c414b499a47920e0ed06aa2f314e08bc39016a08782d00bc00002531aba2cc94f89b046e2018e8c6922e614908e03c618208e02fc0b6000025314d72c2149c99046f2040ebc6922ea14988a839217108702ec0c400002530f022ba946098c4632030edc6a22fd15289043c018108f82f80c2000025309212c114909904601fc0e7867c2dd14188c03aa16f08b02d40ac0000253034e2bb14b89864632050eb469c2eb14688a438616e08282c40c40000252fd562c714b89b64752090ed86b02f814c88dc3c0180090830c0c00000252f7a12a993e493c44a1f98e6468c2e614208a83b817808d02f80c00000252f1b82c294849784562058ee06b62e914608ec3ba18609483140c40000252ebaa2d895189cc4852110ee46b02f9150891c3e618e093833c0c60000252e5c32be94809784652078ef069c2ed14a09003ba17a08a83200c40000252dfe22bf144896c4661fc8e3067a2e514088b03a417a09082f80c60000252d9ed2cd94fc9d04862118eec6bc305158095c3f41a009d83200be0000252d3fb2ca94c499446f20d0ec06a42ff15309203cc188095031c0b80000252ce1b2bd948496e45b2020e8867c2e914788d43b617708b02e40b60000252c83a2bf947098247120a0ef06b230414c08f83cc18b09002e40b60000252c24d2c894cc99846d2090ec86bc2f314d08e43ae17b09002f80c00000252bc632c894e89ac47c20f0ef46bc30215089103cc195095833c0d60000252b66a2cd94e09b04732098ea06862e7144889438c16708482c40a80000252b0772c894a49ae48c2148f046ce30c15b89703e818f09003140ba0000252aa892c794c899e4662020e906802de14188ac39416708582980ae0000252a4ab2c3948c98e4672018ea46a62fb15008fc3dc19609982fc0ac00002529ece2c094849784622068eb46982f214988d43aa17508f83000ba000025298d52c914d49b247720e8efc6ca30a15389403d818509282f80b8000025293152b294289544431f18e1064e2ca136085437416508502b00a600002528d262c1949099a47420d0ecc69a2f614c09003b418609582e80a40000252874f2c114ac98846f2108edc6bc30215209243c818709203040cc0000252812b2e09598a1a4ad2270fc070c32b165898c40419609d83540c400002527b352cb94b49a647120d8ee46bc2f214b08d03a216f08e03000c0000025275412cb14d499c4742068ebc6b22f614e08f03cc18b09883200ce00002526f4d2ca14d89b64812088ec069e2f214508c83b218009083280d40000252695f2c794d89ac46c2050ea469c2f414908a039415f08602c00a6000025263722c5949c98646a2060ea869a2f214e88e43b818409403280d600002525d942bf948c97a4642048e9868e2e914288c43b617a08e03180c6000025257b62bf14549684551f70e4867c2df142889c39216908782e00a8000025251ff2b013b091c42d1e90df86522cd136086838415908582ec0c000002524c0c2cd14d09b247720e0ef46b030114c88f43dc18909603280c6000025246302c1149097c4571fe8e806aa2ef14988cc39617709083280c4000)) else (if i < 386 then 0x2552f662ba94589684572028e686982f114808c03b217a08d82f40b6000025529842c394a89904742020e9867e2ec14388bc3ce19409602e40ac000025523bd2b5142096c4501fb0e7066e2de14108a038c17008b02f80bc00002551de92be147897245c2040eb069e2fb14e08e43ac17b09202fc0ba000025518252b594309664581f68e486642d313f889839816508282c40ae000025512772a713cc9264401f30e0c6522d613b888839616e08b82f40ca00002550ca02bf146897645d2050ea86902f814788ac3a217608b02d00b6000025506b02cc95049e648e2140f106ba2f614c08e03c618a09383000b6000025501022a993e09424411f38e646742e514288c43a417308f03040c00000254fb402b794409764602000ea86b02ee14408ac39a17d09203380d00000254f5502ca94f89c448220d0ee46b42f415088d43ac17e08d83040cc0000254ef642c714ac9ac47b20c0eec6d831015288f83c618109402dc0c40000254e96f2c914b09a446c2060ed86a62f814988e03bc17c08f82c80bc0000254e38c2c0948499a4651fc0e606722df14608d03a417a09103280cc0000254ddae2c2148c98646920a8e9c6a62fc14b08d43a818408e02f40be0000254d7c82c514b49a047320b0ec869c2f814d88e43b017c08e03000be0000254d2092af944895844f1fa8e886742db14188a439617108682a00a00000254cc152c894f09b247a2108f146c630414e09083bc17108e83200c00000254c6672ac142c9584561f78e546782dd13b886038216c08202ac0b20000254c0742d215389d648a20f8ee86c62fe14d08e439c16f08982e00ba0000254ba902c794bc99e4662008e8c6942f0149089c38e16808702bc0ac0000254b4e72a113789144301ee0e1865e2dc13f88c83b617808702c80b00000254af092c114949864692018e9c6902e814608a43b017b08c82f40b20000254a92b2bf14a89864561fe0e846a22f714988b039c17508b02e00b80000254a3472bd94949824631fe8e746822eb14788c43aa17808d82e40ac00002549d6c2be94a09944652050ea468e2e314908cc3aa17108702f80c2000025497c12ac93e493c44c1f80e7067a2e1145089437c15f08182900980000254920e2a413a892a43e1f20e386722e014288cc39c17b08a830c0bc00002548c342c1148497c45a1fb0e6067a2e314388943b818809102e80c20000254864b2c514bc99846b20c8ef06b630115089043c217e08c03280cc0000254806a2c614bc9a446c2078ed46b62f314808d83aa16e08802d00b200002547a692ce94dc9c04902150f306de30d15b09483e019409b036c0dc0000254748c2c394b09a247720a0eb46a02f214a88e83c618008f82d00b600002546eb02c0948c97a45e2058eb06842e414708c039a18009103240d0000025468b72cd94fc9b847620f8f086cc308151092c3d819309303240ca000025462f32b5146497e4662080eb86982f815308e03b217609002e80c800002545d222bd145c97c4612030ebc6882e7144089839617a08e02d40a80000254575a2b6144897845b1ff0e946942e214608c43aa17d08f03040c0000025451852bd145496245a1f48e386662d213e088838a16a08582d00ba00002544bc72b5946897c4652040ea06842e614a88e43b617708d03000ae0000254460d2ab93fc9424431f10e3c65c2cf13b887838e16d08682d00b2000025440462b1940895044f1ff8e6867c2e214008ac38a16c08902f40b400002543a492cc14c49824621fd8e706742e213f888c3a217008782dc0a8000025434622cb14b499e47020b0eec6b62fc14c08f43d218d09183180c200002542e962bc149498c45e2018ea06842eb14088a03a217308a02e80c2000025428b42c014a09844632048e9c6a62ef14b09143ba17e08d03000be000025422c42c0148499a4722050e9c69a2fb14d08d43bc17d08f02f40ba00002541cc52d114dc9aa4672040ee06be2f714c88d839216f08a82fc0bc000025416d62c694a09904682090ed06be30415309143e218d09383040bc0000254111c2b2940494443f1f10e4067e2de13f085c38c15c08002a80a200002540b1d2cd14e89b047820f8f0c6d030114c88f43b818008f030c0c0000025405662a713c89184241e40dbc6382bf135886039c16e08902e00c60000253ff7b2c5948898e46a2060ec86a82f614a88c83b017808d02c00ac0000253f9a92b814789864662038e886942f214a88b039217008c02f40a20000253f3ab2d014ec9b647920c8ef06c82ff14f88e03b617a08c02f00b20000253eddb2c2146097c45a2008ea468e2e2143089038416408683000c60000253e8192ad13f894e4511fb0e6866a2d5139084836e16508382cc0b60000253e2542b3943096044c1fa8e6c6702d913c087439e17208d82f40c40000253dc602c714909864632080e906882e114688b83a016f08b82e00b80000253d6a32ad93dc93843d1f38e406662d913e084c38016508302b00b60000253d0932d8155c9da49021b0f906f831b15c89343d818709503300cc0000253cab82bb94989824621ff8e946762df14208a83a417908b82fc0c20000253c4b62d415189c84862130f346f030415389083bc17508a02e80ba0000253bf022ac93d89464401f10e0464e2d013f087438416b08782ec0c6000 else (if i < 387 then 0x256a74c2bf148499447120a0ed06a62e8144888c38816a08982c80aa0000256a1732c314a09a446d2050ea06962e5145088c39a17908e83100b800002569b992c1947497a45e2028e9466e2ed148088c37816408282bc0ac000025695c32ba147096e4602010e886802e514608cc39817108902d80b000002568ff82b2142496e4531fe0e986a22f114c88f83ca18008d03280d200002568a4b2a293a892c43b1f38df86482cc13f8864376167081829409a000025684422d795309de4942190f346ea31815d09683ec19a099834c0cc00002567e452d1150c9ce4862140f2c6d631515589203d818a09383100d0000025678722bd146c9844571ff8eb46942f314788b03a616f08782d00b2000025672af2af942895644e1f98e746762de13c087036e16d08b82d40b800002566cc22c1147c98c4662008e686922f314a88a039616a08502ec0ae000025666e72c3947098e46d2048e886862e214108b43a217e08e02f40d0000025660eb2ce950c9b84812130f286c230215589343da18e09383200c800002565b2c2af13fc93e4461f30e406662d2135087038a16608482d80c8000025655452c794cc9a24702070ec46a82fa14a08ec3c219109803440de00002564f2c2db95709f848e2138f406f8315157891c3c218509202fc0cc000025649802aa13dc94644b1f78e4466a2d713b884836e15f07e82a80a20000256438f2c914e09b04702080e8868e2f014e08e03ba17808f82f80ba00002563dc32b513f89344481f98e586762ec14a891c3ce18209202f80b8000025637d52c614b499446c2070eb46a82ee14408b039c17909103240da0000256320a2b2145096c4642030e9c6742e214188bc3ba17d09102f40b200002562c602a593d89344411f68e446742e214788cc3ae17108e83080b0000025626702c714d099a46b2038e8c67c2d913b884436815108302e00c4000025620992b894889804541fd8e9868a2e214608cc3b018009102f80be00002561acd2b4144897845e1fc0eb86a82f314888c43a617d08d02e00b2000025614d82c794a899446a2030ea86a02f214b09003d018e09202ec0b200002560ee12cf14f09ae4762098ee86b82f314a089c38c16408482c80a8000025609042c394a898846b20a8eec6bc2fc14d08d03ae16d08802dc0b8000025603362b894409804611fe0e646902e514888ec3b817c08e83200bc0000255fd4e2c8948c9944652038eb46982e4144089838e16608783000b20000255f7842b5943c9644561fb0e706742e014408b83a016a08c82ec0bc0000255f1a02c394b899e47b20b0ee46bc2f714b08dc3b217c090830c0c60000255eba52d095109c44792110ef86ca30714f08f83be18809183100ac0000255e5be2c694d89aa4752090ec46b42fe14a88f03b218408f03200c60000255dff52b1144098c46a2048eb468c2eb14888b43a017809183480d60000255da222b994649924692048eb06a42f514a08cc3ac17f08b82fc0de0000255d4402bf146897e4642050eac68e2de13d88a039e17008902f40c80000255ce3a2d5153c9da4922190f3c6e62fe15789283d019209983300c80000255c8822b0145098e4642020e986882e4145089839216408382e40a20000255c28c2d014f49b64822130f106be2ff14988d83ba17a08f02e80b40000255bcc62b6146c95c4591fc0e806782eb144088839217508f82dc0c00000255b6e02c0949498c46320a0ee46b02f814e08e83a617508b02e40aa0000255b1122bc147097c46b2080ea86a02f5152090c3c817f08e82b40be0000255ab382ba143496445c2058eb869a2f414f88fc3ca17c08c031c0cc0000255a5482c794f09b847c2108f186d830d15289043b617c08c82f00b200002559f762b7146495a45a1ff0e746882f214d09003e618908d83140c4000025599922bd946496a45f1ff0e6c68c2dd140088838016208102b0092000025593bb2bb94909724581fd8e5468e2ea14688b037616108682bc0ac00002558dc72cb94e09b647a20e8ee86c02f114b88f83c017c08b02c80c4000025587d32c8949097645a2060ea86ae2f915008dc3ac16e08682c00ba000025581ba2dd15589e64902190f5c6e830915b09503da18509703280d200002557bdc2bb945897c4651fc8e7868c2e614688b039816608382c00a80000255761e2b093fc93443c1f08de06362d2137886438c16708902c80aa000025570372c414e899e4692090ec06962e814989003bc17809103380c200002556a712b3141c95244b1fe8e7869e2f214788a439a16a09003100c80000255649d2ba947c97a4611ff8e986962fd14d88e83aa17708d82e409e00002555e9f2cd94fc9ca47a20c0efc6d02ff15008ec3be18609382fc0be000025558bd2bf147c9924662098ed46b02f814a88ac3a417208602d00c2000025552cb2c514a89a047120a8eec6ac30314c88f83da18209503080be00002554ce42c614cc9c64852158f3c6c830415209083d418c094830c0da000025546fd2bf144c9644592030e8c6a22f014c89043aa17c08902dc0ac000025541112c794dc9b647d2108f106c0306156893c3fc19509483040b800002553b022d315089a04692050ed069a2ef14988d03b217d08902c40a8000025535382b6944895c4602038ebc6982f2148089c3a017f09483140b8000 else 0x2581fdd2c514b89b64822108ee86a42f614d090c3c418108d82dc0ba000025819e82cc14d899e47c20c8efc6b42fa14988b03ae17508c83040be000025814112b994309564501fb8e5065a2d713d885c38216308982bc0a800002580dfb2db158ca004a72208f8c6fc31616009683ee19009082f40b2000025808212bc147096a4531fb8e6467e2e714308a43ae17608f830c0d4000025802382c594dc9b447720c8f006b82f914908bc39a17d08f83300cc0000257fc4d2c914c09bc4742078eb869c2f514588cc3b617f08982d80b40000257f6902ae941494644d1f60e346602d913f885038816908602f80b60000257f0ab2c214909a047420a8edc6c82fe14b08a43a417108f02e00c20000257eacc2c0948498647520e8f106c8302153091c3da18e09603140d60000257e5072b6144497a4621ff8e9c6962ed146089839616f08c02e40c60000257df2b2c714cc9ae48020a8ec068a2e414308ac39216d08a02b80aa0000257d9422c714c499646f2088ee06b02fc14b08b839616f08782a40b00000257d3512c995289d84912150f246cc30d15989503da188099033c0d00000257cd822b8947c9764642050e946802e6141889839616d08982ec0bc0000257c7862ca94d099e46e20b0ee06be2fb15088cc3b617408d82ec0cc0000257c1952cb14ec9b847d2100ef06c630115089303c618109082f40c80000257bbb32c894e09be47d2078ec46a62fd14c08d83ae17a08c82d40ae0000257b5d92c494f89ba4722068ec06a22f614b88bc39a17108b02e40ac0000257b00a2bc14689644561ff0e4c66e2e2145088c37816708482e80b40000257aa302bf149899647620a0eb86902e2143089838c16b08a82c80b20000257a41a2d715449ec49221d0f606d030915409103da18008e82e00a400002579e2e2c914f49c047a20e8f186c030115509303f018e09403000ba0000257986b2ae93f094a44f1fe0e6c6822e514a08dc3c417f09003100be000025792862c594b89b647720d0ec46bc30214d88f43cc18609202f40b400002578c7f2d4151099a47120f8f2c6e031a156891c3d018109683340d0000025786b02bc149899647e20f8f406d030815389003ce17f09503140e2000025780ce2bf147c96e4662080ec46be30014f08f43c617708702c80ac00002577ad12d115109ce4942180f446f431515a09503d818609303100c6000025774ee2c3145497e4642070ef46b42fa151091c3d018d08d02fc0ca00002576f1c2b9143c96444b1f58e4065e2d1141088c39c17a08a03080c40000257694c2b9144c97245d2008eb46922e314788dc3b218409303040be000025763632c494a498247020b8ef06b82fa14a88e43bc184091832c0c800002575d9a2ba944896e45c2058eb86a42ef14d08ec3ca18608e03100cc000025757cd2bd148c99647420d0ee86c630515109003b8181093031c0ca000025751ea2bc148098245e2040e886942f314a88fc3b818308d82e40ae00002574c212ba146c96e4582008e686802ec14788d83b417c08c82ec0ae000025746282cc14f89c248120d0f246c4304151094c3dc18e09283040c4000025740552ba145c9644541fc8e846a22f614a88dc3a817308b02dc0b200002573a652c794e49b84862120f206b22f514c89043ba18909783100ba0000257346c2cc94f89c44832158f386da31715789183c418108b83000bc00002572e532e315749ea4922180f146dc30b15689343ec19509a83440d0000025728812b8146c97a45c2008e846982f214c08c43b017b08f83180c4000025722a52c2949499c4682078ed46ac2ef14988f43c017f09002fc0b000002571c9f2d695149c24872140f006ca30a15209203c017c08f02ec0c4000025716e32b7144c97045d1fd8e606742dd14088bc3b218008982f40be000025710e22cf94e09d248520e8ee46c430c15489243d818609503540ce00002570b082bf94c89964672058ec069c2eb13f087839217308b82e00a2000025705172cd94d89b04742078eb06942f614988f83bc18509483300c40000256ff3a2bd946c9664591fd8e8467c2e214688ac3a217208b82e40c40000256f9792b3940c94444a1f28e206622cd135883435215308182d40b20000256f3852c894e49b847f2100f046ce30915609303cc18109082e80bc0000256edaa2ba94609644541fa0e846aa2fc14e89043d618d096832c0d80000256e7ce2c614989a04702050edc6ac2ea14a08e03be18009103080c40000256e2162ab13d895044e1f28e346502ca13a086c38816908782bc0b80000256dc422bd94609404471f98e606722e114508c039817708982d80c40000256d6642c0949098846b2088ecc6a02f514e08e43b017808902ec0c20000256d0992b8148c9944742088ebc6922f314e88d83a417808f02f80bc0000256ca8f2cd14c09b047b20c8efc6c230614a09083ce17c08c02d00c00000256c4c62b9144c96245c2020ea467e2e314a08f03a616f08b82e40ba0000256bebf2d1951c9b047d20f8f386f431815f09503d818409003340bc0000256b8d82c814e099847720d8ef86bc30114d08e43ba17c09083040d40000256b30c2b7144c96644c1ff8e8067c2da14708d43ba184095031c0ac0000256ad2c2c4949c9944672038ea46a22ed14688b43a616c08b02fc0c0000))) else (if i < 391 then (if i < 389 then 0x259959b2cb94c49b447720d8ec46b02f314908d43ae17808a82d00b200002598ff22aa13e89464421f38e186402c413b88ac3a417b08a82f00ae00002598a0a2cd14f89b047320b0edc6c030314d88f43c018808d82ec0b2000025984192ca14bc99c46d2088ed06aa2f414908a039816d08882d40be00002597e502b6945097c4591fb0e5068e2df13f089438c15f08482d80ae0000259789c2ab93e89344421f28e3465e2d713c084436815508202b80a6000025972a92cd14ec9c44762058ea86982ea14688c83be18009183040d400002596cf02b3941c9644581fc8e8c6822e2141888c38616108602ec0ca0000259671e2b5943496645e2058ecc6a42f214608c83b017a087029c0b2000025961342c0147c9844571fa0e6866c2de142889c38e16808382b40b600002595b792b594609604501ff0e6c6862e614008743a017e09403040b00000259558f2be949c98646a2010e706762d913b085437215a08102b00b600002594fa82c194b098846d2078eb069c2e914908c83ac17c09182f00ac000025949e82af94249664491f08e1865c2d113e889838a17708982bc0c2000025944212b514549724662070ea469c2ed14708d83ae17508c82cc0b600002593e412c414bc9a447020b8ef46b82ef14608e439817408e83440d40000259384d2ce95049c248921a0f386e231b15f89743d818d09e036c0dc000025932382d794e89c847f2118ee46be30615388fc3b4182091834c0dc00002592c7c2b5142494c4521fc8e7869a2ed14788d03ba17508782d40aa000025926a72b894609684571ff0e7c6822e014188a83aa16f081029c0aa000025921082a713ac9184311e98e0865e2d9143889839416408802cc0b400002591b102d095389c847d20b0ef06b02f415088f83ae18309683200d4000025915372be94b49a847620b8edc6cc30614f88f43ba18108c02fc0b000002590f5b2c094789764591fa0e486602d213a088438c16a08902ec0ba000025909742cc94e49b446c2070ea86922f314988bc39c17108902d80b8000025903c02a813d893643d1f00e2865c2d413c88a038c16408602b40a60000258fde12be149c98846d2078ec06aa2f7151090c3d818c09402f00c00000258f8062b894489824591fa8e2c6642d613d887c39817508d02e40c20000258f2392ba947898c46c2078ed46be30215088d039816b08c82d00c40000258ec6e2ad142894e4511f58e246442c713d087837616a08782b80a60000258e6a62b4143c9704632030ea06a82fa14b09043d218009082e80c00000258e0ef2ac941894e4531f98e5067e2e213f889037815f08102c40bc0000258dae72d414f09ba47520c0ed06a82ec14d08d43b017308982c80b20000258d5172b8945896a45c1fb0e746a02ea14808a43a018109283040d00000258cf1e2cf15289b04732090eb869c2ef14608cc3c217d09083340c20000258c9422c614b89a047520b8eb06922e714d89103ca18509383280c40000258c3832b0941c94a44f1f58e686682d714188b839a17a08e82e00aa0000258bd952cd14ec9a847920d0ec86a42ff151091c3ca18108902bc0b80000258b7ca2ba14689744682080edc6b02f214888c43ac17909103100d60000258b2062b4144c95244a1f38e1c6642d413a885036e16608402ec0c60000258ac3c2b193fc95a4451f40e646742e514388a83a218008e82f80b80000258a6542c494b49944642060e946922e714408a039817108502d00ac0000258a08b2b5144896a4571fe8e6066e2dc14108d43c818709283240ca00002589ac52bc942895845e1fe8e606842df140088437416408382cc0b0000025894cd2c994e499247720e8edc6bc2f314d88f43c418f095830c0b800002588ee62c214a899647620d0ecc6be30215488ec3d018208a02f80d0000025889082b7141c95c4571fb8e546762d3139084838816608402c80a6000025883392b5948096a4591fe0e8c6a02ef14608b839016e08802d00a200002587d432cd14c49a84792128f046c02ff151892c3be17709182fc0ba0000258776a2be94609764541fa8e546622d7142088038816808582d80c0000025871972b8944897244c1f50e186622d513e88a038e166080826c0aa00002586bcc2b6142c95c4511fd0e4c66c2db13c087c3a417b09083180b40000258661f2aa93dc9264441f70e5c6782df14408a038a16d08c02d80c0000025860852a0938490e42c1e98dfc6402cc135085037817008582f40b000002585a8f2c694ac9aa47620b0eac6982ec14c08d43a816c08882dc0ae000025854b12be947096e4551fa8e706662e414588c43b617008a02e00b600002584ec72c394a899646b2000e706682db13e08b83ac17a08b82e40b0000025848d62cb14e49c247f20f0edc6b42fa154092c3de18d090030c0c0000025843192af140c95c45a1fe8e986862f114688dc3c217e09003080b600002583d422bb946896a4622018e906882da13d084037616408402ac0b60000258376c2bb944c95c4551fe8e7c6822ea14b08dc3c018008d02cc0c60000258317f2cc14f49c04842108ee86ae2fb15288fc3b018109403300cc00002582b982c814d89b847c2118f006b02f714a88b839816b08a02d00bc000025825c12c5147c98a46d2048eb06b230315389243c218909303440dc000 else (if i < 390 then 0x25b0c532ba947898245e2028e8c6882e514288a43a217d091031c0c4000025b06702c314a898c4642040e9c6822e514208a83a617808c030c0b6000025b009a2bf147c97e4652070ec86842e214888a839e17508b02f80be000025afaad2c4948899446e2050ea86a22f714308d0394177095032c0d4000025af4ab2d395209b648c2160f206ca30515109043bc18a09783240d6000025aeecf2be14709764561fa8e806922e814388e439a17408782a80b8000025ae91b2a713b891842b1ea8df86402d213a884836616608582b80ae000025ae3372c314d099e4601ff0e746982ef14988a839416708382ac0b8000025add4c2ca94b89a04702078e986982e8142887438216708682c80ac000025ad74e2d095209ca47e2158f346ea31115f09303ee18e09883240d0000025ad1a92a493a491e4331e98dcc6282af12907fc35415708382c00aa000025acbf32ae141c94c4451f40e206642c4135884837c16108602c40a2000025ac6152bd947096c4682048eb86882e214388c039c17f08f03140c2000025ac0612a813f09444451f40e3064e2cd13a884c37615e08902bc0a0000025aba822bf14609824682048e7c6822eb14708f43b617308d02fc0c2000025ab4b72b7141c9604531fd8e646782db142088437a16908802bc0c4000025aaed62bc948898e46f2088ef06c030615109083ce18608e03240d8000025aa8d52d094e89884722090ea869c2f414c88c83b617e09082f40d0000025aa2fd2b7945096245a2018e8067c2e614088ac3a817708902e40b2000025a9d0e2cc95009c047b20e8f086d230f15088d83be18d09602f00ca000025a97322c0148c9964672040eb46982fb14b08b83b019109583200ce000025a91592bf147498046c2090ee86b02f014c88f039c17408902d40be000025a8b862bd946097245b2020ea46962e2141888438416908382b00b2000025a859b2c494a49a047920c0edc6bc30115108d43be18008e030c0b6000025a7fd82b4940c9464421f68e746742e814388bc39e17d08982e40ba000025a79e52ca94d499a4732078ea86962ee14b08b83a417408f03040ac000025a74292ad93f49524471f58e5465e2e1140089c3a216b08902e80b8000025a6e492c894e09ba4862128f106bc30215289143ae18109082e80b6000025a68782b9945895444d1ff0e5c6762dd142888838217108f830c0cc000025a62822c814ac99246e2090ed86aa300156892c3e218c09403300c8000025a5caf2c194a098e46c2070e9c68a2dc14508b839617b09483040cc000025a56e62ba144c96e4571fb0e846662d214388a438617109183140bc000025a50f32c314b099646b2018e6867c2e214a08b43a217a08b03200cc000025a4b072c514bc98a45a1fb8e646942f414a08b83a817508d02f00b2000025a45272c594bc9a846f20a0edc6b42f814c88e83b018109182f40c0000025a3f622b494409664501fb8e9c6762df13d883c37a15f08502ac0a6000025a39992b1944897a44f1f98e5c6802df13d087039c14f07b829c0b2000025a33a92c5949c98e45e1f98e4c6642d213a88903b218309003040ac000025a2da72d115149be4762068ec46922da14988f43c217908c02d80c2000025a27bb2c894c49a84702080eb86b230015509203be18109683380d4000025a21e92c214cc9be4892158f106e830915509583d618209282ec0c6000025a1c122b9145c99446c2070ebc6b430114f88f83d418a08d02f40d4000025a165e2b094389564531ff0e986882e7140086c37c15c07f02d00b6000025a10892b2943495444b1f78e5466c2cf13b888c39816d08702b40ae000025a0abe2b394749844662068eec6ce30415509143cc18309202f80bc000025a04c92ca94c49a846b2048e9c6942e914588c039c17008b02ec0b60000259fed82c194b898a4611ff8e9069c2eb14a08f83a417208e82f80cc0000259f93d2a593d493a43d1f18e446702df14788dc3a217808e83000c00000259f3782bc146497245f1ff8e8c6aa2ee14a08ec3c418409383180d00000259ed7d2d815509e44882150f0c6d2310154093c3de190099832c0d60000259e7bf2b4144c96e4531f70e386622e314188c03b818409282fc0ba0000259e1e72bc943c9624521f98e506762de13d887839016c08a82e00ca0000259dc012c794ac98e4642040ec46a82f414408b039016308882900920000259d6032d214f49ce48020f8ef86d8306153891c3d418709303000c00000259d0442b694649744682040eb068c2e9142886c38816a08502e00b60000259ca702bc148c97245a2008eb86a42fb14f09043ca18009183300c20000259c4942b9145896245b1fd0e3c6722dc139088439616a08982f00b60000259becb2b714409824662060ebc68a2e914488d43a017308882d80c00000259b8fc2ba146c9804601fe0e9c6942f214688cc3a216f08982f00be0000259b3432ad14009544561fd8e6c68c2e014208b03a217208782f00b60000259ad522cb94d49aa47420c0ee46b62f014888ac38c16708802a00ba0000259a75b2ce95309c64822108f046be2fd157093c3ca189098030c0ba0000259a1592d195149d648b2140f1c6c830615509143ce18309483140d200002599b872bb948498045c1fd8e8869e2f414f88d03c818708c02ec0c0000 else 0x25c84472c2949498a46d1fc0e786902f214588ac3a216e08c82e00ac000025c7e612c594b899646c20a0eb469c2f714788bc3ae17608c031c0c8000025c78902b714509724581fd0ebc6a02f814708ec3ac17708f03000b6000025c72e52a513c89244361f00e146462cd13c887039016a08882e00b8000025c6cf22cc95209be4812110f246c82fd15009103d418809383200cc000025c671b2be148898c45e2020e686722e2141887438615f08382d40ba000025c61132d6955c9e84a52200f746ec30f15d09683f619409c03540d2000025c5b342c0948c99447820a0ec06822e114408b039a16608782b40b6000025c55552c0145c97a4612030eb069c2e814188a83aa179090032c0d2000025c4f5c2cd94fc9d24852178f386dc31715a09383e818b09383140ca000025c498c2b4143096a4481fc8e3466a2da142889839616708182e00bc000025c43a82ca14d89b046c2030e9c69c2f814e08f43b417f08982e409c000025c3d8e2df95789ec49421e0f8c6e230615089003c218409082fc0c0000025c37b92b9946896c4662080ee46ae2f214408cc3a817208a02f40c2000025c31d82c194889944762068e9c6922e814588c039a17008a82f40bc000025c2c152ba946c9704602050e986942ec14808a839a16c08682d80b8000025c265f2a793b492043a1f18dfc62c2bb138084436a14e07902900ac000025c20a42ac93e492643d1f00e4466a2dd142889038817008c83040be000025c1acb2ba14889824551fe8e7c6702d4137886438e17408982fc0bc000025c14c02d395409f04912158f486d030f15409203dc19108f83280d4000025c0ee22c3949499046b2088ed06ae2eb143088c38e15b07d02a009c000025c09142be149098c4601ff0e9069c2f3145089c38e16908902f00b2000025c032c2c194909a447620c0ec869c2f714788cc39a16c08a02f80c0000025bfd5c2bc94809864521fb0e686702dd140888838c16808882d80b2000025bf7802bf14a099246d2050ea86ba2f314c08e83ca17c08882e00d4000025bf1862d195449f049f21e0f3c6d831515a09383ec19709b033c0d8000025beba82c2149898846b2080ec86aa2f314708a839816d08a82ec0c6000025be5ae2d015189da4882150f106d230e15488ec3ba17a08d02e40ca000025bdfd72be94849a04661fe8e686862e614408bc39a176093032c0ca000025bda122b814689804612010ea069a2f314d88f43ca18b09183080c0000025bd41a2c915009b84882168f5c6ca30314d88d43a817008d03200ca000025bce532b7943c96c4571fe0ea46822ed14688e43a817408d03080ce000025bc8792be949499a46a2080ed46ac2f414588c43a018009303480c6000025bc29b2be945097c4602000e9868a2ef14708c439c16708d82e00a0000025bbca02d1952c9da49b2178f386d830815589543f419709b03340ca000025bb6e62b394309664561fb0e486602d413d888839616c08802cc0c8000025bb0fc2c414a899846a2020e806862e5142889038616808602cc0a4000025bab122c394a49904672030eac69e2ef14408b439217808882f80c0000025ba5462b7144c9684491f78e6466c2dc142088c37617108682f00ac000025b9f682be14889904672068ed06a02f614908b439e17309783040c2000025b99562de95509f249421d0f706ea30515008f83b617e09383080c0000025b939a2b4942c9564512010e9c67e2df14688d83ae17309202f00b4000025b8dd42b3940094644e1f48e4066a2d7139887438816708682dc0bc000025b87e72be946098c4621fd0ea46a22f4147089c39617108b02ac0aa000025b81e52d094ec9aa4732108f3c6ec319163896c3e419109583400f4000025b7c162bf14509644541fb0e386622db141888c39016f08d82f00c2000025b76562b4140c9384371f08dfc65c2d913f08903ae18509503300de000025b70852bf145898045c1fe8eb86a62f714c88dc39617d09102fc0ac000025b6a812cb14d89b247e2128f306d830715109083cc186096032c0d0000025b64932c514c49ba47d2120f186d230b15989183d818c09483100b8000025b5eba2bb145c98446920a8eb86942ee14c090c3ba17a08b02ec0c0000025b58d82c0946897a4652010ea06942ea14788b039616a08782f80b6000025b52d92ce14c49ae4762108f306dc319158895c3e818609202fc0ca000025b4cf32c694a098e46a2038e8066c2d313c089839a17009002f00c6000025b47172c7148898c46e20b0ed06a42e914d88c83ae17508a02f80c0000025b41202c894bc9bc47f2138f006c630515389343d018309403340d6000025b3b3f2c494d49b84822118ee86b22f514a88e43a817808d82dc0b6000025b356a2bc946c98445c2030eb86aa2f214c88f43b817d08b02b40a4000025b2f7e2c614c499647120d0ed46b2308155892c3c818509002e40a8000025b29ab2b994489604531f98e4c67c2f114608b83a417008f83140d4000025b23e82af94449784581fc0e606862ea14788c039616c08e82e80cc000025b1df72c994cc9a646e2050e846822e314588e83cc18108f83080c4000025b17f12d195089c84812118f0c6d030915389183de19309403000c2000025b122b2b714149524491f68e2c6502d514488a839816b08b02ec0aa000)) else (if i < 393 then (if i < 392 then 0x25dfca92a813a89264351ed8e0c65e2d5143888c38616d08902f00b2000025df6a52d395189d048f2148f006be30415508e83cc18909203040b8000025df0a52d1151c9da4902148f146b430114d89003b418008f82f80be000025deab62c894d89bc4892160f206ca30315709103c218508e82c80a6000025de50a2a893c49264431f50e6c6622e4144889c39a16d08f03200c6000025ddf192cb94d89a047320e0ef06b62ee14488a839616407c82940ac000025dd91c2cc94e49b447620f8f206d430415389243dc18e097035c0d4000025dd3232ce94e498a46f20b0e886862e7143087837615d08482d00b0000025dcd462bd948098c47120c0f146b830014c09083b417808c02e40aa000025dc7762b994509704581f98e586842eb14688cc3b417d08e030c0d0000025dc1c12ae94149444471f70e7c6722dc14188ac39a17208a02d00a4000025dbbe52c414e89b64822120f206c630014d88dc3b817c08d82f80b8000025db5e52cf15009c84742050ebc69e2f314d08dc3a417208902d80a4000025db01b2b4943c96044d1f38e3066c2de14608ac39616208a82e80ba000025daa3f2bf949499045f2020e586962f114d89083be17908b03140d2000025da46a2bd947897044d1fd8e706782e314788f43b617e09303300cc000025d9e822c614bc99646f2050ed86b02f914808f83a417c09182ec0b4000025d98c02b7947496045b2008e886942e813f08ac38a16808802cc0b8000025d92d52cb94d099a46920e0ef86b22fc15009243d619009483240ba000025d8d022bb146098c4621ff0e4c66a2da13a885037416508b82f40c8000025d87072cc94d49a847520a0ed86c630715509403ee18f09082ec0c2000025d810b2d115189c24822130f106c230915289283d618909282f40c6000025d7b332c7949c9944712058ea869e2ef14d08dc3bc17208e02f00cc000025d757f2a714109424541fd0e406622cd137885839616f08882b40b4000025d6fb32b1940495c4521f80e3865a2d4142088c39616908702f00a8000025d69cb2c314c89aa46d2078eb86ac2fa14808d039e17608902bc0c2000025d640d2b0140893a4451f80e6c6762da140887437c16a08982e80b4000025d5dfa2e1155c9f649921b0f486dc30d154891c3c418809683140cc000025d58122c114749864752098ee46a82f314f89003ba17608f02dc0b8000025d52332b5143097245d1fa0e686842dc13e889039616f08882ec0ae000025d4c532c294989ae4702080eac6942f214c08d03a817508d82dc0b6000025d466d2c314a899e46f2058ec86b0307156093c3ec191099831c0d4000025d406c2cf95189d64852118f146ca30915c09483d018508d82f40b4000025d3aa32b5140494644a1f90e4c66c2d413e888038e16c08902cc0aa000025d34c92bb146096e4541f88e6867a2e313f088839216a08502a0096000025d2ec42d395189c44862170f306d031515a09503ea193095031c0c6000025d28d52cc95089b847b2108f1c6d230215109403d417e09083180b8000025d23002bf948898a4672008ec06a02fb14988b43a016e08682cc0aa000025d1cfa2d815509fe4922148f1c6bc2fb14f89043c417c091830c0c8000025d17422ae94289484481fc0e5c6702dc140088838c16508b82e00b0000025d11472ce14f89c847f20e0ef06b02fe14c08c43c617f08c02f40bc000025d0b752b794349704651fc8e6467c2dd14508d03ba18408f82f00be000025d05ac2bb148c99245c2010eb46962eb14908d83b617e090830c0bc000025cffe42bb144096645c2040e906902ee14c09183c017b08e82ec0c0000025cfa042ba94509724591fc0e5467c2e1142087838617408802b40bc000025cf3f42d0152c9c04852158f086be30215309383d418609783080d4000025cee322b814489744611fb8e786822ea14708b839417208702d40b6000025ce8662b3143094c4431f88e5067e2e314408c03ac17908c02e80be000025ce25d2d695349cc48720c8f006be30215188d43c818709483380be000025cdc882be948098a46a2058edc6902eb14588e03ac17609103100de000025cd6c32b194289684541f90e6466a2e014408ac3b616e08f02d40b0000025cd0f72b5942495244f1fd0e806902eb14988903a617708882d00ae000025ccb1e2b914449584551f40e4867a2e4142889c39a17308782c00aa000025cc50f2d7950c9cc48020b8ec46aa2ff14e89043ba17b09283080b6000025cbf1d2cd94f89b84852130f146ca30615089003b217c08b82c40b2000025cb93d2c094a498c46d2078ec86a42f314508d03a417308a82c80bc000025cb3612c014789944802120f286da30a15189143bc18209283100d8000025cada62b194209424451f18df46462c5138087837a15808282a00a4000025ca7d62b9943c96a4581fe8e746722e013e884c36c17008882e80a6000025ca1d12cd14c499a46920b0ecc6a82ee14308d839a16e08a02c80b4000025c9bf32bc148c98046b2010eb06982f914b88d03b217508c02fc0da000025c96142c794b099c4742080ea46a02f314d09003e618609303000c6000025c90282ca14b899447820e0ee46c430615589583e6192099833c0c6000025c8a2a2d315249e249b21c8f9870a31915d09403ca19709482fc0c8000 else 0x25f74682bf947c97846e20b8f046aa2fe15009043c417c08c82e80b8000025f6e5d2ce14cc9a047320d8eec6b02f114808bc39e17008783080b0000025f68892bf14b09884692020eb06ba2f114e08dc39e17809283180ca000025f62b12b9144c9724662060e9c6922ec14388c839617208902cc0bc000025f5cda2be147c98845b1ff8e886762df13e087438616c08e82ec0ca000025f56f62c3949c99646e20a0ebc69a2ea14788c43a417409082ec0bc000025f50f52d395389e048c2138eec6c22f214988f43d4185095832c0ca000025f4b182be146496e45b2030e7c6662d6135882c376163084029c0b6000025f452d2c714c89aa46e2098eb46a82f914c88e83a617408782d00c0000025f3f302cd15109c84842110f206d430b15409183c018508d02e40b6000025f39692b5142c96c4561fc8e806862dc141886c36816408302c00b4000025f33892c514b898a4672070e9c6a02e514108b43bc17b08982d80b6000025f2dc32b5940093843c1f68e4865c2cb136084c37217008502f00b6000025f27d22cd95089cc4782090ed06a02f114488b83a816f08c831c0ba000025f21e02c294ac98846c2078ea468e2e114308a43b217b08f02f00c0000025f1c1b2ad940095e4501f68e5868a2e414388a039e17208b02e80c4000025f16332c494ac99646c2030ecc69c2f414688b43a616b08782d40c0000025f10532c294b099c4672068ebc6aa2f814e08e03ba18409202fc0b4000025f0a6b2c494809864722078e9c68c2e714888d83a017208a82d80b0000025f04842c994d499a46f20f8f006aa2f914c08bc3b417b08f82e00b4000025efeb32b394189504421f18e3c66c2dd14408b039c17f09383280bc000025ef8c12c914d49ce48b2198f046c630d15309343ec18f09583280c4000025ef2d22ca94ec9b848320f0eec6be30215089183be18609783240c8000025eecf62bb946497445a2010ea069a2ed14588c03ae16d08802d40a0000025ee7102c794b49b447f20d8ea869a2eb14508a438c16008882e40c8000025ee11c2c614a098a4702058e8068c2e713f887838415c08502c40ac000025edb9029693448f04241e50dc462c2c813a087037a16e08a02e80c0000025ed58d2d395209c848521b8f586f0319158093c3ec19209483040d8000025ecf962cb15109be4832128f006d430515789083c818c09383000bc000025ec9d72af14089564491f60e5466e2e514a08e03b417208902ec0be000025ec4082bc947495c4561fb8eac68c2ec14908d83be17e09102fc0bc000025ebe3d2b7143c96444f1fb8e9468e2f114b089838816108282c00a4000025eb87c2b4941494a4431f30e446662d713e889438415f08102b0098000025eb28a2d114c899646b2068ec86a42ef14888bc38e16e08482cc0a8000025eac882d415389cc4922158f686f832115e095c3ce18209403300c8000025ea6832d094f89c44782110f006c0305153091c3e619209303000d0000025ea0bb2b7144496e44a1f60e406622d513c089c39617408982dc0b0000025e9ad82c494c899446f20a0eb86962f114e08e83ba18809803580ce000025e95092be14789844672058eb069a2ee14508bc38816508502dc0c0000025e8f302bf149c99846b2030e946982f514d09003c018c09102e00c0000025e89562ba147498846b2090ec46a22f314788b83b216e08802c80b6000025e83842b8145497a46a2040eb46a22f114c08e03aa17d09183000b0000025e7d8b2cf14e49c24802148f1c6d230c15689303d418809283000c8000025e77b12bd145c9724652068ec06aa2f314a08e83b417f09403080be000025e71b22cc14b498c46b20a0ec86a22e7142889038e17608c02fc0ae000025e6bbb2ca14dc9b847620a0ed86b22fa15208d03bc17608f83040bc000025e65fd2af942895644b1fb0e746962e714588ac3b218108a82d00a8000025e60242bd947897846a2088e9c6ba2fc14d89083c617e08d82d00ba000025e5a3f2c514ac9a647e20b0ed46aa2f0145089c38e17208c02cc0a2000025e547d2b9145c9924692038e7c6922eb14788b439416f08902c80b0000025e4e9b2c714a09a847e2090eb06a82eb14808b43a217b08902d00ae000025e48c62b714709604591ff0eac6a02f014788bc3b016d08602cc0b0000025e42b82d415549ec49621a0f3c6d630114b89543ea19109803300c6000025e3d012b0144097c45a2008eb86862f414a88ec3b018c09783440de000025e37202c3148898a46f2068ec868a2f214b88cc3a817808d030c0ca000025e31262d115309cc4822118f286b6303150890c3c817f08f02e40b4000025e2b2a2cf15009c24782120f086b82f014988cc3a417208b82f40ba000025e25632b493f89424451f50e586742df14588c839017608982f80b6000025e1f652d215089c44862138f286a22f414d08f03b217908f03380c2000025e19b12aa93f094043c1ea0df46522ce138888437c16308702c40c2000025e13c82c094b09b648420d0f186ca30215209103e8188097033c0dc000025e0deb2bd94849844642038ea468c2e314808cc3b417a08582d40c0000025e08112c3947097e4561fe8e446782e1138085c37a15e08502c80a0000025e02502b3945096e4591fc0e8068e2e914488b438a16c08b02e80b6000) else (if i < 394 then 0x260eae52b7144c9784612050e9c68e2dc13a884c36e15e08082a40aa0000260e5292aa93b092c4421f68e2c66e2dc13f088c39016e08602bc0ac0000260df262d114c89ae4832160f246da310159891c3ca18f096830c0cc0000260d9512bc146497e4632078ebc6a830314d89083cc18c09402f00bc0000260d3902ac13dc92a4341eb8dd862a2ba12e082434a14d07f02b00b80000260cd942c714a89a44672020e606682e114108a83ac17d08a82cc0b20000260c7c82be149498a4672070ec06be30414e88ec3ca17e090831c0ba0000260c1e82c414c89aa47d20f0f046de30314989003be18609583280ba0000260bc092bd945c9704561fc8e986a22f514908d83bc18009103380d20000260b61b2ca14c499c4622058e886962f014708a838215d08182bc0b60000260b0502b8941494e44e1fd0e486782e214208a438a16308502b00b00000260aa6f2c294c099e47020a0ef06b630315488f43c017f08903000c20000260a4a32b5946096e4592010e906862ef14a08f03ba17b08a82dc0b400002609ea62d315149c44872108ef06c02fb14708d03a016e08d02d00b4000026098cb2bb944896e45b2000e846962ee14b88dc3aa17308d82cc0a8000026092f12ba945096845c1fb0e6468c2f014a08d43a817b08c03000aa00002608d302b594249684561fb8e8c67a2e2140888838e16a08702e00b60000260875e2b994689804692098ecc6b82f614d88b839a177089030c0be000026081862c0945c97645c2030ee86c42ff15008d43a017808902e00a200002607b9b2c0948899646f2080eb86aa2f114b88d43a817808f83040b0000026075b62c5148899646f2040e946802e514908c83b017908e03140bc00002606fc02d095289d048b2180f586d830014c88c83a616c08502bc0be000026069c42cf14d49bc46d20b8f146ca30915689403e018c09002e00b6000026063e02c294749884622010e846662cf13c886837615808502d40ba00002605dff2c3949c9844642080ecc69e2ee14d08f83bc18209202f40b60000260584e2ae141895a4561fb8e586722df14388b03bc17708d82fc0b80000260526c2c6149899246b2038eb46902ee14d88d03b217e08e03100d200002604ca72b9946c98446c2060ec86a02e714788c439016c08682d40ae000026046b22ce94e89ca4942180f546e831415509203e018c09202e80be000026040d02c2149098846a2050eb86962f214988d43ae176092030c0c600002603af22be948099447520d0f106da30014e88d43b017008a02e00ca000026035162bc948498646b20a0efc6b62fc14c09183bc18308f02f00c800002602f612ad93ec94e44f1fb0e686762da13d887838c16608402900a4000026029a82ab93e093a4401f10e1c6662cc135084437a16b08a82d80b2000026023bb2c614b099e4722040e946922e814708c03a816b08b82f40b400002601dd82c114ac98445b1fb0ea06882e914c08c43a817408e03140c4000026017f02c714b89aa4712058e9869a2f114a88c83ae16c08702c00a80000260120c2c194a499c4692028e806922ec14a08e03a617808d82e00bc00002600c362ba144c95e44f1f30e506702d213c888438816608d02dc0c40000260063e2cc14dc99046f2060e8c69a2f614d88e03b218309303080c2000026000722b994409684592008ea068e2f415089103de18c08e02e40b4000025ffa8c2c514a499446e20a0ea869e2ea14708c03ac17108782e40a8000025ff4ce2b1141c94644d1f10e1464a2ce13d889839217608d82f40c4000025fef182ac13f495244b1f88e806862ef144087438c17a08d82fc0b8000025fe9552af94009444531f78e246662e914888a439017508e02ec0b0000025fe3762c594a099446a2028e8c6662d714408a43ac17508f82c80a8000025fdda72b614409704622040eac68e2e714908c43be17e09083140b8000025fd7f42aa13e892a4431f30e246582d513c888038816f08682c4096000025fd1e72d6952c9d648120f8ec46a42fa14e88c039a17808b02f00d2000025fcc022c2949499646d2020ea46802e9143889438416d08b82e80b6000025fc6282bd14789924722080ec06aa2f4147088837616508902d00a6000025fc0372c714cc9b447b2088f046b62fd14e09083cc180092031c0d0000025fba682ba947c9744682020eb46982ef14908d03b618b08f82f00ba000025fb4a02b6143c96e46c2090eec6982f114988dc3ac18209103280d0000025faedd2ab14109504461fb0e7468c2ec14908dc39c17508b02f40a8000025fa90f2b9144096844a1f58e486642da14988b03b417308c02dc0c2000025fa3492b614709744602050ecc6aa2ff15008e43ba17808b02dc0aa000025f9d9a2a513d892a43f1f38e206602d613a089837a16608202cc0b4000025f97bc2c0947c9884632068eb469e2f6140089c3b017208d82bc0b4000025f91da2bc948098e47120d0ed86d431015809403c018709303280d0000025f8be32cc94e49c04822140f106cc30315088f43c817b08c82f40be000025f861b2b414389624511fb0e4865c2dc13b886837e16308482c00aa000025f80272c814b099e47320f0f2c6de31115a09203d618809102fc0bc000025f7a512ba146498046a2078ed86b62ff15089343d018909303240ca000 else 0x2613155000149898245c2080ed06ae2ec14788cc3b016a08702bc0a200002612b662c494a896a4671ff0e6067e2e3146889839617608f02ec0c4000026125832bf948c9804642030ea86a62f314b89043bc17708d03100bc00002611fd32a993ec9424471f88e486682e014088a839016208282b00b4000026119e12cf94a49824672030e9c6942f715209243c418e09c03180b0000026113d12dc15489e649821f0f746de31315c898840a1a309a83440e000002610de62ca94e89a246920b8ec069a2ee14908d03bc17908482d80b20000261080d2ba147497e4692078eb86902e914208a039c17608a82e40b60000261023a2b3944097445e2000ec46a02e214909083aa17908882dc0b80000260fc582bf147c99646d2028e7c6722e313e88a439216208702e00c20000260f68f2b0943095a4581fe0e886762e014288943ae17608d82f40b00000260f0b32bf146c9944692060eb86a62ef143087438416307e826c08e000)))))))))

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



private theorem b390538 : covered 390538 390637 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390637 : covered 390637 390735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390735 : covered 390735 390834 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390834 : covered 390834 390933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390933 : covered 390933 391032 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391032 : covered 391032 391130 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391130 : covered 391130 391229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391229 : covered 391229 391327 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391327 : covered 391327 391426 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391426 : covered 391426 391524 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391524 : covered 391524 391623 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391623 : covered 391623 391721 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391721 : covered 391721 391820 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391820 : covered 391820 391918 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b391918 : covered 391918 392017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392017 : covered 392017 392115 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392115 : covered 392115 392214 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392214 : covered 392214 392312 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392312 : covered 392312 392411 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392411 : covered 392411 392509 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392509 : covered 392509 392608 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392608 : covered 392608 392706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392706 : covered 392706 392805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392805 : covered 392805 392903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b392903 : covered 392903 393002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393002 : covered 393002 393100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393100 : covered 393100 393199 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393199 : covered 393199 393297 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393297 : covered 393297 393396 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393396 : covered 393396 393494 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393494 : covered 393494 393593 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393593 : covered 393593 393691 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393691 : covered 393691 393790 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393790 : covered 393790 393888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393888 : covered 393888 393987 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b393987 : covered 393987 394086 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394086 : covered 394086 394185 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394185 : covered 394185 394283 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394283 : covered 394283 394382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394382 : covered 394382 394480 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394480 : covered 394480 394579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394579 : covered 394579 394677 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394677 : covered 394677 394776 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394776 : covered 394776 394874 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394874 : covered 394874 394973 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b394973 : covered 394973 395071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395071 : covered 395071 395170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395170 : covered 395170 395268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395268 : covered 395268 395367 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395367 : covered 395367 395465 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395465 : covered 395465 395564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395564 : covered 395564 395663 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395663 : covered 395663 395762 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395762 : covered 395762 395860 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395860 : covered 395860 395959 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b395959 : covered 395959 396057 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396057 : covered 396057 396156 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396156 : covered 396156 396254 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396254 : covered 396254 396353 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396353 : covered 396353 396451 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396451 : covered 396451 396550 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396550 : covered 396550 396648 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396648 : covered 396648 396747 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396747 : covered 396747 396845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396845 : covered 396845 396944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b396944 : covered 396944 397042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397042 : covered 397042 397141 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397141 : covered 397141 397240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397240 : covered 397240 397339 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397339 : covered 397339 397437 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397437 : covered 397437 397536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397536 : covered 397536 397634 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397634 : covered 397634 397733 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397733 : covered 397733 397831 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397831 : covered 397831 397930 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b397930 : covered 397930 398028 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398028 : covered 398028 398127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398127 : covered 398127 398225 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398225 : covered 398225 398324 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398324 : covered 398324 398422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398422 : covered 398422 398521 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398521 : covered 398521 398619 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398619 : covered 398619 398718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398718 : covered 398718 398816 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398816 : covered 398816 398915 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b398915 : covered 398915 399013 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399013 : covered 399013 399112 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399112 : covered 399112 399210 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399210 : covered 399210 399309 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399309 : covered 399309 399407 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399407 : covered 399407 399506 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399506 : covered 399506 399604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399604 : covered 399604 399703 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399703 : covered 399703 399801 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399801 : covered 399801 399900 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399900 : covered 399900 399998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b399998 : covered 399998 400097 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400097 : covered 400097 400195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400195 : covered 400195 400294 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400294 : covered 400294 400393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400393 : covered 400393 400492 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400492 : covered 400492 400590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400590 : covered 400590 400689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400689 : covered 400689 400787 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400787 : covered 400787 400886 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400886 : covered 400886 400984 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b400984 : covered 400984 401083 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401083 : covered 401083 401181 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401181 : covered 401181 401280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401280 : covered 401280 401378 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401378 : covered 401378 401477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401477 : covered 401477 401575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401575 : covered 401575 401674 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401674 : covered 401674 401772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401772 : covered 401772 401871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401871 : covered 401871 401970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b401970 : covered 401970 402069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402069 : covered 402069 402167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402167 : covered 402167 402266 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402266 : covered 402266 402364 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402364 : covered 402364 402463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402463 : covered 402463 402561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402561 : covered 402561 402660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402660 : covered 402660 402758 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402758 : covered 402758 402857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402857 : covered 402857 402955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b402955 : covered 402955 403054 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403054 : covered 403054 403152 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403152 : covered 403152 403251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403251 : covered 403251 403349 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403349 : covered 403349 403448 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403448 : covered 403448 403547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b403547 : covered 403547 403646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 390538 403646 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b390538 b390637) (joinCoverage b390735 b390834)) (joinCoverage (joinCoverage b390933 b391032) (joinCoverage b391130 b391229))) (joinCoverage (joinCoverage (joinCoverage b391327 b391426) (joinCoverage b391524 b391623)) (joinCoverage (joinCoverage b391721 b391820) (joinCoverage b391918 b392017)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b392115 b392214) (joinCoverage b392312 b392411)) (joinCoverage (joinCoverage b392509 b392608) (joinCoverage b392706 b392805))) (joinCoverage (joinCoverage (joinCoverage b392903 b393002) (joinCoverage b393100 b393199)) (joinCoverage (joinCoverage b393297 b393396) (joinCoverage b393494 (joinCoverage b393593 b393691)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b393790 b393888) (joinCoverage b393987 b394086)) (joinCoverage (joinCoverage b394185 b394283) (joinCoverage b394382 b394480))) (joinCoverage (joinCoverage (joinCoverage b394579 b394677) (joinCoverage b394776 b394874)) (joinCoverage (joinCoverage b394973 b395071) (joinCoverage b395170 b395268)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b395367 b395465) (joinCoverage b395564 b395663)) (joinCoverage (joinCoverage b395762 b395860) (joinCoverage b395959 b396057))) (joinCoverage (joinCoverage (joinCoverage b396156 b396254) (joinCoverage b396353 b396451)) (joinCoverage (joinCoverage b396550 b396648) (joinCoverage b396747 (joinCoverage b396845 b396944))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b397042 b397141) (joinCoverage b397240 b397339)) (joinCoverage (joinCoverage b397437 b397536) (joinCoverage b397634 b397733))) (joinCoverage (joinCoverage (joinCoverage b397831 b397930) (joinCoverage b398028 b398127)) (joinCoverage (joinCoverage b398225 b398324) (joinCoverage b398422 b398521)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b398619 b398718) (joinCoverage b398816 b398915)) (joinCoverage (joinCoverage b399013 b399112) (joinCoverage b399210 b399309))) (joinCoverage (joinCoverage (joinCoverage b399407 b399506) (joinCoverage b399604 b399703)) (joinCoverage (joinCoverage b399801 b399900) (joinCoverage b399998 (joinCoverage b400097 b400195)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b400294 b400393) (joinCoverage b400492 b400590)) (joinCoverage (joinCoverage b400689 b400787) (joinCoverage b400886 b400984))) (joinCoverage (joinCoverage (joinCoverage b401083 b401181) (joinCoverage b401280 b401378)) (joinCoverage (joinCoverage b401477 b401575) (joinCoverage b401674 (joinCoverage b401772 b401871))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b401970 b402069) (joinCoverage b402167 b402266)) (joinCoverage (joinCoverage b402364 b402463) (joinCoverage b402561 b402660))) (joinCoverage (joinCoverage (joinCoverage b402758 b402857) (joinCoverage b402955 b403054)) (joinCoverage (joinCoverage b403152 b403251) (joinCoverage b403349 (joinCoverage b403448 b403547))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 390538 ≤ index 750000000/512 := by decide +kernel
private theorem starting_value : fast 750000000=38703181 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 750000000=38703181) (n : ℕ) (low : 750000000≤n) (bound : n≤775000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=750000000
    · rw [first,anchor]
      exact starting_value
    · have past : 750000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤775000000 by omega)
        have within : index n / 512 < 403646 := by omega
        have lower : index 750000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤775000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ750000000To775000000
