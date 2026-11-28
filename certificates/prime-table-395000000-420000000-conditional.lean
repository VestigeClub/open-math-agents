import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ395000000To420000000

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




private def radical : ℕ := 0x5f8b8a94363be6b531cf73e875879c50703bdceef8b2c000c23836f2e8eb7e95a673e9a19d15e65718c27bb98aae5d00e0d6959cdf2d0c65756ad4aa63280c78cc703ece393a19db23d5ac8331f9e3d3995cc5ed9de932059ac3c9c218de776114746dfdf9b6d125dd615eff58e1d2c8ff036d094568ee20f8fdf0a368059425c7972543f63a46c96862240b2813db0e64a0d339f46be23ee884cc4a0c00475dd76fe8caaa594990330e4c3a71e90272e2f3120603717649695634d43b2d5248a4cec3d3c2380399974dbc09984d703dd992b28404d80632f9267fca92dfb5fe18931126d942daae32a4b2e0d6521551fa765d9c6471e00e82e932b4275fb42230115dc2ede4b36112d689c065a046f24afb3b88147f2992f4b912362fcb9120c71e1dc3db5f65f7c092e1f5aed05fbc57eb482febda33def5d31e407273e9cd707e046730c7621a3aa6c287188c12279b9a42aedd4f5084b63477b3980d4d5cdb72891c7631e4ae5fb5d19d2e9aaabb58b9a20ef522dae62054a3c9f07e3eef49a812b6c07efc372a7e779e776a554b961eaeccd8d789ac8307fd447a2cef986cf9120f090ffa87b67cb9cacb967c4ffc9c762e94435176d01746f4814c51aed787f788a3dc9935ecfa8576387610cac7e753e4ef150175d76956595073f5e1573fd49337c5d9412afd564d9875d9f86450a17526eb9a1373d75646d9f09aae8158c79de09fa3705cb7da9a827c5f366175964e773b1654de1219024ac584c402c63c0368fe03277901b6b5ef9f036f4568b360406c69709ceffeeec72f30f2abfba0f92a20e3e6a7ce5e71ff6e28893a35ee9221fce053187d87c62335f175f61c2667cd562a039f6bd5335cf0f529b70c384a2854ea471c234cb7e6082087ada5333eb12673c79a14cad2154779d84e195074af6c9100abe62145d7cd0a939bf147db253193f75dd9397dbdf63b7e52318db61b126c501c4b771e13b3b2ccc7c2d6dab200a8a2c894a03ed9780f5eb1f30c1e8c30c4b8f2c28fa0fcd6af34fe475cd9286c18b94c842b56845c66c966e123c5c52bfe35f7cb665a11cbe80406700b9c80fbd90505b3ea40171a88292eabf41d7dff1433cabb3e7673a2590c695e527cf1b02cef33f2abae0bc4b0226b4552f82e2f08da1400f0c1c8e60ba2f6b906fef53c6d7af2c5f15a48d735513085e39ff9522953769544e8a33928d0b22c7ce65f03811c2dee7f8805734eb48836489daf54134a88fa149dec9cc8c7338b91546dfa0f996370888324f23d3055fda41aeb97206e92e01b649a5ee2f3e794934372ef6bee399cb546308fa6941c81d9c812087c56c70ea058baa83ab1f2600ce91aebd0dee522525acfad7ac5c37437db2a18394dfb735210bdf46e2178814ef78ca2a9b616d3f1dfbce17caec73ecf96e5bc73554aca55247216cd06c8588bb862296e3784b4fb94e99ee42d3e2d327f180316f37dd155d966a3291d923582d1b7cae0616fe6f656598c9a0d3e718a78c75b5bad2b3e55bf901a2c6b2f9960757721f50bfbad9c1d55d00bcf25105ba891ecfa43b346380f6b18d60ab872d2f74951844163710e3c93eef263598d0c52138a3a03ba7e2fd038cb4a84a5059b9379c401d262f4757c0db4606e1544146143c28219f090c59ab18f1082c0df4876aeee6164af179c9ee1e6225e97cbb08fdbd24884e75fe88dc72d9e90f5349a8b88734479a02acbf50d94751b53275966d6d0bef7e2269c7e2d08b717d6673c902cfc16702059c629e13fca3f950e77d2681a6e3b2bb29a87f99e3c5327710c17d298a072967464700c882ff709545fb11805c9789e8dc5b2245f239b320eec6f56b2fa8831695b7e7b48ec19b322a899c1ee41bc0ac2bc5b20f0cfd4e815ddc3e13377973b3ef5d13896fffc424756a51382f1093401ce848f89ea94c9b1bf757e12ec7ed1ce2a9730c6df348120fc98d29f16ba2b684280c82734b5d784281107a3ad4d7946365a2f647572372d580c5c1197e1d3812da7ab5503f6c0de155bb2b27e587591cd58146da07337cb3967aa7811fc692ce6f5be7fe4ed48e0c4b25c5c2b4516efe85f15734e7f04f437ad7f11e0a8f0898a27238cb5f4b4c22a738cc69bd379e05f76ca8fd1d57b5a2d862ee575b19feacf20dba7d98627a2e83f602b68ea2f5a6963cba0895da56ee5eb3c2b1bf4e9384ad7da74cf2b9fe9ad224935a3ec01e41c043450b7879196f57ae4bdda37cf68b3616d5ea2552aabbdc4b1c523945b0acf36d226c45f42805c07c4a3912102fc35d29d2315bb4fc8d55aff78fdca6fca3c223d590a7bfcfe3ef727d6a5c314804e13907c33ff7a3e0f7a3ed7eaa3b25a610c4d2e7a37dfaf42ea33ab136f2a0d96c0a94ab6a270039144588a843e3787164e63ecc46572ed494a61a1d8102aa7075674644060110bf3480d4160d8840b86bdc17589ad16858554558ff7478bf4eb26f719909df7d3aafee7886606cf1ab08df80d375ca8aad80d3998f97c617318d4e2d53fb5563bfde2745b5b5e98c48b3797311602021e1e6d814f73a59deb933744b2792d78236faa41ff466a7162c7c3f24409760af50ce3a92ae09888fb9be9104247345dd6df02d11c5ea837c5d57a5611b8a09d7acd71bcab79243ade46076e151554fdfbfe143f4f6d893af39dc4f185e89dc365a13f04670e51ea97e8dc95db10a3566d06222f640dd4f3d680e97d7a9643e0a693d135b4ed2f6cf73379486c425705b5a6098736781673c167440dd16bc8203644513fe35398c34dcb5710dd7f48af4497ba88d4e4f5dd844f51031b1c1aa8f8aad8b9ce07fa9468504c102a4b1b8ed89d746652bf97dee7d94abe8ba7ae2a416edcef250de49cb87d267656e8fcf3935ecbe253c110d4e67d378934d162122eb0eb875f5942dcf0ac0cffd3c441d312cb6a2dc6a2ed435741711ad7a72a68f264d0ec2305393a39d008f555621c04f08298011920b7e3acf6d036756e37246ca7d4a6b424a2161a61d2d3a97d0528a1c772fe17e2a869102ed6dfab992b036a38b0462e351bef9f92bb26126f09a59601c8e992c61c4e6fd09999d57e2ffc05541d5382dba5fbd92b84402f21ff1cfa3350455b64cc1736b634a84e9dcf78ca66f0c4ec819ff4a508b5e7472bc68c71520b0f09a75df3c6ad5b6b0c9cd98447c791330851419fc3d17654ce1dd0581fd25ade4b32709fb8f108e5398b7d6cd89f5f73b9862a0076d7e415c3e57cd075f23095d998e7e0167fa3190abd592c772a542c0db69266551e3d6731cc19fa01ea27cff31db04d5369776750193d0ecea0b73d23e27f0142e498fc119e36cb914c65234c63dd1e84a2396c52a356e5ad0fc6152216b8aaac8326a45ddbb94141b5f4c4efbb5851d7b7644cd0481771e66eae5301c855f5217867acfea66aafaf8f5a093aa75835896cb1f8af175897bac2ac83acbcd918d106c7c57b1cf6e4fe982b04c91ae7747696bca8cc6697080f1d5c599e5b6742ef679dc1eb5d40bcb83ee1e20f4febeb660a6c0137dc4b956e8ef0da753606377f4b48fc90e026aa9083a1dadced48b8a57f6d70d2e6d8dc2ab137ed9617d1840dbbfa4ee13931626e1309eaa318c8ef2194e14395a33b7aeaf2d0526628365eee4f56de3414d664d30d8f66c1e3b95e72a5cb9d4687e36c129be861a5df3f58ca86c04c87ff7f558455ad9e128117f97042aac2f277515bb2fbe6a74c9c6dc7b1d78e23f7035917b9aade3b03b86a9b8f2149e8f7e1d213a329ba4f4d11b0bc99281484f3440eed9c25d224ade3f24fc5fb3262e275ff9a2b174335de4015e089607df907e0d73f27e8f2459595c2437538a1911fb3e6e3bba06a02cff67f570d83eb2c596aad57cf2aed22a3eaedcb8356a82d1db1f1ca21bc97f7b8ece0d439915c48efc2b306286f026803567589eec441c2368f5c9bba38719ec85969e62d6b1590d31c9605086fcd9faed9197955fa7c77d58f2d1ef2e04f3853e7cee37242c60cf11b5ef5723a7a4348635ae392c1416dd1191470b6cb2d54299bd281d137aebe8dd3d9d6ca7c2a198a3758caa7d36f30249a9d61264794c940847de7e9151af3b9520d13faee502f7850524f078c7e0133f035d1367b355fc7069f248e1ee82ab91bc6dd0c686838751e7c6d8755d0faae1c9369d4f7ae45c3d9b73b8d35f7dd190217a46ac72b63bc9819bfc7ee96e8f1a8ab2000683a273479e723471a4528db5f13bf586d725faf62df3f45d50a7875efd46d72d028e46928c7a6fc677298d3cef77930bad0ce4b0e63d2b1ba230c44d630076aafa51438d0ac7d55e48397cd575a154364149dbef9435ea069ad19792b7efc492c1c207f06be2a013fbd43353726de8efe943a1fad9c8ffa79bd8f67a219f5b1bc45ba37f2b524c3178de3a5bf72fe928ad9f359b7ba05bd2adeeb239b25587bf33fe0efda592f700202c739d211bb5509edbd4c1d6e03e81b5099b0c64f44e14175d5e8c765d1131b1d795eef23b4266a36ea5b0a43455dd30b0682b40f3bc4098959f4c8e171165f76c54e265c60d47f77950bf4efdee450995d9e13be0cac9f8f6aac6a59c090e3aefa5ad36d1da288a6dcfeeb820e6e595eb38768d2d41d50ecbe2bebbcd90e681156bf020fac45f353668f6bdc10be5fa2e867cd430b64f75d41d51987867b29d673f3bf4b700567dd9959ae13cb619e56850c8e6087d0878d14fcffb630c76cd37df30f567e927c38165db5e506fc36a585872a3a212f422ed572ced79655935a1f96d6771aafb2273db180b24c0f08458f829f3fd04cf107431a7c3aaa8c00979ea625738e0919dc50f59492f7d449a6ce51fe0a2c151268a0ed028c12dbff41b9b337eb43896d441bd069a6c3b16ae39015237fa1a07ac98841a43d5ebe5bab782d2c70ddf39c504e30dd5f4137bfa431f444f455ba5ed483daa0b00fb9ed48a10c6dc0bb08f2e54d1be367558ec71b9827c544e39e846a821115fb923873583ec10d65574107e057d1827f565a9950d8e0c31e4ac0746c768b97acb5e69f3b5b95039479c66466360982c552501d4db90640531ffa056f26a0c91f340ca5372c52a598d7710137a09717f2ae68473fd160bb4b110af05f1594a7b1f5158182da6c72c9ff3dac614685482cdc62ae1ce7931e

private def light (n : ℕ) : Bool :=
  if n≤143 then decide n.Prime else n.gcd 38543707171800727705215657364933250819444321791546964384326881276202845420193798918144180166658987031965483631719296696351202501036957071818603525354815944336166154976340651887541505545310130488593669331551403376640000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤20493) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 143 = 38543707171800727705215657364933250819444321791546964384326881276202845420193798918144180166658987031965483631719296696351202501036957071818603525354815944336166154976340651887541505545310130488593669331551403376640000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 143 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤20493 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 40 := by unfold smallValid; decide +kernel

private theorem sp40 : smallValid 40 40 := by unfold smallValid; decide +kernel

private theorem sp80 : smallValid 80 40 := by unfold smallValid; decide +kernel

private theorem sp120 : smallValid 120 40 := by unfold smallValid; decide +kernel

private theorem sp160 : smallValid 160 40 := by unfold smallValid; decide +kernel

private theorem sp200 : smallValid 200 40 := by unfold smallValid; decide +kernel

private theorem sp240 : smallValid 240 40 := by unfold smallValid; decide +kernel

private theorem sp280 : smallValid 280 40 := by unfold smallValid; decide +kernel

private theorem sp320 : smallValid 320 40 := by unfold smallValid; decide +kernel

private theorem sp360 : smallValid 360 40 := by unfold smallValid; decide +kernel

private theorem sp400 : smallValid 400 40 := by unfold smallValid; decide +kernel

private theorem sp440 : smallValid 440 40 := by unfold smallValid; decide +kernel

private theorem sp480 : smallValid 480 40 := by unfold smallValid; decide +kernel

private theorem sp520 : smallValid 520 40 := by unfold smallValid; decide +kernel

private theorem sp560 : smallValid 560 40 := by unfold smallValid; decide +kernel

private theorem sp600 : smallValid 600 40 := by unfold smallValid; decide +kernel

private theorem sp640 : smallValid 640 40 := by unfold smallValid; decide +kernel

private theorem sp680 : smallValid 680 40 := by unfold smallValid; decide +kernel

private theorem sp720 : smallValid 720 40 := by unfold smallValid; decide +kernel

private theorem sp760 : smallValid 760 40 := by unfold smallValid; decide +kernel

private theorem sp800 : smallValid 800 40 := by unfold smallValid; decide +kernel

private theorem sp840 : smallValid 840 40 := by unfold smallValid; decide +kernel

private theorem sp880 : smallValid 880 40 := by unfold smallValid; decide +kernel

private theorem sp920 : smallValid 920 40 := by unfold smallValid; decide +kernel

private theorem sp960 : smallValid 960 40 := by unfold smallValid; decide +kernel

private theorem sp1000 : smallValid 1000 40 := by unfold smallValid; decide +kernel

private theorem sp1040 : smallValid 1040 40 := by unfold smallValid; decide +kernel

private theorem sp1080 : smallValid 1080 40 := by unfold smallValid; decide +kernel

private theorem sp1120 : smallValid 1120 40 := by unfold smallValid; decide +kernel

private theorem sp1160 : smallValid 1160 40 := by unfold smallValid; decide +kernel

private theorem sp1200 : smallValid 1200 40 := by unfold smallValid; decide +kernel

private theorem sp1240 : smallValid 1240 40 := by unfold smallValid; decide +kernel

private theorem sp1280 : smallValid 1280 40 := by unfold smallValid; decide +kernel

private theorem sp1320 : smallValid 1320 40 := by unfold smallValid; decide +kernel

private theorem sp1360 : smallValid 1360 40 := by unfold smallValid; decide +kernel

private theorem sp1400 : smallValid 1400 40 := by unfold smallValid; decide +kernel

private theorem sp1440 : smallValid 1440 40 := by unfold smallValid; decide +kernel

private theorem sp1480 : smallValid 1480 40 := by unfold smallValid; decide +kernel

private theorem sp1520 : smallValid 1520 40 := by unfold smallValid; decide +kernel

private theorem sp1560 : smallValid 1560 40 := by unfold smallValid; decide +kernel

private theorem sp1600 : smallValid 1600 40 := by unfold smallValid; decide +kernel

private theorem sp1640 : smallValid 1640 40 := by unfold smallValid; decide +kernel

private theorem sp1680 : smallValid 1680 40 := by unfold smallValid; decide +kernel

private theorem sp1720 : smallValid 1720 40 := by unfold smallValid; decide +kernel

private theorem sp1760 : smallValid 1760 40 := by unfold smallValid; decide +kernel

private theorem sp1800 : smallValid 1800 40 := by unfold smallValid; decide +kernel

private theorem sp1840 : smallValid 1840 40 := by unfold smallValid; decide +kernel

private theorem sp1880 : smallValid 1880 40 := by unfold smallValid; decide +kernel

private theorem sp1920 : smallValid 1920 40 := by unfold smallValid; decide +kernel

private theorem sp1960 : smallValid 1960 40 := by unfold smallValid; decide +kernel

private theorem sp2000 : smallValid 2000 40 := by unfold smallValid; decide +kernel

private theorem sp2040 : smallValid 2040 40 := by unfold smallValid; decide +kernel

private theorem sp2080 : smallValid 2080 40 := by unfold smallValid; decide +kernel

private theorem sp2120 : smallValid 2120 40 := by unfold smallValid; decide +kernel

private theorem sp2160 : smallValid 2160 40 := by unfold smallValid; decide +kernel

private theorem sp2200 : smallValid 2200 40 := by unfold smallValid; decide +kernel

private theorem sp2240 : smallValid 2240 40 := by unfold smallValid; decide +kernel

private theorem sp2280 : smallValid 2280 40 := by unfold smallValid; decide +kernel

private theorem sp2320 : smallValid 2320 40 := by unfold smallValid; decide +kernel

private theorem sp2360 : smallValid 2360 40 := by unfold smallValid; decide +kernel

private theorem sp2400 : smallValid 2400 40 := by unfold smallValid; decide +kernel

private theorem sp2440 : smallValid 2440 40 := by unfold smallValid; decide +kernel

private theorem sp2480 : smallValid 2480 40 := by unfold smallValid; decide +kernel

private theorem sp2520 : smallValid 2520 41 := by unfold smallValid; decide +kernel

private theorem sp2561 : smallValid 2561 40 := by unfold smallValid; decide +kernel

private theorem sp2601 : smallValid 2601 40 := by unfold smallValid; decide +kernel

private theorem sp2641 : smallValid 2641 40 := by unfold smallValid; decide +kernel

private theorem sp2681 : smallValid 2681 40 := by unfold smallValid; decide +kernel

private theorem sp2721 : smallValid 2721 40 := by unfold smallValid; decide +kernel

private theorem sp2761 : smallValid 2761 40 := by unfold smallValid; decide +kernel

private theorem sp2801 : smallValid 2801 40 := by unfold smallValid; decide +kernel

private theorem sp2841 : smallValid 2841 40 := by unfold smallValid; decide +kernel

private theorem sp2881 : smallValid 2881 40 := by unfold smallValid; decide +kernel

private theorem sp2921 : smallValid 2921 40 := by unfold smallValid; decide +kernel

private theorem sp2961 : smallValid 2961 40 := by unfold smallValid; decide +kernel

private theorem sp3001 : smallValid 3001 40 := by unfold smallValid; decide +kernel

private theorem sp3041 : smallValid 3041 40 := by unfold smallValid; decide +kernel

private theorem sp3081 : smallValid 3081 40 := by unfold smallValid; decide +kernel

private theorem sp3121 : smallValid 3121 40 := by unfold smallValid; decide +kernel

private theorem sp3161 : smallValid 3161 40 := by unfold smallValid; decide +kernel

private theorem sp3201 : smallValid 3201 40 := by unfold smallValid; decide +kernel

private theorem sp3241 : smallValid 3241 40 := by unfold smallValid; decide +kernel

private theorem sp3281 : smallValid 3281 40 := by unfold smallValid; decide +kernel

private theorem sp3321 : smallValid 3321 40 := by unfold smallValid; decide +kernel

private theorem sp3361 : smallValid 3361 40 := by unfold smallValid; decide +kernel

private theorem sp3401 : smallValid 3401 40 := by unfold smallValid; decide +kernel

private theorem sp3441 : smallValid 3441 40 := by unfold smallValid; decide +kernel

private theorem sp3481 : smallValid 3481 40 := by unfold smallValid; decide +kernel

private theorem sp3521 : smallValid 3521 40 := by unfold smallValid; decide +kernel

private theorem sp3561 : smallValid 3561 40 := by unfold smallValid; decide +kernel

private theorem sp3601 : smallValid 3601 40 := by unfold smallValid; decide +kernel

private theorem sp3641 : smallValid 3641 40 := by unfold smallValid; decide +kernel

private theorem sp3681 : smallValid 3681 40 := by unfold smallValid; decide +kernel

private theorem sp3721 : smallValid 3721 40 := by unfold smallValid; decide +kernel

private theorem sp3761 : smallValid 3761 40 := by unfold smallValid; decide +kernel

private theorem sp3801 : smallValid 3801 41 := by unfold smallValid; decide +kernel

private theorem sp3842 : smallValid 3842 40 := by unfold smallValid; decide +kernel

private theorem sp3882 : smallValid 3882 40 := by unfold smallValid; decide +kernel

private theorem sp3922 : smallValid 3922 40 := by unfold smallValid; decide +kernel

private theorem sp3962 : smallValid 3962 40 := by unfold smallValid; decide +kernel

private theorem sp4002 : smallValid 4002 40 := by unfold smallValid; decide +kernel

private theorem sp4042 : smallValid 4042 40 := by unfold smallValid; decide +kernel

private theorem sp4082 : smallValid 4082 40 := by unfold smallValid; decide +kernel

private theorem sp4122 : smallValid 4122 40 := by unfold smallValid; decide +kernel

private theorem sp4162 : smallValid 4162 40 := by unfold smallValid; decide +kernel

private theorem sp4202 : smallValid 4202 40 := by unfold smallValid; decide +kernel

private theorem sp4242 : smallValid 4242 40 := by unfold smallValid; decide +kernel

private theorem sp4282 : smallValid 4282 40 := by unfold smallValid; decide +kernel

private theorem sp4322 : smallValid 4322 40 := by unfold smallValid; decide +kernel

private theorem sp4362 : smallValid 4362 40 := by unfold smallValid; decide +kernel

private theorem sp4402 : smallValid 4402 40 := by unfold smallValid; decide +kernel

private theorem sp4442 : smallValid 4442 40 := by unfold smallValid; decide +kernel

private theorem sp4482 : smallValid 4482 40 := by unfold smallValid; decide +kernel

private theorem sp4522 : smallValid 4522 40 := by unfold smallValid; decide +kernel

private theorem sp4562 : smallValid 4562 40 := by unfold smallValid; decide +kernel

private theorem sp4602 : smallValid 4602 40 := by unfold smallValid; decide +kernel

private theorem sp4642 : smallValid 4642 40 := by unfold smallValid; decide +kernel

private theorem sp4682 : smallValid 4682 40 := by unfold smallValid; decide +kernel

private theorem sp4722 : smallValid 4722 40 := by unfold smallValid; decide +kernel

private theorem sp4762 : smallValid 4762 40 := by unfold smallValid; decide +kernel

private theorem sp4802 : smallValid 4802 40 := by unfold smallValid; decide +kernel

private theorem sp4842 : smallValid 4842 40 := by unfold smallValid; decide +kernel

private theorem sp4882 : smallValid 4882 40 := by unfold smallValid; decide +kernel

private theorem sp4922 : smallValid 4922 40 := by unfold smallValid; decide +kernel

private theorem sp4962 : smallValid 4962 40 := by unfold smallValid; decide +kernel

private theorem sp5002 : smallValid 5002 40 := by unfold smallValid; decide +kernel

private theorem sp5042 : smallValid 5042 40 := by unfold smallValid; decide +kernel

private theorem sp5082 : smallValid 5082 41 := by unfold smallValid; decide +kernel

private theorem sp5123 : smallValid 5123 40 := by unfold smallValid; decide +kernel

private theorem sp5163 : smallValid 5163 40 := by unfold smallValid; decide +kernel

private theorem sp5203 : smallValid 5203 40 := by unfold smallValid; decide +kernel

private theorem sp5243 : smallValid 5243 40 := by unfold smallValid; decide +kernel

private theorem sp5283 : smallValid 5283 40 := by unfold smallValid; decide +kernel

private theorem sp5323 : smallValid 5323 40 := by unfold smallValid; decide +kernel

private theorem sp5363 : smallValid 5363 40 := by unfold smallValid; decide +kernel

private theorem sp5403 : smallValid 5403 40 := by unfold smallValid; decide +kernel

private theorem sp5443 : smallValid 5443 40 := by unfold smallValid; decide +kernel

private theorem sp5483 : smallValid 5483 40 := by unfold smallValid; decide +kernel

private theorem sp5523 : smallValid 5523 40 := by unfold smallValid; decide +kernel

private theorem sp5563 : smallValid 5563 40 := by unfold smallValid; decide +kernel

private theorem sp5603 : smallValid 5603 40 := by unfold smallValid; decide +kernel

private theorem sp5643 : smallValid 5643 40 := by unfold smallValid; decide +kernel

private theorem sp5683 : smallValid 5683 40 := by unfold smallValid; decide +kernel

private theorem sp5723 : smallValid 5723 40 := by unfold smallValid; decide +kernel

private theorem sp5763 : smallValid 5763 40 := by unfold smallValid; decide +kernel

private theorem sp5803 : smallValid 5803 40 := by unfold smallValid; decide +kernel

private theorem sp5843 : smallValid 5843 40 := by unfold smallValid; decide +kernel

private theorem sp5883 : smallValid 5883 40 := by unfold smallValid; decide +kernel

private theorem sp5923 : smallValid 5923 40 := by unfold smallValid; decide +kernel

private theorem sp5963 : smallValid 5963 40 := by unfold smallValid; decide +kernel

private theorem sp6003 : smallValid 6003 40 := by unfold smallValid; decide +kernel

private theorem sp6043 : smallValid 6043 40 := by unfold smallValid; decide +kernel

private theorem sp6083 : smallValid 6083 40 := by unfold smallValid; decide +kernel

private theorem sp6123 : smallValid 6123 40 := by unfold smallValid; decide +kernel

private theorem sp6163 : smallValid 6163 40 := by unfold smallValid; decide +kernel

private theorem sp6203 : smallValid 6203 40 := by unfold smallValid; decide +kernel

private theorem sp6243 : smallValid 6243 40 := by unfold smallValid; decide +kernel

private theorem sp6283 : smallValid 6283 40 := by unfold smallValid; decide +kernel

private theorem sp6323 : smallValid 6323 40 := by unfold smallValid; decide +kernel

private theorem sp6363 : smallValid 6363 41 := by unfold smallValid; decide +kernel

private theorem sp6404 : smallValid 6404 40 := by unfold smallValid; decide +kernel

private theorem sp6444 : smallValid 6444 40 := by unfold smallValid; decide +kernel

private theorem sp6484 : smallValid 6484 40 := by unfold smallValid; decide +kernel

private theorem sp6524 : smallValid 6524 40 := by unfold smallValid; decide +kernel

private theorem sp6564 : smallValid 6564 40 := by unfold smallValid; decide +kernel

private theorem sp6604 : smallValid 6604 40 := by unfold smallValid; decide +kernel

private theorem sp6644 : smallValid 6644 40 := by unfold smallValid; decide +kernel

private theorem sp6684 : smallValid 6684 40 := by unfold smallValid; decide +kernel

private theorem sp6724 : smallValid 6724 40 := by unfold smallValid; decide +kernel

private theorem sp6764 : smallValid 6764 40 := by unfold smallValid; decide +kernel

private theorem sp6804 : smallValid 6804 40 := by unfold smallValid; decide +kernel

private theorem sp6844 : smallValid 6844 40 := by unfold smallValid; decide +kernel

private theorem sp6884 : smallValid 6884 40 := by unfold smallValid; decide +kernel

private theorem sp6924 : smallValid 6924 40 := by unfold smallValid; decide +kernel

private theorem sp6964 : smallValid 6964 40 := by unfold smallValid; decide +kernel

private theorem sp7004 : smallValid 7004 40 := by unfold smallValid; decide +kernel

private theorem sp7044 : smallValid 7044 40 := by unfold smallValid; decide +kernel

private theorem sp7084 : smallValid 7084 40 := by unfold smallValid; decide +kernel

private theorem sp7124 : smallValid 7124 40 := by unfold smallValid; decide +kernel

private theorem sp7164 : smallValid 7164 40 := by unfold smallValid; decide +kernel

private theorem sp7204 : smallValid 7204 40 := by unfold smallValid; decide +kernel

private theorem sp7244 : smallValid 7244 40 := by unfold smallValid; decide +kernel

private theorem sp7284 : smallValid 7284 40 := by unfold smallValid; decide +kernel

private theorem sp7324 : smallValid 7324 40 := by unfold smallValid; decide +kernel

private theorem sp7364 : smallValid 7364 40 := by unfold smallValid; decide +kernel

private theorem sp7404 : smallValid 7404 40 := by unfold smallValid; decide +kernel

private theorem sp7444 : smallValid 7444 40 := by unfold smallValid; decide +kernel

private theorem sp7484 : smallValid 7484 40 := by unfold smallValid; decide +kernel

private theorem sp7524 : smallValid 7524 40 := by unfold smallValid; decide +kernel

private theorem sp7564 : smallValid 7564 40 := by unfold smallValid; decide +kernel

private theorem sp7604 : smallValid 7604 40 := by unfold smallValid; decide +kernel

private theorem sp7644 : smallValid 7644 41 := by unfold smallValid; decide +kernel

private theorem sp7685 : smallValid 7685 40 := by unfold smallValid; decide +kernel

private theorem sp7725 : smallValid 7725 40 := by unfold smallValid; decide +kernel

private theorem sp7765 : smallValid 7765 40 := by unfold smallValid; decide +kernel

private theorem sp7805 : smallValid 7805 40 := by unfold smallValid; decide +kernel

private theorem sp7845 : smallValid 7845 40 := by unfold smallValid; decide +kernel

private theorem sp7885 : smallValid 7885 40 := by unfold smallValid; decide +kernel

private theorem sp7925 : smallValid 7925 40 := by unfold smallValid; decide +kernel

private theorem sp7965 : smallValid 7965 40 := by unfold smallValid; decide +kernel

private theorem sp8005 : smallValid 8005 40 := by unfold smallValid; decide +kernel

private theorem sp8045 : smallValid 8045 40 := by unfold smallValid; decide +kernel

private theorem sp8085 : smallValid 8085 40 := by unfold smallValid; decide +kernel

private theorem sp8125 : smallValid 8125 40 := by unfold smallValid; decide +kernel

private theorem sp8165 : smallValid 8165 40 := by unfold smallValid; decide +kernel

private theorem sp8205 : smallValid 8205 40 := by unfold smallValid; decide +kernel

private theorem sp8245 : smallValid 8245 40 := by unfold smallValid; decide +kernel

private theorem sp8285 : smallValid 8285 40 := by unfold smallValid; decide +kernel

private theorem sp8325 : smallValid 8325 40 := by unfold smallValid; decide +kernel

private theorem sp8365 : smallValid 8365 40 := by unfold smallValid; decide +kernel

private theorem sp8405 : smallValid 8405 40 := by unfold smallValid; decide +kernel

private theorem sp8445 : smallValid 8445 40 := by unfold smallValid; decide +kernel

private theorem sp8485 : smallValid 8485 40 := by unfold smallValid; decide +kernel

private theorem sp8525 : smallValid 8525 40 := by unfold smallValid; decide +kernel

private theorem sp8565 : smallValid 8565 40 := by unfold smallValid; decide +kernel

private theorem sp8605 : smallValid 8605 40 := by unfold smallValid; decide +kernel

private theorem sp8645 : smallValid 8645 40 := by unfold smallValid; decide +kernel

private theorem sp8685 : smallValid 8685 40 := by unfold smallValid; decide +kernel

private theorem sp8725 : smallValid 8725 40 := by unfold smallValid; decide +kernel

private theorem sp8765 : smallValid 8765 40 := by unfold smallValid; decide +kernel

private theorem sp8805 : smallValid 8805 40 := by unfold smallValid; decide +kernel

private theorem sp8845 : smallValid 8845 40 := by unfold smallValid; decide +kernel

private theorem sp8885 : smallValid 8885 40 := by unfold smallValid; decide +kernel

private theorem sp8925 : smallValid 8925 41 := by unfold smallValid; decide +kernel

private theorem sp8966 : smallValid 8966 40 := by unfold smallValid; decide +kernel

private theorem sp9006 : smallValid 9006 40 := by unfold smallValid; decide +kernel

private theorem sp9046 : smallValid 9046 40 := by unfold smallValid; decide +kernel

private theorem sp9086 : smallValid 9086 40 := by unfold smallValid; decide +kernel

private theorem sp9126 : smallValid 9126 40 := by unfold smallValid; decide +kernel

private theorem sp9166 : smallValid 9166 40 := by unfold smallValid; decide +kernel

private theorem sp9206 : smallValid 9206 40 := by unfold smallValid; decide +kernel

private theorem sp9246 : smallValid 9246 40 := by unfold smallValid; decide +kernel

private theorem sp9286 : smallValid 9286 40 := by unfold smallValid; decide +kernel

private theorem sp9326 : smallValid 9326 40 := by unfold smallValid; decide +kernel

private theorem sp9366 : smallValid 9366 40 := by unfold smallValid; decide +kernel

private theorem sp9406 : smallValid 9406 40 := by unfold smallValid; decide +kernel

private theorem sp9446 : smallValid 9446 40 := by unfold smallValid; decide +kernel

private theorem sp9486 : smallValid 9486 40 := by unfold smallValid; decide +kernel

private theorem sp9526 : smallValid 9526 40 := by unfold smallValid; decide +kernel

private theorem sp9566 : smallValid 9566 40 := by unfold smallValid; decide +kernel

private theorem sp9606 : smallValid 9606 40 := by unfold smallValid; decide +kernel

private theorem sp9646 : smallValid 9646 40 := by unfold smallValid; decide +kernel

private theorem sp9686 : smallValid 9686 40 := by unfold smallValid; decide +kernel

private theorem sp9726 : smallValid 9726 40 := by unfold smallValid; decide +kernel

private theorem sp9766 : smallValid 9766 40 := by unfold smallValid; decide +kernel

private theorem sp9806 : smallValid 9806 40 := by unfold smallValid; decide +kernel

private theorem sp9846 : smallValid 9846 40 := by unfold smallValid; decide +kernel

private theorem sp9886 : smallValid 9886 40 := by unfold smallValid; decide +kernel

private theorem sp9926 : smallValid 9926 40 := by unfold smallValid; decide +kernel

private theorem sp9966 : smallValid 9966 40 := by unfold smallValid; decide +kernel

private theorem sp10006 : smallValid 10006 40 := by unfold smallValid; decide +kernel

private theorem sp10046 : smallValid 10046 40 := by unfold smallValid; decide +kernel

private theorem sp10086 : smallValid 10086 40 := by unfold smallValid; decide +kernel

private theorem sp10126 : smallValid 10126 40 := by unfold smallValid; decide +kernel

private theorem sp10166 : smallValid 10166 40 := by unfold smallValid; decide +kernel

private theorem sp10206 : smallValid 10206 41 := by unfold smallValid; decide +kernel

private theorem sp10247 : smallValid 10247 40 := by unfold smallValid; decide +kernel

private theorem sp10287 : smallValid 10287 40 := by unfold smallValid; decide +kernel

private theorem sp10327 : smallValid 10327 40 := by unfold smallValid; decide +kernel

private theorem sp10367 : smallValid 10367 40 := by unfold smallValid; decide +kernel

private theorem sp10407 : smallValid 10407 40 := by unfold smallValid; decide +kernel

private theorem sp10447 : smallValid 10447 40 := by unfold smallValid; decide +kernel

private theorem sp10487 : smallValid 10487 40 := by unfold smallValid; decide +kernel

private theorem sp10527 : smallValid 10527 40 := by unfold smallValid; decide +kernel

private theorem sp10567 : smallValid 10567 40 := by unfold smallValid; decide +kernel

private theorem sp10607 : smallValid 10607 40 := by unfold smallValid; decide +kernel

private theorem sp10647 : smallValid 10647 40 := by unfold smallValid; decide +kernel

private theorem sp10687 : smallValid 10687 40 := by unfold smallValid; decide +kernel

private theorem sp10727 : smallValid 10727 40 := by unfold smallValid; decide +kernel

private theorem sp10767 : smallValid 10767 40 := by unfold smallValid; decide +kernel

private theorem sp10807 : smallValid 10807 40 := by unfold smallValid; decide +kernel

private theorem sp10847 : smallValid 10847 40 := by unfold smallValid; decide +kernel

private theorem sp10887 : smallValid 10887 40 := by unfold smallValid; decide +kernel

private theorem sp10927 : smallValid 10927 40 := by unfold smallValid; decide +kernel

private theorem sp10967 : smallValid 10967 40 := by unfold smallValid; decide +kernel

private theorem sp11007 : smallValid 11007 40 := by unfold smallValid; decide +kernel

private theorem sp11047 : smallValid 11047 40 := by unfold smallValid; decide +kernel

private theorem sp11087 : smallValid 11087 40 := by unfold smallValid; decide +kernel

private theorem sp11127 : smallValid 11127 40 := by unfold smallValid; decide +kernel

private theorem sp11167 : smallValid 11167 40 := by unfold smallValid; decide +kernel

private theorem sp11207 : smallValid 11207 40 := by unfold smallValid; decide +kernel

private theorem sp11247 : smallValid 11247 40 := by unfold smallValid; decide +kernel

private theorem sp11287 : smallValid 11287 40 := by unfold smallValid; decide +kernel

private theorem sp11327 : smallValid 11327 40 := by unfold smallValid; decide +kernel

private theorem sp11367 : smallValid 11367 40 := by unfold smallValid; decide +kernel

private theorem sp11407 : smallValid 11407 40 := by unfold smallValid; decide +kernel

private theorem sp11447 : smallValid 11447 40 := by unfold smallValid; decide +kernel

private theorem sp11487 : smallValid 11487 40 := by unfold smallValid; decide +kernel

private theorem sp11527 : smallValid 11527 40 := by unfold smallValid; decide +kernel

private theorem sp11567 : smallValid 11567 40 := by unfold smallValid; decide +kernel

private theorem sp11607 : smallValid 11607 40 := by unfold smallValid; decide +kernel

private theorem sp11647 : smallValid 11647 40 := by unfold smallValid; decide +kernel

private theorem sp11687 : smallValid 11687 40 := by unfold smallValid; decide +kernel

private theorem sp11727 : smallValid 11727 40 := by unfold smallValid; decide +kernel

private theorem sp11767 : smallValid 11767 40 := by unfold smallValid; decide +kernel

private theorem sp11807 : smallValid 11807 40 := by unfold smallValid; decide +kernel

private theorem sp11847 : smallValid 11847 40 := by unfold smallValid; decide +kernel

private theorem sp11887 : smallValid 11887 40 := by unfold smallValid; decide +kernel

private theorem sp11927 : smallValid 11927 40 := by unfold smallValid; decide +kernel

private theorem sp11967 : smallValid 11967 40 := by unfold smallValid; decide +kernel

private theorem sp12007 : smallValid 12007 40 := by unfold smallValid; decide +kernel

private theorem sp12047 : smallValid 12047 40 := by unfold smallValid; decide +kernel

private theorem sp12087 : smallValid 12087 40 := by unfold smallValid; decide +kernel

private theorem sp12127 : smallValid 12127 40 := by unfold smallValid; decide +kernel

private theorem sp12167 : smallValid 12167 40 := by unfold smallValid; decide +kernel

private theorem sp12207 : smallValid 12207 40 := by unfold smallValid; decide +kernel

private theorem sp12247 : smallValid 12247 40 := by unfold smallValid; decide +kernel

private theorem sp12287 : smallValid 12287 40 := by unfold smallValid; decide +kernel

private theorem sp12327 : smallValid 12327 40 := by unfold smallValid; decide +kernel

private theorem sp12367 : smallValid 12367 40 := by unfold smallValid; decide +kernel

private theorem sp12407 : smallValid 12407 40 := by unfold smallValid; decide +kernel

private theorem sp12447 : smallValid 12447 40 := by unfold smallValid; decide +kernel

private theorem sp12487 : smallValid 12487 40 := by unfold smallValid; decide +kernel

private theorem sp12527 : smallValid 12527 40 := by unfold smallValid; decide +kernel

private theorem sp12567 : smallValid 12567 40 := by unfold smallValid; decide +kernel

private theorem sp12607 : smallValid 12607 40 := by unfold smallValid; decide +kernel

private theorem sp12647 : smallValid 12647 40 := by unfold smallValid; decide +kernel

private theorem sp12687 : smallValid 12687 40 := by unfold smallValid; decide +kernel

private theorem sp12727 : smallValid 12727 40 := by unfold smallValid; decide +kernel

private theorem sp12767 : smallValid 12767 41 := by unfold smallValid; decide +kernel

private theorem sp12808 : smallValid 12808 40 := by unfold smallValid; decide +kernel

private theorem sp12848 : smallValid 12848 40 := by unfold smallValid; decide +kernel

private theorem sp12888 : smallValid 12888 40 := by unfold smallValid; decide +kernel

private theorem sp12928 : smallValid 12928 40 := by unfold smallValid; decide +kernel

private theorem sp12968 : smallValid 12968 40 := by unfold smallValid; decide +kernel

private theorem sp13008 : smallValid 13008 40 := by unfold smallValid; decide +kernel

private theorem sp13048 : smallValid 13048 40 := by unfold smallValid; decide +kernel

private theorem sp13088 : smallValid 13088 40 := by unfold smallValid; decide +kernel

private theorem sp13128 : smallValid 13128 40 := by unfold smallValid; decide +kernel

private theorem sp13168 : smallValid 13168 40 := by unfold smallValid; decide +kernel

private theorem sp13208 : smallValid 13208 40 := by unfold smallValid; decide +kernel

private theorem sp13248 : smallValid 13248 40 := by unfold smallValid; decide +kernel

private theorem sp13288 : smallValid 13288 40 := by unfold smallValid; decide +kernel

private theorem sp13328 : smallValid 13328 40 := by unfold smallValid; decide +kernel

private theorem sp13368 : smallValid 13368 40 := by unfold smallValid; decide +kernel

private theorem sp13408 : smallValid 13408 40 := by unfold smallValid; decide +kernel

private theorem sp13448 : smallValid 13448 40 := by unfold smallValid; decide +kernel

private theorem sp13488 : smallValid 13488 40 := by unfold smallValid; decide +kernel

private theorem sp13528 : smallValid 13528 40 := by unfold smallValid; decide +kernel

private theorem sp13568 : smallValid 13568 40 := by unfold smallValid; decide +kernel

private theorem sp13608 : smallValid 13608 40 := by unfold smallValid; decide +kernel

private theorem sp13648 : smallValid 13648 40 := by unfold smallValid; decide +kernel

private theorem sp13688 : smallValid 13688 40 := by unfold smallValid; decide +kernel

private theorem sp13728 : smallValid 13728 40 := by unfold smallValid; decide +kernel

private theorem sp13768 : smallValid 13768 40 := by unfold smallValid; decide +kernel

private theorem sp13808 : smallValid 13808 40 := by unfold smallValid; decide +kernel

private theorem sp13848 : smallValid 13848 40 := by unfold smallValid; decide +kernel

private theorem sp13888 : smallValid 13888 40 := by unfold smallValid; decide +kernel

private theorem sp13928 : smallValid 13928 40 := by unfold smallValid; decide +kernel

private theorem sp13968 : smallValid 13968 40 := by unfold smallValid; decide +kernel

private theorem sp14008 : smallValid 14008 40 := by unfold smallValid; decide +kernel

private theorem sp14048 : smallValid 14048 41 := by unfold smallValid; decide +kernel

private theorem sp14089 : smallValid 14089 40 := by unfold smallValid; decide +kernel

private theorem sp14129 : smallValid 14129 40 := by unfold smallValid; decide +kernel

private theorem sp14169 : smallValid 14169 40 := by unfold smallValid; decide +kernel

private theorem sp14209 : smallValid 14209 40 := by unfold smallValid; decide +kernel

private theorem sp14249 : smallValid 14249 40 := by unfold smallValid; decide +kernel

private theorem sp14289 : smallValid 14289 40 := by unfold smallValid; decide +kernel

private theorem sp14329 : smallValid 14329 40 := by unfold smallValid; decide +kernel

private theorem sp14369 : smallValid 14369 40 := by unfold smallValid; decide +kernel

private theorem sp14409 : smallValid 14409 40 := by unfold smallValid; decide +kernel

private theorem sp14449 : smallValid 14449 40 := by unfold smallValid; decide +kernel

private theorem sp14489 : smallValid 14489 40 := by unfold smallValid; decide +kernel

private theorem sp14529 : smallValid 14529 40 := by unfold smallValid; decide +kernel

private theorem sp14569 : smallValid 14569 40 := by unfold smallValid; decide +kernel

private theorem sp14609 : smallValid 14609 40 := by unfold smallValid; decide +kernel

private theorem sp14649 : smallValid 14649 40 := by unfold smallValid; decide +kernel

private theorem sp14689 : smallValid 14689 40 := by unfold smallValid; decide +kernel

private theorem sp14729 : smallValid 14729 40 := by unfold smallValid; decide +kernel

private theorem sp14769 : smallValid 14769 40 := by unfold smallValid; decide +kernel

private theorem sp14809 : smallValid 14809 40 := by unfold smallValid; decide +kernel

private theorem sp14849 : smallValid 14849 40 := by unfold smallValid; decide +kernel

private theorem sp14889 : smallValid 14889 40 := by unfold smallValid; decide +kernel

private theorem sp14929 : smallValid 14929 40 := by unfold smallValid; decide +kernel

private theorem sp14969 : smallValid 14969 40 := by unfold smallValid; decide +kernel

private theorem sp15009 : smallValid 15009 40 := by unfold smallValid; decide +kernel

private theorem sp15049 : smallValid 15049 40 := by unfold smallValid; decide +kernel

private theorem sp15089 : smallValid 15089 40 := by unfold smallValid; decide +kernel

private theorem sp15129 : smallValid 15129 40 := by unfold smallValid; decide +kernel

private theorem sp15169 : smallValid 15169 40 := by unfold smallValid; decide +kernel

private theorem sp15209 : smallValid 15209 40 := by unfold smallValid; decide +kernel

private theorem sp15249 : smallValid 15249 40 := by unfold smallValid; decide +kernel

private theorem sp15289 : smallValid 15289 40 := by unfold smallValid; decide +kernel

private theorem sp15329 : smallValid 15329 41 := by unfold smallValid; decide +kernel

private theorem sp15370 : smallValid 15370 40 := by unfold smallValid; decide +kernel

private theorem sp15410 : smallValid 15410 40 := by unfold smallValid; decide +kernel

private theorem sp15450 : smallValid 15450 40 := by unfold smallValid; decide +kernel

private theorem sp15490 : smallValid 15490 40 := by unfold smallValid; decide +kernel

private theorem sp15530 : smallValid 15530 40 := by unfold smallValid; decide +kernel

private theorem sp15570 : smallValid 15570 40 := by unfold smallValid; decide +kernel

private theorem sp15610 : smallValid 15610 40 := by unfold smallValid; decide +kernel

private theorem sp15650 : smallValid 15650 40 := by unfold smallValid; decide +kernel

private theorem sp15690 : smallValid 15690 40 := by unfold smallValid; decide +kernel

private theorem sp15730 : smallValid 15730 40 := by unfold smallValid; decide +kernel

private theorem sp15770 : smallValid 15770 40 := by unfold smallValid; decide +kernel

private theorem sp15810 : smallValid 15810 40 := by unfold smallValid; decide +kernel

private theorem sp15850 : smallValid 15850 40 := by unfold smallValid; decide +kernel

private theorem sp15890 : smallValid 15890 40 := by unfold smallValid; decide +kernel

private theorem sp15930 : smallValid 15930 40 := by unfold smallValid; decide +kernel

private theorem sp15970 : smallValid 15970 40 := by unfold smallValid; decide +kernel

private theorem sp16010 : smallValid 16010 40 := by unfold smallValid; decide +kernel

private theorem sp16050 : smallValid 16050 40 := by unfold smallValid; decide +kernel

private theorem sp16090 : smallValid 16090 40 := by unfold smallValid; decide +kernel

private theorem sp16130 : smallValid 16130 40 := by unfold smallValid; decide +kernel

private theorem sp16170 : smallValid 16170 40 := by unfold smallValid; decide +kernel

private theorem sp16210 : smallValid 16210 40 := by unfold smallValid; decide +kernel

private theorem sp16250 : smallValid 16250 40 := by unfold smallValid; decide +kernel

private theorem sp16290 : smallValid 16290 40 := by unfold smallValid; decide +kernel

private theorem sp16330 : smallValid 16330 40 := by unfold smallValid; decide +kernel

private theorem sp16370 : smallValid 16370 40 := by unfold smallValid; decide +kernel

private theorem sp16410 : smallValid 16410 40 := by unfold smallValid; decide +kernel

private theorem sp16450 : smallValid 16450 40 := by unfold smallValid; decide +kernel

private theorem sp16490 : smallValid 16490 40 := by unfold smallValid; decide +kernel

private theorem sp16530 : smallValid 16530 40 := by unfold smallValid; decide +kernel

private theorem sp16570 : smallValid 16570 40 := by unfold smallValid; decide +kernel

private theorem sp16610 : smallValid 16610 41 := by unfold smallValid; decide +kernel

private theorem sp16651 : smallValid 16651 40 := by unfold smallValid; decide +kernel

private theorem sp16691 : smallValid 16691 40 := by unfold smallValid; decide +kernel

private theorem sp16731 : smallValid 16731 40 := by unfold smallValid; decide +kernel

private theorem sp16771 : smallValid 16771 40 := by unfold smallValid; decide +kernel

private theorem sp16811 : smallValid 16811 40 := by unfold smallValid; decide +kernel

private theorem sp16851 : smallValid 16851 40 := by unfold smallValid; decide +kernel

private theorem sp16891 : smallValid 16891 40 := by unfold smallValid; decide +kernel

private theorem sp16931 : smallValid 16931 40 := by unfold smallValid; decide +kernel

private theorem sp16971 : smallValid 16971 40 := by unfold smallValid; decide +kernel

private theorem sp17011 : smallValid 17011 40 := by unfold smallValid; decide +kernel

private theorem sp17051 : smallValid 17051 40 := by unfold smallValid; decide +kernel

private theorem sp17091 : smallValid 17091 40 := by unfold smallValid; decide +kernel

private theorem sp17131 : smallValid 17131 40 := by unfold smallValid; decide +kernel

private theorem sp17171 : smallValid 17171 40 := by unfold smallValid; decide +kernel

private theorem sp17211 : smallValid 17211 40 := by unfold smallValid; decide +kernel

private theorem sp17251 : smallValid 17251 40 := by unfold smallValid; decide +kernel

private theorem sp17291 : smallValid 17291 40 := by unfold smallValid; decide +kernel

private theorem sp17331 : smallValid 17331 40 := by unfold smallValid; decide +kernel

private theorem sp17371 : smallValid 17371 40 := by unfold smallValid; decide +kernel

private theorem sp17411 : smallValid 17411 40 := by unfold smallValid; decide +kernel

private theorem sp17451 : smallValid 17451 40 := by unfold smallValid; decide +kernel

private theorem sp17491 : smallValid 17491 40 := by unfold smallValid; decide +kernel

private theorem sp17531 : smallValid 17531 40 := by unfold smallValid; decide +kernel

private theorem sp17571 : smallValid 17571 40 := by unfold smallValid; decide +kernel

private theorem sp17611 : smallValid 17611 40 := by unfold smallValid; decide +kernel

private theorem sp17651 : smallValid 17651 40 := by unfold smallValid; decide +kernel

private theorem sp17691 : smallValid 17691 40 := by unfold smallValid; decide +kernel

private theorem sp17731 : smallValid 17731 40 := by unfold smallValid; decide +kernel

private theorem sp17771 : smallValid 17771 40 := by unfold smallValid; decide +kernel

private theorem sp17811 : smallValid 17811 40 := by unfold smallValid; decide +kernel

private theorem sp17851 : smallValid 17851 40 := by unfold smallValid; decide +kernel

private theorem sp17891 : smallValid 17891 41 := by unfold smallValid; decide +kernel

private theorem sp17932 : smallValid 17932 40 := by unfold smallValid; decide +kernel

private theorem sp17972 : smallValid 17972 40 := by unfold smallValid; decide +kernel

private theorem sp18012 : smallValid 18012 40 := by unfold smallValid; decide +kernel

private theorem sp18052 : smallValid 18052 40 := by unfold smallValid; decide +kernel

private theorem sp18092 : smallValid 18092 40 := by unfold smallValid; decide +kernel

private theorem sp18132 : smallValid 18132 40 := by unfold smallValid; decide +kernel

private theorem sp18172 : smallValid 18172 40 := by unfold smallValid; decide +kernel

private theorem sp18212 : smallValid 18212 40 := by unfold smallValid; decide +kernel

private theorem sp18252 : smallValid 18252 40 := by unfold smallValid; decide +kernel

private theorem sp18292 : smallValid 18292 40 := by unfold smallValid; decide +kernel

private theorem sp18332 : smallValid 18332 40 := by unfold smallValid; decide +kernel

private theorem sp18372 : smallValid 18372 40 := by unfold smallValid; decide +kernel

private theorem sp18412 : smallValid 18412 40 := by unfold smallValid; decide +kernel

private theorem sp18452 : smallValid 18452 40 := by unfold smallValid; decide +kernel

private theorem sp18492 : smallValid 18492 40 := by unfold smallValid; decide +kernel

private theorem sp18532 : smallValid 18532 40 := by unfold smallValid; decide +kernel

private theorem sp18572 : smallValid 18572 40 := by unfold smallValid; decide +kernel

private theorem sp18612 : smallValid 18612 40 := by unfold smallValid; decide +kernel

private theorem sp18652 : smallValid 18652 40 := by unfold smallValid; decide +kernel

private theorem sp18692 : smallValid 18692 40 := by unfold smallValid; decide +kernel

private theorem sp18732 : smallValid 18732 40 := by unfold smallValid; decide +kernel

private theorem sp18772 : smallValid 18772 40 := by unfold smallValid; decide +kernel

private theorem sp18812 : smallValid 18812 40 := by unfold smallValid; decide +kernel

private theorem sp18852 : smallValid 18852 40 := by unfold smallValid; decide +kernel

private theorem sp18892 : smallValid 18892 40 := by unfold smallValid; decide +kernel

private theorem sp18932 : smallValid 18932 40 := by unfold smallValid; decide +kernel

private theorem sp18972 : smallValid 18972 40 := by unfold smallValid; decide +kernel

private theorem sp19012 : smallValid 19012 40 := by unfold smallValid; decide +kernel

private theorem sp19052 : smallValid 19052 40 := by unfold smallValid; decide +kernel

private theorem sp19092 : smallValid 19092 40 := by unfold smallValid; decide +kernel

private theorem sp19132 : smallValid 19132 40 := by unfold smallValid; decide +kernel

private theorem sp19172 : smallValid 19172 41 := by unfold smallValid; decide +kernel

private theorem sp19213 : smallValid 19213 40 := by unfold smallValid; decide +kernel

private theorem sp19253 : smallValid 19253 40 := by unfold smallValid; decide +kernel

private theorem sp19293 : smallValid 19293 40 := by unfold smallValid; decide +kernel

private theorem sp19333 : smallValid 19333 40 := by unfold smallValid; decide +kernel

private theorem sp19373 : smallValid 19373 40 := by unfold smallValid; decide +kernel

private theorem sp19413 : smallValid 19413 40 := by unfold smallValid; decide +kernel

private theorem sp19453 : smallValid 19453 40 := by unfold smallValid; decide +kernel

private theorem sp19493 : smallValid 19493 40 := by unfold smallValid; decide +kernel

private theorem sp19533 : smallValid 19533 40 := by unfold smallValid; decide +kernel

private theorem sp19573 : smallValid 19573 40 := by unfold smallValid; decide +kernel

private theorem sp19613 : smallValid 19613 40 := by unfold smallValid; decide +kernel

private theorem sp19653 : smallValid 19653 40 := by unfold smallValid; decide +kernel

private theorem sp19693 : smallValid 19693 40 := by unfold smallValid; decide +kernel

private theorem sp19733 : smallValid 19733 40 := by unfold smallValid; decide +kernel

private theorem sp19773 : smallValid 19773 40 := by unfold smallValid; decide +kernel

private theorem sp19813 : smallValid 19813 40 := by unfold smallValid; decide +kernel

private theorem sp19853 : smallValid 19853 40 := by unfold smallValid; decide +kernel

private theorem sp19893 : smallValid 19893 40 := by unfold smallValid; decide +kernel

private theorem sp19933 : smallValid 19933 40 := by unfold smallValid; decide +kernel

private theorem sp19973 : smallValid 19973 40 := by unfold smallValid; decide +kernel

private theorem sp20013 : smallValid 20013 40 := by unfold smallValid; decide +kernel

private theorem sp20053 : smallValid 20053 40 := by unfold smallValid; decide +kernel

private theorem sp20093 : smallValid 20093 40 := by unfold smallValid; decide +kernel

private theorem sp20133 : smallValid 20133 40 := by unfold smallValid; decide +kernel

private theorem sp20173 : smallValid 20173 40 := by unfold smallValid; decide +kernel

private theorem sp20213 : smallValid 20213 40 := by unfold smallValid; decide +kernel

private theorem sp20253 : smallValid 20253 40 := by unfold smallValid; decide +kernel

private theorem sp20293 : smallValid 20293 40 := by unfold smallValid; decide +kernel

private theorem sp20333 : smallValid 20333 40 := by unfold smallValid; decide +kernel

private theorem sp20373 : smallValid 20373 40 := by unfold smallValid; decide +kernel

private theorem sp20413 : smallValid 20413 40 := by unfold smallValid; decide +kernel

private theorem sp20453 : smallValid 20453 41 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤20493) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 20494 := (joinSmall (lo:=0) (a:=10247) (b:=10247) (joinSmall (lo:=0) (a:=5123) (b:=5124) (joinSmall (lo:=0) (a:=2561) (b:=2562) (joinSmall (lo:=0) (a:=1280) (b:=1281) (joinSmall (lo:=0) (a:=640) (b:=640) (joinSmall (lo:=0) (a:=320) (b:=320) (joinSmall (lo:=0) (a:=160) (b:=160) (joinSmall (lo:=0) (a:=80) (b:=80) (joinSmall (lo:=0) (a:=40) (b:=40) sp0 sp40) (joinSmall (lo:=80) (a:=40) (b:=40) sp80 sp120)) (joinSmall (lo:=160) (a:=80) (b:=80) (joinSmall (lo:=160) (a:=40) (b:=40) sp160 sp200) (joinSmall (lo:=240) (a:=40) (b:=40) sp240 sp280))) (joinSmall (lo:=320) (a:=160) (b:=160) (joinSmall (lo:=320) (a:=80) (b:=80) (joinSmall (lo:=320) (a:=40) (b:=40) sp320 sp360) (joinSmall (lo:=400) (a:=40) (b:=40) sp400 sp440)) (joinSmall (lo:=480) (a:=80) (b:=80) (joinSmall (lo:=480) (a:=40) (b:=40) sp480 sp520) (joinSmall (lo:=560) (a:=40) (b:=40) sp560 sp600)))) (joinSmall (lo:=640) (a:=320) (b:=320) (joinSmall (lo:=640) (a:=160) (b:=160) (joinSmall (lo:=640) (a:=80) (b:=80) (joinSmall (lo:=640) (a:=40) (b:=40) sp640 sp680) (joinSmall (lo:=720) (a:=40) (b:=40) sp720 sp760)) (joinSmall (lo:=800) (a:=80) (b:=80) (joinSmall (lo:=800) (a:=40) (b:=40) sp800 sp840) (joinSmall (lo:=880) (a:=40) (b:=40) sp880 sp920))) (joinSmall (lo:=960) (a:=160) (b:=160) (joinSmall (lo:=960) (a:=80) (b:=80) (joinSmall (lo:=960) (a:=40) (b:=40) sp960 sp1000) (joinSmall (lo:=1040) (a:=40) (b:=40) sp1040 sp1080)) (joinSmall (lo:=1120) (a:=80) (b:=80) (joinSmall (lo:=1120) (a:=40) (b:=40) sp1120 sp1160) (joinSmall (lo:=1200) (a:=40) (b:=40) sp1200 sp1240))))) (joinSmall (lo:=1280) (a:=640) (b:=641) (joinSmall (lo:=1280) (a:=320) (b:=320) (joinSmall (lo:=1280) (a:=160) (b:=160) (joinSmall (lo:=1280) (a:=80) (b:=80) (joinSmall (lo:=1280) (a:=40) (b:=40) sp1280 sp1320) (joinSmall (lo:=1360) (a:=40) (b:=40) sp1360 sp1400)) (joinSmall (lo:=1440) (a:=80) (b:=80) (joinSmall (lo:=1440) (a:=40) (b:=40) sp1440 sp1480) (joinSmall (lo:=1520) (a:=40) (b:=40) sp1520 sp1560))) (joinSmall (lo:=1600) (a:=160) (b:=160) (joinSmall (lo:=1600) (a:=80) (b:=80) (joinSmall (lo:=1600) (a:=40) (b:=40) sp1600 sp1640) (joinSmall (lo:=1680) (a:=40) (b:=40) sp1680 sp1720)) (joinSmall (lo:=1760) (a:=80) (b:=80) (joinSmall (lo:=1760) (a:=40) (b:=40) sp1760 sp1800) (joinSmall (lo:=1840) (a:=40) (b:=40) sp1840 sp1880)))) (joinSmall (lo:=1920) (a:=320) (b:=321) (joinSmall (lo:=1920) (a:=160) (b:=160) (joinSmall (lo:=1920) (a:=80) (b:=80) (joinSmall (lo:=1920) (a:=40) (b:=40) sp1920 sp1960) (joinSmall (lo:=2000) (a:=40) (b:=40) sp2000 sp2040)) (joinSmall (lo:=2080) (a:=80) (b:=80) (joinSmall (lo:=2080) (a:=40) (b:=40) sp2080 sp2120) (joinSmall (lo:=2160) (a:=40) (b:=40) sp2160 sp2200))) (joinSmall (lo:=2240) (a:=160) (b:=161) (joinSmall (lo:=2240) (a:=80) (b:=80) (joinSmall (lo:=2240) (a:=40) (b:=40) sp2240 sp2280) (joinSmall (lo:=2320) (a:=40) (b:=40) sp2320 sp2360)) (joinSmall (lo:=2400) (a:=80) (b:=81) (joinSmall (lo:=2400) (a:=40) (b:=40) sp2400 sp2440) (joinSmall (lo:=2480) (a:=40) (b:=41) sp2480 sp2520)))))) (joinSmall (lo:=2561) (a:=1281) (b:=1281) (joinSmall (lo:=2561) (a:=640) (b:=641) (joinSmall (lo:=2561) (a:=320) (b:=320) (joinSmall (lo:=2561) (a:=160) (b:=160) (joinSmall (lo:=2561) (a:=80) (b:=80) (joinSmall (lo:=2561) (a:=40) (b:=40) sp2561 sp2601) (joinSmall (lo:=2641) (a:=40) (b:=40) sp2641 sp2681)) (joinSmall (lo:=2721) (a:=80) (b:=80) (joinSmall (lo:=2721) (a:=40) (b:=40) sp2721 sp2761) (joinSmall (lo:=2801) (a:=40) (b:=40) sp2801 sp2841))) (joinSmall (lo:=2881) (a:=160) (b:=160) (joinSmall (lo:=2881) (a:=80) (b:=80) (joinSmall (lo:=2881) (a:=40) (b:=40) sp2881 sp2921) (joinSmall (lo:=2961) (a:=40) (b:=40) sp2961 sp3001)) (joinSmall (lo:=3041) (a:=80) (b:=80) (joinSmall (lo:=3041) (a:=40) (b:=40) sp3041 sp3081) (joinSmall (lo:=3121) (a:=40) (b:=40) sp3121 sp3161)))) (joinSmall (lo:=3201) (a:=320) (b:=321) (joinSmall (lo:=3201) (a:=160) (b:=160) (joinSmall (lo:=3201) (a:=80) (b:=80) (joinSmall (lo:=3201) (a:=40) (b:=40) sp3201 sp3241) (joinSmall (lo:=3281) (a:=40) (b:=40) sp3281 sp3321)) (joinSmall (lo:=3361) (a:=80) (b:=80) (joinSmall (lo:=3361) (a:=40) (b:=40) sp3361 sp3401) (joinSmall (lo:=3441) (a:=40) (b:=40) sp3441 sp3481))) (joinSmall (lo:=3521) (a:=160) (b:=161) (joinSmall (lo:=3521) (a:=80) (b:=80) (joinSmall (lo:=3521) (a:=40) (b:=40) sp3521 sp3561) (joinSmall (lo:=3601) (a:=40) (b:=40) sp3601 sp3641)) (joinSmall (lo:=3681) (a:=80) (b:=81) (joinSmall (lo:=3681) (a:=40) (b:=40) sp3681 sp3721) (joinSmall (lo:=3761) (a:=40) (b:=41) sp3761 sp3801))))) (joinSmall (lo:=3842) (a:=640) (b:=641) (joinSmall (lo:=3842) (a:=320) (b:=320) (joinSmall (lo:=3842) (a:=160) (b:=160) (joinSmall (lo:=3842) (a:=80) (b:=80) (joinSmall (lo:=3842) (a:=40) (b:=40) sp3842 sp3882) (joinSmall (lo:=3922) (a:=40) (b:=40) sp3922 sp3962)) (joinSmall (lo:=4002) (a:=80) (b:=80) (joinSmall (lo:=4002) (a:=40) (b:=40) sp4002 sp4042) (joinSmall (lo:=4082) (a:=40) (b:=40) sp4082 sp4122))) (joinSmall (lo:=4162) (a:=160) (b:=160) (joinSmall (lo:=4162) (a:=80) (b:=80) (joinSmall (lo:=4162) (a:=40) (b:=40) sp4162 sp4202) (joinSmall (lo:=4242) (a:=40) (b:=40) sp4242 sp4282)) (joinSmall (lo:=4322) (a:=80) (b:=80) (joinSmall (lo:=4322) (a:=40) (b:=40) sp4322 sp4362) (joinSmall (lo:=4402) (a:=40) (b:=40) sp4402 sp4442)))) (joinSmall (lo:=4482) (a:=320) (b:=321) (joinSmall (lo:=4482) (a:=160) (b:=160) (joinSmall (lo:=4482) (a:=80) (b:=80) (joinSmall (lo:=4482) (a:=40) (b:=40) sp4482 sp4522) (joinSmall (lo:=4562) (a:=40) (b:=40) sp4562 sp4602)) (joinSmall (lo:=4642) (a:=80) (b:=80) (joinSmall (lo:=4642) (a:=40) (b:=40) sp4642 sp4682) (joinSmall (lo:=4722) (a:=40) (b:=40) sp4722 sp4762))) (joinSmall (lo:=4802) (a:=160) (b:=161) (joinSmall (lo:=4802) (a:=80) (b:=80) (joinSmall (lo:=4802) (a:=40) (b:=40) sp4802 sp4842) (joinSmall (lo:=4882) (a:=40) (b:=40) sp4882 sp4922)) (joinSmall (lo:=4962) (a:=80) (b:=81) (joinSmall (lo:=4962) (a:=40) (b:=40) sp4962 sp5002) (joinSmall (lo:=5042) (a:=40) (b:=41) sp5042 sp5082))))))) (joinSmall (lo:=5123) (a:=2562) (b:=2562) (joinSmall (lo:=5123) (a:=1281) (b:=1281) (joinSmall (lo:=5123) (a:=640) (b:=641) (joinSmall (lo:=5123) (a:=320) (b:=320) (joinSmall (lo:=5123) (a:=160) (b:=160) (joinSmall (lo:=5123) (a:=80) (b:=80) (joinSmall (lo:=5123) (a:=40) (b:=40) sp5123 sp5163) (joinSmall (lo:=5203) (a:=40) (b:=40) sp5203 sp5243)) (joinSmall (lo:=5283) (a:=80) (b:=80) (joinSmall (lo:=5283) (a:=40) (b:=40) sp5283 sp5323) (joinSmall (lo:=5363) (a:=40) (b:=40) sp5363 sp5403))) (joinSmall (lo:=5443) (a:=160) (b:=160) (joinSmall (lo:=5443) (a:=80) (b:=80) (joinSmall (lo:=5443) (a:=40) (b:=40) sp5443 sp5483) (joinSmall (lo:=5523) (a:=40) (b:=40) sp5523 sp5563)) (joinSmall (lo:=5603) (a:=80) (b:=80) (joinSmall (lo:=5603) (a:=40) (b:=40) sp5603 sp5643) (joinSmall (lo:=5683) (a:=40) (b:=40) sp5683 sp5723)))) (joinSmall (lo:=5763) (a:=320) (b:=321) (joinSmall (lo:=5763) (a:=160) (b:=160) (joinSmall (lo:=5763) (a:=80) (b:=80) (joinSmall (lo:=5763) (a:=40) (b:=40) sp5763 sp5803) (joinSmall (lo:=5843) (a:=40) (b:=40) sp5843 sp5883)) (joinSmall (lo:=5923) (a:=80) (b:=80) (joinSmall (lo:=5923) (a:=40) (b:=40) sp5923 sp5963) (joinSmall (lo:=6003) (a:=40) (b:=40) sp6003 sp6043))) (joinSmall (lo:=6083) (a:=160) (b:=161) (joinSmall (lo:=6083) (a:=80) (b:=80) (joinSmall (lo:=6083) (a:=40) (b:=40) sp6083 sp6123) (joinSmall (lo:=6163) (a:=40) (b:=40) sp6163 sp6203)) (joinSmall (lo:=6243) (a:=80) (b:=81) (joinSmall (lo:=6243) (a:=40) (b:=40) sp6243 sp6283) (joinSmall (lo:=6323) (a:=40) (b:=41) sp6323 sp6363))))) (joinSmall (lo:=6404) (a:=640) (b:=641) (joinSmall (lo:=6404) (a:=320) (b:=320) (joinSmall (lo:=6404) (a:=160) (b:=160) (joinSmall (lo:=6404) (a:=80) (b:=80) (joinSmall (lo:=6404) (a:=40) (b:=40) sp6404 sp6444) (joinSmall (lo:=6484) (a:=40) (b:=40) sp6484 sp6524)) (joinSmall (lo:=6564) (a:=80) (b:=80) (joinSmall (lo:=6564) (a:=40) (b:=40) sp6564 sp6604) (joinSmall (lo:=6644) (a:=40) (b:=40) sp6644 sp6684))) (joinSmall (lo:=6724) (a:=160) (b:=160) (joinSmall (lo:=6724) (a:=80) (b:=80) (joinSmall (lo:=6724) (a:=40) (b:=40) sp6724 sp6764) (joinSmall (lo:=6804) (a:=40) (b:=40) sp6804 sp6844)) (joinSmall (lo:=6884) (a:=80) (b:=80) (joinSmall (lo:=6884) (a:=40) (b:=40) sp6884 sp6924) (joinSmall (lo:=6964) (a:=40) (b:=40) sp6964 sp7004)))) (joinSmall (lo:=7044) (a:=320) (b:=321) (joinSmall (lo:=7044) (a:=160) (b:=160) (joinSmall (lo:=7044) (a:=80) (b:=80) (joinSmall (lo:=7044) (a:=40) (b:=40) sp7044 sp7084) (joinSmall (lo:=7124) (a:=40) (b:=40) sp7124 sp7164)) (joinSmall (lo:=7204) (a:=80) (b:=80) (joinSmall (lo:=7204) (a:=40) (b:=40) sp7204 sp7244) (joinSmall (lo:=7284) (a:=40) (b:=40) sp7284 sp7324))) (joinSmall (lo:=7364) (a:=160) (b:=161) (joinSmall (lo:=7364) (a:=80) (b:=80) (joinSmall (lo:=7364) (a:=40) (b:=40) sp7364 sp7404) (joinSmall (lo:=7444) (a:=40) (b:=40) sp7444 sp7484)) (joinSmall (lo:=7524) (a:=80) (b:=81) (joinSmall (lo:=7524) (a:=40) (b:=40) sp7524 sp7564) (joinSmall (lo:=7604) (a:=40) (b:=41) sp7604 sp7644)))))) (joinSmall (lo:=7685) (a:=1281) (b:=1281) (joinSmall (lo:=7685) (a:=640) (b:=641) (joinSmall (lo:=7685) (a:=320) (b:=320) (joinSmall (lo:=7685) (a:=160) (b:=160) (joinSmall (lo:=7685) (a:=80) (b:=80) (joinSmall (lo:=7685) (a:=40) (b:=40) sp7685 sp7725) (joinSmall (lo:=7765) (a:=40) (b:=40) sp7765 sp7805)) (joinSmall (lo:=7845) (a:=80) (b:=80) (joinSmall (lo:=7845) (a:=40) (b:=40) sp7845 sp7885) (joinSmall (lo:=7925) (a:=40) (b:=40) sp7925 sp7965))) (joinSmall (lo:=8005) (a:=160) (b:=160) (joinSmall (lo:=8005) (a:=80) (b:=80) (joinSmall (lo:=8005) (a:=40) (b:=40) sp8005 sp8045) (joinSmall (lo:=8085) (a:=40) (b:=40) sp8085 sp8125)) (joinSmall (lo:=8165) (a:=80) (b:=80) (joinSmall (lo:=8165) (a:=40) (b:=40) sp8165 sp8205) (joinSmall (lo:=8245) (a:=40) (b:=40) sp8245 sp8285)))) (joinSmall (lo:=8325) (a:=320) (b:=321) (joinSmall (lo:=8325) (a:=160) (b:=160) (joinSmall (lo:=8325) (a:=80) (b:=80) (joinSmall (lo:=8325) (a:=40) (b:=40) sp8325 sp8365) (joinSmall (lo:=8405) (a:=40) (b:=40) sp8405 sp8445)) (joinSmall (lo:=8485) (a:=80) (b:=80) (joinSmall (lo:=8485) (a:=40) (b:=40) sp8485 sp8525) (joinSmall (lo:=8565) (a:=40) (b:=40) sp8565 sp8605))) (joinSmall (lo:=8645) (a:=160) (b:=161) (joinSmall (lo:=8645) (a:=80) (b:=80) (joinSmall (lo:=8645) (a:=40) (b:=40) sp8645 sp8685) (joinSmall (lo:=8725) (a:=40) (b:=40) sp8725 sp8765)) (joinSmall (lo:=8805) (a:=80) (b:=81) (joinSmall (lo:=8805) (a:=40) (b:=40) sp8805 sp8845) (joinSmall (lo:=8885) (a:=40) (b:=41) sp8885 sp8925))))) (joinSmall (lo:=8966) (a:=640) (b:=641) (joinSmall (lo:=8966) (a:=320) (b:=320) (joinSmall (lo:=8966) (a:=160) (b:=160) (joinSmall (lo:=8966) (a:=80) (b:=80) (joinSmall (lo:=8966) (a:=40) (b:=40) sp8966 sp9006) (joinSmall (lo:=9046) (a:=40) (b:=40) sp9046 sp9086)) (joinSmall (lo:=9126) (a:=80) (b:=80) (joinSmall (lo:=9126) (a:=40) (b:=40) sp9126 sp9166) (joinSmall (lo:=9206) (a:=40) (b:=40) sp9206 sp9246))) (joinSmall (lo:=9286) (a:=160) (b:=160) (joinSmall (lo:=9286) (a:=80) (b:=80) (joinSmall (lo:=9286) (a:=40) (b:=40) sp9286 sp9326) (joinSmall (lo:=9366) (a:=40) (b:=40) sp9366 sp9406)) (joinSmall (lo:=9446) (a:=80) (b:=80) (joinSmall (lo:=9446) (a:=40) (b:=40) sp9446 sp9486) (joinSmall (lo:=9526) (a:=40) (b:=40) sp9526 sp9566)))) (joinSmall (lo:=9606) (a:=320) (b:=321) (joinSmall (lo:=9606) (a:=160) (b:=160) (joinSmall (lo:=9606) (a:=80) (b:=80) (joinSmall (lo:=9606) (a:=40) (b:=40) sp9606 sp9646) (joinSmall (lo:=9686) (a:=40) (b:=40) sp9686 sp9726)) (joinSmall (lo:=9766) (a:=80) (b:=80) (joinSmall (lo:=9766) (a:=40) (b:=40) sp9766 sp9806) (joinSmall (lo:=9846) (a:=40) (b:=40) sp9846 sp9886))) (joinSmall (lo:=9926) (a:=160) (b:=161) (joinSmall (lo:=9926) (a:=80) (b:=80) (joinSmall (lo:=9926) (a:=40) (b:=40) sp9926 sp9966) (joinSmall (lo:=10006) (a:=40) (b:=40) sp10006 sp10046)) (joinSmall (lo:=10086) (a:=80) (b:=81) (joinSmall (lo:=10086) (a:=40) (b:=40) sp10086 sp10126) (joinSmall (lo:=10166) (a:=40) (b:=41) sp10166 sp10206)))))))) (joinSmall (lo:=10247) (a:=5123) (b:=5124) (joinSmall (lo:=10247) (a:=2561) (b:=2562) (joinSmall (lo:=10247) (a:=1280) (b:=1281) (joinSmall (lo:=10247) (a:=640) (b:=640) (joinSmall (lo:=10247) (a:=320) (b:=320) (joinSmall (lo:=10247) (a:=160) (b:=160) (joinSmall (lo:=10247) (a:=80) (b:=80) (joinSmall (lo:=10247) (a:=40) (b:=40) sp10247 sp10287) (joinSmall (lo:=10327) (a:=40) (b:=40) sp10327 sp10367)) (joinSmall (lo:=10407) (a:=80) (b:=80) (joinSmall (lo:=10407) (a:=40) (b:=40) sp10407 sp10447) (joinSmall (lo:=10487) (a:=40) (b:=40) sp10487 sp10527))) (joinSmall (lo:=10567) (a:=160) (b:=160) (joinSmall (lo:=10567) (a:=80) (b:=80) (joinSmall (lo:=10567) (a:=40) (b:=40) sp10567 sp10607) (joinSmall (lo:=10647) (a:=40) (b:=40) sp10647 sp10687)) (joinSmall (lo:=10727) (a:=80) (b:=80) (joinSmall (lo:=10727) (a:=40) (b:=40) sp10727 sp10767) (joinSmall (lo:=10807) (a:=40) (b:=40) sp10807 sp10847)))) (joinSmall (lo:=10887) (a:=320) (b:=320) (joinSmall (lo:=10887) (a:=160) (b:=160) (joinSmall (lo:=10887) (a:=80) (b:=80) (joinSmall (lo:=10887) (a:=40) (b:=40) sp10887 sp10927) (joinSmall (lo:=10967) (a:=40) (b:=40) sp10967 sp11007)) (joinSmall (lo:=11047) (a:=80) (b:=80) (joinSmall (lo:=11047) (a:=40) (b:=40) sp11047 sp11087) (joinSmall (lo:=11127) (a:=40) (b:=40) sp11127 sp11167))) (joinSmall (lo:=11207) (a:=160) (b:=160) (joinSmall (lo:=11207) (a:=80) (b:=80) (joinSmall (lo:=11207) (a:=40) (b:=40) sp11207 sp11247) (joinSmall (lo:=11287) (a:=40) (b:=40) sp11287 sp11327)) (joinSmall (lo:=11367) (a:=80) (b:=80) (joinSmall (lo:=11367) (a:=40) (b:=40) sp11367 sp11407) (joinSmall (lo:=11447) (a:=40) (b:=40) sp11447 sp11487))))) (joinSmall (lo:=11527) (a:=640) (b:=641) (joinSmall (lo:=11527) (a:=320) (b:=320) (joinSmall (lo:=11527) (a:=160) (b:=160) (joinSmall (lo:=11527) (a:=80) (b:=80) (joinSmall (lo:=11527) (a:=40) (b:=40) sp11527 sp11567) (joinSmall (lo:=11607) (a:=40) (b:=40) sp11607 sp11647)) (joinSmall (lo:=11687) (a:=80) (b:=80) (joinSmall (lo:=11687) (a:=40) (b:=40) sp11687 sp11727) (joinSmall (lo:=11767) (a:=40) (b:=40) sp11767 sp11807))) (joinSmall (lo:=11847) (a:=160) (b:=160) (joinSmall (lo:=11847) (a:=80) (b:=80) (joinSmall (lo:=11847) (a:=40) (b:=40) sp11847 sp11887) (joinSmall (lo:=11927) (a:=40) (b:=40) sp11927 sp11967)) (joinSmall (lo:=12007) (a:=80) (b:=80) (joinSmall (lo:=12007) (a:=40) (b:=40) sp12007 sp12047) (joinSmall (lo:=12087) (a:=40) (b:=40) sp12087 sp12127)))) (joinSmall (lo:=12167) (a:=320) (b:=321) (joinSmall (lo:=12167) (a:=160) (b:=160) (joinSmall (lo:=12167) (a:=80) (b:=80) (joinSmall (lo:=12167) (a:=40) (b:=40) sp12167 sp12207) (joinSmall (lo:=12247) (a:=40) (b:=40) sp12247 sp12287)) (joinSmall (lo:=12327) (a:=80) (b:=80) (joinSmall (lo:=12327) (a:=40) (b:=40) sp12327 sp12367) (joinSmall (lo:=12407) (a:=40) (b:=40) sp12407 sp12447))) (joinSmall (lo:=12487) (a:=160) (b:=161) (joinSmall (lo:=12487) (a:=80) (b:=80) (joinSmall (lo:=12487) (a:=40) (b:=40) sp12487 sp12527) (joinSmall (lo:=12567) (a:=40) (b:=40) sp12567 sp12607)) (joinSmall (lo:=12647) (a:=80) (b:=81) (joinSmall (lo:=12647) (a:=40) (b:=40) sp12647 sp12687) (joinSmall (lo:=12727) (a:=40) (b:=41) sp12727 sp12767)))))) (joinSmall (lo:=12808) (a:=1281) (b:=1281) (joinSmall (lo:=12808) (a:=640) (b:=641) (joinSmall (lo:=12808) (a:=320) (b:=320) (joinSmall (lo:=12808) (a:=160) (b:=160) (joinSmall (lo:=12808) (a:=80) (b:=80) (joinSmall (lo:=12808) (a:=40) (b:=40) sp12808 sp12848) (joinSmall (lo:=12888) (a:=40) (b:=40) sp12888 sp12928)) (joinSmall (lo:=12968) (a:=80) (b:=80) (joinSmall (lo:=12968) (a:=40) (b:=40) sp12968 sp13008) (joinSmall (lo:=13048) (a:=40) (b:=40) sp13048 sp13088))) (joinSmall (lo:=13128) (a:=160) (b:=160) (joinSmall (lo:=13128) (a:=80) (b:=80) (joinSmall (lo:=13128) (a:=40) (b:=40) sp13128 sp13168) (joinSmall (lo:=13208) (a:=40) (b:=40) sp13208 sp13248)) (joinSmall (lo:=13288) (a:=80) (b:=80) (joinSmall (lo:=13288) (a:=40) (b:=40) sp13288 sp13328) (joinSmall (lo:=13368) (a:=40) (b:=40) sp13368 sp13408)))) (joinSmall (lo:=13448) (a:=320) (b:=321) (joinSmall (lo:=13448) (a:=160) (b:=160) (joinSmall (lo:=13448) (a:=80) (b:=80) (joinSmall (lo:=13448) (a:=40) (b:=40) sp13448 sp13488) (joinSmall (lo:=13528) (a:=40) (b:=40) sp13528 sp13568)) (joinSmall (lo:=13608) (a:=80) (b:=80) (joinSmall (lo:=13608) (a:=40) (b:=40) sp13608 sp13648) (joinSmall (lo:=13688) (a:=40) (b:=40) sp13688 sp13728))) (joinSmall (lo:=13768) (a:=160) (b:=161) (joinSmall (lo:=13768) (a:=80) (b:=80) (joinSmall (lo:=13768) (a:=40) (b:=40) sp13768 sp13808) (joinSmall (lo:=13848) (a:=40) (b:=40) sp13848 sp13888)) (joinSmall (lo:=13928) (a:=80) (b:=81) (joinSmall (lo:=13928) (a:=40) (b:=40) sp13928 sp13968) (joinSmall (lo:=14008) (a:=40) (b:=41) sp14008 sp14048))))) (joinSmall (lo:=14089) (a:=640) (b:=641) (joinSmall (lo:=14089) (a:=320) (b:=320) (joinSmall (lo:=14089) (a:=160) (b:=160) (joinSmall (lo:=14089) (a:=80) (b:=80) (joinSmall (lo:=14089) (a:=40) (b:=40) sp14089 sp14129) (joinSmall (lo:=14169) (a:=40) (b:=40) sp14169 sp14209)) (joinSmall (lo:=14249) (a:=80) (b:=80) (joinSmall (lo:=14249) (a:=40) (b:=40) sp14249 sp14289) (joinSmall (lo:=14329) (a:=40) (b:=40) sp14329 sp14369))) (joinSmall (lo:=14409) (a:=160) (b:=160) (joinSmall (lo:=14409) (a:=80) (b:=80) (joinSmall (lo:=14409) (a:=40) (b:=40) sp14409 sp14449) (joinSmall (lo:=14489) (a:=40) (b:=40) sp14489 sp14529)) (joinSmall (lo:=14569) (a:=80) (b:=80) (joinSmall (lo:=14569) (a:=40) (b:=40) sp14569 sp14609) (joinSmall (lo:=14649) (a:=40) (b:=40) sp14649 sp14689)))) (joinSmall (lo:=14729) (a:=320) (b:=321) (joinSmall (lo:=14729) (a:=160) (b:=160) (joinSmall (lo:=14729) (a:=80) (b:=80) (joinSmall (lo:=14729) (a:=40) (b:=40) sp14729 sp14769) (joinSmall (lo:=14809) (a:=40) (b:=40) sp14809 sp14849)) (joinSmall (lo:=14889) (a:=80) (b:=80) (joinSmall (lo:=14889) (a:=40) (b:=40) sp14889 sp14929) (joinSmall (lo:=14969) (a:=40) (b:=40) sp14969 sp15009))) (joinSmall (lo:=15049) (a:=160) (b:=161) (joinSmall (lo:=15049) (a:=80) (b:=80) (joinSmall (lo:=15049) (a:=40) (b:=40) sp15049 sp15089) (joinSmall (lo:=15129) (a:=40) (b:=40) sp15129 sp15169)) (joinSmall (lo:=15209) (a:=80) (b:=81) (joinSmall (lo:=15209) (a:=40) (b:=40) sp15209 sp15249) (joinSmall (lo:=15289) (a:=40) (b:=41) sp15289 sp15329))))))) (joinSmall (lo:=15370) (a:=2562) (b:=2562) (joinSmall (lo:=15370) (a:=1281) (b:=1281) (joinSmall (lo:=15370) (a:=640) (b:=641) (joinSmall (lo:=15370) (a:=320) (b:=320) (joinSmall (lo:=15370) (a:=160) (b:=160) (joinSmall (lo:=15370) (a:=80) (b:=80) (joinSmall (lo:=15370) (a:=40) (b:=40) sp15370 sp15410) (joinSmall (lo:=15450) (a:=40) (b:=40) sp15450 sp15490)) (joinSmall (lo:=15530) (a:=80) (b:=80) (joinSmall (lo:=15530) (a:=40) (b:=40) sp15530 sp15570) (joinSmall (lo:=15610) (a:=40) (b:=40) sp15610 sp15650))) (joinSmall (lo:=15690) (a:=160) (b:=160) (joinSmall (lo:=15690) (a:=80) (b:=80) (joinSmall (lo:=15690) (a:=40) (b:=40) sp15690 sp15730) (joinSmall (lo:=15770) (a:=40) (b:=40) sp15770 sp15810)) (joinSmall (lo:=15850) (a:=80) (b:=80) (joinSmall (lo:=15850) (a:=40) (b:=40) sp15850 sp15890) (joinSmall (lo:=15930) (a:=40) (b:=40) sp15930 sp15970)))) (joinSmall (lo:=16010) (a:=320) (b:=321) (joinSmall (lo:=16010) (a:=160) (b:=160) (joinSmall (lo:=16010) (a:=80) (b:=80) (joinSmall (lo:=16010) (a:=40) (b:=40) sp16010 sp16050) (joinSmall (lo:=16090) (a:=40) (b:=40) sp16090 sp16130)) (joinSmall (lo:=16170) (a:=80) (b:=80) (joinSmall (lo:=16170) (a:=40) (b:=40) sp16170 sp16210) (joinSmall (lo:=16250) (a:=40) (b:=40) sp16250 sp16290))) (joinSmall (lo:=16330) (a:=160) (b:=161) (joinSmall (lo:=16330) (a:=80) (b:=80) (joinSmall (lo:=16330) (a:=40) (b:=40) sp16330 sp16370) (joinSmall (lo:=16410) (a:=40) (b:=40) sp16410 sp16450)) (joinSmall (lo:=16490) (a:=80) (b:=81) (joinSmall (lo:=16490) (a:=40) (b:=40) sp16490 sp16530) (joinSmall (lo:=16570) (a:=40) (b:=41) sp16570 sp16610))))) (joinSmall (lo:=16651) (a:=640) (b:=641) (joinSmall (lo:=16651) (a:=320) (b:=320) (joinSmall (lo:=16651) (a:=160) (b:=160) (joinSmall (lo:=16651) (a:=80) (b:=80) (joinSmall (lo:=16651) (a:=40) (b:=40) sp16651 sp16691) (joinSmall (lo:=16731) (a:=40) (b:=40) sp16731 sp16771)) (joinSmall (lo:=16811) (a:=80) (b:=80) (joinSmall (lo:=16811) (a:=40) (b:=40) sp16811 sp16851) (joinSmall (lo:=16891) (a:=40) (b:=40) sp16891 sp16931))) (joinSmall (lo:=16971) (a:=160) (b:=160) (joinSmall (lo:=16971) (a:=80) (b:=80) (joinSmall (lo:=16971) (a:=40) (b:=40) sp16971 sp17011) (joinSmall (lo:=17051) (a:=40) (b:=40) sp17051 sp17091)) (joinSmall (lo:=17131) (a:=80) (b:=80) (joinSmall (lo:=17131) (a:=40) (b:=40) sp17131 sp17171) (joinSmall (lo:=17211) (a:=40) (b:=40) sp17211 sp17251)))) (joinSmall (lo:=17291) (a:=320) (b:=321) (joinSmall (lo:=17291) (a:=160) (b:=160) (joinSmall (lo:=17291) (a:=80) (b:=80) (joinSmall (lo:=17291) (a:=40) (b:=40) sp17291 sp17331) (joinSmall (lo:=17371) (a:=40) (b:=40) sp17371 sp17411)) (joinSmall (lo:=17451) (a:=80) (b:=80) (joinSmall (lo:=17451) (a:=40) (b:=40) sp17451 sp17491) (joinSmall (lo:=17531) (a:=40) (b:=40) sp17531 sp17571))) (joinSmall (lo:=17611) (a:=160) (b:=161) (joinSmall (lo:=17611) (a:=80) (b:=80) (joinSmall (lo:=17611) (a:=40) (b:=40) sp17611 sp17651) (joinSmall (lo:=17691) (a:=40) (b:=40) sp17691 sp17731)) (joinSmall (lo:=17771) (a:=80) (b:=81) (joinSmall (lo:=17771) (a:=40) (b:=40) sp17771 sp17811) (joinSmall (lo:=17851) (a:=40) (b:=41) sp17851 sp17891)))))) (joinSmall (lo:=17932) (a:=1281) (b:=1281) (joinSmall (lo:=17932) (a:=640) (b:=641) (joinSmall (lo:=17932) (a:=320) (b:=320) (joinSmall (lo:=17932) (a:=160) (b:=160) (joinSmall (lo:=17932) (a:=80) (b:=80) (joinSmall (lo:=17932) (a:=40) (b:=40) sp17932 sp17972) (joinSmall (lo:=18012) (a:=40) (b:=40) sp18012 sp18052)) (joinSmall (lo:=18092) (a:=80) (b:=80) (joinSmall (lo:=18092) (a:=40) (b:=40) sp18092 sp18132) (joinSmall (lo:=18172) (a:=40) (b:=40) sp18172 sp18212))) (joinSmall (lo:=18252) (a:=160) (b:=160) (joinSmall (lo:=18252) (a:=80) (b:=80) (joinSmall (lo:=18252) (a:=40) (b:=40) sp18252 sp18292) (joinSmall (lo:=18332) (a:=40) (b:=40) sp18332 sp18372)) (joinSmall (lo:=18412) (a:=80) (b:=80) (joinSmall (lo:=18412) (a:=40) (b:=40) sp18412 sp18452) (joinSmall (lo:=18492) (a:=40) (b:=40) sp18492 sp18532)))) (joinSmall (lo:=18572) (a:=320) (b:=321) (joinSmall (lo:=18572) (a:=160) (b:=160) (joinSmall (lo:=18572) (a:=80) (b:=80) (joinSmall (lo:=18572) (a:=40) (b:=40) sp18572 sp18612) (joinSmall (lo:=18652) (a:=40) (b:=40) sp18652 sp18692)) (joinSmall (lo:=18732) (a:=80) (b:=80) (joinSmall (lo:=18732) (a:=40) (b:=40) sp18732 sp18772) (joinSmall (lo:=18812) (a:=40) (b:=40) sp18812 sp18852))) (joinSmall (lo:=18892) (a:=160) (b:=161) (joinSmall (lo:=18892) (a:=80) (b:=80) (joinSmall (lo:=18892) (a:=40) (b:=40) sp18892 sp18932) (joinSmall (lo:=18972) (a:=40) (b:=40) sp18972 sp19012)) (joinSmall (lo:=19052) (a:=80) (b:=81) (joinSmall (lo:=19052) (a:=40) (b:=40) sp19052 sp19092) (joinSmall (lo:=19132) (a:=40) (b:=41) sp19132 sp19172))))) (joinSmall (lo:=19213) (a:=640) (b:=641) (joinSmall (lo:=19213) (a:=320) (b:=320) (joinSmall (lo:=19213) (a:=160) (b:=160) (joinSmall (lo:=19213) (a:=80) (b:=80) (joinSmall (lo:=19213) (a:=40) (b:=40) sp19213 sp19253) (joinSmall (lo:=19293) (a:=40) (b:=40) sp19293 sp19333)) (joinSmall (lo:=19373) (a:=80) (b:=80) (joinSmall (lo:=19373) (a:=40) (b:=40) sp19373 sp19413) (joinSmall (lo:=19453) (a:=40) (b:=40) sp19453 sp19493))) (joinSmall (lo:=19533) (a:=160) (b:=160) (joinSmall (lo:=19533) (a:=80) (b:=80) (joinSmall (lo:=19533) (a:=40) (b:=40) sp19533 sp19573) (joinSmall (lo:=19613) (a:=40) (b:=40) sp19613 sp19653)) (joinSmall (lo:=19693) (a:=80) (b:=80) (joinSmall (lo:=19693) (a:=40) (b:=40) sp19693 sp19733) (joinSmall (lo:=19773) (a:=40) (b:=40) sp19773 sp19813)))) (joinSmall (lo:=19853) (a:=320) (b:=321) (joinSmall (lo:=19853) (a:=160) (b:=160) (joinSmall (lo:=19853) (a:=80) (b:=80) (joinSmall (lo:=19853) (a:=40) (b:=40) sp19853 sp19893) (joinSmall (lo:=19933) (a:=40) (b:=40) sp19933 sp19973)) (joinSmall (lo:=20013) (a:=80) (b:=80) (joinSmall (lo:=20013) (a:=40) (b:=40) sp20013 sp20053) (joinSmall (lo:=20093) (a:=40) (b:=40) sp20093 sp20133))) (joinSmall (lo:=20173) (a:=160) (b:=161) (joinSmall (lo:=20173) (a:=80) (b:=80) (joinSmall (lo:=20173) (a:=40) (b:=40) sp20173 sp20213) (joinSmall (lo:=20253) (a:=40) (b:=40) sp20253 sp20293)) (joinSmall (lo:=20333) (a:=80) (b:=81) (joinSmall (lo:=20333) (a:=40) (b:=40) sp20333 sp20373) (joinSmall (lo:=20413) (a:=40) (b:=41) sp20413 sp20453)))))))))
  have good : (List.range 20494).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 420000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 20493 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 20493 := by
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


private def packet (i : ℕ) : ℕ := (if i < 107 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else 0)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0 else (if i < 15 then 0 else 0)) else (if i < 17 then 0 else (if i < 18 then 0 else 0))) else (if i < 22 then (if i < 20 then 0 else (if i < 21 then 0 else 0)) else (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else 0))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 0 else (if i < 28 then 0 else 0)) else (if i < 30 then 0 else (if i < 31 then 0 else 0))) else (if i < 35 then (if i < 33 then 0 else (if i < 34 then 0 else 0)) else (if i < 37 then (if i < 36 then 0 else 0) else (if i < 38 then 0 else 0)))) else (if i < 46 then (if i < 42 then (if i < 40 then 0 else (if i < 41 then 0 else 0)) else (if i < 44 then (if i < 43 then 0 else 0) else (if i < 45 then 0 else 0))) else (if i < 49 then (if i < 47 then 0 else (if i < 48 then 0 else 0)) else (if i < 51 then (if i < 50 then 0 else 0) else (if i < 52 then 0 else 0)))))) else (if i < 80 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then 0 else (if i < 55 then 0 else 0)) else (if i < 57 then 0 else (if i < 58 then 0 else 0))) else (if i < 62 then (if i < 60 then 0 else (if i < 61 then 0 else 0)) else (if i < 64 then (if i < 63 then 0 else 0) else (if i < 65 then 0 else 0)))) else (if i < 73 then (if i < 69 then (if i < 67 then 0 else (if i < 68 then 0 else 0)) else (if i < 71 then (if i < 70 then 0 else 0) else (if i < 72 then 0 else 0))) else (if i < 76 then (if i < 74 then 0 else (if i < 75 then 0 else 0)) else (if i < 78 then (if i < 77 then 0 else 0) else (if i < 79 then 0 else 0))))) else (if i < 93 then (if i < 86 then (if i < 83 then (if i < 81 then 0 else (if i < 82 then 0 else 0)) else (if i < 84 then 0 else (if i < 85 then 0 else 0))) else (if i < 89 then (if i < 87 then 0 else (if i < 88 then 0 else 0)) else (if i < 91 then (if i < 90 then 0 else 0) else (if i < 92 then 0 else 0)))) else (if i < 100 then (if i < 96 then (if i < 94 then 0 else (if i < 95 then 0 else 0)) else (if i < 98 then (if i < 97 then 0 else 0) else (if i < 99 then 0 else 0))) else (if i < 103 then (if i < 101 then 0 else (if i < 102 then 0 else 0)) else (if i < 105 then (if i < 104 then 0 else 0) else (if i < 106 then 0 else 0))))))) else (if i < 160 then (if i < 133 then (if i < 120 then (if i < 113 then (if i < 110 then (if i < 108 then 0 else (if i < 109 then 0 else 0)) else (if i < 111 then 0 else (if i < 112 then 0 else 0))) else (if i < 116 then (if i < 114 then 0 else (if i < 115 then 0 else 0)) else (if i < 118 then (if i < 117 then 0 else 0) else (if i < 119 then 0 else 0)))) else (if i < 126 then (if i < 123 then (if i < 121 then 0 else (if i < 122 then 0 else 0)) else (if i < 124 then 0 else (if i < 125 then 0 else 0))) else (if i < 129 then (if i < 127 then 0 else (if i < 128 then 0 else 0)) else (if i < 131 then (if i < 130 then 0 else 0) else (if i < 132 then 0 else 0))))) else (if i < 146 then (if i < 139 then (if i < 136 then (if i < 134 then 0 else (if i < 135 then 0 else 0)) else (if i < 137 then 0 else (if i < 138 then 0 else 0))) else (if i < 142 then (if i < 140 then 0 else (if i < 141 then 0 else 0)) else (if i < 144 then (if i < 143 then 0 else 0) else (if i < 145 then 0 else 0)))) else (if i < 153 then (if i < 149 then (if i < 147 then 0 else (if i < 148 then 0 else 0)) else (if i < 151 then (if i < 150 then 0 else 0) else (if i < 152 then 0 else 0))) else (if i < 156 then (if i < 154 then 0 else (if i < 155 then 0 else 0)) else (if i < 158 then (if i < 157 then 0 else 0) else (if i < 159 then 0 else 0)))))) else (if i < 187 then (if i < 173 then (if i < 166 then (if i < 163 then (if i < 161 then 0 else (if i < 162 then 0 else 0)) else (if i < 164 then 0 else (if i < 165 then 0 else 0))) else (if i < 169 then (if i < 167 then 0 else (if i < 168 then 0 else 0)) else (if i < 171 then (if i < 170 then 0 else 0) else (if i < 172 then 0 else 0)))) else (if i < 180 then (if i < 176 then (if i < 174 then 0 else (if i < 175 then 0 else 0)) else (if i < 178 then (if i < 177 then 0 else 0) else (if i < 179 then 0 else 0))) else (if i < 183 then (if i < 181 then 0 else (if i < 182 then 0 else 0)) else (if i < 185 then (if i < 184 then 0 else 0) else (if i < 186 then 0 else 0))))) else (if i < 200 then (if i < 193 then (if i < 190 then (if i < 188 then 0 else (if i < 189 then 0 else 0)) else (if i < 191 then 0 else (if i < 192 then 0 else 0))) else (if i < 196 then (if i < 194 then 0 else (if i < 195 then 0 else 0)) else (if i < 198 then (if i < 197 then 0 else 0) else (if i < 199 then 0 else 0)))) else (if i < 207 then (if i < 203 then (if i < 201 then 0x141d4892d695589ea4932188f386e031415489443d817b09083040b00000141ce752d495089c647820c8ef46aa2f414d88f03c418c09402e00aa0000141c8462e2159ca1a4a12298fe072432915f89683f219109b83200be0000141c2182df157ca0c4af2238fa472031e16009503e819c09c83540da0000141bc1d2d115249cc4782098f006c430f15909643e818b095833c0d60000141b6152cf15109bc48d2120ef86d230d157892c3da18c09083140c60000141b0122d195089e44942198f0c6c230215108e83b417a09082e40c00000141aa1b2cd14dc9b44772080ec46a22fd151090c3ac17f08d83000c80000141a4112d615289c648b2110eec6a82f514b09083c617708c82e40b600001419df12df15709e649320f8ef06b02eb14688d03b417608d82f40ac000014197b32ef95f0a364ad2250fb871232916209884121a309d83380ce0000141916c2f3160ca3a4c122f900c73e34216889c03fe19b096831c0c200001418b3d2e59594a084a42218f706f831815709543d819309083280d6000014185352d095209b847020a0ec06a22f314308b438817008c02e00b800001417f432c714c89b04802070ea86962f714c08d43b817a08702ec0aa000014179092ec15cca104ad2250f946f6317158097040019d09b83400c8000014172f02da95509ea48d2150f2c6d830314d88e43b817708883280c800001416cf62cc94bc9964712070ebc69a2ee14888d039617108a82f00b0000014166e92cf94f499e47820a0edc6b02f414a08dc3c617808702b40aa000014160f42c694e09c447920e0ee46a42f714888e43ba18009103100c600001415af42ce15009d248e2178f1c6c030c15189143be17908902e00b8000014154cc2e395a8a0849621b8f486d030215208f43a816f08c82fc0c200001414ec72d814f09cc48b2150f246d230e15c09083c8183098832c0ca000014148c32cd14a498c4732078ed46bc2f915109203ba18008f03100c8000014142cd2ca14ac98246c2098eb46982e6144889839417108882d00b600001413cdf2ca14b898c46c20d8ef86b82f914d09043d218709182e40ac000014136b92df15909f449521a0f80700312160899c3ec18909483300d0000014130b02d895449f849f2228f586ce30e14e88e43d2186097033c0c800001412abb2d015249d04852148f2c6c42fa14f891c3ba18209183000b8000014124b62d715589ea48b2180f686da30715408f03b217d08a82d00b400001411eb92c3949c9944782110eec6b02fa15009103c418108d02f40b2000014118852e6956ca084a22228f646d631815909503ca18909283300cc0000141126e2d314e49b247a20e0ef46c830014f892c3bc18209282e00ac00001410c4a2e4159ca0e4a82230f8070632e163897c3f818e09583440c80000141061e2e215489ea4912150f006d430114f09103d418d09703340c4000014100122da15349f249f2168f206bc2ff14c08cc3b618208c02e80cc0000140f9db2e895d8a204b52288fcc72a331168899040a1a309a03600de0000140f3c52e195609e04932190f646e4315156096840219809c03200d60000140edb32dc157ca0048d2180f2c6dc30b159895c3e418a093832c0ba0000140e79a2df15889ec4922158f186ba2f114708c439617008802ec0c20000140e18b2da15049c847920a8edc6a02fc14688d83cc18709103180bc0000140db8d2d915409e048c2160f506d430114e08e43a016808182b80aa0000140d5872da95349de4902178f246d830314f89203ca18809282ec0b40000140cf592e615b0a124a722a8fc471832615f89903e218108f82cc0b20000140c9552d295089b848a2130f346dc30b14f08e83ba17f09082f80b80000140c3352db153c9dc4922168f2c6cc30e15609543e219109182ec0b20000140bd3d2c714bc99e4672048e9469c2e914308bc398175091030c0be0000140b7372d7952c9ca47820b0efc6c830515889403da18d09003100ca0000140b11f2d5952c9de49621c8f646e231815c09583d417e08c02e00b40000140ab152cf14f49ba47d20e0f006dc30a15208ec3c018308f02f40c80000140a5192ce151c9de4902148f206b22fd14b88f43b217a08a82d80b800001409f0e2d795049a84652000e6c68a2e013c88bc3a217008982cc0ae000014098fc2d695249c647d20b0ec06a82fb14e09143d019709983200cc000014092ee2dc1564a084a02178f3c6dc31315989303fa18f09703200bc00001408cec2d1952c9d247e20e0ee86aa2f615109103bc18208f83180c6000014086c62e0154c9e449621c8f846fc32315e09403e418708f82ec0b6000014080c22d114f899c4732090ecc68e2ee14988d43b417d09083280c800001407a792f215f8a224a12210f9070a31d16209944161a80a403600ec000014074692d9152c9d44892140f306ec317159096041819e099036c0e400001406e6e2ca95009cc48b2138f286ce2fb15189303e218909003340c20000140682e2f515e4a1e4af2288fc871c33016909ec4201a309c834c0cc000014062472ca14bc9a84842110ee86b62f614e88d03a817708b02f00ce00001405c342da15289ec48d21f0f386e230115008ec3b618608f02f80ae0000140564e2c4148898e4662020e986962ed14b08e83cc18109182fc0ce000 else (if i < 202 then 0x14357d52c794dc9ac46a2050e806982e2141889838217308702d80b4000014351b52dc95709f849f21e0f5c6f231a15c89583e419309783540dc00001434b9d2d395209d848620d8efc6be301150891c3cc18408c02d00b2000014345872dc15649e649b2248f746de2fb14b08c43c018909b83400d000001433f862ce14f49be47c20e8f0c6ce30514f89203ba18209703240c2000014339752d9956c9ec4972160f0c6d231415609343c818909383080c40000143337c2cc14d49a24681ff0ecc6b030114c08d43bc17e090030c0d200001432d552d7956c9f249b2138f306dc30615189143be17108e82ec0b2000014327132f19604a284af2228fac71a330169099c3fc197097030c0ca0000143212d2c2947c99246b20b0ed86b62ff14c08c039017408882ec0c200001431b422c2149498245e1fa8e406802e3145089c38617408d82d80be000014315342d695289da48820e0f0c6c22f814c08d43a016e08402980ac00001430f032ee15dca1c4ab2220f606e430d15589343c618509302fc0ba000014308f52d915509f649921a0f306d02fe14b88d839417508e83100b0000014302f32ce14f89b04802140f386ce30e15409303da18d093830c0d40000142fd092c794d09b847a20e8ef86cc2fd14c890c3c617808802d00bc0000142f6db2e715a0a0e4a52208f786f031015889543d218d09302f80c40000142f0b82da953c9de48a2150ef86ac2f915189103de18e097832c0cc0000142eac32d014f49c44702080ea068e2ea14608b439e16e08b82d80b00000142e4992e315749de48e2150f146dc30d157092c3ea19209783080c80000142de682e715ac9fc4a52230f9c6f831315609343d2183090831c0c40000142d8692cb94e49ac47e20f8ed868e2e914a08ac3a817a09303240d20000142d26f2cb94d89b04842120f1c6b830014c88f43b017608f83000c60000142cc3e2ea15c8a0c4ac2248f6c6fe32315b89583dc18d096033c0d00000142c62d2da955c9dc4912170f6c6f8315158895c3e018809803380d40000142c0102e395609ec4912188f7c6fc32515c09643d8187093832c0ce0000142ba232c614b49a04662038e9c69a2eb14908d03be17f09183040c40000142b42a2cc14b09a046d2058ea069a2fe14b89003b618709302fc0ba0000142ae082da95749f649d21b0f2c6d2304153091c3c217808e83000ac0000142a7e82e015889ee49d2218f8c6fa31a16109943fa19a09a833c0d00000142a1f22c814c89904682030ea46922eb143085c38c17008c82dc0c000001429c072c7948c9824692060ec06b02ea14688ec3c017e08a02d80b20000142961a2cb94d899e4702070e8867a2dc143889839216d08682c80c2000014290172d015049d047820d0f046c42fb14f88e03ba18109383040cc00001428a322c394889784631fe0e6c6842e013b886c38215a08502c00c4000014284182db95609ec4902130f2c6dc30e14f88dc39817209103140be00001427e002d895689dc4912138efc6bc30514f89043b817008c83000ca000014278042cc94ec9c04892108f206dc30314e08f83d418008f03000b2000014272012ca94bc9a647120d0f0c6cc2fe15109143cc191096831c0ca00001426c162ca14d49a44762100f0c6ce31015c89603f618909302d40c4000014265fc2d995809f44962138f186c830815389183b618509603380da00001425fdb2e4957c9f849921a8f5c6e430a15188f83be18008f82e80aa000014259cf2d895609ec48f2148f306e230e15789443c618509183180c6000014253f22be948097a4571ff8e806802df14088c83a017708f02f40c600001424db92ee1618a364bc22c0f9870632416209783f819209803480d60000142478c2e715bca164aa2208f606fe31a16389a440a19209683300c60000142416f2df15789f649821b8f2c6e631715689343ca17f08a82e00ba00001423b572dd95809ea49121b8f406e030d15509403c818609803080c40000142357f2ba945898646c2038eb869a2ec145889839016608602e00b800001422f7e2d615189d04952190f4c70031d15b09443e619309483280d2000014229612e0158c9fa48e2148f106ca2fd14d88f03a017308882dc0b6000014223612d114e09c44822130f446de31415d89303be17a08782a80a600001421d582d495309cc47d20d0ec86aa2f114b88c03a617908c82fc0b4000014217432dc95689d648a2140f186de30d15709343bc18b08f82e00cc000014211682b9945c95a44c1fc8e4467a2df14288903a217908a83180c200001420b442e295889f44942188f286e630f155093c3ee18c09203140d0000014205382d194f49c04832108f086d22fc14d88dc3be17a08f83140c00000141ff292cf95109b647320b0ef06cc30214d88c83b417808882f80ba0000141f9322c894ac9a04712030ecc6ae2f414b88b03a017a08c03140ba0000141f31f2d795309e64902160f0c6a62fc153890c3e618f09503180c00000141ed2a2cc150c9ca4812130ef86ae2ea14608cc39617008a82c40bc0000141e6f32ed15b4a164a321d8f746e631215e89883ec19209182f40b40000141e0cb2e395a4a124a821c0f486e431315a09243ac17608d83040d00000141da912ee95b8a0c49c2168f546dc309151890c3ca17b09303180c0000 else 0x144db702d715589ee49e21a0f346ec30e15609343ce18b09503240bc0000144d5892c594a09984752090eb468c2e414608cc3c0181093830c0cc0000144cf6d2db957c9f249621b8f846f231215809483d219109482fc0c00000144c9432e49598a184a221e8f646ec306157091c3b017a08e83000be0000144c3302da15249e649f21d8f5c6ee31815b89343d018208c83040ca0000144bd352d395009b44942128f186ce2fe15409203be18009783280d00000144b7232dc95509d04872148f406d230615509083ca18809182f80c80000144b1142d494fc9c047c20d8ef06ac2fb14a08d43b017208902b40b00000144aaf82df1598a0c4a52250fc071c32b166898c40a1a009d03480c20000144a4d32e415c4a124a421c8f746fe31c15f09503ce18409182f80c200001449eeb2c814ec9c047720b0ecc6a82f514708b038c17008902fc0a8000014498e02d595289d04822130f646e231115b094c3f2194099831c0c4000014492f52ce14e899846e20b8ef86ca30515189143c2182095030c0cc00001448cef2d695309ca48220f0f186d830e15b89683e4191098032c0d6000014486fb2ce15089bc4892180f786fa31715989643ea19309803080d0000014480d02e79590a064ac2268fc06f8304156095c3fc19609a83780e600001447af12c494b89b24782088ea06962f014208b43a417a08c02e40bc000014474fe2c4949c99e46e2048eb86962e914308b43ac17b08482c40be00001446eef2d5951c9d248220e8ee86b22ff15188ec3a817c08e83240d6000014468d82db95449ec49521c8f346d2303155891c3c017808a82a80b2000014462e72c794d09bc47e20b8ed86ac2f714c08d839016308582c80c200001445cec2cc94cc9b24732088edc6be30515289043ac17508c82e80be000014456c52e1158ca064aa2240f8c6e830b15009203d819509703180c8000014450b62d8150c9ba47120b8ef06be301156093c3f61a0099834c0d000001444a962dc15449d048a2158f286d030d14e88f83ba18508f82fc0be000014444a22ca14c098c46d20b8ef86ac2ed14588d43ba17f08b02e40ae00001443e912d395189ce4892158f346c42ff15289203cc18a091832c0c6000014438892d414b09b247220e0ef06aa2fa14e88f039e17208e02f00ae0000144325e2e215689f84902138f2c6de30415489303d018909302f00b400001442c442de15289d84962170f3c6d830515608fc3d218109003000ca000014426252dd15549f24982178f746f231815809743fa19809583140b8000014420352c3146c97e45d2058e9c6aa2ee141888039417008d02f00d600001441a032ea95bca164a62208f8070631815889403d618209283500d6000014413fd2c794e89c647b2138ed06b62ef14908dc3aa17508882f40bc00001440ddb2de95589e048e2130ee86ae2fb15008f03ce18708e82d80c0000014407c12d8150c9cc4902170f306dc31215288e43ae17a08e02e80b0000014401c92cc15089d84962158f106d42ff14e890c3d418108a02d80ba0000143fbbd2db95509d648c2100f246e430e157891c3d217c08f82f80c60000143f5a52e11598a044a62240f8870632915f09603e818e094832c0b80000143efc22bc146897a45b1fa8e5466a2e114388c038c16e08482bc0a20000143e98d2e815aca0a4932188f2c6e031015608f43b218609783200c80000143e3422f9963ca364b72238f8470431d15b093c3e218d093030c0a80000143dd2f2d915489de48a2170f346d230315389283ca18208e02e40c20000143d7462c594c899e4752090f006c82f314b88f43a817408b02c40b60000143d1072ee15d8a1c4b12278f7470232515e89543e0195094830c0c00000143cafd2d495309c84892110f086d430f15789403da18c095031c0c60000143c4cf2ed1600a2c4b82240f9070e32916389743f419f09a83540c40000143be9c2e495749e64972168f2c6bc2f914888c03a217908d03080b60000143b8a92c694c89b247b2078ea06902e614688903ae17b093031c0c60000143b2a52d115209da4912158f246e830a15008dc39217e08d82f00c20000143ac882da15389d048e2180f146ce31115509403de18a09183100c40000143a6852d015149ca48220c0ee46bc2f814c08d43ae17908d83000cc0000143a0662de158c9e649e21f8f546e4310158895c3e819409703240ce00001439a892c294c899a47220c8ed06b62ef14788c83aa17609483100c80000143947f2d7153c9d049a2258fc472032115909303cc18e097032c0c400001438e492e6157c9f448d21a0f446d630b15409143d018708c83000c20000143881f2e895b0a0e4b022d8fc871231e15a89303de18609303080bc000014382342ca94f499e47320c0eb86ac2ff14e08f43ce18d09383000c000001437c222d995609d648320f0efc6de30d15509343d8197093031c0c40000143761e2d115249dc48e2120f246d030c15c09603dc18a095032c0d80000143700a2da1564a0049821d8f5c6fe2ff15209483d819009183180be00001436a192cb94dc9864652038ea069e2f314a88d83ba18008b82e80a6000014363c92f595f0a2e4b42260fc872c32915f89583ca17b08f03000b800001435dc32d295049c447f20a8eec6c630314d88c83a816f08502a40a8000)) else (if i < 205 then (if i < 204 then 0x1465f992d194f89b248320e0edc6a62f414b08dc3a418209503140b2000014659a12d315109c24852148f406e030b15709383d418609003080c0000014653c42c494b09aa4742068e986722d413f089c39a16a08602c80b600001464dc92ce95089ba47a20b8ef86bc2fd15089003ba17c08d82f80b8000014647a42e2956ca0e4a52218f686f231f162099840c1a109a83400c4000014641982d495149c647d2138f146ea31815509143da18f09803040ca00001463b772dd9560a0249e21b8f4c70c31c15e09783dc19209883280bc000014635662de95749de48d21b0f606e631615388f43de18a08f82e80c200001462f622d6953c9d64902198f6870631d15589103d0182090030c0c60000146294f2d895389dc48f2170f286d230a15208f83ae17b09003040b4000014623382dc958ca0a4942190f146b8302150891c3b816f08c82f40c400001461d282d795309d448921a0f406e630d15109003b217b08d82e40b0000014616f72e51588a024a92230fbc71a32b15d896c3f6197094030c0ac000014610ed2d515389ca47c2118f046c82f514d88f83d818f09503140be00001460ac72e3957c9f049921e8f846fe32116089603e218d09502f80be000014604bd2d695309b847720c0f006b42f514a08ec3b416e08902d80bc0000145feba2d714f09c248d2158efc6bc2f114a08d83c017d08f03240c40000145f8c82c314b09ba4852158f006c830615308e43be17f094032c0d40000145f2d52cd94b89a847d20f8eec6b630115408f83ac17709403100b80000145ecd12d115089c049021d0f486f631f16209603f81a30a1837c0e40000145e6c72d2150c9d448f2148f306ea31015509383fc192094830c0ba0000145e0d12ca14dc9a847f20b8ef06d630915609443de19809f833c0d20000145dab52de953c9f04872110f106c4301153891c3a4182093030c0c60000145d49c2d995309d84852148f386dc2fd14a88ec3ac18709282f00d40000145ce7b2e215589f24932150f486e8316157892c3be18608e02d80aa0000145c8852ca14bc9b047720c8ef86a42ef14908ac3a216a08902e40c60000145c2732da95589d848620f8f146de31615a89103c018308f03040c40000145bc4a2e015909f84972178f206d830a14f88cc3a817f09302f40c40000145b63e2d4952c9e04862128f0c6c230814f89203e218d09683600d00000145b0312d695409ea49e21c0f7470631a15e89884001a009a834c0c80000145a9f82ed95a4a0c49f21f8f7470831d15d89503d2180091832c0c60000145a4282ba943c96c45c1f98e4c6702e0143888438a16a08682b40b800001459e352ca14dc9b848420d8edc6b02fe14f09083e0187097834c0d8000014598132e0957ca0049621c8f846f431615b09343d218709282fc0a20000145920e2cc94f89ac47320c8eb86902eb14688bc39e17008b82fc0a400001458be12e495889fe49d21a8f606fa31715509143c417e091032c0d6000014585d02d915789f04952140f306d630d15689443dc18208d02bc0ba00001457fcd2cf14fc9ba4812160f486ea31c15e89603e4193098031c0ce000014579ae2dd9574a064a121e0f806f4310155894c3cc18209582ec0b4000014573bf2c794b09a04712098ee06b42f715389343de18909282f40b600001456d822ea95c0a0e4a82240f586f631f15e89883fa19909783500da0000145676f2e095689f649821a8f546ee31115989243d0188099831c0d4000014561502de95889fe4ad2200f6c6f231816009843e418708d830c0be00001455b1d2e6958ca1e49c21e8f706ee310155091c3ca18f094032c0ce000014554e92e315789f249a21b0f406d230614e88e83be17908d02f00b800001454edc2d095209bc47820e8ee86aa2ef14708cc3b018008c03080b6000014548bc2da1588a1049c21e0f8c6fe31215789303ca18b09502cc0b4000014542bc2ce94e89aa47320c0f346da31215889703de19209303040a800001453c892e815c09fe4af2288fac71232a15f89803fc19309783180d4000014536832d1951c9c847f20e0ecc69a2eb14508e039616708582c80ae000014530542e49590a044a32220f6c6ea31e15889143e219009383300ce00001452a2d2e215809f649621b0f3c6da306151091c3cc17e08f02ec0b8000014524302d015249c84812130ef86c230715389083bc17e09383040bc00001451e2b2d095009d248a2188f706f032016309603fe191095033c0c8000014518112e1157c9e248a2148f4c6da30515288f83ae17c090031c0cc000014511ed2dc15449dc4842168f506ea31715789383d417e08d832c0bc00001450bdb2da153c9cc4832138f106cc30315289283d618609683200c4000014505be2e0955c9e649521b0f5c6fe31a15a095c3ee18e097036c0e40000144ffda2bd147497e45b1ff0ea869a2ed14408c03ae17608c82e00aa0000144f9d42cf95009b447920c0ecc6a62f214b88e43ca18108e03080c60000144f3c12df15289c848b2160f406e831a158894c3e018f09683000c20000144edb42ce14e89924692080eb069c2fa15109183be17708b82fc0b80000144e7962d995289d249221b8f4c6dc31015409143dc18b09082e40c40000144e1852d4953c9ec4882160f406dc31715a09543de18508e83140b6000 else 0x147e3192de157c9fe4992180f486f0312154092c3ca18408d82c80b40000147dd022db1590a004a221f0fcc712326162898c41219c09903300c40000147d6e82e115849e24952168f146cc31b15a094c3e819a09b037c0e40000147d0cb2d995a4a044942168f5c6e230815189203c2187090830c0b60000147ca912e715bca0e49a21e8f746da30014d88fc3c218409603140d60000147c49f2c714a898e4602080ed86bc2f815088e43b017308e82e00b80000147bebb2c214b49a047120b0ef06cc302152090c3b618909783400cc0000147b87e2ec95c8a124a42250f987043251660994410197094031c0d60000147b2902c294bc9ca48e2158f246e431015709383c418509082e80ae0000147ac922cb94e499846d2048e946962e714408bc39016b08682c40aa0000147a6a12cd15109c24822120f146dc30c15789443da19009903040c00000147a0992d795409e849421b8f586fa31415909003c217c09103040ac00001479a842dd15889ea4962178f546f631615a89583ce17c08d02f80ba000014794672de154c9fa4982198f286e631315689303ca17b09183240d000001478e6d2c594cc9a247e2130f1c6dc31115989643ea19709a033c0de0000147884a2de15489f249121a0f186da30615289143c417b08d82cc0bc000014782632c994f09a847320c8ee06ae30414b88dc3be17f09182f00d800001477c2d2e8159ca0a4ab21f0f7071032315b09703f819d09803240ca0000147762e2d415309e048b2118f086c430015089003b618c09383240d4000014770112df15609f64932170f146ca30d15709283cc18309282e40ba000014769f02e015aca064a021b8f546e631b15c89343e819109503140c2000014763ee2d295209c447d2088eb46a02f514c08d83b617e08c02ac0a000001475dcf2e095749e24962158f4c6dc315159096c3f419f09f03380dc000014757d02d014e49b447b2108f2c6be2f614a08bc3a016908a02ec0b6000014751eb2c4949c98445d2028e9868a2e714608d03b418208f03000c000001474bfa2cb94ec9c647c2098eec6a42f114608bc3a816f08982c40aa000014745b62ed15cca224a921b0f3c6f0318159894c3de18808c02dc0bc00001473fbf2cc95149ce4892128f446d22fe14e09083b018208b02e00aa000014739d62c4948c9804641ff8ee86bc2fc14f09103c418909082f00b0000014733ac2df15549e24892168f206d830615b89383d218d09783180da00001472d7f2e015809f449b21b8f4c6d630114d08f83c418208902ec0c40000147277d2d495189c84872130f206bc30314c88e03c218008e82f40b6000014721642db955c9f449721d0f406ca30d15188f43d417e08d82f40c200001471b472dc15709f44a82208fa86f431815609283ce18209383280c4000014715482ce14f49b647a20d8ec46b42f314e88e83b217908682dc0ba00001470f1e2e315789f449c2190f3c70432315f09703f018708e83280cc0000147091d2d495289ec48f2170f446c630614b891c3bc17f09383100d20000147031c2ca14f49c447e2118eec6a62f614c09283bc18509282f00b40000146fce12e715809fc4a02208f806f431d16009383dc18e092030c0ca0000146f6c32d9956ca044a42250fa471432016209583f019c09803300ca0000146f0d22cb14f49a646f20c8edc6a62e314809003a218009083280c80000146eadc2cb94e89b84802118efc6d030515509183ca18e095030c0b00000146e4fe2c314ac98e4652038e5c6682d714008cc3ae18609383240ca0000146deb12f71628a364c422d0fdc73833f16389a04221a109d83540dc0000146d8a72d615449dc4922140ef46c230415409203ee18a098032c0d20000146d2572f8964ca4a4bd2240f746f6315157891c3ea18b09603240be0000146cc682c914d099c4712010e906842d7143087837e16d08602ac09a0000146c65e2d995509de4852118ef86c42f714d88ec3aa17709183180d20000146c0412dd95589d647e20f0ed46ac2f515509083da18409883140cc0000146ba1f2d995189de49a2180f386d431015208ec3a617b08b02f40b40000146b3f82e2156c9f44a12200f606d830e154091c3ca18608c82d00b60000146adcd2e595a0a004942170f2c6dc30a156893c3e2185093831c0c20000146a7aa2e195709fc48f2158f146c62fc15088fc3b817c09182f00c60000146a19d2d415089c648420e8eb46842ed14808c83a817308902c80c800001469b8a2d61540a0449d2198f3c6ee31215689483cc18608d02d40b6000014695802d795389da48b2178f146d0311153891c3ca18409082ec0b600001468f8b2cc94f49ac4782090ed06c22fe15209143c818b09a83500c80000146898b2d014fc9c648120c0ec46ae2fb14d88d43a816908882d40b8000014683812d395309ce4902150f006c230015188f43b618109583380cc00001467d992c414ac9964722060ed068c2dd14088a838216208282b00a6000014677962ce14e89b647b20b0ee86c830b151890c3cc18609183280c20000146719f2c414ac9a246c2088ed06b62f114988ec3b017208a82d40c000001466b8c2d915289ca4832148f286dc30f15109203c218409303300dc0000146659a2cb14c099847220d0ed46a22f314908c038c16008582e00c0000) else (if i < 206 then 0x14966ca2d1151c9e249321a0f306da31115c094c3e819c0a0032c0d4000014960d42d3950c9dc48d2178f306c830214e89143c217e08e02f40b200001495ac62d5152c9de48d2128f106be2fb14988f03b217f08e82e80d20000149549a2e495989fc49921b0f606e8315158095c3d818a09303000d200001494e822d694f09a047120c0ef06a62f014d08f03ba17e08902fc0c0000014948992c094909904612018e986a42ea13d08803a817b08902f80aa000014942592ee95d0a104a52210f9870e31c15b09243de18a099033c0cc00001493c492db9578a0249b2160f346ca30a15609343e019c09a03400c4000014936372de955c9fc4a82290fa870631a15c89803fe18f09603240de0000149304a2c694b49a64712058ebc6ac2f414a89083cc18108c02e40b200001492a302db955c9e24a22158f086da30215489143e2196096832c0da0000149241f2db95689fe4932208f5c6cc2fb14c08f03b817e08982e40c000001491df62e01584a0e4a92288fb870231a15609383d618f09203180ca000014917ee2cf14e49c84832178f486ee30c15989443d018a09082f80b4000014911f72cf94e89a646f2060eb86a42f214808b039616908782bc0b200001490c092c994d49a44712050eac69a2e514288d039816508482dc0a6000014905d52e615b8a124a22228fc070832515e89683f419009483180c80000148ffcd2d3150c9c04762090ec469e2f614b88f83be17e08d82e80c00000148f9ee2c394889864682040e8c69830015108f83b417608a82e00b60000148f3f02d515109c047b20e0f186ca308152890c3c017708882c80aa0000148edcf2da1568a0c4a62200f8870431f15f89843f419909b83380be0000148e7a12df159c9fc49d2200f786f0313159091c3c017c09002f00ac0000148e1852dc957c9ec49e2238f706fa31e15e09543f0184091831c0dc0000148db9d2c4949497846a2008e8868a2ea142088038c16908382dc0a60000148d5992d3150c9d64882090ed068e2f914d08e03ba16908182a80a20000148cfb52c294b098e4682060ecc6b02e714708b43ac18008d02e80aa0000148c9a22e1157c9f049b21b8f986e430a15409083da17f08f033c0d80000148c3822e11594a0249b21b8f3c6ec31015209083ca18908a02fc0c60000148bd6a2da15389d048b21a0f206c830515089143d419109483300d00000148b75d2cd14ec9ae47e20c0f046d030d15709183ae17508782d00b80000148b1522d995249da48720f8ef06ca30a15a89283dc18a09183340c40000148ab4c2d515189cc48a2110f2c6c830715108ec3c018a096831c0c40000148a5082ec15dca204a521f0f586e831115509203ba18108e82cc0b800001489f1f2c514a49984752080ee46aa2ef145089838216108402c40be000014899072d915249d048f2108ed46aa2f615008d83ac17c090830c0b8000014893062cf14f09c64892118f0c6bc2fb14f88ec3b617708e02f80ba00001488ce42dd156c9f649c21e8f846f231c15a09503e019009082e80ce000014886b42e195849f449a21c0f146f631f16089583de18d09b03500d0000014880a02d915449d449521a8f306fa31215809103d018509103080b600001487a862d9953c9d449921e0f686f232315e094c3e818309582fc0b6000014874852cf94d09ae47020b8ef86c030715789103be18709883180c800001486e982c714b49ae47e20d8ef86b02f814d88cc3b217708b82e40b0000014868b22c094bc99446a2090eec6be30114988d43ca18809183100ae0000148628a2e4159ca0a49e21f0f786f630f15c09783d418e09583400be00001485c6f2db950c9c047720d8f106ca2fa14b08f43be18008c02f80c6000014856592d415349d448d2108f1c6ce30515089303c217a08b83000b4000014850772bd946c98a46d2048ef06dc31015209183ca18109383200d000001484a692d5950c9be48a2158f546f4318159894c3f419209483240c0000014844622d294f49ba47e2108eec6b8306151090c3d218509303000b800001483e632ce14f49d647f20e0f0c6c42f914708b03a217808a02d40c2000014838302e595a4a004a52238f546da31414f09143b416e08d02fc0ca000014832212d615489ce4822108ef06b22f414888a438c16908982f80c000001482c142d914fc9aa47c2158f346d031115709143d618308f83180b8000014825e02e395749fc4942190f486e031215a096c3f619709583280ca00001481fd72cd14f89d24872100ef86be2f414d89003ca18d09082e40b4000014819b12dc95489ea4992170f046b62f414508a838c17108982e40b2000014813932dd15789fc49221c8f586ea31a15a89503ea19b09a034c0d400001480d5e2ec15d0a224a72220f6c6e030f15889483e619b09f835c0d6000014807622cd94f49b847f20e0f1c6dc310156890c3e218609783380d0000014801762c514a09ba47720d0ec06a82f815209083c217a09083080cc0000147fb612dd154c9de48a2158f086c630115289003d018f09402f40be0000147f5562dc95549ec48c2108f1c6b830a15389203d818e09383000be0000147ef472d6155c9d448c2170f1c6b02f414808d83ba18008d83040b40000147e9332d49558a0c4a02208f846f031a154093c3d619509e035c0e2000 else 0x14aea4e2f515f8a264af2228f7c6ec30b15408f83c017708a82e40b6000014ae4412d695089c84882168f346c230815589083c617b08d032c0ce000014ade222de1574a064a721e8f806ec31515909183cc18e09583200c0000014ad8172d815489e44a321f8f586f431515389143bc16d08202bc0aa000014ad2102d795489e44922160f346cc30915608ec3be17908702d40ac000014acbf22e11584a0249b2178f446ec31d15e89443de18808c83040da000014ac5cb2e1157c9f649a21c0f406da30d15489243d6191097830c0ba000014abfb22d81554a0249a21b8f2c6d430914c09083c618608d03080d0000014ab9b02cd94a899e47520c0eac6ac2ed14888c83b417408b03000b0000014ab3bd2ce94d899647120c8f046c02f615209283d818009182f00cc000014aadd42bf945097e4642060ec869a2f314d08e43b2183091832c0cc000014aa7c82db15549fa4942190f606ea31d159092c3c618e09a03240ce000014aa1d12cc15109d848e21a0f446e030814d08ec3c017a08c02f00be000014a9bc22d995509ee48c2158f246d4301151891c3d418509502fc0c0000014a95d82c6949098846d2048ecc6ac2fa14708bc3a017408c83000ca000014a8fe52d014e09ae47c20f0edc6b22f714e88f03d018108e83100be000014a89d82d295049c248c2178f286c430315589283d619508f832c0d6000014a83e62c915089d648a2160f486e031315089243c817c08b82ec0c2000014a7de62ce14e49d24872150f206ca30314e88f83c218208b02f00b6000014a77ed2ca14c49a447220d0f186d22fd15088d83ba17408682ec0be000014a71d12d81548a0049421b8f706f230f15789203ca18e09603440da000014a6bc82d6152c9da49b21a0f706ec317159091c3e018709403140be000014a65912e915809fe49721f8f7070432316409803f81980a1835c0de000014a5f6a2e915b4a1a4a92228f706f030d159095c3d818f09a03240c2000014a597e2cb94ec9b24852110efc6b42f714f08f83c817708b83000bc000014a53672d395249c24802110ef46ca2fd14f08d83a817e08b82d00b2000014a4d532e09584a0c49c21f0f846ea314157896040019609402ec0b4000014a47492d415389da4902148ee46aa2fc15209143c818609003080d0000014a413d2d615449f049721b0f406da31015b094c3dc18408f82f80d0000014a3b452c714889944692098ec86b630514e88f03bc183090830c0cc000014a35242dc15689e848f2160f346ce312155890c3d0185094832c0da000014a2f172db95749fc4a72200f6c6d430a15409143c818009082e00b4000014a291e2cd94f09ac47420e8f206dc30114d88f83ba17108c82e40bc000014a231f2cc94fc9c04852108ee86b82ff14988dc3ae17908a82c40ac000014a1ce92eb95bca104b122a0fec73033116689c43f418e09303100bc000014a16a82f2961ca464c6234900c74a34916a8a044201b50a383540c2000014a10682e695b0a0c4a721c8f486ee31815709183e018e09583100c0000014a0a602cd95289d048c2170f4c6f031615b09383e018208c82e40c6000014a04412df1584a184a72230f606f830d15609103d219109b83380d60000149fe692be947098845f2040e9067e2e214108a037a16108602dc0be0000149f83a2e915909e24902198f3c6e8308153891c3d218f09583080cc0000149f2292cf15189cc4842130f106bc2fc153090c3c818109283380ca0000149ec0d2e095709d848f2198f4c6e8303157890c3d018709202f80bc0000149e61d2c714b49a64812098ef06aa2f414788d83b017709102f00bc0000149e00d2d595209c447b20e8efc6b82fb15008f43b417708b02e00b20000149da152cf14e49b647620b8ef06b82f214808c83aa17708902a009a0000149d3dd2ea95a4a0249621a0f306dc311156094c3e418809403100b20000149cdb12e415809e44942148f2c6e431515e09503e618d09403140ce0000149c7ac2d695189ba4782118efc6c630815008ec3cc18609302fc0d20000149c1a72d094f89e44892140f1c6d430d15109083b218409203100c40000149bba42cf95189ce4842110f006b030614f89083d217d08b82e40b20000149b5a02ce14f89b246d2060ed86be2fc14a08d43b417808f82f00bc0000149af9e2cd14ec9c04782078eec6b82fe14988fc39617408a02cc0b40000149a9712e29584a104a621d0f406e231615a09383c6187096032c0c40000149a3792ce94e09ae47a20d8edc6c22f514e08d83ae17809302e40c600001499d742d4952c9c847b2120f146b630815789283c218808f83100b60000149975e2d89550a0649f2210f6c70632215e095c3de18809403340da000014991512d595289d648420a0f086c42f615208f03a817e08d02ec0b800001498b1f2e315849ea49021a8f406de31315609503ee191090030c0b80000149852e2c694d09a246b2008e786982ee14888f43b818308f03140c200001497f092eb15cca204a621d0f406e630915309303ca18508f832c0c6000014978e42e01564a064a421e8f606f231615d09503d218809182f40ac000014972d62d594ec9be47820d0f046d8308150890c3a417308682d40a800001496cc92d8153c9d04942178f1c6bc30115289083c218509082d40b0000))) else (if i < 210 then (if i < 208 then 0x14c6d7c2e715c49f649f2158f246da30b15108f43ba17c09203380be000014c675f2dc15789e84a22238fa870832616189943f619609983280cc000014c615e2cf15089ca48520e0efc6b42f614e890c3d6187093030c0c8000014c5b532d995489e64902160f206e8311158091c3e618809103200c6000014c553f2d815749e84922170f286ce300151890c3ca18a09683040ca000014c4f232dd959ca044a221f0f506ee31c16089703e2188098830c0c2000014c490b2da157c9fa49721f0f586ca31215108f83be18d09503300c8000014c43102d515009ce48b2110efc6c030a15388d439416c08602dc0b6000014c3cd52e915cca224ac2230f8870431815909443c418108f83380d4000014c36c02d915289b047120c0ea46962ee14888d03a417508802b00a6000014c30c12d314f09a847820e0ee06a82fa15008e03b217a08e82c40b8000014c2abd2cf94f49bc48120f8eec6ae2f714b08f43b417708602b008e000014c249d2e21590a024a42228f9070432215e89a43f0197096030c0ce000014c1ec32c094a09a847320c8ed86a02f614988c43bc17b09803100b6000014c18a62df1578a0649c21d0f746ee31315509183dc18809402ec0c2000014c12b92c514bc99247220d8ed06ac2ff15509383f019709d03440d6000014c0cb32cf951c9ba47c20c8eec6a22fa14b88f83a617208e83040ba000014c06a42da95589f04982188f286ae2f614c88f03ae180093831c0b6000014c006f2e995e4a2c4ae2240f9470c32015e89884021a309b03200bc000014bfa712ca94cc9a647a20f0f046ac2f914a08d03a217908f82cc0c2000014bf4692d2952c9c248520e0f086b42ed142088039216b08682a00b2000014bee692ce950c9ca48e2188f086ba302155092c3e018209482ec0b2000014be8722cb94d89b246f2078edc6ae2f314a88cc3ba17808f02f00c2000014be2782c7146c9684672038e906922e413f88c03b417c08d02d80c6000014bdc572e595c4a084a721f0f486d62fe14d08bc3ac17708e02f80ac000014bd67c2be14749884631fe0e646622d813a085439617308c02c80aa000014bd0962c314a499a45f2028e7868e2ef14588c43bc17b08f03140bc000014bca782e015949f849b2188f2c6dc30c15a093c3e218d09583300ca000014bc4852c714a89a047920e8ef46b82ed14b88d83b418309583280d6000014bbe442ea95cca184a02218fa071231915f89743fc1a60a003580e0000014bb8352d395149e048d2150f306d630d151090c3c217608d02d40bc000014bb2382ce95109b847820a0ee06a02f214708c83a617708b82f40ba000014bac1b2dd15349d44882170f006e030914f88ec3b617e09283100cc000014ba6082d715109c847f2120ef06b02ff14b88bc38a17008a82f80ce000014ba02c2bd94749704662070ee06aa2fc14e88e03b818308d82f80ca000014b9a072e39594a0449b2218fa06fa31915a894c3f619409a02fc0cc000014b93cf2eb15dca3c4aa21e8f2c6d630c15889443e819309503100ca000014b8dc52d415309da4922128f186d030f15489203c217909003040c2000014b87d42c494b49ae47c2090ec06a22ee14908d83bc17708982c80aa000014b81db2c2947c98a4602018eb06a02e914988c439a17408902fc0b8000014b7bbd2dc15589fe49821a8f506de312159095c3e219509803280d0000014b75b62d695549ea4a521f8f806f632015d89543f218e09283240ca000014b6fa82d8954c9e449321a8f686d4310155892c3d2188090831c0ce000014b69b12cb94dc9b64802128f246c430715009183d818d09603040ba000014b63892e395949ee49e2168f506f831b15d89503e419309b03540d4000014b5d8a2d115449f44982208f646ee31215989283d018209503300ce000014b574c2f1960ca4e4bb22a8fb472031e15d09603f618a09503000bc000014b513b2db153c9e248e21e0f6c6e830415208f83b617a09003240d8000014b4b422ca14ec9b847d20d8eec69e2fd14f08e43a417408902d00b4000014b456a2bf94c09964652020ea067e2e814408a83ae17808c83000c0000014b3f632d215209ce4832100f286d630815008fc3c017c08e02f00c6000014b39522d815109c448520b0ef46c630715489483da18909282e00b4000014b33732c2146c9724531f98e5067a2e013c887838816608682d40aa000014b2d652d515549ec4912158f546d22fc15209183ba18008e031c0cc000014b27672cd15109c448120c0eec6ba2f414688c83a617a09303240d2000014b215b2d214f09c24902188f7870031715889303d618509503180d6000014b1b4b2d314f49c64842150f086b22f814908cc3b417908982bc0b8000014b15382d515049b84772110f446dc30315189003ca18008882c40a8000014b0f052e615b8a2a4b02260fb871832e16589703cc17f08e82e40b0000014b08eb2d815449ea49521a0f606ec2ff14c89083be18309503180c8000014b02d42df15a0a1a4ab2270fb870a32715d89843f619809f03540ce000014afcdb2cc14f49ce48c2160f206b62ee144089838015a08382e80c6000014af6d52d4150c9b24782090ec06b830215389583ce18209002ec09a000014af09b2e815bca284a92210f9070432215c09743e2182091031c0b2000 else (if i < 209 then 0x14df1222b414289684531f90e4065a2da13f889438216008602d80ae000014deae72eb9600a444c6235901c74c34717389c04081a009b03300dc000014de4bf2e395809fe49b21b8f206d430b15789583f219d09c83380d8000014dde802ef15e0a304b62300ff074034216b89dc4321b40a503840e8000014dd8872cd150c9b847f2108f086d22ff153890c3bc17808d82c40b0000014dd2692de1564a084992210f88704329160898c3da19609b83280c6000014dcc752c714cc99645e1ff8eb46862e714688fc39c174090832c0cc000014dc65f2e015809f849921e0f4c6fa31815e89883f019609683300b4000014dc04c2d995509ee49521f8f586e430b15689203d218008f02ec0b6000014dba222e815dca084a52230f8070032215989283c618609682fc0b8000014db4122d715349dc49221b8f386e431615c09483f019509983340c0000014dade92e415b8a0e4b02240f9470e32815f09283d418c09382e80b0000014da7e52d9156c9d849621d0f646ea31115609183ce18e095030c0c6000014da1c22dd95789ea49a2188f206dc30c14d88fc3bc17c08a02f00c4000014d9bb82d414f89b647e2128f186b62fd14e08d83aa17809183100ca000014d958d2ea95e4a184b32270fac70e32115f098c3ee19209202e00ba000014d8f9b2cb14d09a246c20b8ef06a62ec143888839817708d03100c6000014d89632e915d0a344bb2278fa471832215e09843f81a30a083600d8000014d837a2c614c09b648220f8f046ac304153891c3cc18408e83200d4000014d7d642d495349d647e20d8ee46c22fb14e08f43b617808f02e00c2000014d77812bc145c9724571fd0e9c6a02f514a08d83bc18509182f00da000014d71a22ba947899246c2078eb46b02f415008dc39e17408c82fc0b8000014d6b862df15789f649921b0f486e230214f89243dc186096832c0d4000014d65412ee15e4a224ac2200f9870a31a15c89543e219009683300d4000014d5f542c695009be48020c8f046b42f615089183c618108f030c0ca000014d596e2cb94f09a447820a8ec06a42ed14a88f43ae17308902c00c4000014d536b2d795509ea48b2128ee46c630c15a09243c418409103000ba000014d4d652d215489d448d2160f446d830415188f83b618609303080c2000014d47552dc95a0a0449c2190f8c6ea31a15889303cc18d094030c0be000014d41272e815b0a0e4912150f306ce30d15689203b2180092831c0c0000014d3b052d995589ea4942178f546e031715c89683fa19009883340be000014d35002d714f89ae47c2128ef86be30215109043e419409603080ac000014d2eef2d695389f44ab2268f806f430d15489183cc18909a83440d6000014d28f12d495389e048a2118ef86c22fe15289003b217a08d82e00b2000014d22e42de95789ec4952168f086dc31a15909503f219609a83280d4000014d1cf72c914a099e46b2030eb06a42f214a88c83a417c09203280c4000014d16c42e495b8a104a02218f886f231115609283ca18909383200c2000014d109a2e1156c9d64832120f086c830615088fc3be17d09003180b8000014d0a972ce15149de4942198f446e2310155090c3cc18308f02f00ce000014d04812da15209c648320d8ed86a22ef14708b43a217d08c82ec0b6000014cfe572e795b09fe4a921f0f646de30515689003c618709203280d4000014cf84d2d114f49b44782108f146b62f8150091c3be17808702cc0ae000014cf2482d314c899c46f2050eb46962e8145089439816a08b82cc0b4000014cec3d2d314d89a846c2028e906882ec14a08d83b8182092831c0cc000014ce6302db951c9ca4802170f3c6c030015389403e419609a03200bc000014ce0172d995649e648e2168f546d830415309283d418309002dc0bc000014cd9f52dc1580a1c4a121f0f486fa31815b893c3e019509503100d0000014cd3f72c794ac9a04722070e946782e815189083b417608c83000d0000014cce0c2c694d899e47320b8edc6b830115009183d618909102ec0c8000014cc7ff2d8953c9f849a2258fbc70c31d164098c3fe19309a83500d4000014cc2052ce95349e848a2190f346ca2fa14908c43be17508e82e80c2000014cbbd42e995b8a124b92280f606ec31a158894c3cc18709983580da000014cb5e52c594e49b247b2078ecc6a82ef14808f03c618008c02dc0c2000014cafbf2e715bca0c4a32200f706ee31b15d09783fc19909b83640f2000014ca9ad2d815609f84a121e0f1c6cc30415609443e418f09382f80b8000014ca3ca2c2947498c4682040edc6962e1140889c38c17108682b40a8000014c9dbd2d0951c9bc47920a0ef06b42f1146088038e16c08982e00a6000014c97e02b693e494444a1fa0e8468a2e8141089c39a16b08682c40b4000014c91f92c2149499246c2038e946922f514d08fc3b417608b02b009c000014c8bda2e195889fa49121e0f586de30c15189103c818408e02ec0ba000014c85e92c394a099447620b0ed46ac2ed14e88e43b017208982e00b2000014c7fd32d615389cc47b20b8edc6ac2fa147089438a15408082b80c8000014c79812f29608a3c4c02300ff472a33016909b44061a209c833c0da000014c73a92bb146c99045c1f78e2c6562ce13e089839e16b08b02f40b8000 else 0x14f73b92da15049cc47f20f8eec6ac2f714e08f03d618f09903140ce000014f6da92db15209d64882100ee06b030615609203c618308f831c0ce000014f678c2db15609ea4962178f686f031515609283bc17e094031c0d4000014f619b2c814b49984662038e986922e914d88b03a817d09083080c8000014f5b9f2ce14dc9d048020f8ed86a62e414388a438a16908802e80bc000014f556c2e395909f84a72270f8c70632d167099c40419b09c83340de000014f4f5d2d495189d647b2090f046ba2fd15309103d218d095831c0c2000014f49442de15589f04a02230fb0716322163898040c1a109883440da000014f43282d715489e04942180f6870231f15989703de18d092031c0c4000014f3d1f2ce14e89d44942180f586ee31d15e89603fc19709b03540cc000014f372e2c994d09a04652028e8c69e2eb14488b43a417208d82ec0a6000014f30f12ef15f0a284ad21f8f7c6ec30215109243b217b08f03000b4000014f2b282b194149504501f40e446722e814588a83a618209302f40ac000014f25202d895449c848220d8eec6ac2f3146089838416d08a02cc0b0000014f1f1a2d7951c9bc48320d0f086c62f214b08d03ae16d08382ec0c6000014f18e22ee95d8a244af2230f5c6da31115489443d418509483380e0000014f130f2bc146097a4622048ea46a22f3145088839816608402d00ba000014f0d102d115109c247e20f0ef46c22ff14f88e43ac17a08a82e80b0000014f06a63019678a784ce238104075233416389744041a209f03500d6000014f00cc2bf949099046a2088eb469a2fa14e88e03ae179090831c0b8000014efaed2c214709704652048eac6802e514288a439817608d03100cc000014ef4fd2c714a09984631fe0ea46862e614288c43a617308c02cc0ae000014eeee52e195a0a0c4a12260f8c71e33116089943ee19609f83640e0000014ee8b82e815d0a364c022a0fa86f431815f095c40a19609583140bc000014ee2c02d195049d048320f8ef46d42ff15188ec3c618109283180c8000014edcdb2c494a498e4621fc8e9c6962e3145887c38e16b08b02d80b8000014ed6a32e415bc9f04962218f7470832d16089443cc18509783240c4000014ed0b52c4149c9984712098eb86982dd14408cc3b817808f03080c6000014eca682f395eca324ad2218f8c6f831a15e89583dc19609a03340c2000014ec4692d314dc9a64722050ec46c02fc14b88b83aa17808d03080c2000014ebe832c1949899446b2030ee06c62fd14e88d03bc17708f03040c8000014eb8852ce95009b646d2088ec46a42e714408bc3a817e09102e40b6000014eb2812d495109a84762080ed46a62f714c88c03ae17808c02ec0c2000014eac492e615b8a084a42258f8c70031315809603d619309c83440c8000014ea65f2c794d09ae47d2080e846802e714288903a217008702cc0a4000014ea0662c694909864752050eb46a02f114e88f03c418108c82f40ba000014e9a502d715309da48a2148f0c6c02fc14d08f03c018108c02d40b0000014e946c2c514a09a046e2068ed06a02f014308c83a217208c83000aa000014e8e532d5151c9de48a21a8f046d230e15989503f8193096031c0b4000014e884b2d1951c9d047d20f8f046c430715188ec3a217108682e00be000014e82342d795449ea4872138f0c6c62f914a88d43b017a09003040b8000014e7c252d715409c047e20c0eb46982f314788bc3ac17708e82e80ca000014e75f62e315849f04952188f2c6cc2f614a08ec3a618308c02f00c6000014e6fda2e115849f049f2220f606f231d16289603f019d09b833c0d6000014e69c52d915449ea49121c8f606ec30615188f03c4182093033c0e6000014e63b32db156c9fe4a22228f646e831015509203ba17608802d00a2000014e5dab2d995449de48f2118ef86a42f614888c439e16c08a82b80aa000014e57bb2c294d89ae47420a0ec46902ee14588d03b418409402f00d2000014e51e72c2149498045c2038e8c6822e814888cc3a416c08702b40b0000014e4bce2d595509fc49921c0f546e831115109203ce18809283040ac000014e45ad2dc95489da49521d0f5c6e831415789583ea19409683400d0000014e3f8f2e115a4a024a92210f8c6fc31215809483da195095832c0d8000014e398f2cf15109b047b20a8f186b42fc150091c3bc18409403180c0000014e33782d795489ce4872118ef06ca30915b89243dc18609203180be000014e2d5b2db95589e649421e8f446ce2fc14c08fc3c218109103200cc000014e27702c594e09d04812100eec6b02f214908cc3b417f09383140b0000014e21612d615209d04842160f7c70231c15b09483ec19809a83240c8000014e1b4f2db15589dc4862150f1c6be2f114808e83a816f08d83140d0000014e153d2db95489d848c2188f186d030f15509183d618909403180d6000014e0f112e915b4a0c49821a0f446c42fb14f89103be18009082e40bc000014e090c2d295189d84872108ef46a02ea14908b439816c08a02f80b0000014e031a2cf14e89a44712088ec06b42fe14d08f83ce18409803380d4000014dfd1f2cf14e09ae47520c8eec6aa2ea14a08d43ac17b08c82ec0c8000014df6f12e6957c9ee49c21b0f706ec31615b89403f618509382fc0d0000)) else (if i < 212 then (if i < 211 then 0x150f7522db95689e649221c8f4c6fa31a157893c3c818e095033c0cc0000150f15f2ca14d09a247c20d0f086bc2f714888d43b217608b02b80b00000150eb182f11600a304b02268f786f830e15b09643d618309303180c00000150e5042d615189cc4872130f3c6e431615a89183cc17d09003040bc0000150df2e2b8944096c45e1ff0e5c6742d3139084836e15c07d02a80b20000150d9292cf94ec9c24802108ef06bc304151892c3c018809603280c40000150d3422c614d09ae47720d8f006a42ee14688a037e16b08a02c00bc0000150cd2c2d995649f64a82218f586fa31915609083c8180093030c0dc0000150c7142dc956c9fa49b21f8f786fc32b15f8974406190092033c0c80000150c0f02e01590a104a521b0f546f831115209183c418009783480d60000150bb032ce14f49b847b2128ec46a82f914a08c03bc17f08f03100ca0000150b4ec2dc15449da48a2160f306e430a15989383ec19209f035c0d00000150aebb2e995b4a124a82260fd073232d16089b03fa19c09d83840ea0000150a8c02cf94e89b247720d8ef06a42ed14608e83ac16f08902d00b40000150a2be2d415309e24912180f306b82fc14c08f43c2187095833c0d000001509c7d2ee1620a304ac2278fac72a331164095c3ee19709b03240c4000015096702d395489d64882128ee46c830415509003d017708c82e00c0000015090622d615449e849421d8f3c6e430b15809503e618b09403240a200001508a7e2c214a49764692060ea869c2ef14588a839016708402d00ba0000150843b2f21608a344bd22e8fa4700314157893c3c217a08e83000aa00001507e282db955c9de49121e0f306f832915c09343ea19409603280ba000015078352c914c89a44702068edc6b22f514c09003ac17208702dc0c00000150720a2e0158c9fe4a421d0fa071232215d89703de18509483080b600001506beb2d89564a0249c21f0f486d830915789343c218508f82e40ce000015065e62d815649f24942168f346c02fa14e88e43a617c09002f40be00001505fe12d395089ac4772098ea06942ef14a08cc3bc17e08e82cc0ac000015059d62d395349e648c21a0f5870231515b891c3d818208b82d80b2000015053ac2e495b89f44942170f3c6ec30f156092c3de19409583300be00001504d872e215689c64862128f206d631a15f09b040819c09a831c0c20000150477c2d815549de49e2200f8c6f231c15889603ec18d08e83000c4000015041822d215049b247620d0ef86bc30514f09043c618309482ec0a200001503ba02c414a098e46d2080e8c67e2e914388bc39e16b08882e80c6000015035b82c914bc9b646a2058ed46a62ec14908c83ba17908782cc0ba00001502fa82d795589f64982198f546fc32015d896c3e819409483380d0000015029912dd1568a004a021a8f2c6d830e15289403e018709102e40b4000015023712e315889fa49d2210f586dc30f15389083d218809683340da00001501d502e395a0a1849d21e8f6c6ec32116009583d4188092830c0c0000015017282e215b0a004922190f186c82fe14c89143b817f08e82f80ba000015011252cf14f89b848020f0f206d430c15689443d218d096032c0bc00001500b0c2de956c9ee49e21e0f8c71432015e09303d619509583100b8000015004ed2df9574a144a121c0f646da30915108f83c218309083000c4000014ffecb2da1564a144ad21c8f546e431615b09303da18d09703040c6000014ff8cc2cf94f89c44752090eb46ae2ed14988d43ae17f09002f80b4000014ff2c82cd14dc9a446e2070ea46a02f114c08d43a417208c83040b8000014fecc02d295049ce4802130f306d230a15109183c817a09002e40c6000014fe6b02dd95609ee48f2138efc6c630515209203c617b08f02f80c0000014fe0a92d715309da48120f8f1c6ce30215188e83c618509483200de000014fdaa52d2152c9e048d2130ee86c82ff14688f43c817608983080cc000014fd49d2d015289ce48620c0ee06b22f114908d83ae17108d02e80b8000014fce5d2ef9600a324ad2228f80704323158891c3be18309702f80ca000014fc84f2d795049b84742040eb06a42f714788b437e16008682d80be000014fc2642c994c09904672090ef06d231115a09683d018709483180be000014fbc672ce94e49c64802110ee86a42f114408b038e16c08982e80ba000014fb66c2ca94e89a047a20b8ee46a02f814c08ec3ba183093832c0d2000014fb07a2cd94e899846b2080ebc6ac2ed14b88d439817408f82fc0b4000014faa6a2dc95609fa48d2170f206be30b15389583e418908f82dc0aa000014fa46d2d194e49ac46e20a0ef86bc2f314888d839416c08682d00aa000014f9e382ea95c0a084ab21e0f5c6f231d15a89683dc18a09403280b6000014f98482d1950c9b447f20b8eec6b42ff146888c38216b08582ac0aa000014f92242df15549e44932210f646fe32015d098c40018b09002f80c6000014f8bf72e71598a0849f21f8f486ce30f153892c3e018809103200ce000014f85ef2d895549d648f21c0f686d830d15689483dc18c09182f80bc000014f7fd92dc15789fe4942170f6470032215b89583de18e09503040ba000014f79d12d895149da4842120f346d630614f091c3dc18109202fc0b4000 else 0x1527a742c995089ba4882130f246be2fc147089c38816a08402d40b0000015274532dd15549ca48d2130f246c830c15809543d217d08b83140c400001526e3e2d495489ee49b21c0f586e030915088f83a617c09003100cc000015268172e1156c9e04942148f306d830c15289043ba17c08c030c0cc000015262182cb94c89a647620a8ec86c630414d08ec3c8185095030c0ac00001525be12e795c0a204a32248fc072232816089643ee19609c83500ce000015255d32d415409da4912168f106d430e15489143cc18309503140be00001524fd92d094e89b847c20f0ee46a62f814888b43a017008c83080c4000015249bc2d995389e44932178f606d630a152891c3c017c08882d00c2000015243a02d815509dc4892130f246ca30114808dc39617109083100c800001523d932d295049ba47c2080ea86982eb14e890c3ca18109583380de000015237b32c1948098246f20a0ed46aa2f114c88c43b218509282e80b2000015231af2cb94ec9b24752030eac69e2f615009383da18409003100ac00001522b882e615b0a204a321a8f2c6d230b14f89083d018d097032c0c20000152255d2e315649fe4a221d8f646ec321160099440819809d83600d600001521f652c714ec9d24872128f146c630114d89203da18a09003000c8000015219582d995349c64862138f046c230915509503ee18a09303080c2000015213572cd14dc9b448020e8f1c6be2f914e08f83b817c08d82f00ca00001520d4d2d695389d848a21a8f506d630515008d03ac17908902f80b8000015207012f39624a4a4c922e8fe471c32a166098440a1a50a203640ca000015201122c714d49b24712070ecc6a02f814988c039816908202940b80000151fb0a2ce94f49d44832188f386d030915208f43ca18209383180be0000151f5092d195109c247d20f0f386ca2ff14b08d43b217e09583280cc0000151ef112ca14e49a447620e0efc69c2ef14c08d03c218309403300d00000151e90f2d395289d248c2130f406c82fa14d09043d218009283200b60000151e3062d395149cc4782110f446f631715b895c3e819409703280c20000151dcb62f81644a5a4b72300ff473432d167899040a19a09d03280ca0000151d6d02cb14dc98e4642038e986b22fd14f08fc3a016908602dc0c20000151d0d52c614b899a46a2088ed06ca30514808f83c818309203240c60000151cacc2d114fc9ca47f2148f3c6ec31b15689183c618008f03380ce0000151c4c82d595449d448a2128f346cc30715609183d419709703580d20000151bebe2d8153c9d04882100edc6c230215408fc3ae18508f02fc0c20000151b89f2e01594a0a4b02230f6c6e830b15189243dc18509803100c80000151b2872dd153c9ca48a2120f346ce30d15889683e618b09683240c20000151ac912cb14b09ae4702040e8066a2d114088b839816e08682c80b20000151a6932cd95089ce48c2158f046da30f15409243d418c09503280ca0000151a07e2d9952c9d04852168f306c830715589343d219009803300d400001519a812ce94e09a64722058ea06802e1144089839417408702b009e0000151948d2ca94bc99e46d20b0efc6d830515609003b818109082f00b800001518ea42c614c49ae47120c8ec46ae2fb14788dc3a817708682e80b6000015188b82c814a499e4672020eb86962e814508c039616908602d80ca000015182a42dc153c9e44942150f206d830c15608e03a616d08a03180cc00001517c952d8951c9b84822108f046a02f114f091c3c018209002e009c0000151767f2d815449ee4962188f186bc30415889603da18809102fc0bc000015170492e2957c9e249921d0f586f032415f09643e618e096030c0ae00001516a492ce14bc9b247c20f0ee06c430215188f83c018d09b032c0cc000015164232e395aca0048d2168efc6c22fe14f89203d817f09002f40c400001515e0f2d2150c9c048d2190f246d4311153892c3e618609183140d0000015158092d014fc9d047720c0ed06ba30015209303c818909202f80b6000015152012d194d49c64842130ee06962ee14488bc39c16a08e02f00ca00001514c082ce95149da47f2110f106c830715489143c817e08e03140ce000015145d02ef95eca2a4a72268fac71a330160898040419c09e03400ca00001513fc02d715309dc4822148f1c6b230215288e83b617e08b82e40ba000015139872ea95cca124ad2268f6c6fc31915c09583d817f09002ec0be000015133892d315489ee49a2198f3c6d831715788f43ce17e09082f80c600001512d642df95849f849421d0f606f4326163896c3e418f092831c0ac0000151277e2c294709824621fd8e7c6862e114408a83a417b08c02dc0ae000015121882cd14d49a84802120ef46b22f314c88c43be18008e02d40be00001511b682dd15509de49821b8f486de311154892c3cc18009182f80ba000015115472dd15689dc48b2188f506de30215089043d217e08b83000c400001510f5b2c914b899c46a2098ed06ae2ff14e88f03d018c09803380ce000015109632d1951c9c24852118f086b22fc14e88f03a417308b02fc0a60000151035a2d714ec9c448020a0ef86c030114f89103e219209c83200c80000150fd702c694ac99c4682080ea46902ec14808e43a616c08d02d00bc000) else (if i < 213 then 0x153fd072cf95109be4882198f586e230e156091c3c417708d83000ca0000153f70d2d094e09c24802148f146de30d14f89083bc17808c02d80d60000153f0e82e795a8a004a521a0f346ee31616189843f219509083080c00000153eadd2d695489dc48a2170f306d830d15188e83c217b08f82f40c40000153e4bf2dd95389d247a2080ec46942f114e08fc3ba18909883240b20000153decb2c714b099447520e8ed06a82f414808ec3b617608682940b20000153d8d42cd14e09a247b20c8ecc6c62fb15089083d618a09802fc0a60000153d2d22d595309c847e2120ef86ac2fa14d89003c819509703540e40000153cc992ec15b0a0249821e8f786ec30915189203b617a08b02c80aa0000153c6942d715089a646f2058eb869c2ed14a88c43ac16f08a82ec0b60000153c08e2ce94f89ca47b20c0ec86982e113d087c38816408982dc0c80000153bab32bc945496a4511fd0e686802df140089439c16b08302cc0b60000153b4932e39590a064a22210f906fe31d15509343e018c09303040c40000153ae9e2ce95289d64812120f206e8312157891c3c417f09202e40aa0000153a8992d4951c9c84892180f706fc32a16309743f619209383140ca0000153a2882da95789fe49e2218f386e831a15b89583e818909383040b800001539c782da95449de4972158f246c42fd14a08c83aa16b08702d80be0000153967b2d315449e449a21b0f5c6dc30e15409183e0193099030c0b80000153908e2c694ec9a246e20a8f006cc30815189043ba17b08f82e80b400001538a452f21624a4a4b02278f9470c32616209743ee197096830c0c4000015383e72fb9648a6c4cd2328fe872e33216509d04181ab0a3035c0ee00001537de92d5152c9d04802118ee46a22f314e89003be187097030c0c6000015377fd2c394d09a647720b8eb86982e214788e03ac17608e02dc0be0000153720f2c894dc9a24712030ec86a8304153090c3c418509102f00b200001536c1a2c794dc9a446d20b0eec6ba2fe14f08c43ac17308c02e40ba000015365f32e29598a084a721c8f606dc30315189043ca184094830c0c8000015360142c0148897c4581fd0e5067e2e514408a43aa17608e031c0c800001535a262c5949c9b047b2160f006d430314e08cc39e16e08a82f40c00000153540d2d995409f64a32208f7871832416089783e218609103040b200001534e0b2d315189c247320a0ec86c42fb14a88f83bc17b08802d00a40000153482a2c314a89a846e20b0edc6b02f714c88e83b618609382f40c2000015342272ce14dc9b84742030e9c6962f414708d83a817208e82e00ba00001533c312ca14e09ba47e20a8ef06b02fe14d08b03a017208c03140bc0000153362d2d1150c9dc4992168f306d230c15609183cc18e09602f80c800001532ff32eb156c9fc49c21e0f5c6d230614f89103cc18b093831c0c0000015329de2d895149d44902190f586ec31215f89683e818c09503000b6000015323f22c894d89ae47e20f8efc6ce30b15909483da18f09803300da00001531df12ce14e89b047e20a0f006cc2fe14c88cc3ae17308c82ec0ca000015317ca2e01590a1e4a721b8f646f231b15389243c018208f02e40ae000015311b62dc154c9d84812108f186c830a15208f03b217f093833c0da00001530bd12c4948c9824652038e7c6782d913c887c37a15908202b80ae000015305bc2df15789ee48c2180f286c430815109083c017708d02f00b60000152ffb62d1950c9ba47e20b8efc6a42f214888f03be17008782b80b60000152f9782eb95e8a3e4bf22f0fb8718331165099040819c099833c0d20000152f37a2cf14e09b848020f8f046ca300153091c3ce19009583000de0000152ed782d215149ca4832150f0c6c830115289083c818009702d00ba0000152e7592e0954c9de49c21d8f846f431215c89303e418409203040c60000152e1532d495149ca4872158f486d62f514f08f03d2191098033c0cc0000152db382e315a0a064aa2288f9870832315b09643f219709783080c00000152d5142e795b0a1e4a12230f806f231f15f095c3d218309283040b20000152cf0b2d595109be4742098ee86ac30315109303e418f09202f00be0000152c8e32e595c8a1e4ad2250f9c70831c15989343d618809583200be0000152c2f22c694b098245f1fe0e886802da13c087436c15607b82900a20000152bced2d114fc9c448920f8ef46c02f515689243d619209483000be0000152b6cf2e215409ce48620e8ef06c42fb14f88f83c418508f03100d00000152b0b52de958c9ee48c2150f3c6d031215c09543e018e09e03540ce0000152aab12d415189da49721a8f346ac2ff15088f03b418009202f40bc0000152a4b02cf94ec9ca4822100f106c82f714b88ec3aa16e08602e00b000001529ead2d695249ce48d2130f286dc30815388f43b617b09203140d0000015298b62ce95009cc4902198f3c6ba2f714e08ec3aa17808c02fc0c2000015292b32cd950c9c448720c8ea06822e814788c03b017808c02f80b000001528c5b2fd9648a404be22d0fe472632916709b041a1ac09d83500c6000015286442da154c9d24812108f286d630915709383ec18c09203080ce000015280602c294b49bc47e20e0f106cc30114c08e03b817a08a82c009a000 else 0x154edf52c5949c9944672088eb46a02f214788ec3c618708b82f40be0000154e80a2c294a49b447320c0edc6a82f315109043ba16f08882d40b60000154e1fe2da157c9ea4912190f006c831115d893c3e819809983400e00000154dc3d2b7145496e4571fc0e4866a2d8142087c37016808782cc0b00000154d6442c794a899c46f2088eec6a62ee14988d43b817608c82f00c20000154d0422d314f89aa47720b0ed069c2e914508a039816708382bc0aa0000154ca0b2ea95b0a0049f2210f6c6ee31515609043f218d096033c0cc0000154c3df2e315709fa4a021d0f6c6f031a15e89743f018f09303080d60000154bdd32d515389e049a2178f146d030d154893c3f018b09b03200c40000154b7dd2c794dc99c46d20c8ecc6b62fe15008cc3b817c093831c0d20000154b1c42dd95549f44932198f3c6e430715209243e218609783180ba0000154abb52d695149cc4882110f206c82f7152090c3ac17e08f03300be0000154a5952e015749f249521b8f186ca308151090c3b817b09003080c800001549f8d2d895449e649321a0f286ca304151891c3c818409083140ba0000154999a2c514b49ac47e20c8f186e430f14f08cc3a417208f030c0b4000015493a22cb94f89b847620b0edc6c630114e89183bc18208f02e80b800001548d822e015709ee49821b8f6470631815a89503da18f09883300ba000015487ab2bb947096844d1fa8e8c6842df141888839216907e82c009e000015481752e915cca144a72258f9470c31a15e094c3f219109583180be00001547b6a2d6954c9dc4872158f006b030115709403f619f09c03340bc000015475722ce94e49984611ff8ea869a2e814588b43ae18c09503240cc00001546f752cd14c899246e2088ed86b02f914b88c83a217008782fc0b8000015469772cc14d89ca4832138f0c6b62fc14e88e83ac17f09283040cc0000154636f2d395089ce48d21b0f506de30d157091c3c418a09483180c800001545d6d2cc94b097846e20a0ef86cc306158892c3d417c08d82fc0b00000154575b2da152c9d44912160f246c630214b88d03ac17d09182ec0c6000015451412e21578a0c4a42228f786e6311159093c3e219109583300dc00001544b3e2d595189e449321c8f406d830614f08e03c018d09483180b8000015445372d995409fa4a12240f8871231c16009643e618609003100c400001543f4b2c594c09aa47820b8ec46ae2ec14408c83b217b08f82e80ae0000154394c2d095109d247e20b0edc6be2fa14908c03b418008e83100ba000015433602c514b898c45b1ff8e7867a2e314688e439e17808d03040c600001542d4c2d215549ee4992188f546dc31315789203d218809403200c8000015427352d715349da49821c0f6c70231f15c89583ea19209682e80ae000015421342cf14cc9ac4732088ef46ca307157093c3e618909583480cc00001541b462c094ac9a64822150f586dc30f15608ec3c017808c82f00b4000015415262dc95489d248120d0ef86ae2f814b88f43c218009203240be00001540f452c294609744642048eb868a2ee14708b03a216b08a82f40c20000154092e2de956c9c84842160f386dc31415e898840219209503000c2000015403052e4156c9f849d2220f786e6319157093c3ce18509483340ca000))))))))

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



private theorem b205719 : covered 205719 205826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205826 : covered 205826 205933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205933 : covered 205933 206039 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206039 : covered 206039 206146 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206146 : covered 206146 206253 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206253 : covered 206253 206360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206360 : covered 206360 206467 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206467 : covered 206467 206574 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206574 : covered 206574 206681 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206681 : covered 206681 206788 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206788 : covered 206788 206894 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b206894 : covered 206894 207001 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207001 : covered 207001 207108 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207108 : covered 207108 207215 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207215 : covered 207215 207321 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207321 : covered 207321 207428 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207428 : covered 207428 207535 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207535 : covered 207535 207642 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207642 : covered 207642 207748 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207748 : covered 207748 207855 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207855 : covered 207855 207962 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b207962 : covered 207962 208069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208069 : covered 208069 208176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208176 : covered 208176 208283 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208283 : covered 208283 208390 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208390 : covered 208390 208497 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208497 : covered 208497 208603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208603 : covered 208603 208710 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208710 : covered 208710 208817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208817 : covered 208817 208924 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b208924 : covered 208924 209030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209030 : covered 209030 209137 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209137 : covered 209137 209244 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209244 : covered 209244 209351 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209351 : covered 209351 209457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209457 : covered 209457 209564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209564 : covered 209564 209671 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209671 : covered 209671 209778 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209778 : covered 209778 209885 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209885 : covered 209885 209992 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b209992 : covered 209992 210099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210099 : covered 210099 210206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210206 : covered 210206 210312 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210312 : covered 210312 210419 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210419 : covered 210419 210526 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210526 : covered 210526 210633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210633 : covered 210633 210739 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210739 : covered 210739 210846 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210846 : covered 210846 210953 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b210953 : covered 210953 211060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211060 : covered 211060 211166 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211166 : covered 211166 211273 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211273 : covered 211273 211380 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211380 : covered 211380 211487 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211487 : covered 211487 211594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211594 : covered 211594 211701 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211701 : covered 211701 211808 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211808 : covered 211808 211915 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211915 : covered 211915 212021 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212021 : covered 212021 212128 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212128 : covered 212128 212235 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212235 : covered 212235 212342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212342 : covered 212342 212448 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212448 : covered 212448 212555 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212555 : covered 212555 212662 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212662 : covered 212662 212769 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212769 : covered 212769 212875 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212875 : covered 212875 212982 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b212982 : covered 212982 213089 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213089 : covered 213089 213196 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213196 : covered 213196 213303 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213303 : covered 213303 213410 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213410 : covered 213410 213517 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213517 : covered 213517 213624 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213624 : covered 213624 213730 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213730 : covered 213730 213837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213837 : covered 213837 213944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b213944 : covered 213944 214051 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214051 : covered 214051 214157 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214157 : covered 214157 214264 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214264 : covered 214264 214371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214371 : covered 214371 214478 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214478 : covered 214478 214584 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214584 : covered 214584 214691 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214691 : covered 214691 214798 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214798 : covered 214798 214905 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b214905 : covered 214905 215012 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215012 : covered 215012 215119 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215119 : covered 215119 215226 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215226 : covered 215226 215333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215333 : covered 215333 215439 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215439 : covered 215439 215546 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215546 : covered 215546 215653 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215653 : covered 215653 215760 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215760 : covered 215760 215866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215866 : covered 215866 215973 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b215973 : covered 215973 216080 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216080 : covered 216080 216187 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216187 : covered 216187 216293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216293 : covered 216293 216400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216400 : covered 216400 216507 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216507 : covered 216507 216614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216614 : covered 216614 216721 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216721 : covered 216721 216828 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216828 : covered 216828 216935 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b216935 : covered 216935 217042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217042 : covered 217042 217148 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217148 : covered 217148 217255 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217255 : covered 217255 217362 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217362 : covered 217362 217469 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217469 : covered 217469 217575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217575 : covered 217575 217682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217682 : covered 217682 217789 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217789 : covered 217789 217896 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b217896 : covered 217896 218002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218002 : covered 218002 218109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218109 : covered 218109 218216 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218216 : covered 218216 218323 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218323 : covered 218323 218430 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218430 : covered 218430 218537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218537 : covered 218537 218644 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b218644 : covered 218644 218751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 205719 218751 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b205719 (joinCoverage b205826 b205933)) (joinCoverage (joinCoverage b206039 b206146) (joinCoverage b206253 b206360))) (joinCoverage (joinCoverage (joinCoverage b206467 b206574) (joinCoverage b206681 b206788)) (joinCoverage (joinCoverage b206894 b207001) (joinCoverage b207108 b207215)))) (joinCoverage (joinCoverage (joinCoverage b207321 (joinCoverage b207428 b207535)) (joinCoverage (joinCoverage b207642 b207748) (joinCoverage b207855 b207962))) (joinCoverage (joinCoverage (joinCoverage b208069 b208176) (joinCoverage b208283 b208390)) (joinCoverage (joinCoverage b208497 b208603) (joinCoverage b208710 b208817))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b208924 (joinCoverage b209030 b209137)) (joinCoverage (joinCoverage b209244 b209351) (joinCoverage b209457 b209564))) (joinCoverage (joinCoverage (joinCoverage b209671 b209778) (joinCoverage b209885 b209992)) (joinCoverage (joinCoverage b210099 b210206) (joinCoverage b210312 b210419)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b210526 b210633) (joinCoverage b210739 b210846)) (joinCoverage (joinCoverage b210953 b211060) (joinCoverage b211166 b211273))) (joinCoverage (joinCoverage (joinCoverage b211380 b211487) (joinCoverage b211594 b211701)) (joinCoverage (joinCoverage b211808 b211915) (joinCoverage b212021 b212128)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b212235 (joinCoverage b212342 b212448)) (joinCoverage (joinCoverage b212555 b212662) (joinCoverage b212769 b212875))) (joinCoverage (joinCoverage (joinCoverage b212982 b213089) (joinCoverage b213196 b213303)) (joinCoverage (joinCoverage b213410 b213517) (joinCoverage b213624 b213730)))) (joinCoverage (joinCoverage (joinCoverage b213837 (joinCoverage b213944 b214051)) (joinCoverage (joinCoverage b214157 b214264) (joinCoverage b214371 b214478))) (joinCoverage (joinCoverage (joinCoverage b214584 b214691) (joinCoverage b214798 b214905)) (joinCoverage (joinCoverage b215012 b215119) (joinCoverage b215226 b215333))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b215439 (joinCoverage b215546 b215653)) (joinCoverage (joinCoverage b215760 b215866) (joinCoverage b215973 b216080))) (joinCoverage (joinCoverage (joinCoverage b216187 b216293) (joinCoverage b216400 b216507)) (joinCoverage (joinCoverage b216614 b216721) (joinCoverage b216828 b216935)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b217042 b217148) (joinCoverage b217255 b217362)) (joinCoverage (joinCoverage b217469 b217575) (joinCoverage b217682 b217789))) (joinCoverage (joinCoverage (joinCoverage b217896 b218002) (joinCoverage b218109 b218216)) (joinCoverage (joinCoverage b218323 b218430) (joinCoverage b218537 b218644)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 205719 ≤ index 395000000/512 := by decide +kernel
private theorem starting_value : fast 395000000=21083785 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 395000000=21083785) (n : ℕ) (low : 395000000≤n) (bound : n≤420000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=395000000
    · rw [first,anchor]
      exact starting_value
    · have past : 395000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤420000000 by omega)
        have within : index n / 512 < 218751 := by omega
        have lower : index 395000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤420000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ395000000To420000000
