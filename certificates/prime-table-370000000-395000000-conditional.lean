import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ370000000To395000000

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




private def radical : ℕ := 0x2108cccc02d83328543db72f4df713cbafb67eedd1996df3b9c2ef96df97f820c75489e4287ef1b3a43ebeba138afed3913079af801c3a9be5d170e4ab2728be028354ef6ef12a95a476d4fa3f7360c35d97adae31cc08f0980a19432f9b0376707ddc5cb41734db8734b714d33c2735e733c4bb3df25173e6043b1489476596485d148b45252e9c4ca5d1f7f74fa4b33132c0c2c09811bfc991bf6049b57ca6210b0d0bd89cbb4b5a9cb5279f58a9bced2d3df611cf21e9978ab8c63dc6883b5dbb208fac7f13febc12d80513aefa665df5456595e984a622243823fa46b94ce67bd8c2f0d3b710fa9b670643fbc88cee585346d3d65cdab6f0db0cf5a25cf750d41dd91943108cfbe9739faabe7ff40df56bbc3651b9e4e4fe042161672990ec3c5d718df8f0cbf29fc8112d64ed35e3e0658f12d0410614d20389b1aae7373302ee41ee15b02091e83e21d6857a6b895fb405f8cf019da9273f820bfaf9beaacb04bcbe826ece30779775aaa67dc2be03cec5b5ede1c02137392d18617ce88ed10bb6a07da74b7b168fa30e0670fd18154f58845dd0eec6c152d05f6152ed2e9c5ef5c08a995e418376c429a31d817fc7763170979b8df4598f1ebe35d5e0d60cc8e8e1b038a02d830594aeb84a85cce0d698fabe8ce0639dd956ebd7122f8996f900fba41f2f02aec4be4e57c6fb487c0057c925b4c45e8719457870feb08807eca358a1b003ec0c1dc1051c939209c51b1fca8f61f7f4788f571bb37b8a5f28863757a487a39ccce8b48eb9cfdd508c9412c6ce23d1461456d84ff652a927e4265949544096940b1d22ec34550593ada0a9b10cb1e5c5414fcab2e4553cee9a891990a1577fa7b697c591ca3f84923d0a50c732c882ce01d99621c84e04fa28071557c87c7966118798292e8b353bf427b71a2707d1135443f74587cddd761ec030a61c8e262f2f480e894c34505dcd74351b454d03428d134d19c99ded65bed21ac2a6766e3dafb8b112918fed474ae199cd4db0812012773fdb8f292ac778f768fa2754157922cad72be3f2d11ff377264ae12d7e260bc6e4748b03e45f6e05550ed60461db3ffb30705a30574b251a54455cf9a66e4df9cc029e08ece02f3e1b69bea484d99d72e71387a262870f6c216d9e20608acb3506c47915f7744f4f626cdbfe69d47e4f6392620a57336cd5fc67047db2f74c0295b5f9ef58b2901d3465162ec9689de3cb70030c87af806caf5b44824b0a620b81376df80aa8ba2623fbac0d824737928c1d35c6bc452c2c142fc41282485f0d83be71626c7d4e857e3849c0545b9e076a86862e2b14420d4a4530740d62a417f4cec0ddae716759f25e35d4967ad7d5d8c8fc2d2299a438e082b702e3a5e8817b0689f095a6f2eef17440f5c54f0bc389fcb3309c133d841560f801909524dd94b01a2d5d3b70ae292dc15a5e834689feaebdea382584ae103a1f60d7eebf78c556a4ab862aba266bb2c56de59ec05df16bec156ba7f4d107cc5d15075125230fff47e1001f8470146da63266ecbe911ce962c29c3b6ed10d54aa540a89d9864adbe94f546bb82f98fef296d2dcbed5b49bfa12a936d8821868bc11dc17b5540962db62a64d2732ca03a80d4fe999375f27596fe60c314f4e9d207632e2f5c221c30a1c22f6975566cea0fd733c6aa336ebf8da805411d51a4efcd3477364c2caddcc88a06b44302710aefbe479041aa027f41b908d9f5bc15cb9af947464ba9e2af42152adba6eed37809c9afe1d1718aa77af3732b8d7df4cbf66ea17d1b9dfb9f4f27a8ef6d060af95dbdf6834895812449f8b4669c0273499db01c2e878957db59b8f06c3fee0e36dd4d5f1653fcc03f80a1d2cfcf6fa9aa12761ca2d7977aeb282646d591b720d6d4992fd7625bb7d70432ad90971293c21f1744382711469d71ccd37c611f33cfb08be2f6aa7fa8727b41273ec0fdac6ddeeeb0a24be732d1ac2f7558b87ded8c32b4791eda5ae61efc438c17b10216ac18cde576fdcc6a391fd2dc92f789593548829c9cc8fe74024e5780b3eb62a61577c551d2b5e76086b2f8f7e87143f906a0f048865372ffc2f130b8dea21fc24305f7e8c49cd149c146917bf3f8ee5778a81179d9a8b89133828452f4192e7565896634a0bdbd882759fa5818896a97f90fd7f4313927f39a868f2913c61008439e262d23080f73e0820aeb0efcda91531d96dea1dc4e000153aaa64f1a365c5e147e0dbf85fb1972af02fd4170b5fd03036ea582625ab9bcd243908d0ffb0ab09172b1f1eb70c68259d1d247fcd6302b6f72017feee235cf207d2944e7105ad8dc1e1287c9971917488a9fed3d412c1c71ad252fb37729f527f617ab4057bdb5b9f7d713c3508afd2a875f5949fcdb7fd00e2cd816428a9b307832125cfbea3da31b9dbc50701d2397d842a96f5169eab3dfc31183270462cfe45a326e820096e02cd7c88768d84d2680ab0f7167b8618a4f0664dd9d2ef359650a8e63f9168cb486f29998ddf213272fda5023012cae7c130e1077f47f22b90fa155f91eeac59524412e52817d9648a51390f2297944e3e4b408c98e8ace38c6aec2cf4ce720c4c83797716e957d8af6ff0869e9347f955047ea89e28a640660bfb9856a2954864073af0d32cb4d087509c67cd7e0742021d57eb3c1ed87fcca56fafd3e293165cca295822d6c091aed5e41697b2dbebb6c2020e473a26a7bee5434832c24ba1fb338a89abf4f343c46e2737ffa5152cd1243b381c7ac778571540df910190b76bea0322b5cd378ff8e185845d21a75c7944d1164d21bad2c01d38fa0fd7f46f04e3460539837577ae0fc210220e5ce84a2af1194804c349ca33a412e7e2acc8b28c5c41a2d211520d5d5d4003b1995e66f4ea6c5bf8e723c0d9116b3241263a2dbe1b3cf8d3de00a65704ef93ab07ea1f7d97797cc27c4e95b34778c2c18155d7ee350de37a0b16fad4da32672e72105cf283f4cc5b445ff27a6b9ebf64fe22fcc167932a368e57e232236c34012f2f3ab0861bc8668eabfe3f8b3e3a9b2edf0a1bce0ca610844eb8c9f4b0a5f76fc797ed0d15093c19e3254dc1431fef4700b5fec74699cdd4db811495017987bd3733fb1c92fe561f4238000a693b6c660f2786cd6524d0eb8e811008449bf844dcf08333c791a2b8b7d5bc03d3aa9f60cb8645efc32155accd3230b50d33c4227e7f9f4f744e322d2f3117a8a0966a956bcf194c647047def393104ea3b20255932b0e2c3145caa7d8b26c1efeb1661d6b7a7659cc57faf62d89c23e910fa9ac73265a3843c73fcc750e6f643c984afc31d9c63f7afb5630db0b3acfa351dd83cdf6000c6ccfe10729104a004b65e703ead10b47c6a4899e7bdc64cefdcfa07931f5e08252c9ad3bf6a58a8e015d7c5ccb74cd85db7359f7cb87f443ff034f66a8bdd6cb08bc842d7580d4132aaba0f2274fb6894d2ee5e1b20454c09433c10df89d718b9a63e3939dbdd2c36145b794c56e9a6c5537c1f424636efcf50bec57c48c0fdf69ab9d69ca7686df6243ce4782dfe417267fe2d864c9c630fd4a3f75b58742ce956ebcf2c0c86754523943081505360e7308e67f254b460b40a5f3ffde3f34b9eb554a155f6a059200701aeccd01043d06ab35580a852f6e5fc998995b4f3bbb3507f91bfcfbd324067b9dcc5cd1c285547ae97a4478ea6125049d101bb3f0562aa171d035a852cb1f623f30f96b3d25625376571b9a49b6937ee6afe65194461c4c2f060aa74f89d753e45178b6231edc967be5d074392e8e9aa9d60046a9bdefbcc2b0d0623f3cbb4a3bafde21e3833c46fda3671ea6c2f3027f930657d6e1cefaabbe7c8efbd6d9f04898066ebf92d2a64b95b80af322557b94befb5a3e31bcb59918ed7d96622d8d95f30f488aed9b04f67798001bba62377e036c7d824275439783ffc9ddc8f29ea6f5c187508532fefe09ba653757144fb219661f92a3af48e07533c3e1ce61afc0b3d5563e3b17e5569e2c276b2e9f671b60c1f8e8232f8e574c4d7c24c37ba98d5e5c4629f9c2f4221e08160a2ab675fc4c00e8ae03e1d7ce8b4b9c7db794b652088a585128d7a98282ed87eb7e83e899a5fc7bddaac12c33c3f9d1419e5c2857209dcac38670c4cc9831e523060c53c68daf7f1123dd41d6d6522123d8e8f8ed2579be2c990cc7b49379e10a1008a3cee7345572cec37d6df0b91d371a768232390450d225d0f4bf84c85094b79643ed18f91a332fd2ce970f2995f96c27656d3ea90f623c2d3c4ebb67bd9208c11af162ba2ab45e2cc284f6e23f0562bcd09feb3d76e5b8bd360a51b7f6378e0ead2c680e0eb9764d53177996e2ee1436dfd5e87beee5ac719023a3f45c41a09fde005d40ce0462f5b67c1958a3834f7a4ea7a3ff7cbacd0e1be243894b92ec9a23a7e8f75bb07de423e8fbd866b412e5e1fbe9c5a9337890d675b71820c73a12278efeb7918a23e3e946dd3a94624cbd87a2a859625867cb440e6b9e09f532482dc30ade23de9cbe0ab31ce6c15e3b0189177f0692e6a3009aa71e572f4329f3d9f20c51e5ad4bd487db9c20180b076954bef0c9c1931c4ced0f669d938ba9cf8a0e884bd3f167d45541072e39903e9c4a4ad226405a244fd837393ce1ed3ac26a8b320236ee272436b7a4f9b299f5c1be3ad116cd9a5d099e1965ad1c20337eef748226a60fdb090368c99b29ddd3d91a5ca2af7c34f9356fb597541e755abfad9f56c0d1f614ffab03ec515a6f5b523913150ca22df39226d1ec359c05ac5687a979f587a1d749acb136df63a69a87f84ae3d6f9e81947a545b3b7b67d912fd820baba492be6b3223ffb9ad210450c34487bbcc253d55a6b6b0fd4ae2cd092816857b4ea8af0edcaa01513ff77086de7c5543cc99a6160bb03b7576570c27dc908c921302145485dca7fea319accb493280a9a1b1990a6bb3cf16d1164db9ff3779f0ed27835e24b1230a43c49d271850fe24d51e1ce12e2

private def light (n : ℕ) : Bool :=
  if n≤140 then decide n.Prime else n.gcd 13462012475717524605876073858941615558355851148193967190051391468057460367090535696797920946629681836680869097041958983702264048370902871114013579941370766400374327741701139895604871545254810788060989321379840000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤19874) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 140 = 13462012475717524605876073858941615558355851148193967190051391468057460367090535696797920946629681836680869097041958983702264048370902871114013579941370766400374327741701139895604871545254810788060989321379840000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 140 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤19874 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 38 := by unfold smallValid; decide +kernel

private theorem sp38 : smallValid 38 39 := by unfold smallValid; decide +kernel

private theorem sp77 : smallValid 77 39 := by unfold smallValid; decide +kernel

private theorem sp116 : smallValid 116 39 := by unfold smallValid; decide +kernel

private theorem sp155 : smallValid 155 38 := by unfold smallValid; decide +kernel

private theorem sp193 : smallValid 193 39 := by unfold smallValid; decide +kernel

private theorem sp232 : smallValid 232 39 := by unfold smallValid; decide +kernel

private theorem sp271 : smallValid 271 39 := by unfold smallValid; decide +kernel

private theorem sp310 : smallValid 310 38 := by unfold smallValid; decide +kernel

private theorem sp348 : smallValid 348 39 := by unfold smallValid; decide +kernel

private theorem sp387 : smallValid 387 39 := by unfold smallValid; decide +kernel

private theorem sp426 : smallValid 426 39 := by unfold smallValid; decide +kernel

private theorem sp465 : smallValid 465 39 := by unfold smallValid; decide +kernel

private theorem sp504 : smallValid 504 39 := by unfold smallValid; decide +kernel

private theorem sp543 : smallValid 543 39 := by unfold smallValid; decide +kernel

private theorem sp582 : smallValid 582 39 := by unfold smallValid; decide +kernel

private theorem sp621 : smallValid 621 38 := by unfold smallValid; decide +kernel

private theorem sp659 : smallValid 659 39 := by unfold smallValid; decide +kernel

private theorem sp698 : smallValid 698 39 := by unfold smallValid; decide +kernel

private theorem sp737 : smallValid 737 39 := by unfold smallValid; decide +kernel

private theorem sp776 : smallValid 776 38 := by unfold smallValid; decide +kernel

private theorem sp814 : smallValid 814 39 := by unfold smallValid; decide +kernel

private theorem sp853 : smallValid 853 39 := by unfold smallValid; decide +kernel

private theorem sp892 : smallValid 892 39 := by unfold smallValid; decide +kernel

private theorem sp931 : smallValid 931 38 := by unfold smallValid; decide +kernel

private theorem sp969 : smallValid 969 39 := by unfold smallValid; decide +kernel

private theorem sp1008 : smallValid 1008 39 := by unfold smallValid; decide +kernel

private theorem sp1047 : smallValid 1047 39 := by unfold smallValid; decide +kernel

private theorem sp1086 : smallValid 1086 39 := by unfold smallValid; decide +kernel

private theorem sp1125 : smallValid 1125 39 := by unfold smallValid; decide +kernel

private theorem sp1164 : smallValid 1164 39 := by unfold smallValid; decide +kernel

private theorem sp1203 : smallValid 1203 39 := by unfold smallValid; decide +kernel

private theorem sp1242 : smallValid 1242 38 := by unfold smallValid; decide +kernel

private theorem sp1280 : smallValid 1280 39 := by unfold smallValid; decide +kernel

private theorem sp1319 : smallValid 1319 39 := by unfold smallValid; decide +kernel

private theorem sp1358 : smallValid 1358 39 := by unfold smallValid; decide +kernel

private theorem sp1397 : smallValid 1397 38 := by unfold smallValid; decide +kernel

private theorem sp1435 : smallValid 1435 39 := by unfold smallValid; decide +kernel

private theorem sp1474 : smallValid 1474 39 := by unfold smallValid; decide +kernel

private theorem sp1513 : smallValid 1513 39 := by unfold smallValid; decide +kernel

private theorem sp1552 : smallValid 1552 38 := by unfold smallValid; decide +kernel

private theorem sp1590 : smallValid 1590 39 := by unfold smallValid; decide +kernel

private theorem sp1629 : smallValid 1629 39 := by unfold smallValid; decide +kernel

private theorem sp1668 : smallValid 1668 39 := by unfold smallValid; decide +kernel

private theorem sp1707 : smallValid 1707 39 := by unfold smallValid; decide +kernel

private theorem sp1746 : smallValid 1746 39 := by unfold smallValid; decide +kernel

private theorem sp1785 : smallValid 1785 39 := by unfold smallValid; decide +kernel

private theorem sp1824 : smallValid 1824 39 := by unfold smallValid; decide +kernel

private theorem sp1863 : smallValid 1863 38 := by unfold smallValid; decide +kernel

private theorem sp1901 : smallValid 1901 39 := by unfold smallValid; decide +kernel

private theorem sp1940 : smallValid 1940 39 := by unfold smallValid; decide +kernel

private theorem sp1979 : smallValid 1979 39 := by unfold smallValid; decide +kernel

private theorem sp2018 : smallValid 2018 38 := by unfold smallValid; decide +kernel

private theorem sp2056 : smallValid 2056 39 := by unfold smallValid; decide +kernel

private theorem sp2095 : smallValid 2095 39 := by unfold smallValid; decide +kernel

private theorem sp2134 : smallValid 2134 39 := by unfold smallValid; decide +kernel

private theorem sp2173 : smallValid 2173 38 := by unfold smallValid; decide +kernel

private theorem sp2211 : smallValid 2211 39 := by unfold smallValid; decide +kernel

private theorem sp2250 : smallValid 2250 39 := by unfold smallValid; decide +kernel

private theorem sp2289 : smallValid 2289 39 := by unfold smallValid; decide +kernel

private theorem sp2328 : smallValid 2328 39 := by unfold smallValid; decide +kernel

private theorem sp2367 : smallValid 2367 39 := by unfold smallValid; decide +kernel

private theorem sp2406 : smallValid 2406 39 := by unfold smallValid; decide +kernel

private theorem sp2445 : smallValid 2445 39 := by unfold smallValid; decide +kernel

private theorem sp2484 : smallValid 2484 38 := by unfold smallValid; decide +kernel

private theorem sp2522 : smallValid 2522 39 := by unfold smallValid; decide +kernel

private theorem sp2561 : smallValid 2561 39 := by unfold smallValid; decide +kernel

private theorem sp2600 : smallValid 2600 39 := by unfold smallValid; decide +kernel

private theorem sp2639 : smallValid 2639 38 := by unfold smallValid; decide +kernel

private theorem sp2677 : smallValid 2677 39 := by unfold smallValid; decide +kernel

private theorem sp2716 : smallValid 2716 39 := by unfold smallValid; decide +kernel

private theorem sp2755 : smallValid 2755 39 := by unfold smallValid; decide +kernel

private theorem sp2794 : smallValid 2794 38 := by unfold smallValid; decide +kernel

private theorem sp2832 : smallValid 2832 39 := by unfold smallValid; decide +kernel

private theorem sp2871 : smallValid 2871 39 := by unfold smallValid; decide +kernel

private theorem sp2910 : smallValid 2910 39 := by unfold smallValid; decide +kernel

private theorem sp2949 : smallValid 2949 39 := by unfold smallValid; decide +kernel

private theorem sp2988 : smallValid 2988 39 := by unfold smallValid; decide +kernel

private theorem sp3027 : smallValid 3027 39 := by unfold smallValid; decide +kernel

private theorem sp3066 : smallValid 3066 39 := by unfold smallValid; decide +kernel

private theorem sp3105 : smallValid 3105 38 := by unfold smallValid; decide +kernel

private theorem sp3143 : smallValid 3143 39 := by unfold smallValid; decide +kernel

private theorem sp3182 : smallValid 3182 39 := by unfold smallValid; decide +kernel

private theorem sp3221 : smallValid 3221 39 := by unfold smallValid; decide +kernel

private theorem sp3260 : smallValid 3260 38 := by unfold smallValid; decide +kernel

private theorem sp3298 : smallValid 3298 39 := by unfold smallValid; decide +kernel

private theorem sp3337 : smallValid 3337 39 := by unfold smallValid; decide +kernel

private theorem sp3376 : smallValid 3376 39 := by unfold smallValid; decide +kernel

private theorem sp3415 : smallValid 3415 38 := by unfold smallValid; decide +kernel

private theorem sp3453 : smallValid 3453 39 := by unfold smallValid; decide +kernel

private theorem sp3492 : smallValid 3492 39 := by unfold smallValid; decide +kernel

private theorem sp3531 : smallValid 3531 39 := by unfold smallValid; decide +kernel

private theorem sp3570 : smallValid 3570 39 := by unfold smallValid; decide +kernel

private theorem sp3609 : smallValid 3609 39 := by unfold smallValid; decide +kernel

private theorem sp3648 : smallValid 3648 39 := by unfold smallValid; decide +kernel

private theorem sp3687 : smallValid 3687 39 := by unfold smallValid; decide +kernel

private theorem sp3726 : smallValid 3726 38 := by unfold smallValid; decide +kernel

private theorem sp3764 : smallValid 3764 39 := by unfold smallValid; decide +kernel

private theorem sp3803 : smallValid 3803 39 := by unfold smallValid; decide +kernel

private theorem sp3842 : smallValid 3842 39 := by unfold smallValid; decide +kernel

private theorem sp3881 : smallValid 3881 38 := by unfold smallValid; decide +kernel

private theorem sp3919 : smallValid 3919 39 := by unfold smallValid; decide +kernel

private theorem sp3958 : smallValid 3958 39 := by unfold smallValid; decide +kernel

private theorem sp3997 : smallValid 3997 39 := by unfold smallValid; decide +kernel

private theorem sp4036 : smallValid 4036 38 := by unfold smallValid; decide +kernel

private theorem sp4074 : smallValid 4074 39 := by unfold smallValid; decide +kernel

private theorem sp4113 : smallValid 4113 39 := by unfold smallValid; decide +kernel

private theorem sp4152 : smallValid 4152 39 := by unfold smallValid; decide +kernel

private theorem sp4191 : smallValid 4191 39 := by unfold smallValid; decide +kernel

private theorem sp4230 : smallValid 4230 39 := by unfold smallValid; decide +kernel

private theorem sp4269 : smallValid 4269 39 := by unfold smallValid; decide +kernel

private theorem sp4308 : smallValid 4308 39 := by unfold smallValid; decide +kernel

private theorem sp4347 : smallValid 4347 38 := by unfold smallValid; decide +kernel

private theorem sp4385 : smallValid 4385 39 := by unfold smallValid; decide +kernel

private theorem sp4424 : smallValid 4424 39 := by unfold smallValid; decide +kernel

private theorem sp4463 : smallValid 4463 39 := by unfold smallValid; decide +kernel

private theorem sp4502 : smallValid 4502 38 := by unfold smallValid; decide +kernel

private theorem sp4540 : smallValid 4540 39 := by unfold smallValid; decide +kernel

private theorem sp4579 : smallValid 4579 39 := by unfold smallValid; decide +kernel

private theorem sp4618 : smallValid 4618 39 := by unfold smallValid; decide +kernel

private theorem sp4657 : smallValid 4657 38 := by unfold smallValid; decide +kernel

private theorem sp4695 : smallValid 4695 39 := by unfold smallValid; decide +kernel

private theorem sp4734 : smallValid 4734 39 := by unfold smallValid; decide +kernel

private theorem sp4773 : smallValid 4773 39 := by unfold smallValid; decide +kernel

private theorem sp4812 : smallValid 4812 39 := by unfold smallValid; decide +kernel

private theorem sp4851 : smallValid 4851 39 := by unfold smallValid; decide +kernel

private theorem sp4890 : smallValid 4890 39 := by unfold smallValid; decide +kernel

private theorem sp4929 : smallValid 4929 39 := by unfold smallValid; decide +kernel

private theorem sp4968 : smallValid 4968 38 := by unfold smallValid; decide +kernel

private theorem sp5006 : smallValid 5006 39 := by unfold smallValid; decide +kernel

private theorem sp5045 : smallValid 5045 39 := by unfold smallValid; decide +kernel

private theorem sp5084 : smallValid 5084 39 := by unfold smallValid; decide +kernel

private theorem sp5123 : smallValid 5123 38 := by unfold smallValid; decide +kernel

private theorem sp5161 : smallValid 5161 39 := by unfold smallValid; decide +kernel

private theorem sp5200 : smallValid 5200 39 := by unfold smallValid; decide +kernel

private theorem sp5239 : smallValid 5239 39 := by unfold smallValid; decide +kernel

private theorem sp5278 : smallValid 5278 38 := by unfold smallValid; decide +kernel

private theorem sp5316 : smallValid 5316 39 := by unfold smallValid; decide +kernel

private theorem sp5355 : smallValid 5355 39 := by unfold smallValid; decide +kernel

private theorem sp5394 : smallValid 5394 39 := by unfold smallValid; decide +kernel

private theorem sp5433 : smallValid 5433 39 := by unfold smallValid; decide +kernel

private theorem sp5472 : smallValid 5472 39 := by unfold smallValid; decide +kernel

private theorem sp5511 : smallValid 5511 39 := by unfold smallValid; decide +kernel

private theorem sp5550 : smallValid 5550 39 := by unfold smallValid; decide +kernel

private theorem sp5589 : smallValid 5589 38 := by unfold smallValid; decide +kernel

private theorem sp5627 : smallValid 5627 39 := by unfold smallValid; decide +kernel

private theorem sp5666 : smallValid 5666 39 := by unfold smallValid; decide +kernel

private theorem sp5705 : smallValid 5705 39 := by unfold smallValid; decide +kernel

private theorem sp5744 : smallValid 5744 38 := by unfold smallValid; decide +kernel

private theorem sp5782 : smallValid 5782 39 := by unfold smallValid; decide +kernel

private theorem sp5821 : smallValid 5821 39 := by unfold smallValid; decide +kernel

private theorem sp5860 : smallValid 5860 39 := by unfold smallValid; decide +kernel

private theorem sp5899 : smallValid 5899 38 := by unfold smallValid; decide +kernel

private theorem sp5937 : smallValid 5937 39 := by unfold smallValid; decide +kernel

private theorem sp5976 : smallValid 5976 39 := by unfold smallValid; decide +kernel

private theorem sp6015 : smallValid 6015 39 := by unfold smallValid; decide +kernel

private theorem sp6054 : smallValid 6054 39 := by unfold smallValid; decide +kernel

private theorem sp6093 : smallValid 6093 39 := by unfold smallValid; decide +kernel

private theorem sp6132 : smallValid 6132 39 := by unfold smallValid; decide +kernel

private theorem sp6171 : smallValid 6171 39 := by unfold smallValid; decide +kernel

private theorem sp6210 : smallValid 6210 38 := by unfold smallValid; decide +kernel

private theorem sp6248 : smallValid 6248 39 := by unfold smallValid; decide +kernel

private theorem sp6287 : smallValid 6287 39 := by unfold smallValid; decide +kernel

private theorem sp6326 : smallValid 6326 39 := by unfold smallValid; decide +kernel

private theorem sp6365 : smallValid 6365 38 := by unfold smallValid; decide +kernel

private theorem sp6403 : smallValid 6403 39 := by unfold smallValid; decide +kernel

private theorem sp6442 : smallValid 6442 39 := by unfold smallValid; decide +kernel

private theorem sp6481 : smallValid 6481 39 := by unfold smallValid; decide +kernel

private theorem sp6520 : smallValid 6520 38 := by unfold smallValid; decide +kernel

private theorem sp6558 : smallValid 6558 39 := by unfold smallValid; decide +kernel

private theorem sp6597 : smallValid 6597 39 := by unfold smallValid; decide +kernel

private theorem sp6636 : smallValid 6636 39 := by unfold smallValid; decide +kernel

private theorem sp6675 : smallValid 6675 39 := by unfold smallValid; decide +kernel

private theorem sp6714 : smallValid 6714 39 := by unfold smallValid; decide +kernel

private theorem sp6753 : smallValid 6753 39 := by unfold smallValid; decide +kernel

private theorem sp6792 : smallValid 6792 39 := by unfold smallValid; decide +kernel

private theorem sp6831 : smallValid 6831 38 := by unfold smallValid; decide +kernel

private theorem sp6869 : smallValid 6869 39 := by unfold smallValid; decide +kernel

private theorem sp6908 : smallValid 6908 39 := by unfold smallValid; decide +kernel

private theorem sp6947 : smallValid 6947 39 := by unfold smallValid; decide +kernel

private theorem sp6986 : smallValid 6986 38 := by unfold smallValid; decide +kernel

private theorem sp7024 : smallValid 7024 39 := by unfold smallValid; decide +kernel

private theorem sp7063 : smallValid 7063 39 := by unfold smallValid; decide +kernel

private theorem sp7102 : smallValid 7102 39 := by unfold smallValid; decide +kernel

private theorem sp7141 : smallValid 7141 38 := by unfold smallValid; decide +kernel

private theorem sp7179 : smallValid 7179 39 := by unfold smallValid; decide +kernel

private theorem sp7218 : smallValid 7218 39 := by unfold smallValid; decide +kernel

private theorem sp7257 : smallValid 7257 39 := by unfold smallValid; decide +kernel

private theorem sp7296 : smallValid 7296 39 := by unfold smallValid; decide +kernel

private theorem sp7335 : smallValid 7335 39 := by unfold smallValid; decide +kernel

private theorem sp7374 : smallValid 7374 39 := by unfold smallValid; decide +kernel

private theorem sp7413 : smallValid 7413 39 := by unfold smallValid; decide +kernel

private theorem sp7452 : smallValid 7452 38 := by unfold smallValid; decide +kernel

private theorem sp7490 : smallValid 7490 39 := by unfold smallValid; decide +kernel

private theorem sp7529 : smallValid 7529 39 := by unfold smallValid; decide +kernel

private theorem sp7568 : smallValid 7568 39 := by unfold smallValid; decide +kernel

private theorem sp7607 : smallValid 7607 38 := by unfold smallValid; decide +kernel

private theorem sp7645 : smallValid 7645 39 := by unfold smallValid; decide +kernel

private theorem sp7684 : smallValid 7684 39 := by unfold smallValid; decide +kernel

private theorem sp7723 : smallValid 7723 39 := by unfold smallValid; decide +kernel

private theorem sp7762 : smallValid 7762 38 := by unfold smallValid; decide +kernel

private theorem sp7800 : smallValid 7800 39 := by unfold smallValid; decide +kernel

private theorem sp7839 : smallValid 7839 39 := by unfold smallValid; decide +kernel

private theorem sp7878 : smallValid 7878 39 := by unfold smallValid; decide +kernel

private theorem sp7917 : smallValid 7917 39 := by unfold smallValid; decide +kernel

private theorem sp7956 : smallValid 7956 39 := by unfold smallValid; decide +kernel

private theorem sp7995 : smallValid 7995 39 := by unfold smallValid; decide +kernel

private theorem sp8034 : smallValid 8034 39 := by unfold smallValid; decide +kernel

private theorem sp8073 : smallValid 8073 38 := by unfold smallValid; decide +kernel

private theorem sp8111 : smallValid 8111 39 := by unfold smallValid; decide +kernel

private theorem sp8150 : smallValid 8150 39 := by unfold smallValid; decide +kernel

private theorem sp8189 : smallValid 8189 39 := by unfold smallValid; decide +kernel

private theorem sp8228 : smallValid 8228 38 := by unfold smallValid; decide +kernel

private theorem sp8266 : smallValid 8266 39 := by unfold smallValid; decide +kernel

private theorem sp8305 : smallValid 8305 39 := by unfold smallValid; decide +kernel

private theorem sp8344 : smallValid 8344 39 := by unfold smallValid; decide +kernel

private theorem sp8383 : smallValid 8383 38 := by unfold smallValid; decide +kernel

private theorem sp8421 : smallValid 8421 39 := by unfold smallValid; decide +kernel

private theorem sp8460 : smallValid 8460 39 := by unfold smallValid; decide +kernel

private theorem sp8499 : smallValid 8499 39 := by unfold smallValid; decide +kernel

private theorem sp8538 : smallValid 8538 39 := by unfold smallValid; decide +kernel

private theorem sp8577 : smallValid 8577 39 := by unfold smallValid; decide +kernel

private theorem sp8616 : smallValid 8616 39 := by unfold smallValid; decide +kernel

private theorem sp8655 : smallValid 8655 39 := by unfold smallValid; decide +kernel

private theorem sp8694 : smallValid 8694 38 := by unfold smallValid; decide +kernel

private theorem sp8732 : smallValid 8732 39 := by unfold smallValid; decide +kernel

private theorem sp8771 : smallValid 8771 39 := by unfold smallValid; decide +kernel

private theorem sp8810 : smallValid 8810 39 := by unfold smallValid; decide +kernel

private theorem sp8849 : smallValid 8849 38 := by unfold smallValid; decide +kernel

private theorem sp8887 : smallValid 8887 39 := by unfold smallValid; decide +kernel

private theorem sp8926 : smallValid 8926 39 := by unfold smallValid; decide +kernel

private theorem sp8965 : smallValid 8965 39 := by unfold smallValid; decide +kernel

private theorem sp9004 : smallValid 9004 38 := by unfold smallValid; decide +kernel

private theorem sp9042 : smallValid 9042 39 := by unfold smallValid; decide +kernel

private theorem sp9081 : smallValid 9081 39 := by unfold smallValid; decide +kernel

private theorem sp9120 : smallValid 9120 39 := by unfold smallValid; decide +kernel

private theorem sp9159 : smallValid 9159 39 := by unfold smallValid; decide +kernel

private theorem sp9198 : smallValid 9198 39 := by unfold smallValid; decide +kernel

private theorem sp9237 : smallValid 9237 39 := by unfold smallValid; decide +kernel

private theorem sp9276 : smallValid 9276 39 := by unfold smallValid; decide +kernel

private theorem sp9315 : smallValid 9315 38 := by unfold smallValid; decide +kernel

private theorem sp9353 : smallValid 9353 39 := by unfold smallValid; decide +kernel

private theorem sp9392 : smallValid 9392 39 := by unfold smallValid; decide +kernel

private theorem sp9431 : smallValid 9431 39 := by unfold smallValid; decide +kernel

private theorem sp9470 : smallValid 9470 39 := by unfold smallValid; decide +kernel

private theorem sp9509 : smallValid 9509 39 := by unfold smallValid; decide +kernel

private theorem sp9548 : smallValid 9548 39 := by unfold smallValid; decide +kernel

private theorem sp9587 : smallValid 9587 39 := by unfold smallValid; decide +kernel

private theorem sp9626 : smallValid 9626 38 := by unfold smallValid; decide +kernel

private theorem sp9664 : smallValid 9664 39 := by unfold smallValid; decide +kernel

private theorem sp9703 : smallValid 9703 39 := by unfold smallValid; decide +kernel

private theorem sp9742 : smallValid 9742 39 := by unfold smallValid; decide +kernel

private theorem sp9781 : smallValid 9781 39 := by unfold smallValid; decide +kernel

private theorem sp9820 : smallValid 9820 39 := by unfold smallValid; decide +kernel

private theorem sp9859 : smallValid 9859 39 := by unfold smallValid; decide +kernel

private theorem sp9898 : smallValid 9898 39 := by unfold smallValid; decide +kernel

private theorem sp9937 : smallValid 9937 38 := by unfold smallValid; decide +kernel

private theorem sp9975 : smallValid 9975 39 := by unfold smallValid; decide +kernel

private theorem sp10014 : smallValid 10014 39 := by unfold smallValid; decide +kernel

private theorem sp10053 : smallValid 10053 39 := by unfold smallValid; decide +kernel

private theorem sp10092 : smallValid 10092 38 := by unfold smallValid; decide +kernel

private theorem sp10130 : smallValid 10130 39 := by unfold smallValid; decide +kernel

private theorem sp10169 : smallValid 10169 39 := by unfold smallValid; decide +kernel

private theorem sp10208 : smallValid 10208 39 := by unfold smallValid; decide +kernel

private theorem sp10247 : smallValid 10247 38 := by unfold smallValid; decide +kernel

private theorem sp10285 : smallValid 10285 39 := by unfold smallValid; decide +kernel

private theorem sp10324 : smallValid 10324 39 := by unfold smallValid; decide +kernel

private theorem sp10363 : smallValid 10363 39 := by unfold smallValid; decide +kernel

private theorem sp10402 : smallValid 10402 39 := by unfold smallValid; decide +kernel

private theorem sp10441 : smallValid 10441 39 := by unfold smallValid; decide +kernel

private theorem sp10480 : smallValid 10480 39 := by unfold smallValid; decide +kernel

private theorem sp10519 : smallValid 10519 39 := by unfold smallValid; decide +kernel

private theorem sp10558 : smallValid 10558 38 := by unfold smallValid; decide +kernel

private theorem sp10596 : smallValid 10596 39 := by unfold smallValid; decide +kernel

private theorem sp10635 : smallValid 10635 39 := by unfold smallValid; decide +kernel

private theorem sp10674 : smallValid 10674 39 := by unfold smallValid; decide +kernel

private theorem sp10713 : smallValid 10713 38 := by unfold smallValid; decide +kernel

private theorem sp10751 : smallValid 10751 39 := by unfold smallValid; decide +kernel

private theorem sp10790 : smallValid 10790 39 := by unfold smallValid; decide +kernel

private theorem sp10829 : smallValid 10829 39 := by unfold smallValid; decide +kernel

private theorem sp10868 : smallValid 10868 38 := by unfold smallValid; decide +kernel

private theorem sp10906 : smallValid 10906 39 := by unfold smallValid; decide +kernel

private theorem sp10945 : smallValid 10945 39 := by unfold smallValid; decide +kernel

private theorem sp10984 : smallValid 10984 39 := by unfold smallValid; decide +kernel

private theorem sp11023 : smallValid 11023 39 := by unfold smallValid; decide +kernel

private theorem sp11062 : smallValid 11062 39 := by unfold smallValid; decide +kernel

private theorem sp11101 : smallValid 11101 39 := by unfold smallValid; decide +kernel

private theorem sp11140 : smallValid 11140 39 := by unfold smallValid; decide +kernel

private theorem sp11179 : smallValid 11179 38 := by unfold smallValid; decide +kernel

private theorem sp11217 : smallValid 11217 39 := by unfold smallValid; decide +kernel

private theorem sp11256 : smallValid 11256 39 := by unfold smallValid; decide +kernel

private theorem sp11295 : smallValid 11295 39 := by unfold smallValid; decide +kernel

private theorem sp11334 : smallValid 11334 38 := by unfold smallValid; decide +kernel

private theorem sp11372 : smallValid 11372 39 := by unfold smallValid; decide +kernel

private theorem sp11411 : smallValid 11411 39 := by unfold smallValid; decide +kernel

private theorem sp11450 : smallValid 11450 39 := by unfold smallValid; decide +kernel

private theorem sp11489 : smallValid 11489 38 := by unfold smallValid; decide +kernel

private theorem sp11527 : smallValid 11527 39 := by unfold smallValid; decide +kernel

private theorem sp11566 : smallValid 11566 39 := by unfold smallValid; decide +kernel

private theorem sp11605 : smallValid 11605 39 := by unfold smallValid; decide +kernel

private theorem sp11644 : smallValid 11644 39 := by unfold smallValid; decide +kernel

private theorem sp11683 : smallValid 11683 39 := by unfold smallValid; decide +kernel

private theorem sp11722 : smallValid 11722 39 := by unfold smallValid; decide +kernel

private theorem sp11761 : smallValid 11761 39 := by unfold smallValid; decide +kernel

private theorem sp11800 : smallValid 11800 38 := by unfold smallValid; decide +kernel

private theorem sp11838 : smallValid 11838 39 := by unfold smallValid; decide +kernel

private theorem sp11877 : smallValid 11877 39 := by unfold smallValid; decide +kernel

private theorem sp11916 : smallValid 11916 39 := by unfold smallValid; decide +kernel

private theorem sp11955 : smallValid 11955 38 := by unfold smallValid; decide +kernel

private theorem sp11993 : smallValid 11993 39 := by unfold smallValid; decide +kernel

private theorem sp12032 : smallValid 12032 39 := by unfold smallValid; decide +kernel

private theorem sp12071 : smallValid 12071 39 := by unfold smallValid; decide +kernel

private theorem sp12110 : smallValid 12110 38 := by unfold smallValid; decide +kernel

private theorem sp12148 : smallValid 12148 39 := by unfold smallValid; decide +kernel

private theorem sp12187 : smallValid 12187 39 := by unfold smallValid; decide +kernel

private theorem sp12226 : smallValid 12226 39 := by unfold smallValid; decide +kernel

private theorem sp12265 : smallValid 12265 39 := by unfold smallValid; decide +kernel

private theorem sp12304 : smallValid 12304 39 := by unfold smallValid; decide +kernel

private theorem sp12343 : smallValid 12343 39 := by unfold smallValid; decide +kernel

private theorem sp12382 : smallValid 12382 39 := by unfold smallValid; decide +kernel

private theorem sp12421 : smallValid 12421 38 := by unfold smallValid; decide +kernel

private theorem sp12459 : smallValid 12459 39 := by unfold smallValid; decide +kernel

private theorem sp12498 : smallValid 12498 39 := by unfold smallValid; decide +kernel

private theorem sp12537 : smallValid 12537 39 := by unfold smallValid; decide +kernel

private theorem sp12576 : smallValid 12576 38 := by unfold smallValid; decide +kernel

private theorem sp12614 : smallValid 12614 39 := by unfold smallValid; decide +kernel

private theorem sp12653 : smallValid 12653 39 := by unfold smallValid; decide +kernel

private theorem sp12692 : smallValid 12692 39 := by unfold smallValid; decide +kernel

private theorem sp12731 : smallValid 12731 38 := by unfold smallValid; decide +kernel

private theorem sp12769 : smallValid 12769 39 := by unfold smallValid; decide +kernel

private theorem sp12808 : smallValid 12808 39 := by unfold smallValid; decide +kernel

private theorem sp12847 : smallValid 12847 39 := by unfold smallValid; decide +kernel

private theorem sp12886 : smallValid 12886 39 := by unfold smallValid; decide +kernel

private theorem sp12925 : smallValid 12925 39 := by unfold smallValid; decide +kernel

private theorem sp12964 : smallValid 12964 39 := by unfold smallValid; decide +kernel

private theorem sp13003 : smallValid 13003 39 := by unfold smallValid; decide +kernel

private theorem sp13042 : smallValid 13042 38 := by unfold smallValid; decide +kernel

private theorem sp13080 : smallValid 13080 39 := by unfold smallValid; decide +kernel

private theorem sp13119 : smallValid 13119 39 := by unfold smallValid; decide +kernel

private theorem sp13158 : smallValid 13158 39 := by unfold smallValid; decide +kernel

private theorem sp13197 : smallValid 13197 38 := by unfold smallValid; decide +kernel

private theorem sp13235 : smallValid 13235 39 := by unfold smallValid; decide +kernel

private theorem sp13274 : smallValid 13274 39 := by unfold smallValid; decide +kernel

private theorem sp13313 : smallValid 13313 39 := by unfold smallValid; decide +kernel

private theorem sp13352 : smallValid 13352 38 := by unfold smallValid; decide +kernel

private theorem sp13390 : smallValid 13390 39 := by unfold smallValid; decide +kernel

private theorem sp13429 : smallValid 13429 39 := by unfold smallValid; decide +kernel

private theorem sp13468 : smallValid 13468 39 := by unfold smallValid; decide +kernel

private theorem sp13507 : smallValid 13507 39 := by unfold smallValid; decide +kernel

private theorem sp13546 : smallValid 13546 39 := by unfold smallValid; decide +kernel

private theorem sp13585 : smallValid 13585 39 := by unfold smallValid; decide +kernel

private theorem sp13624 : smallValid 13624 39 := by unfold smallValid; decide +kernel

private theorem sp13663 : smallValid 13663 38 := by unfold smallValid; decide +kernel

private theorem sp13701 : smallValid 13701 39 := by unfold smallValid; decide +kernel

private theorem sp13740 : smallValid 13740 39 := by unfold smallValid; decide +kernel

private theorem sp13779 : smallValid 13779 39 := by unfold smallValid; decide +kernel

private theorem sp13818 : smallValid 13818 38 := by unfold smallValid; decide +kernel

private theorem sp13856 : smallValid 13856 39 := by unfold smallValid; decide +kernel

private theorem sp13895 : smallValid 13895 39 := by unfold smallValid; decide +kernel

private theorem sp13934 : smallValid 13934 39 := by unfold smallValid; decide +kernel

private theorem sp13973 : smallValid 13973 38 := by unfold smallValid; decide +kernel

private theorem sp14011 : smallValid 14011 39 := by unfold smallValid; decide +kernel

private theorem sp14050 : smallValid 14050 39 := by unfold smallValid; decide +kernel

private theorem sp14089 : smallValid 14089 39 := by unfold smallValid; decide +kernel

private theorem sp14128 : smallValid 14128 39 := by unfold smallValid; decide +kernel

private theorem sp14167 : smallValid 14167 39 := by unfold smallValid; decide +kernel

private theorem sp14206 : smallValid 14206 39 := by unfold smallValid; decide +kernel

private theorem sp14245 : smallValid 14245 39 := by unfold smallValid; decide +kernel

private theorem sp14284 : smallValid 14284 38 := by unfold smallValid; decide +kernel

private theorem sp14322 : smallValid 14322 39 := by unfold smallValid; decide +kernel

private theorem sp14361 : smallValid 14361 39 := by unfold smallValid; decide +kernel

private theorem sp14400 : smallValid 14400 39 := by unfold smallValid; decide +kernel

private theorem sp14439 : smallValid 14439 39 := by unfold smallValid; decide +kernel

private theorem sp14478 : smallValid 14478 39 := by unfold smallValid; decide +kernel

private theorem sp14517 : smallValid 14517 39 := by unfold smallValid; decide +kernel

private theorem sp14556 : smallValid 14556 39 := by unfold smallValid; decide +kernel

private theorem sp14595 : smallValid 14595 38 := by unfold smallValid; decide +kernel

private theorem sp14633 : smallValid 14633 39 := by unfold smallValid; decide +kernel

private theorem sp14672 : smallValid 14672 39 := by unfold smallValid; decide +kernel

private theorem sp14711 : smallValid 14711 39 := by unfold smallValid; decide +kernel

private theorem sp14750 : smallValid 14750 39 := by unfold smallValid; decide +kernel

private theorem sp14789 : smallValid 14789 39 := by unfold smallValid; decide +kernel

private theorem sp14828 : smallValid 14828 39 := by unfold smallValid; decide +kernel

private theorem sp14867 : smallValid 14867 39 := by unfold smallValid; decide +kernel

private theorem sp14906 : smallValid 14906 38 := by unfold smallValid; decide +kernel

private theorem sp14944 : smallValid 14944 39 := by unfold smallValid; decide +kernel

private theorem sp14983 : smallValid 14983 39 := by unfold smallValid; decide +kernel

private theorem sp15022 : smallValid 15022 39 := by unfold smallValid; decide +kernel

private theorem sp15061 : smallValid 15061 38 := by unfold smallValid; decide +kernel

private theorem sp15099 : smallValid 15099 39 := by unfold smallValid; decide +kernel

private theorem sp15138 : smallValid 15138 39 := by unfold smallValid; decide +kernel

private theorem sp15177 : smallValid 15177 39 := by unfold smallValid; decide +kernel

private theorem sp15216 : smallValid 15216 38 := by unfold smallValid; decide +kernel

private theorem sp15254 : smallValid 15254 39 := by unfold smallValid; decide +kernel

private theorem sp15293 : smallValid 15293 39 := by unfold smallValid; decide +kernel

private theorem sp15332 : smallValid 15332 39 := by unfold smallValid; decide +kernel

private theorem sp15371 : smallValid 15371 39 := by unfold smallValid; decide +kernel

private theorem sp15410 : smallValid 15410 39 := by unfold smallValid; decide +kernel

private theorem sp15449 : smallValid 15449 39 := by unfold smallValid; decide +kernel

private theorem sp15488 : smallValid 15488 39 := by unfold smallValid; decide +kernel

private theorem sp15527 : smallValid 15527 38 := by unfold smallValid; decide +kernel

private theorem sp15565 : smallValid 15565 39 := by unfold smallValid; decide +kernel

private theorem sp15604 : smallValid 15604 39 := by unfold smallValid; decide +kernel

private theorem sp15643 : smallValid 15643 39 := by unfold smallValid; decide +kernel

private theorem sp15682 : smallValid 15682 38 := by unfold smallValid; decide +kernel

private theorem sp15720 : smallValid 15720 39 := by unfold smallValid; decide +kernel

private theorem sp15759 : smallValid 15759 39 := by unfold smallValid; decide +kernel

private theorem sp15798 : smallValid 15798 39 := by unfold smallValid; decide +kernel

private theorem sp15837 : smallValid 15837 38 := by unfold smallValid; decide +kernel

private theorem sp15875 : smallValid 15875 39 := by unfold smallValid; decide +kernel

private theorem sp15914 : smallValid 15914 39 := by unfold smallValid; decide +kernel

private theorem sp15953 : smallValid 15953 39 := by unfold smallValid; decide +kernel

private theorem sp15992 : smallValid 15992 39 := by unfold smallValid; decide +kernel

private theorem sp16031 : smallValid 16031 39 := by unfold smallValid; decide +kernel

private theorem sp16070 : smallValid 16070 39 := by unfold smallValid; decide +kernel

private theorem sp16109 : smallValid 16109 39 := by unfold smallValid; decide +kernel

private theorem sp16148 : smallValid 16148 38 := by unfold smallValid; decide +kernel

private theorem sp16186 : smallValid 16186 39 := by unfold smallValid; decide +kernel

private theorem sp16225 : smallValid 16225 39 := by unfold smallValid; decide +kernel

private theorem sp16264 : smallValid 16264 39 := by unfold smallValid; decide +kernel

private theorem sp16303 : smallValid 16303 38 := by unfold smallValid; decide +kernel

private theorem sp16341 : smallValid 16341 39 := by unfold smallValid; decide +kernel

private theorem sp16380 : smallValid 16380 39 := by unfold smallValid; decide +kernel

private theorem sp16419 : smallValid 16419 39 := by unfold smallValid; decide +kernel

private theorem sp16458 : smallValid 16458 38 := by unfold smallValid; decide +kernel

private theorem sp16496 : smallValid 16496 39 := by unfold smallValid; decide +kernel

private theorem sp16535 : smallValid 16535 39 := by unfold smallValid; decide +kernel

private theorem sp16574 : smallValid 16574 39 := by unfold smallValid; decide +kernel

private theorem sp16613 : smallValid 16613 39 := by unfold smallValid; decide +kernel

private theorem sp16652 : smallValid 16652 39 := by unfold smallValid; decide +kernel

private theorem sp16691 : smallValid 16691 39 := by unfold smallValid; decide +kernel

private theorem sp16730 : smallValid 16730 39 := by unfold smallValid; decide +kernel

private theorem sp16769 : smallValid 16769 38 := by unfold smallValid; decide +kernel

private theorem sp16807 : smallValid 16807 39 := by unfold smallValid; decide +kernel

private theorem sp16846 : smallValid 16846 39 := by unfold smallValid; decide +kernel

private theorem sp16885 : smallValid 16885 39 := by unfold smallValid; decide +kernel

private theorem sp16924 : smallValid 16924 38 := by unfold smallValid; decide +kernel

private theorem sp16962 : smallValid 16962 39 := by unfold smallValid; decide +kernel

private theorem sp17001 : smallValid 17001 39 := by unfold smallValid; decide +kernel

private theorem sp17040 : smallValid 17040 39 := by unfold smallValid; decide +kernel

private theorem sp17079 : smallValid 17079 38 := by unfold smallValid; decide +kernel

private theorem sp17117 : smallValid 17117 39 := by unfold smallValid; decide +kernel

private theorem sp17156 : smallValid 17156 39 := by unfold smallValid; decide +kernel

private theorem sp17195 : smallValid 17195 39 := by unfold smallValid; decide +kernel

private theorem sp17234 : smallValid 17234 39 := by unfold smallValid; decide +kernel

private theorem sp17273 : smallValid 17273 39 := by unfold smallValid; decide +kernel

private theorem sp17312 : smallValid 17312 39 := by unfold smallValid; decide +kernel

private theorem sp17351 : smallValid 17351 39 := by unfold smallValid; decide +kernel

private theorem sp17390 : smallValid 17390 38 := by unfold smallValid; decide +kernel

private theorem sp17428 : smallValid 17428 39 := by unfold smallValid; decide +kernel

private theorem sp17467 : smallValid 17467 39 := by unfold smallValid; decide +kernel

private theorem sp17506 : smallValid 17506 39 := by unfold smallValid; decide +kernel

private theorem sp17545 : smallValid 17545 38 := by unfold smallValid; decide +kernel

private theorem sp17583 : smallValid 17583 39 := by unfold smallValid; decide +kernel

private theorem sp17622 : smallValid 17622 39 := by unfold smallValid; decide +kernel

private theorem sp17661 : smallValid 17661 39 := by unfold smallValid; decide +kernel

private theorem sp17700 : smallValid 17700 38 := by unfold smallValid; decide +kernel

private theorem sp17738 : smallValid 17738 39 := by unfold smallValid; decide +kernel

private theorem sp17777 : smallValid 17777 39 := by unfold smallValid; decide +kernel

private theorem sp17816 : smallValid 17816 39 := by unfold smallValid; decide +kernel

private theorem sp17855 : smallValid 17855 39 := by unfold smallValid; decide +kernel

private theorem sp17894 : smallValid 17894 39 := by unfold smallValid; decide +kernel

private theorem sp17933 : smallValid 17933 39 := by unfold smallValid; decide +kernel

private theorem sp17972 : smallValid 17972 39 := by unfold smallValid; decide +kernel

private theorem sp18011 : smallValid 18011 38 := by unfold smallValid; decide +kernel

private theorem sp18049 : smallValid 18049 39 := by unfold smallValid; decide +kernel

private theorem sp18088 : smallValid 18088 39 := by unfold smallValid; decide +kernel

private theorem sp18127 : smallValid 18127 39 := by unfold smallValid; decide +kernel

private theorem sp18166 : smallValid 18166 38 := by unfold smallValid; decide +kernel

private theorem sp18204 : smallValid 18204 39 := by unfold smallValid; decide +kernel

private theorem sp18243 : smallValid 18243 39 := by unfold smallValid; decide +kernel

private theorem sp18282 : smallValid 18282 39 := by unfold smallValid; decide +kernel

private theorem sp18321 : smallValid 18321 38 := by unfold smallValid; decide +kernel

private theorem sp18359 : smallValid 18359 39 := by unfold smallValid; decide +kernel

private theorem sp18398 : smallValid 18398 39 := by unfold smallValid; decide +kernel

private theorem sp18437 : smallValid 18437 39 := by unfold smallValid; decide +kernel

private theorem sp18476 : smallValid 18476 39 := by unfold smallValid; decide +kernel

private theorem sp18515 : smallValid 18515 39 := by unfold smallValid; decide +kernel

private theorem sp18554 : smallValid 18554 39 := by unfold smallValid; decide +kernel

private theorem sp18593 : smallValid 18593 39 := by unfold smallValid; decide +kernel

private theorem sp18632 : smallValid 18632 38 := by unfold smallValid; decide +kernel

private theorem sp18670 : smallValid 18670 39 := by unfold smallValid; decide +kernel

private theorem sp18709 : smallValid 18709 39 := by unfold smallValid; decide +kernel

private theorem sp18748 : smallValid 18748 39 := by unfold smallValid; decide +kernel

private theorem sp18787 : smallValid 18787 38 := by unfold smallValid; decide +kernel

private theorem sp18825 : smallValid 18825 39 := by unfold smallValid; decide +kernel

private theorem sp18864 : smallValid 18864 39 := by unfold smallValid; decide +kernel

private theorem sp18903 : smallValid 18903 39 := by unfold smallValid; decide +kernel

private theorem sp18942 : smallValid 18942 38 := by unfold smallValid; decide +kernel

private theorem sp18980 : smallValid 18980 39 := by unfold smallValid; decide +kernel

private theorem sp19019 : smallValid 19019 39 := by unfold smallValid; decide +kernel

private theorem sp19058 : smallValid 19058 39 := by unfold smallValid; decide +kernel

private theorem sp19097 : smallValid 19097 39 := by unfold smallValid; decide +kernel

private theorem sp19136 : smallValid 19136 39 := by unfold smallValid; decide +kernel

private theorem sp19175 : smallValid 19175 39 := by unfold smallValid; decide +kernel

private theorem sp19214 : smallValid 19214 39 := by unfold smallValid; decide +kernel

private theorem sp19253 : smallValid 19253 38 := by unfold smallValid; decide +kernel

private theorem sp19291 : smallValid 19291 39 := by unfold smallValid; decide +kernel

private theorem sp19330 : smallValid 19330 39 := by unfold smallValid; decide +kernel

private theorem sp19369 : smallValid 19369 39 := by unfold smallValid; decide +kernel

private theorem sp19408 : smallValid 19408 39 := by unfold smallValid; decide +kernel

private theorem sp19447 : smallValid 19447 39 := by unfold smallValid; decide +kernel

private theorem sp19486 : smallValid 19486 39 := by unfold smallValid; decide +kernel

private theorem sp19525 : smallValid 19525 39 := by unfold smallValid; decide +kernel

private theorem sp19564 : smallValid 19564 38 := by unfold smallValid; decide +kernel

private theorem sp19602 : smallValid 19602 39 := by unfold smallValid; decide +kernel

private theorem sp19641 : smallValid 19641 39 := by unfold smallValid; decide +kernel

private theorem sp19680 : smallValid 19680 39 := by unfold smallValid; decide +kernel

private theorem sp19719 : smallValid 19719 39 := by unfold smallValid; decide +kernel

private theorem sp19758 : smallValid 19758 39 := by unfold smallValid; decide +kernel

private theorem sp19797 : smallValid 19797 39 := by unfold smallValid; decide +kernel

private theorem sp19836 : smallValid 19836 39 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤19874) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 19875 := (joinSmall (lo:=0) (a:=9937) (b:=9938) (joinSmall (lo:=0) (a:=4968) (b:=4969) (joinSmall (lo:=0) (a:=2484) (b:=2484) (joinSmall (lo:=0) (a:=1242) (b:=1242) (joinSmall (lo:=0) (a:=621) (b:=621) (joinSmall (lo:=0) (a:=310) (b:=311) (joinSmall (lo:=0) (a:=155) (b:=155) (joinSmall (lo:=0) (a:=77) (b:=78) (joinSmall (lo:=0) (a:=38) (b:=39) sp0 sp38) (joinSmall (lo:=77) (a:=39) (b:=39) sp77 sp116)) (joinSmall (lo:=155) (a:=77) (b:=78) (joinSmall (lo:=155) (a:=38) (b:=39) sp155 sp193) (joinSmall (lo:=232) (a:=39) (b:=39) sp232 sp271))) (joinSmall (lo:=310) (a:=155) (b:=156) (joinSmall (lo:=310) (a:=77) (b:=78) (joinSmall (lo:=310) (a:=38) (b:=39) sp310 sp348) (joinSmall (lo:=387) (a:=39) (b:=39) sp387 sp426)) (joinSmall (lo:=465) (a:=78) (b:=78) (joinSmall (lo:=465) (a:=39) (b:=39) sp465 sp504) (joinSmall (lo:=543) (a:=39) (b:=39) sp543 sp582)))) (joinSmall (lo:=621) (a:=310) (b:=311) (joinSmall (lo:=621) (a:=155) (b:=155) (joinSmall (lo:=621) (a:=77) (b:=78) (joinSmall (lo:=621) (a:=38) (b:=39) sp621 sp659) (joinSmall (lo:=698) (a:=39) (b:=39) sp698 sp737)) (joinSmall (lo:=776) (a:=77) (b:=78) (joinSmall (lo:=776) (a:=38) (b:=39) sp776 sp814) (joinSmall (lo:=853) (a:=39) (b:=39) sp853 sp892))) (joinSmall (lo:=931) (a:=155) (b:=156) (joinSmall (lo:=931) (a:=77) (b:=78) (joinSmall (lo:=931) (a:=38) (b:=39) sp931 sp969) (joinSmall (lo:=1008) (a:=39) (b:=39) sp1008 sp1047)) (joinSmall (lo:=1086) (a:=78) (b:=78) (joinSmall (lo:=1086) (a:=39) (b:=39) sp1086 sp1125) (joinSmall (lo:=1164) (a:=39) (b:=39) sp1164 sp1203))))) (joinSmall (lo:=1242) (a:=621) (b:=621) (joinSmall (lo:=1242) (a:=310) (b:=311) (joinSmall (lo:=1242) (a:=155) (b:=155) (joinSmall (lo:=1242) (a:=77) (b:=78) (joinSmall (lo:=1242) (a:=38) (b:=39) sp1242 sp1280) (joinSmall (lo:=1319) (a:=39) (b:=39) sp1319 sp1358)) (joinSmall (lo:=1397) (a:=77) (b:=78) (joinSmall (lo:=1397) (a:=38) (b:=39) sp1397 sp1435) (joinSmall (lo:=1474) (a:=39) (b:=39) sp1474 sp1513))) (joinSmall (lo:=1552) (a:=155) (b:=156) (joinSmall (lo:=1552) (a:=77) (b:=78) (joinSmall (lo:=1552) (a:=38) (b:=39) sp1552 sp1590) (joinSmall (lo:=1629) (a:=39) (b:=39) sp1629 sp1668)) (joinSmall (lo:=1707) (a:=78) (b:=78) (joinSmall (lo:=1707) (a:=39) (b:=39) sp1707 sp1746) (joinSmall (lo:=1785) (a:=39) (b:=39) sp1785 sp1824)))) (joinSmall (lo:=1863) (a:=310) (b:=311) (joinSmall (lo:=1863) (a:=155) (b:=155) (joinSmall (lo:=1863) (a:=77) (b:=78) (joinSmall (lo:=1863) (a:=38) (b:=39) sp1863 sp1901) (joinSmall (lo:=1940) (a:=39) (b:=39) sp1940 sp1979)) (joinSmall (lo:=2018) (a:=77) (b:=78) (joinSmall (lo:=2018) (a:=38) (b:=39) sp2018 sp2056) (joinSmall (lo:=2095) (a:=39) (b:=39) sp2095 sp2134))) (joinSmall (lo:=2173) (a:=155) (b:=156) (joinSmall (lo:=2173) (a:=77) (b:=78) (joinSmall (lo:=2173) (a:=38) (b:=39) sp2173 sp2211) (joinSmall (lo:=2250) (a:=39) (b:=39) sp2250 sp2289)) (joinSmall (lo:=2328) (a:=78) (b:=78) (joinSmall (lo:=2328) (a:=39) (b:=39) sp2328 sp2367) (joinSmall (lo:=2406) (a:=39) (b:=39) sp2406 sp2445)))))) (joinSmall (lo:=2484) (a:=1242) (b:=1242) (joinSmall (lo:=2484) (a:=621) (b:=621) (joinSmall (lo:=2484) (a:=310) (b:=311) (joinSmall (lo:=2484) (a:=155) (b:=155) (joinSmall (lo:=2484) (a:=77) (b:=78) (joinSmall (lo:=2484) (a:=38) (b:=39) sp2484 sp2522) (joinSmall (lo:=2561) (a:=39) (b:=39) sp2561 sp2600)) (joinSmall (lo:=2639) (a:=77) (b:=78) (joinSmall (lo:=2639) (a:=38) (b:=39) sp2639 sp2677) (joinSmall (lo:=2716) (a:=39) (b:=39) sp2716 sp2755))) (joinSmall (lo:=2794) (a:=155) (b:=156) (joinSmall (lo:=2794) (a:=77) (b:=78) (joinSmall (lo:=2794) (a:=38) (b:=39) sp2794 sp2832) (joinSmall (lo:=2871) (a:=39) (b:=39) sp2871 sp2910)) (joinSmall (lo:=2949) (a:=78) (b:=78) (joinSmall (lo:=2949) (a:=39) (b:=39) sp2949 sp2988) (joinSmall (lo:=3027) (a:=39) (b:=39) sp3027 sp3066)))) (joinSmall (lo:=3105) (a:=310) (b:=311) (joinSmall (lo:=3105) (a:=155) (b:=155) (joinSmall (lo:=3105) (a:=77) (b:=78) (joinSmall (lo:=3105) (a:=38) (b:=39) sp3105 sp3143) (joinSmall (lo:=3182) (a:=39) (b:=39) sp3182 sp3221)) (joinSmall (lo:=3260) (a:=77) (b:=78) (joinSmall (lo:=3260) (a:=38) (b:=39) sp3260 sp3298) (joinSmall (lo:=3337) (a:=39) (b:=39) sp3337 sp3376))) (joinSmall (lo:=3415) (a:=155) (b:=156) (joinSmall (lo:=3415) (a:=77) (b:=78) (joinSmall (lo:=3415) (a:=38) (b:=39) sp3415 sp3453) (joinSmall (lo:=3492) (a:=39) (b:=39) sp3492 sp3531)) (joinSmall (lo:=3570) (a:=78) (b:=78) (joinSmall (lo:=3570) (a:=39) (b:=39) sp3570 sp3609) (joinSmall (lo:=3648) (a:=39) (b:=39) sp3648 sp3687))))) (joinSmall (lo:=3726) (a:=621) (b:=621) (joinSmall (lo:=3726) (a:=310) (b:=311) (joinSmall (lo:=3726) (a:=155) (b:=155) (joinSmall (lo:=3726) (a:=77) (b:=78) (joinSmall (lo:=3726) (a:=38) (b:=39) sp3726 sp3764) (joinSmall (lo:=3803) (a:=39) (b:=39) sp3803 sp3842)) (joinSmall (lo:=3881) (a:=77) (b:=78) (joinSmall (lo:=3881) (a:=38) (b:=39) sp3881 sp3919) (joinSmall (lo:=3958) (a:=39) (b:=39) sp3958 sp3997))) (joinSmall (lo:=4036) (a:=155) (b:=156) (joinSmall (lo:=4036) (a:=77) (b:=78) (joinSmall (lo:=4036) (a:=38) (b:=39) sp4036 sp4074) (joinSmall (lo:=4113) (a:=39) (b:=39) sp4113 sp4152)) (joinSmall (lo:=4191) (a:=78) (b:=78) (joinSmall (lo:=4191) (a:=39) (b:=39) sp4191 sp4230) (joinSmall (lo:=4269) (a:=39) (b:=39) sp4269 sp4308)))) (joinSmall (lo:=4347) (a:=310) (b:=311) (joinSmall (lo:=4347) (a:=155) (b:=155) (joinSmall (lo:=4347) (a:=77) (b:=78) (joinSmall (lo:=4347) (a:=38) (b:=39) sp4347 sp4385) (joinSmall (lo:=4424) (a:=39) (b:=39) sp4424 sp4463)) (joinSmall (lo:=4502) (a:=77) (b:=78) (joinSmall (lo:=4502) (a:=38) (b:=39) sp4502 sp4540) (joinSmall (lo:=4579) (a:=39) (b:=39) sp4579 sp4618))) (joinSmall (lo:=4657) (a:=155) (b:=156) (joinSmall (lo:=4657) (a:=77) (b:=78) (joinSmall (lo:=4657) (a:=38) (b:=39) sp4657 sp4695) (joinSmall (lo:=4734) (a:=39) (b:=39) sp4734 sp4773)) (joinSmall (lo:=4812) (a:=78) (b:=78) (joinSmall (lo:=4812) (a:=39) (b:=39) sp4812 sp4851) (joinSmall (lo:=4890) (a:=39) (b:=39) sp4890 sp4929))))))) (joinSmall (lo:=4968) (a:=2484) (b:=2485) (joinSmall (lo:=4968) (a:=1242) (b:=1242) (joinSmall (lo:=4968) (a:=621) (b:=621) (joinSmall (lo:=4968) (a:=310) (b:=311) (joinSmall (lo:=4968) (a:=155) (b:=155) (joinSmall (lo:=4968) (a:=77) (b:=78) (joinSmall (lo:=4968) (a:=38) (b:=39) sp4968 sp5006) (joinSmall (lo:=5045) (a:=39) (b:=39) sp5045 sp5084)) (joinSmall (lo:=5123) (a:=77) (b:=78) (joinSmall (lo:=5123) (a:=38) (b:=39) sp5123 sp5161) (joinSmall (lo:=5200) (a:=39) (b:=39) sp5200 sp5239))) (joinSmall (lo:=5278) (a:=155) (b:=156) (joinSmall (lo:=5278) (a:=77) (b:=78) (joinSmall (lo:=5278) (a:=38) (b:=39) sp5278 sp5316) (joinSmall (lo:=5355) (a:=39) (b:=39) sp5355 sp5394)) (joinSmall (lo:=5433) (a:=78) (b:=78) (joinSmall (lo:=5433) (a:=39) (b:=39) sp5433 sp5472) (joinSmall (lo:=5511) (a:=39) (b:=39) sp5511 sp5550)))) (joinSmall (lo:=5589) (a:=310) (b:=311) (joinSmall (lo:=5589) (a:=155) (b:=155) (joinSmall (lo:=5589) (a:=77) (b:=78) (joinSmall (lo:=5589) (a:=38) (b:=39) sp5589 sp5627) (joinSmall (lo:=5666) (a:=39) (b:=39) sp5666 sp5705)) (joinSmall (lo:=5744) (a:=77) (b:=78) (joinSmall (lo:=5744) (a:=38) (b:=39) sp5744 sp5782) (joinSmall (lo:=5821) (a:=39) (b:=39) sp5821 sp5860))) (joinSmall (lo:=5899) (a:=155) (b:=156) (joinSmall (lo:=5899) (a:=77) (b:=78) (joinSmall (lo:=5899) (a:=38) (b:=39) sp5899 sp5937) (joinSmall (lo:=5976) (a:=39) (b:=39) sp5976 sp6015)) (joinSmall (lo:=6054) (a:=78) (b:=78) (joinSmall (lo:=6054) (a:=39) (b:=39) sp6054 sp6093) (joinSmall (lo:=6132) (a:=39) (b:=39) sp6132 sp6171))))) (joinSmall (lo:=6210) (a:=621) (b:=621) (joinSmall (lo:=6210) (a:=310) (b:=311) (joinSmall (lo:=6210) (a:=155) (b:=155) (joinSmall (lo:=6210) (a:=77) (b:=78) (joinSmall (lo:=6210) (a:=38) (b:=39) sp6210 sp6248) (joinSmall (lo:=6287) (a:=39) (b:=39) sp6287 sp6326)) (joinSmall (lo:=6365) (a:=77) (b:=78) (joinSmall (lo:=6365) (a:=38) (b:=39) sp6365 sp6403) (joinSmall (lo:=6442) (a:=39) (b:=39) sp6442 sp6481))) (joinSmall (lo:=6520) (a:=155) (b:=156) (joinSmall (lo:=6520) (a:=77) (b:=78) (joinSmall (lo:=6520) (a:=38) (b:=39) sp6520 sp6558) (joinSmall (lo:=6597) (a:=39) (b:=39) sp6597 sp6636)) (joinSmall (lo:=6675) (a:=78) (b:=78) (joinSmall (lo:=6675) (a:=39) (b:=39) sp6675 sp6714) (joinSmall (lo:=6753) (a:=39) (b:=39) sp6753 sp6792)))) (joinSmall (lo:=6831) (a:=310) (b:=311) (joinSmall (lo:=6831) (a:=155) (b:=155) (joinSmall (lo:=6831) (a:=77) (b:=78) (joinSmall (lo:=6831) (a:=38) (b:=39) sp6831 sp6869) (joinSmall (lo:=6908) (a:=39) (b:=39) sp6908 sp6947)) (joinSmall (lo:=6986) (a:=77) (b:=78) (joinSmall (lo:=6986) (a:=38) (b:=39) sp6986 sp7024) (joinSmall (lo:=7063) (a:=39) (b:=39) sp7063 sp7102))) (joinSmall (lo:=7141) (a:=155) (b:=156) (joinSmall (lo:=7141) (a:=77) (b:=78) (joinSmall (lo:=7141) (a:=38) (b:=39) sp7141 sp7179) (joinSmall (lo:=7218) (a:=39) (b:=39) sp7218 sp7257)) (joinSmall (lo:=7296) (a:=78) (b:=78) (joinSmall (lo:=7296) (a:=39) (b:=39) sp7296 sp7335) (joinSmall (lo:=7374) (a:=39) (b:=39) sp7374 sp7413)))))) (joinSmall (lo:=7452) (a:=1242) (b:=1243) (joinSmall (lo:=7452) (a:=621) (b:=621) (joinSmall (lo:=7452) (a:=310) (b:=311) (joinSmall (lo:=7452) (a:=155) (b:=155) (joinSmall (lo:=7452) (a:=77) (b:=78) (joinSmall (lo:=7452) (a:=38) (b:=39) sp7452 sp7490) (joinSmall (lo:=7529) (a:=39) (b:=39) sp7529 sp7568)) (joinSmall (lo:=7607) (a:=77) (b:=78) (joinSmall (lo:=7607) (a:=38) (b:=39) sp7607 sp7645) (joinSmall (lo:=7684) (a:=39) (b:=39) sp7684 sp7723))) (joinSmall (lo:=7762) (a:=155) (b:=156) (joinSmall (lo:=7762) (a:=77) (b:=78) (joinSmall (lo:=7762) (a:=38) (b:=39) sp7762 sp7800) (joinSmall (lo:=7839) (a:=39) (b:=39) sp7839 sp7878)) (joinSmall (lo:=7917) (a:=78) (b:=78) (joinSmall (lo:=7917) (a:=39) (b:=39) sp7917 sp7956) (joinSmall (lo:=7995) (a:=39) (b:=39) sp7995 sp8034)))) (joinSmall (lo:=8073) (a:=310) (b:=311) (joinSmall (lo:=8073) (a:=155) (b:=155) (joinSmall (lo:=8073) (a:=77) (b:=78) (joinSmall (lo:=8073) (a:=38) (b:=39) sp8073 sp8111) (joinSmall (lo:=8150) (a:=39) (b:=39) sp8150 sp8189)) (joinSmall (lo:=8228) (a:=77) (b:=78) (joinSmall (lo:=8228) (a:=38) (b:=39) sp8228 sp8266) (joinSmall (lo:=8305) (a:=39) (b:=39) sp8305 sp8344))) (joinSmall (lo:=8383) (a:=155) (b:=156) (joinSmall (lo:=8383) (a:=77) (b:=78) (joinSmall (lo:=8383) (a:=38) (b:=39) sp8383 sp8421) (joinSmall (lo:=8460) (a:=39) (b:=39) sp8460 sp8499)) (joinSmall (lo:=8538) (a:=78) (b:=78) (joinSmall (lo:=8538) (a:=39) (b:=39) sp8538 sp8577) (joinSmall (lo:=8616) (a:=39) (b:=39) sp8616 sp8655))))) (joinSmall (lo:=8694) (a:=621) (b:=622) (joinSmall (lo:=8694) (a:=310) (b:=311) (joinSmall (lo:=8694) (a:=155) (b:=155) (joinSmall (lo:=8694) (a:=77) (b:=78) (joinSmall (lo:=8694) (a:=38) (b:=39) sp8694 sp8732) (joinSmall (lo:=8771) (a:=39) (b:=39) sp8771 sp8810)) (joinSmall (lo:=8849) (a:=77) (b:=78) (joinSmall (lo:=8849) (a:=38) (b:=39) sp8849 sp8887) (joinSmall (lo:=8926) (a:=39) (b:=39) sp8926 sp8965))) (joinSmall (lo:=9004) (a:=155) (b:=156) (joinSmall (lo:=9004) (a:=77) (b:=78) (joinSmall (lo:=9004) (a:=38) (b:=39) sp9004 sp9042) (joinSmall (lo:=9081) (a:=39) (b:=39) sp9081 sp9120)) (joinSmall (lo:=9159) (a:=78) (b:=78) (joinSmall (lo:=9159) (a:=39) (b:=39) sp9159 sp9198) (joinSmall (lo:=9237) (a:=39) (b:=39) sp9237 sp9276)))) (joinSmall (lo:=9315) (a:=311) (b:=311) (joinSmall (lo:=9315) (a:=155) (b:=156) (joinSmall (lo:=9315) (a:=77) (b:=78) (joinSmall (lo:=9315) (a:=38) (b:=39) sp9315 sp9353) (joinSmall (lo:=9392) (a:=39) (b:=39) sp9392 sp9431)) (joinSmall (lo:=9470) (a:=78) (b:=78) (joinSmall (lo:=9470) (a:=39) (b:=39) sp9470 sp9509) (joinSmall (lo:=9548) (a:=39) (b:=39) sp9548 sp9587))) (joinSmall (lo:=9626) (a:=155) (b:=156) (joinSmall (lo:=9626) (a:=77) (b:=78) (joinSmall (lo:=9626) (a:=38) (b:=39) sp9626 sp9664) (joinSmall (lo:=9703) (a:=39) (b:=39) sp9703 sp9742)) (joinSmall (lo:=9781) (a:=78) (b:=78) (joinSmall (lo:=9781) (a:=39) (b:=39) sp9781 sp9820) (joinSmall (lo:=9859) (a:=39) (b:=39) sp9859 sp9898)))))))) (joinSmall (lo:=9937) (a:=4969) (b:=4969) (joinSmall (lo:=9937) (a:=2484) (b:=2485) (joinSmall (lo:=9937) (a:=1242) (b:=1242) (joinSmall (lo:=9937) (a:=621) (b:=621) (joinSmall (lo:=9937) (a:=310) (b:=311) (joinSmall (lo:=9937) (a:=155) (b:=155) (joinSmall (lo:=9937) (a:=77) (b:=78) (joinSmall (lo:=9937) (a:=38) (b:=39) sp9937 sp9975) (joinSmall (lo:=10014) (a:=39) (b:=39) sp10014 sp10053)) (joinSmall (lo:=10092) (a:=77) (b:=78) (joinSmall (lo:=10092) (a:=38) (b:=39) sp10092 sp10130) (joinSmall (lo:=10169) (a:=39) (b:=39) sp10169 sp10208))) (joinSmall (lo:=10247) (a:=155) (b:=156) (joinSmall (lo:=10247) (a:=77) (b:=78) (joinSmall (lo:=10247) (a:=38) (b:=39) sp10247 sp10285) (joinSmall (lo:=10324) (a:=39) (b:=39) sp10324 sp10363)) (joinSmall (lo:=10402) (a:=78) (b:=78) (joinSmall (lo:=10402) (a:=39) (b:=39) sp10402 sp10441) (joinSmall (lo:=10480) (a:=39) (b:=39) sp10480 sp10519)))) (joinSmall (lo:=10558) (a:=310) (b:=311) (joinSmall (lo:=10558) (a:=155) (b:=155) (joinSmall (lo:=10558) (a:=77) (b:=78) (joinSmall (lo:=10558) (a:=38) (b:=39) sp10558 sp10596) (joinSmall (lo:=10635) (a:=39) (b:=39) sp10635 sp10674)) (joinSmall (lo:=10713) (a:=77) (b:=78) (joinSmall (lo:=10713) (a:=38) (b:=39) sp10713 sp10751) (joinSmall (lo:=10790) (a:=39) (b:=39) sp10790 sp10829))) (joinSmall (lo:=10868) (a:=155) (b:=156) (joinSmall (lo:=10868) (a:=77) (b:=78) (joinSmall (lo:=10868) (a:=38) (b:=39) sp10868 sp10906) (joinSmall (lo:=10945) (a:=39) (b:=39) sp10945 sp10984)) (joinSmall (lo:=11023) (a:=78) (b:=78) (joinSmall (lo:=11023) (a:=39) (b:=39) sp11023 sp11062) (joinSmall (lo:=11101) (a:=39) (b:=39) sp11101 sp11140))))) (joinSmall (lo:=11179) (a:=621) (b:=621) (joinSmall (lo:=11179) (a:=310) (b:=311) (joinSmall (lo:=11179) (a:=155) (b:=155) (joinSmall (lo:=11179) (a:=77) (b:=78) (joinSmall (lo:=11179) (a:=38) (b:=39) sp11179 sp11217) (joinSmall (lo:=11256) (a:=39) (b:=39) sp11256 sp11295)) (joinSmall (lo:=11334) (a:=77) (b:=78) (joinSmall (lo:=11334) (a:=38) (b:=39) sp11334 sp11372) (joinSmall (lo:=11411) (a:=39) (b:=39) sp11411 sp11450))) (joinSmall (lo:=11489) (a:=155) (b:=156) (joinSmall (lo:=11489) (a:=77) (b:=78) (joinSmall (lo:=11489) (a:=38) (b:=39) sp11489 sp11527) (joinSmall (lo:=11566) (a:=39) (b:=39) sp11566 sp11605)) (joinSmall (lo:=11644) (a:=78) (b:=78) (joinSmall (lo:=11644) (a:=39) (b:=39) sp11644 sp11683) (joinSmall (lo:=11722) (a:=39) (b:=39) sp11722 sp11761)))) (joinSmall (lo:=11800) (a:=310) (b:=311) (joinSmall (lo:=11800) (a:=155) (b:=155) (joinSmall (lo:=11800) (a:=77) (b:=78) (joinSmall (lo:=11800) (a:=38) (b:=39) sp11800 sp11838) (joinSmall (lo:=11877) (a:=39) (b:=39) sp11877 sp11916)) (joinSmall (lo:=11955) (a:=77) (b:=78) (joinSmall (lo:=11955) (a:=38) (b:=39) sp11955 sp11993) (joinSmall (lo:=12032) (a:=39) (b:=39) sp12032 sp12071))) (joinSmall (lo:=12110) (a:=155) (b:=156) (joinSmall (lo:=12110) (a:=77) (b:=78) (joinSmall (lo:=12110) (a:=38) (b:=39) sp12110 sp12148) (joinSmall (lo:=12187) (a:=39) (b:=39) sp12187 sp12226)) (joinSmall (lo:=12265) (a:=78) (b:=78) (joinSmall (lo:=12265) (a:=39) (b:=39) sp12265 sp12304) (joinSmall (lo:=12343) (a:=39) (b:=39) sp12343 sp12382)))))) (joinSmall (lo:=12421) (a:=1242) (b:=1243) (joinSmall (lo:=12421) (a:=621) (b:=621) (joinSmall (lo:=12421) (a:=310) (b:=311) (joinSmall (lo:=12421) (a:=155) (b:=155) (joinSmall (lo:=12421) (a:=77) (b:=78) (joinSmall (lo:=12421) (a:=38) (b:=39) sp12421 sp12459) (joinSmall (lo:=12498) (a:=39) (b:=39) sp12498 sp12537)) (joinSmall (lo:=12576) (a:=77) (b:=78) (joinSmall (lo:=12576) (a:=38) (b:=39) sp12576 sp12614) (joinSmall (lo:=12653) (a:=39) (b:=39) sp12653 sp12692))) (joinSmall (lo:=12731) (a:=155) (b:=156) (joinSmall (lo:=12731) (a:=77) (b:=78) (joinSmall (lo:=12731) (a:=38) (b:=39) sp12731 sp12769) (joinSmall (lo:=12808) (a:=39) (b:=39) sp12808 sp12847)) (joinSmall (lo:=12886) (a:=78) (b:=78) (joinSmall (lo:=12886) (a:=39) (b:=39) sp12886 sp12925) (joinSmall (lo:=12964) (a:=39) (b:=39) sp12964 sp13003)))) (joinSmall (lo:=13042) (a:=310) (b:=311) (joinSmall (lo:=13042) (a:=155) (b:=155) (joinSmall (lo:=13042) (a:=77) (b:=78) (joinSmall (lo:=13042) (a:=38) (b:=39) sp13042 sp13080) (joinSmall (lo:=13119) (a:=39) (b:=39) sp13119 sp13158)) (joinSmall (lo:=13197) (a:=77) (b:=78) (joinSmall (lo:=13197) (a:=38) (b:=39) sp13197 sp13235) (joinSmall (lo:=13274) (a:=39) (b:=39) sp13274 sp13313))) (joinSmall (lo:=13352) (a:=155) (b:=156) (joinSmall (lo:=13352) (a:=77) (b:=78) (joinSmall (lo:=13352) (a:=38) (b:=39) sp13352 sp13390) (joinSmall (lo:=13429) (a:=39) (b:=39) sp13429 sp13468)) (joinSmall (lo:=13507) (a:=78) (b:=78) (joinSmall (lo:=13507) (a:=39) (b:=39) sp13507 sp13546) (joinSmall (lo:=13585) (a:=39) (b:=39) sp13585 sp13624))))) (joinSmall (lo:=13663) (a:=621) (b:=622) (joinSmall (lo:=13663) (a:=310) (b:=311) (joinSmall (lo:=13663) (a:=155) (b:=155) (joinSmall (lo:=13663) (a:=77) (b:=78) (joinSmall (lo:=13663) (a:=38) (b:=39) sp13663 sp13701) (joinSmall (lo:=13740) (a:=39) (b:=39) sp13740 sp13779)) (joinSmall (lo:=13818) (a:=77) (b:=78) (joinSmall (lo:=13818) (a:=38) (b:=39) sp13818 sp13856) (joinSmall (lo:=13895) (a:=39) (b:=39) sp13895 sp13934))) (joinSmall (lo:=13973) (a:=155) (b:=156) (joinSmall (lo:=13973) (a:=77) (b:=78) (joinSmall (lo:=13973) (a:=38) (b:=39) sp13973 sp14011) (joinSmall (lo:=14050) (a:=39) (b:=39) sp14050 sp14089)) (joinSmall (lo:=14128) (a:=78) (b:=78) (joinSmall (lo:=14128) (a:=39) (b:=39) sp14128 sp14167) (joinSmall (lo:=14206) (a:=39) (b:=39) sp14206 sp14245)))) (joinSmall (lo:=14284) (a:=311) (b:=311) (joinSmall (lo:=14284) (a:=155) (b:=156) (joinSmall (lo:=14284) (a:=77) (b:=78) (joinSmall (lo:=14284) (a:=38) (b:=39) sp14284 sp14322) (joinSmall (lo:=14361) (a:=39) (b:=39) sp14361 sp14400)) (joinSmall (lo:=14439) (a:=78) (b:=78) (joinSmall (lo:=14439) (a:=39) (b:=39) sp14439 sp14478) (joinSmall (lo:=14517) (a:=39) (b:=39) sp14517 sp14556))) (joinSmall (lo:=14595) (a:=155) (b:=156) (joinSmall (lo:=14595) (a:=77) (b:=78) (joinSmall (lo:=14595) (a:=38) (b:=39) sp14595 sp14633) (joinSmall (lo:=14672) (a:=39) (b:=39) sp14672 sp14711)) (joinSmall (lo:=14750) (a:=78) (b:=78) (joinSmall (lo:=14750) (a:=39) (b:=39) sp14750 sp14789) (joinSmall (lo:=14828) (a:=39) (b:=39) sp14828 sp14867))))))) (joinSmall (lo:=14906) (a:=2484) (b:=2485) (joinSmall (lo:=14906) (a:=1242) (b:=1242) (joinSmall (lo:=14906) (a:=621) (b:=621) (joinSmall (lo:=14906) (a:=310) (b:=311) (joinSmall (lo:=14906) (a:=155) (b:=155) (joinSmall (lo:=14906) (a:=77) (b:=78) (joinSmall (lo:=14906) (a:=38) (b:=39) sp14906 sp14944) (joinSmall (lo:=14983) (a:=39) (b:=39) sp14983 sp15022)) (joinSmall (lo:=15061) (a:=77) (b:=78) (joinSmall (lo:=15061) (a:=38) (b:=39) sp15061 sp15099) (joinSmall (lo:=15138) (a:=39) (b:=39) sp15138 sp15177))) (joinSmall (lo:=15216) (a:=155) (b:=156) (joinSmall (lo:=15216) (a:=77) (b:=78) (joinSmall (lo:=15216) (a:=38) (b:=39) sp15216 sp15254) (joinSmall (lo:=15293) (a:=39) (b:=39) sp15293 sp15332)) (joinSmall (lo:=15371) (a:=78) (b:=78) (joinSmall (lo:=15371) (a:=39) (b:=39) sp15371 sp15410) (joinSmall (lo:=15449) (a:=39) (b:=39) sp15449 sp15488)))) (joinSmall (lo:=15527) (a:=310) (b:=311) (joinSmall (lo:=15527) (a:=155) (b:=155) (joinSmall (lo:=15527) (a:=77) (b:=78) (joinSmall (lo:=15527) (a:=38) (b:=39) sp15527 sp15565) (joinSmall (lo:=15604) (a:=39) (b:=39) sp15604 sp15643)) (joinSmall (lo:=15682) (a:=77) (b:=78) (joinSmall (lo:=15682) (a:=38) (b:=39) sp15682 sp15720) (joinSmall (lo:=15759) (a:=39) (b:=39) sp15759 sp15798))) (joinSmall (lo:=15837) (a:=155) (b:=156) (joinSmall (lo:=15837) (a:=77) (b:=78) (joinSmall (lo:=15837) (a:=38) (b:=39) sp15837 sp15875) (joinSmall (lo:=15914) (a:=39) (b:=39) sp15914 sp15953)) (joinSmall (lo:=15992) (a:=78) (b:=78) (joinSmall (lo:=15992) (a:=39) (b:=39) sp15992 sp16031) (joinSmall (lo:=16070) (a:=39) (b:=39) sp16070 sp16109))))) (joinSmall (lo:=16148) (a:=621) (b:=621) (joinSmall (lo:=16148) (a:=310) (b:=311) (joinSmall (lo:=16148) (a:=155) (b:=155) (joinSmall (lo:=16148) (a:=77) (b:=78) (joinSmall (lo:=16148) (a:=38) (b:=39) sp16148 sp16186) (joinSmall (lo:=16225) (a:=39) (b:=39) sp16225 sp16264)) (joinSmall (lo:=16303) (a:=77) (b:=78) (joinSmall (lo:=16303) (a:=38) (b:=39) sp16303 sp16341) (joinSmall (lo:=16380) (a:=39) (b:=39) sp16380 sp16419))) (joinSmall (lo:=16458) (a:=155) (b:=156) (joinSmall (lo:=16458) (a:=77) (b:=78) (joinSmall (lo:=16458) (a:=38) (b:=39) sp16458 sp16496) (joinSmall (lo:=16535) (a:=39) (b:=39) sp16535 sp16574)) (joinSmall (lo:=16613) (a:=78) (b:=78) (joinSmall (lo:=16613) (a:=39) (b:=39) sp16613 sp16652) (joinSmall (lo:=16691) (a:=39) (b:=39) sp16691 sp16730)))) (joinSmall (lo:=16769) (a:=310) (b:=311) (joinSmall (lo:=16769) (a:=155) (b:=155) (joinSmall (lo:=16769) (a:=77) (b:=78) (joinSmall (lo:=16769) (a:=38) (b:=39) sp16769 sp16807) (joinSmall (lo:=16846) (a:=39) (b:=39) sp16846 sp16885)) (joinSmall (lo:=16924) (a:=77) (b:=78) (joinSmall (lo:=16924) (a:=38) (b:=39) sp16924 sp16962) (joinSmall (lo:=17001) (a:=39) (b:=39) sp17001 sp17040))) (joinSmall (lo:=17079) (a:=155) (b:=156) (joinSmall (lo:=17079) (a:=77) (b:=78) (joinSmall (lo:=17079) (a:=38) (b:=39) sp17079 sp17117) (joinSmall (lo:=17156) (a:=39) (b:=39) sp17156 sp17195)) (joinSmall (lo:=17234) (a:=78) (b:=78) (joinSmall (lo:=17234) (a:=39) (b:=39) sp17234 sp17273) (joinSmall (lo:=17312) (a:=39) (b:=39) sp17312 sp17351)))))) (joinSmall (lo:=17390) (a:=1242) (b:=1243) (joinSmall (lo:=17390) (a:=621) (b:=621) (joinSmall (lo:=17390) (a:=310) (b:=311) (joinSmall (lo:=17390) (a:=155) (b:=155) (joinSmall (lo:=17390) (a:=77) (b:=78) (joinSmall (lo:=17390) (a:=38) (b:=39) sp17390 sp17428) (joinSmall (lo:=17467) (a:=39) (b:=39) sp17467 sp17506)) (joinSmall (lo:=17545) (a:=77) (b:=78) (joinSmall (lo:=17545) (a:=38) (b:=39) sp17545 sp17583) (joinSmall (lo:=17622) (a:=39) (b:=39) sp17622 sp17661))) (joinSmall (lo:=17700) (a:=155) (b:=156) (joinSmall (lo:=17700) (a:=77) (b:=78) (joinSmall (lo:=17700) (a:=38) (b:=39) sp17700 sp17738) (joinSmall (lo:=17777) (a:=39) (b:=39) sp17777 sp17816)) (joinSmall (lo:=17855) (a:=78) (b:=78) (joinSmall (lo:=17855) (a:=39) (b:=39) sp17855 sp17894) (joinSmall (lo:=17933) (a:=39) (b:=39) sp17933 sp17972)))) (joinSmall (lo:=18011) (a:=310) (b:=311) (joinSmall (lo:=18011) (a:=155) (b:=155) (joinSmall (lo:=18011) (a:=77) (b:=78) (joinSmall (lo:=18011) (a:=38) (b:=39) sp18011 sp18049) (joinSmall (lo:=18088) (a:=39) (b:=39) sp18088 sp18127)) (joinSmall (lo:=18166) (a:=77) (b:=78) (joinSmall (lo:=18166) (a:=38) (b:=39) sp18166 sp18204) (joinSmall (lo:=18243) (a:=39) (b:=39) sp18243 sp18282))) (joinSmall (lo:=18321) (a:=155) (b:=156) (joinSmall (lo:=18321) (a:=77) (b:=78) (joinSmall (lo:=18321) (a:=38) (b:=39) sp18321 sp18359) (joinSmall (lo:=18398) (a:=39) (b:=39) sp18398 sp18437)) (joinSmall (lo:=18476) (a:=78) (b:=78) (joinSmall (lo:=18476) (a:=39) (b:=39) sp18476 sp18515) (joinSmall (lo:=18554) (a:=39) (b:=39) sp18554 sp18593))))) (joinSmall (lo:=18632) (a:=621) (b:=622) (joinSmall (lo:=18632) (a:=310) (b:=311) (joinSmall (lo:=18632) (a:=155) (b:=155) (joinSmall (lo:=18632) (a:=77) (b:=78) (joinSmall (lo:=18632) (a:=38) (b:=39) sp18632 sp18670) (joinSmall (lo:=18709) (a:=39) (b:=39) sp18709 sp18748)) (joinSmall (lo:=18787) (a:=77) (b:=78) (joinSmall (lo:=18787) (a:=38) (b:=39) sp18787 sp18825) (joinSmall (lo:=18864) (a:=39) (b:=39) sp18864 sp18903))) (joinSmall (lo:=18942) (a:=155) (b:=156) (joinSmall (lo:=18942) (a:=77) (b:=78) (joinSmall (lo:=18942) (a:=38) (b:=39) sp18942 sp18980) (joinSmall (lo:=19019) (a:=39) (b:=39) sp19019 sp19058)) (joinSmall (lo:=19097) (a:=78) (b:=78) (joinSmall (lo:=19097) (a:=39) (b:=39) sp19097 sp19136) (joinSmall (lo:=19175) (a:=39) (b:=39) sp19175 sp19214)))) (joinSmall (lo:=19253) (a:=311) (b:=311) (joinSmall (lo:=19253) (a:=155) (b:=156) (joinSmall (lo:=19253) (a:=77) (b:=78) (joinSmall (lo:=19253) (a:=38) (b:=39) sp19253 sp19291) (joinSmall (lo:=19330) (a:=39) (b:=39) sp19330 sp19369)) (joinSmall (lo:=19408) (a:=78) (b:=78) (joinSmall (lo:=19408) (a:=39) (b:=39) sp19408 sp19447) (joinSmall (lo:=19486) (a:=39) (b:=39) sp19486 sp19525))) (joinSmall (lo:=19564) (a:=155) (b:=156) (joinSmall (lo:=19564) (a:=77) (b:=78) (joinSmall (lo:=19564) (a:=38) (b:=39) sp19564 sp19602) (joinSmall (lo:=19641) (a:=39) (b:=39) sp19641 sp19680)) (joinSmall (lo:=19719) (a:=78) (b:=78) (joinSmall (lo:=19719) (a:=39) (b:=39) sp19719 sp19758) (joinSmall (lo:=19797) (a:=39) (b:=39) sp19797 sp19836)))))))))
  have good : (List.range 19875).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 395000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 19874 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 19874 := by
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


private def packet (i : ℕ) : ℕ := (if i < 100 then (if i < 50 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 10 then 0 else (if i < 11 then 0 else 0)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0 else (if i < 14 then 0 else 0)) else (if i < 16 then 0 else (if i < 17 then 0 else 0))) else (if i < 21 then (if i < 19 then 0 else (if i < 20 then 0 else 0)) else (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else 0))))) else (if i < 37 then (if i < 31 then (if i < 28 then (if i < 26 then 0 else (if i < 27 then 0 else 0)) else (if i < 29 then 0 else (if i < 30 then 0 else 0))) else (if i < 34 then (if i < 32 then 0 else (if i < 33 then 0 else 0)) else (if i < 35 then 0 else (if i < 36 then 0 else 0)))) else (if i < 43 then (if i < 40 then (if i < 38 then 0 else (if i < 39 then 0 else 0)) else (if i < 41 then 0 else (if i < 42 then 0 else 0))) else (if i < 46 then (if i < 44 then 0 else (if i < 45 then 0 else 0)) else (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else 0)))))) else (if i < 75 then (if i < 62 then (if i < 56 then (if i < 53 then (if i < 51 then 0 else (if i < 52 then 0 else 0)) else (if i < 54 then 0 else (if i < 55 then 0 else 0))) else (if i < 59 then (if i < 57 then 0 else (if i < 58 then 0 else 0)) else (if i < 60 then 0 else (if i < 61 then 0 else 0)))) else (if i < 68 then (if i < 65 then (if i < 63 then 0 else (if i < 64 then 0 else 0)) else (if i < 66 then 0 else (if i < 67 then 0 else 0))) else (if i < 71 then (if i < 69 then 0 else (if i < 70 then 0 else 0)) else (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else 0))))) else (if i < 87 then (if i < 81 then (if i < 78 then (if i < 76 then 0 else (if i < 77 then 0 else 0)) else (if i < 79 then 0 else (if i < 80 then 0 else 0))) else (if i < 84 then (if i < 82 then 0 else (if i < 83 then 0 else 0)) else (if i < 85 then 0 else (if i < 86 then 0 else 0)))) else (if i < 93 then (if i < 90 then (if i < 88 then 0 else (if i < 89 then 0 else 0)) else (if i < 91 then 0 else (if i < 92 then 0 else 0))) else (if i < 96 then (if i < 94 then 0 else (if i < 95 then 0 else 0)) else (if i < 98 then (if i < 97 then 0 else 0) else (if i < 99 then 0 else 0))))))) else (if i < 150 then (if i < 125 then (if i < 112 then (if i < 106 then (if i < 103 then (if i < 101 then 0 else (if i < 102 then 0 else 0)) else (if i < 104 then 0 else (if i < 105 then 0 else 0))) else (if i < 109 then (if i < 107 then 0 else (if i < 108 then 0 else 0)) else (if i < 110 then 0 else (if i < 111 then 0 else 0)))) else (if i < 118 then (if i < 115 then (if i < 113 then 0 else (if i < 114 then 0 else 0)) else (if i < 116 then 0 else (if i < 117 then 0 else 0))) else (if i < 121 then (if i < 119 then 0 else (if i < 120 then 0 else 0)) else (if i < 123 then (if i < 122 then 0 else 0) else (if i < 124 then 0 else 0))))) else (if i < 137 then (if i < 131 then (if i < 128 then (if i < 126 then 0 else (if i < 127 then 0 else 0)) else (if i < 129 then 0 else (if i < 130 then 0 else 0))) else (if i < 134 then (if i < 132 then 0 else (if i < 133 then 0 else 0)) else (if i < 135 then 0 else (if i < 136 then 0 else 0)))) else (if i < 143 then (if i < 140 then (if i < 138 then 0 else (if i < 139 then 0 else 0)) else (if i < 141 then 0 else (if i < 142 then 0 else 0))) else (if i < 146 then (if i < 144 then 0 else (if i < 145 then 0 else 0)) else (if i < 148 then (if i < 147 then 0 else 0) else (if i < 149 then 0 else 0)))))) else (if i < 175 then (if i < 162 then (if i < 156 then (if i < 153 then (if i < 151 then 0 else (if i < 152 then 0 else 0)) else (if i < 154 then 0 else (if i < 155 then 0 else 0))) else (if i < 159 then (if i < 157 then 0 else (if i < 158 then 0 else 0)) else (if i < 160 then 0 else (if i < 161 then 0 else 0)))) else (if i < 168 then (if i < 165 then (if i < 163 then 0 else (if i < 164 then 0 else 0)) else (if i < 166 then 0 else (if i < 167 then 0 else 0))) else (if i < 171 then (if i < 169 then 0 else (if i < 170 then 0 else 0)) else (if i < 173 then (if i < 172 then 0 else 0) else (if i < 174 then 0 else 0))))) else (if i < 188 then (if i < 181 then (if i < 178 then (if i < 176 then 0 else (if i < 177 then 0 else 0)) else (if i < 179 then 0 else (if i < 180 then 0 else 0))) else (if i < 184 then (if i < 182 then 0 else (if i < 183 then 0 else 0)) else (if i < 186 then (if i < 185 then 0 else 0) else (if i < 187 then 0 else 0)))) else (if i < 194 then (if i < 191 then (if i < 189 then 0x12f9b852c794c09ac47720e8f046c42f314c88d039617008d82e80ae000012f956e2d595009a647220a8ee06a42f614a08ec39a16e08b02c00b2000012f8f5b2d795309e449c21d0f586e231015789483e019509d03640da000012f89372e415aca0849d2228f9470831e15d09703e818509483140c6000012f83372cf15089c44842110f146ce30015189243c217108f03040cc000012f7ce92f11624a484bc2290fbc72c33115d89683e819609883340d0000012f77052c414ac99846c20b8ec46902e114908f43c0184092832c0ce000012f70f42d695409e249821e0f746ee31615909543dc19109883400d8000012f6add2df1568a0449c2198f3c6e431014f890c3b817708982c40aa000012f64ce2d295049a646b2078edc6be2fd14f88d43aa17408802dc0be000012f5eb52de15789f249c2218f9071432415e89683e418a094031c0c2000012f589c2da95709f24922180f506ea30915208ec3bc19009983400e6000012f52812dd15549cc49321b0f4c6dc30b14d08d43ac17108f82f00ba000012f4c802cc15289da4832140f146b62fb150892c3d818e09483340bc000012f464d2eb1594a0a4a32190f306ea31f16389883ee19309a03240d2000012f404f2c694c49c04712090ee46b82f714b88c03ba17808d02ec0c2000012f3a142eb95d0a264b82220f886f431615889443e418d09703140dc000012f33da2ed95c8a1a4b02248f806f831b15e8988404199099834c0be000012f2de12d014d49b247720b8ec06a62f714e08f83b417008882b80b8000012f27c22df95609e64942168f486c831415209303e019209783440de000012f21be2cd951c9d24862100ec86962e814608b03a416b08b82ec0b6000012f1bad2dd15449da48b2178f606f431d163099840c19809683200d4000012f159b2d6152c9d047f20d0ee46b230315588f83c217f08e83200b2000012f0f942d214f09c64862140f2c6de30014b08f03be18209082ec0b8000012f09852d395289dc4852110f146ba2f614f09043c617508a02cc0b6000012f03882ca94f09b248320b8eec6be30115208f83bc181092830c0ca000012efd582e615aca224ab2200f946f030c15408f83b817808b02f00c0000012ef7662c714bc9a447220a8eec6b62f514c08b83bc182093832c0d4000012ef1582d495249d848a2150f106ca30815188f43ce17e09002f80a6000012eeb7a2c114a499e4732088eb868e2e7144889c39017808f830c0c4000012ee5612db95549e64962190f2c6be30315889243c819109783440ce000012edf322e915b4a1e49e2160f106bc2f114b08f43ba180091031c0ba000012ed9232d995249d248c2150f386d830b15809643de18709102f00c8000012ed32c2ca15009be48a20e8ee86ce30514d88f03ba17e08a02c40be000012ecd282d195189d648420c8ee46a22f514d08bc3a017608382b40b2000012ec7022e095449d448a2148f1c6ce2fb15109243ce18509383200b4000012ec0e62df15609e048c2118ef86b831315b095c40819e09a03340d8000012ebadb2d5151c9c447620a0ecc69e2f114988cc3a817a08882c40a4000012eb4d22d895489ea49321c8f786ec31015388ec3b017808d02ec0c6000012eaec52d915489e44922190f4c6c830415109103d818909502fc0c6000012ea8ba2d515249c047f20e0ef86b02fb15108ec3c618309603340cc000012ea2bf2d195209d648220f8f106c230314f08fc3a817b08b03000b2000012e9cb22d395509f649a21c0f6c6dc31115609303ea18f09a83000b6000012e96aa2d094f09c04772118f086c630f15609443de18e098833c0ce000012e90902d8151c9de48d2130f186e030415889303dc18508f82f40b6000012e8a6d2e3156c9f049b2208f7470431f16289a83f619209803380da000012e84362e615b4a2c4af22c8fc071432416089783fa19509803180b2000012e7e1c2de9584a0a4ac2208f886ee31a15909243d0181094830c0c4000012e783e2bc146898245e2028ea869a2ee14808d83ac17609203080b6000012e72352da15189cc4912158f306ce30815409383dc18509102e00a8000012e6c072e79598a0e4a42228f8c70c327162098c4101a009e03440e6000012e66152cb14c49aa4662050ecc6a42f014708a039a16e08402dc0b6000012e5ff22dc15709ec4972198f346e030b15809283d218b097832c0c6000012e59e12d815549ec48b2170f4c6da30714f89003b218308f83080ca000012e53c72e0156c9fc49f21d0f806fe31a15b89303cc19909503340ca000012e4dab2e195809fa48d2148ef06c830715088c839e16f08702cc0b2000012e47642f415e0a244ad2240f7c6f231c15c092c3c818b09602c40ca000012e413f2e115aca1e4b022a8fa46fe31515b09583fc19509783240be000012e3b112e1156ca0e4b02240fa071431b15b09603e619109303040c6000012e35152d114e49c647720d0ec86a42ee14608c43b217f090031c0b8000012e2ed62f215cca204af2260fac70e32716109803fa19a09683140d8000012e28d32d095309d447e2160f506e430b14b08c43b618209203040c8000012e22cf2d495589d248f2140f006b62f914b88d43b217608802d40b2000012e1cd12c994d09ac4752050ec06ac2f714c09003c618608f82e40ba000 else (if i < 190 then 0x13120932d4950c9d049121a8f086c630315088f83ba17908e031c0b000001311a6f2df15749f04842118ee86b42fb14608b439c16708102c40a8000013114552d9953c9d248320e8f086be2ff15209283ce19109583040c000001310e322dc95449f64992190f446de31415c09703e619509983180ce0000131083b2d495449de48a21a0f546ec31515a894c3ec194098831c0b00000131021a2da95649fc49a21b0f506cc31115509183b218008c02ec0b00000130fbc82f6161ca3a4b722b0fb072633216589743d818208f83040d00000130f5982e815c8a344ab2240fcc71e33016809bc4141a50a483800ea0000130efb22c314b499847120a8ed06a42e714408b43a817708a82e40be0000130e9b12ca14bc9a647620a0ec86b42fa14f08f43b017909382ec0c40000130e3942d995409e649b2170f4c6e6314154890c3d6192098031c0d60000130dd632e695a0a104a12238f8070431c15e09643ee18808f83040c20000130d7442e11588a0c4a52218fc070832215f09503e218c09083080c60000130d1502c614bc99246e2088eac6842e014308c43a216e08982b00960000130cb2c2e69598a0449f2200f7c71c329164098040819e09983300c20000130c53b2c514a09904682068e9c69e2f214988fc3c418509283180d40000130bf1e2df9588a044942188f106d831215689503e218b09183200d60000130b9062d79560a004992220f886f230a15689103bc18109082e00b40000130b2ee2dd958ca0e4a42230f9871e32315c89643e018409803300c20000130acac2ee15d8a1c4a22228f8870032016209743fa19509583380ca0000130a6ad2cf14e89924782100f146ca30214d88d83be18609203200cc0000130a0882e515a4a064962178f486d230a15809483e219409703140c200001309a7e2d214e89ae47620e0f0c6a42f914d08e83a417d08c03180c0000013094872cf94d89b64852118f206cc30715009383d418808d03080ba00001308e642e515889f44a02200f786f431315a89103d218609402f80be0000130884d2dd957ca164a52258f9871232d16289743e419609783300ce000013082552cc15009944692060ecc6a82ef142089438816a08902a40a400001307c542cd94d09c047920d8ee469a2f714a08d03aa17a08c02e80b60000130763f2cf15009ac47120a8f186be2fd14a08e83c617909202ec0ba000013070132dd95449e248a2158f246d230315409083c818c098833c0ea00001306a0c2cf151c9c04722098ed06ac2f614b08c43c217908e02cc0c0000013063f92df9590a084aa2218fa46fe31b15609143b0177090031c0c000001305df02d315189c64822108ef86be30914f89243cc19309883280d4000013057e32d115309c64882108ed06ca31115909443d818a09583340da000013051fb2c894dc9be47c2110f306d430b15309083c017908f03280c200001304c062ce94d09b04762088eb46862ef14b88f03c217708c02fc0b8000013045d42e2158c9fe49c2200f786e830e15589243ea18e099832c0c800001303ff42bf947898845f2070ea869c2f414b08fc3c017e08a82d80b0000013039cd2dc156c9f449e21f0f5c6dc31215a09443f819a09903280d0000013033b12e395b4a064a42280f9071c336162898c3ce18b09503080b600001302da42d915609f84942150f306e031015a095c3f819b09c03540e00000130277b2df9574a184a92258fa86f4318158894c3e619a09b833c0cc000013021712d194f49be47a20b8ec06aa2f214f88f03b217f09583000aa00001301b5b2e095849f84942180f3c6d2309155892c3da18d09a02fc0ba000013015472d595209da48c2110f306dc310158092c3d017f09002d40be00001300f242e215749fc49a21d8f606e430915589143dc19109503140b0000013009122d815249cc4882100f206da30b15709103c018508d02c80a8000013002f52dc156c9e24902168f0c6b82f514a88c839616308802bc0c2000012ffce62d5150c9b84892120ed46c6308157093c3e019009703200ce000012ff6cf2d695289c447c2108f006c42ff14c89043ce18709282f40c2000012ff0c52d915789f04962228f446e431415309343d017f093033c0d0000012feacc2c794cc9a247c2130f286dc307153092c3d818208e03300d0000012fe49f2e6158ca1a4ac2260fbc70431d16109503e219409202f40c4000012fde742df15789f449921f8f9070032115e896c3de18109482e40b8000012fd86b2d815609f248f2198f786e830c156093c3d6186093833c0dc000012fd24d2e195709f84a321e0f346ca30f15a09283bc18208c02c80bc000012fcc392da15589dc49021a8f506e231815b89403d018c08d02f00ce000012fc6042e915a8a004a42230f886f031d15c89583d218609082f80c8000012fbfae2f91610a504d2234903074833a16489b43fe19709203140cc000012fb9a52cb14d89b247a2080edc6aa2f614b08e039817509202e00bc000012fb3932d895649f44912190f406ce307150891c3c618108d83040cc000012fad982cc94ec9c24832140f406ea30e15389383e819309c033c0da000012fa76d2e815dca124b22288fc870231a15689643ee19209a834c0ca000012fa17a2cc94e89b04742108ef06c030514f08f439c17708782d80ca000 else 0x132a68e2e2958ca204a82218f986fc32115f09703ec19109402fc0bc0000132a05e2e495849fa4a02200f7c6f831c15d89643ea197099033c0d200001329a6f2cc94e89ca48220c8ef46a82f314a88bc3a817108802d00c40000132944b2e395e0a344ba22f0fc471c33516289703e818209182f40d000001328e4a2d015109d648620d8ee06a22ee14908983a217308882a00aa0000132883d2cf14e89c848020a0ec469e2f714c09083d418b09783340ca000013282352d3150c9c247720a8ee06b42f0147889839017708e83100be00001327c1f2d794ec9be4862130efc6c430614d08fc3d618908f02ec0c40000132761e2d5952c9de4882130ef06ba2ff15489183d618509083100d800001326ff52e09578a0e4a521f8f806f030a15289083d418c09482f40ba000013269e82d595209d648d2138f0c6ce31115d09483d018e09302e40b6000013263d32da952c9c247b2098ee86b430414d08e03b817f09203080be00001325dc42d294ec9ae47e20e0f186d030315208fc3c418509582f40b20000132578f2e69578a024a021c0f5c6e231115a094c3e819209503300cc000013251a52be14a898445e1fc8e6c67a2e914b08f43a817908b02cc0ae00001324b46300166ca4c4c32328ff8736331164898440619809a03280c0000013245112f29614a3c4c222b900c73033216789ac41219709b83300d400001323f012db95189d047d20e8ef06a42f014708e43b417408782d40ac000013238b32ee15f0a284b12258fb471e32a16409783f018e09203580ea000013232a42de15489e44892170f306e231015889283e017f09383140ca00001322c9b2d295089c048d2150f186b82f714a88ec3be18609602f40be000013226602ef15f4a264ab2228fac70432115d09443c618109383080b00000132205e2d395189ac47b20f0ed46b02f915189243d217c08d83000c400001321a3c2d8154c9ca48b2150f146bc2fb14c88ec3bc17c09203100ca000013214292d615509d648a21b0f306da31515889583ec19309c831c0d000001320e2b2d3152c9de4952188f206c830114e88cc3b017608f83200ca000013207f32ea95cca1a4a82278fc870e31a15809503fe1a309a83280b4000013201e42da955c9da4802120f0c6ce30a153891c3da18b098031c0ba0000131fbe92cf94c49a047020c8f006bc30b15409343c017c091830c0ce0000131f5ca2de9594a184b22228f906f431315989283e018709483240ca0000131efa62e31588a004ad2260f6c6ca2ff14d08f43a217608982ec0b20000131e9902d695409e04892140f346d231315309043be17808f03040bc0000131e3492ee95c8a0c4a32248fa470431615c097c3e819109483240c20000131dd362d915449d449421d8f9c71632615b89683ea191094833c0c20000131d7092e715b0a204b42298fbc70832015b09443d618a09082ec0b20000131d1152cb14fc9ba4892140ed86b22f814f09083c417d09082ec0d20000131caca2f395d4a284ad2248f586f031515889603fc19209403200c80000131c48c2ee95c8a3a4b722c0fb072a33616a89ac40c1a709703300ca0000131be942cf950c9be47920d8ef46b42f414f09003b017909003040c00000131b85f2ea95bca264b522a8fe871a32f16709843f819109283300d40000131b24b2d715589ee4972178f586d030615789683de18e09a834c0da0000131ac462cf15049b447b2080eb46aa2f314f08f83bc18509002fc0cc0000131a6472cc14c89b247320b8ee06a62e8142888c38016708882c80a60000131a0282d795209d64872118eec6a22f0141086c38c16c08802dc0b4000013199fb2e315b4a224a621e8f786ee30c15109103e8194098831c0c2000013193bc2ed15c4a2c4a62268f7c70631715a09643ee19609a83400ce00001318d992d8954c9f449a21e0f4c6d630015508fc3c017708e83000b8000013187872dd95649fe4a62238f7c6f832116089603e819209a83100ca000013181592e795a4a104a721e8f646f030e15789403d8181096832c0d800001317b492dd15709fc4962190f446e2318158893c3d418409303280ce000013175402d495009be48d2110f186c830915008e43b417e090030c0ca00001316f462ce15049b44832128f046c430015409043c4185094830c0ca000013169332da954c9de48e2180f306de306154891c3be17608b02c40b20000131634c2be146497c46a2040eb46922f614b88f03b017908802b40a800001315d772b7144897c4622010ebc6aa2ee14688b438c17a08b02d80c0000013157882c894b099c47420a8ee06a42e714a88e43a817f08c03000ce000013151742dc95389c048120f8f0c6d430c15689383d818108b02f00be00001314b432e215b8a164b32238f9c71232416289683e218d09783100b00000131452d2d715349f04912188f406e8317156891c3ce18208e82ec0c800001313f022e315809ee49621c8f506e431215e895c3d218608f82d00ae000013138e72df95889ee49321a0f246c430a15389243c818609303300c8000013132b72e315849d84942180f546e030415089043be18509383200bc00001312ca42dd9570a0c49c21f0f646ec31d15d895c3ea18a09082e00b00000131269b2d8155c9fa49a21a8f6870832715a09603f019509502f00b2000)) else (if i < 192 then 0x1342c1d2c494d49b047320c8f086b82fc14f89003b817608982d00a6000013426102d014f49be4802118f306e431815389243ee1a009a83040b400001341fe52dd15909f449521a8f7c708325163899c40c19d09903500ec000013419e72ce95249d648e2158f146cc304151091c3ca18408f02e80b8000013413c02d9152c9e44922160f1c6d22ff14b88f43ba18409302bc0b400001340da82dc956c9ee4962238f8871632916509b04021ad0a403880dc000013407922d895589de4882110f146d42fc156893c3e018c09482f00c0000013401592e895b0a1c4b72248f9470432716109a04021aa09c83440c80000133fb562d195189d44882138f186bc30314f09103ce17e09302f80b80000133f5542cf94fc9ce47f2100f006c22fe15008e43ac17208c82fc0b40000133ef2b2e1956ca0a4a92210fa06f031215a894c3ec18909483000b40000133e91d2d795749ec4912178f0c6e230414b08d43c017d09103100b80000133e30e2d7152c9d648b20f8f106c230614f88d43be17e08f03180bc0000133dced2dd15689f04812100efc6c430015308ec3ae17808a82e00ba0000133d6d52d9154c9e248d2160f0c6c830114888cc3b817908782e80b80000133d0e92cc94e499647a20f0eec6b430115308f83ae17c08f03080d00000133cac72e41570a0a49f2250f9c71c32f15f896c3ea199099034c0dc0000133c4a42e515909f84a22240f8c70a320156890c3c618c09283240c80000133be7a2e215a89f44aa2230f9070431a155891c3be17f09583280be0000133b8672da95409e848c21a8f486cc304155090c3d018108d03040be0000133b26a2d094ec9d248a2160f2c6d430815a89343de18c093030c0d40000133ac5b2d8954c9d24842088e8c69c2e814688cc39a17b08e03080c00000133a6302e515a8a064942190f4c6e231b15809183bc18308f03000c00000133a01d2d995609f849621c8f946ea30a15108f03ac17d08582bc0ac00001339a012da15589fe49921f8f746f831315889683e618c09303340e0000013393da2e815849f448d21d0f686fa322161094c3d218009302f00bc00001338dcf2d415189c84812120f306dc30815409403bc17708d02d40ac000013387cb2ca94d49b84782100ee86ca30815789403dc18408982d40ba0000133818d2f51600a4c4c2237901072032716289b840019d09503380e600001337b972ca14c49a647120a0f146cc30614f09003d018409003200d0000013375842dd956c9da4902130f206da31115709203c818509683200b200001336f3a2f395f8a264ba22a8fd871a32916709903f619109283240c8000013369182e395789f849c2208f7c70e32a16889b83f4193092032c0c80000133630d2d695449d44892110f086cc30415289103d419409783340ca00001335cd92e995d4a204b02270fbc70e31c15b09483da19009883540d8000013356e02d115109c647f2118ef86d230e15108fc3c018709503280c6000013350ba2e795909f849621c8f5c6f831615809603ea19309202d00a800001334aa42e095489d64882148f2c6e231515a09443d418e09183000c60000133446d2ea95cca2a4b622d0fe473033016909a43fc19b096834c0dc00001333e6d2d115189d44932150f246d630e15109343d218c092030c0b80000133385a2d695249d648d2168f286bc2f414908d43bc18609703300cc000013332592d015149ac46f2030eb46b030615088e03b617808c02c80b600001332c0c2f11618a584cd2300fc071232215f09683e818f09102e40b4000013326142c894b099a47420b8ec46b22fa14d890c3d218d099031c0c40000133202a2c614a499446a2090edc6962ed14988e43ba18209383180d000001331a1e2d614f49b847120d8f046aa2f414788dc39817408982d80c80000133140d2d815389e049c2208f6c6e030215989183d018d09283040b200001330ddc2e315b4a2a4b42280fa871632216209743f419b09f03500dc000013307d72d195409da49021f0fb06ee31015709043cc17f09102f40b4000013301d62cd14e89ae47120b8ee06b62fd150891c3da18809282fc0b80000132fbb22de95689e048b2150f186c02fb14e89183b217e08f03000c40000132f5c92c514b49a247a20a0ef86d230b15589343dc19509c032c0c40000132ef8e2eb95d8a364b02268fa071e327164098c3f6195096030c0d40000132e98c2d014e49b447420b8edc6aa2f314f89043bc17508b02f40d80000132e36d2e0158c9ec4902190f5c6f432b16489a040019809983600da0000132dd282f59628a504c822c0fb870230e15208f83c8188095032c0d80000132d7072e515d4a1e4aa2270fd071032a16609b43f819009483380b40000132d1022cb14c899a47620b0ef46b02fb14908cc3aa16808882e80cc0000132caeb2dc95689f848f2190f0c6c830615209003c8187094832c0e80000132c4e52d215049c047a20f0ef46c230615109183b817a08f82f80c20000132bed32d495489ec49621b8f606d830315208ec3bc18108d02ec0bc0000132b8d32d595189ce48720d0f006ba30315308e43b818109483180c60000132b2c12db95509c84852130f3c6d831615b89243ca18d09282f40c80000132acb32cd15189c648b2120ee86a82ed14508c83ae17608602b00aa000 else (if i < 193 then 0x135b19c2d695289e64952158f386ea31915789443d218f094832c0c60000135ab622ec15c4a124ad2270f9c72432315b89243d419109503080b60000135a56e2c914d09aa4722090edc6a02e7147088039a16d08c83280b400001359f672d515009b04792120ee46a62ee14c08cc39016908902b80b6000013599602d395289c24912180f346da30515789483dc19009903380b00000135932e2e295509d84922170f486da30b15b89643e818909503400ca00001358d332d095149c44892108f286ca30415409143b417b09003100dc0000135873d2cb94ac99a4692098eac68a2ef14988c43bc17e09083200dc0000135814b2ca14dc9c047e20b8ec86aa2fa14788d83ac17208a83040c200001357b2a2e095709ee4942180f246e830915189283c017708e830c0c00000135751d2d495289c247820d8ecc6a22fc15189083d418a09683100c800001356eda2ed15cca1c4ae2220f606e031215589203e418c09303040c8000013568dd2cf95089ce47f2158f586ec317159891c3ca18b09203480c6000013562dc2cf14e49a847c20e0ee86be30715189103c017d08f02dc0a800001355ca02ec9600a3a4c0232100473832b162098440419809483240c8000013556962dd155c9f649e21d8f746f631c15d095c3e618e09102e00c80000135508f2d6153c9d248f2148f406da31015309143cc18b08f82fc0b000001354a8f2d215089c048c2170f346cc30315088fc3c818609483080d2000013544842d595389d648520f8f106ea31015a09543de18309083240c800001353e5c2df95649fa4a12238f606de30315309083cc18e093030c0ce000013538302e295789f648d2158f386da31215789243ee19409282f80ba0000135321e2d915589f449221a8f346c230315609303d017f08d82d40b400001352be82e795749e64892148f1c6d030215089183ac17d08c82f40c0000013525ef2c894e49c447d20f0ed46b42fe14f08fc3b017c09003240d800001351fe62d995209d448220e0efc6de31015589103de19109303280ca000013519b02e595a89ee49321a0f746e031515209043bc19009802e40b8000013513c62c194949964692020e8c6802de13f887c38c15e08402c40be00001350db42db956c9e64882198f146d830c15689383e619309a83540cc000013507b02d095209ea49121e0f506e631215989383e018909182e40ac000013501b32d4154c9fa4962210f9c70a31815f095c3dc19709c034c0e60000134fbcf2c194b89a847720f0f2c6d630a15089043be17e09103080cc0000134f5cc2d114f09c44892158f086c430d15a89343e418d09903240d00000134ef8e2ee1600a3a4ba22b8fd473233416489b041219b09d033c0cc0000134e9782dc954c9e649021b8f746ee31b15c09683da18509b83640ea0000134e3412ea15d4a224aa2238f9c71232a163099c4141ab09f83540e60000134dd2f2da15489ea4892170f0c6bc30a15909603fc19509503340ce0000134d7122de952c9e04862160f386d02fa14f08dc3b018309603300c40000134d0d12ee95dca384b42258f9470431415489203ba18709703480d80000134cad82d014ac9a44732088ee06a22ec14488c439a17308482e00cc0000134c4d82d114e49a047620c0ed86b430114e89183ca18909303140b40000134bec32dc95349da48b2180f386d02fa153891c3d418d09103000bc0000134b8b82d595149ce49621d0f586e830815309183bc18b09403180d00000134b29c2d8952c9da4942190f206e02fe14b09003b618709482f00b00000134ac812dd1568a0a4ab2238fb870a32215f09883ee18b09283480d80000134a66d2dc95689fc4972148f2c6d42fe14c08d83c617408902e40b80000134a01f2f7164ca644c322f902473c33916a09b442419e096032c0d6000013499fe2e01584a084a32268fb871832215c89303c217f09082ec0b2000013493cc2e695d0a144a62210f9c70031115809543e018608e82d40a400001348d872ec15b4a364a721c0f286e830f15f09a04061a109b83400ca000013487762da15349ec4962188f586de30714e88e83c2186092831c0be000013481622db95249ce48f2130f2c6ec31915789343e619409203200c200001347b462e115609e44912180eec6ac30114988e03c617d08e02e00b2000013475352d9951c9e64992218f686de30f15809243c017c09803280ca00001346f1a2df1584a164a02210f8c6e230114f09103ba17b090832c0ca000013468fa2e215749fc49b2200f806e231115a89583fa19b09783180ba000013462b72f295c4a224aa2230f9071c33016989c44181af0a203540ca00001345cd72be145497c4611fc8e686882e414388c439016708382f00b20000134569a2e795a89fe4a02200f9470c32b163897c3ea19009803400d60000134508e2d9956ca044a121c0f386d230c15289143d218d093030c0a200001344a7e2d595209ca48a2180f046b82fa14b890c3bc18408f82cc09e000013444522e41594a164a42208f686f231215909203d618b09303380de00001343e562d014fc9b84842180f486e631415d093c3ec186094032c0d0000013438232ed15c4a244af2270fb070c32a164098c4061a509f03440c40000134320c2dc15589dc48f21c0f546e231915889503f619a09a833c0dc000 else 0x137375a2cf95049c847c20f8f086ba30d152893c3e619109b032c0c20000137314b2cf94e09a847f20d0eec6c030414d88d03ac16e08b82c80b200001372b3f2d414f49b24792060ebc6ac2f7145087838e16608582c80b6000013724db2fb9660a5e4c42320fe472a32f16489603e619209983640d200001371ec72d515349d84812100f106cc30715809203d418309082e80c0000013718a92dc153c9ca47f2100f186b6308153893c3e219809a03480c2000013712ad2d2153c9d84882078ec46a02f314808d03aa17508e03000ba00001370cb82c814c09aa47a2118f0c6ce30415009103bc18809183100c00000137069f2de95889f449b21f8f8070231815b094c3d818108d82e80c8000013700992cf14e89c647b20e0ef86c8307156092c3d218c099834c0d80000136fa8c2db1588a0e4af2220f786ec31c15b894c3e218b09403200dc0000136f43c2f395f0a3a4bd22e8fe472c33116409a83e219509503340bc0000136ee4f2c594c099c4772168f1c6d430b15e897c3ee19d098031c0cc0000136e8402d795309d648e2170f206d431715408f83ae18008d03040c20000136e2462d715349d648420c0ef06b42f214c09003a016a08582e80cc0000136dc3d2d515149da4892148f186ca30915709403d618e094831c0ca0000136d6222d895689dc49621d8f2c6e031115989283e819709683240c00000136d01f2d395249c048120e0f186c830015409183b417408e03000b40000136ca1c2d395249d04822128f0c6c8304153094c3d8187096830c0c00000136c4072da953c9d24872130f206c230615389143d218a09403380ba0000136bdfd2cf14f89b247f20d8f0c6c2306156093c3e417c09403100e00000136b7ea2dc9570a0849e21b0f546da30d15d892c3d4195099834c0d00000136b1be2e895c0a204ab2220f9c71231f15a89503fc189092831c0da0000136ab8a2eb15c4a184ad2270fac6fa31b15b89543e818a08f03200c20000136a56e2dd15449f64a721e0f786ee31615c09443e419509f034c0de00001369f3e2e615bca244aa2240f786ec31315f09483e019609783280be000013699452cf95389d448f2160f446ee312155890c3ba18108d82f00be000013693162e395909fe49821a0f446d230d15389203d218c09083140d200001368d072d615089ce4892160f3c6ea31815909343c618209103180bc000013686f92d995309ea4912158f346da30a15489043c218508e83240d8000013680f82d3150c9d44902168f706e231215289303d618208d82f00c000001367ade2dc95189ce4742098ed86ae2f214b88dc3c417f09603200c2000013674c52e015789f049621f8f5c6f831b15d894c3d2190096831c0b200001366e7a2ec95a4a084a92248f846f832516209703ee19009483100c6000013668362eb95c49f849b21c0f586e631815b09283d618b09503240c4000013662222d895589ea49e21d0f406f432215e097c3fa19c09d03280e200001365c172d89568a144ab22b8fb470831d15c89443ce19109603440b4000013655e72e21588a0c4a021a8f506de30e15789303dc17d08d83100ac00001364fd92d715349d048c2168f206ca31315509403d819409703140b8000013649d72cd950c9d64852100efc6b22f914a88d43b217e08e82ec0a8000013643d32d194f09ae4742098ea06a82f114a08d83b818609002d80c000001363dbe2da95689f849521b0f586e630515409283c618309103180d00000136378f2e715c0a1a4a521c8f386d230c15289283d4185097032c0c80000136318c2d095089c648c2178f2c6e630415109283c018509283080ce00001362b832d215249bc48f2198f5c6fe31715c096c40219809b035c0d40000136252f2f89654a524c322e0ff872232015f09783f419109b036c0cc00001361f162e2157ca084a321d0f706ea31b15809703ea19009b83440ea000013618fc2e01560a0649d21c0f686f4311156091c3c018109683080c0000013612f42da153c9ca4832130f1c6d030f15909103c418309483300d000001360ce82db155c9e04922148f406c0301150091c3e8194097031c0be000013606e22cf950c9b047d2118f146c430115389283d218509383140c6000013600e12ce14e89ca4822108f0c6d030514d09043be184090832c0c80000135faca2dd15549da4842100ee46bc2f514988e83b618608a82d00c20000135f4c42d3154c9f64912128f2c6dc30e15189203be17d08d02fc0ce0000135eeb52d795009d648c2158efc6c630315989283d018c09983300d60000135e8852e415749f64a021c0f486da30515109043c817808602c40b60000135e2512eb95c4a2c4b02278fa071632115b09603e218909582f80ce0000135dc3e2dc953c9be4812148f246c230315309043dc19109603380ae0000135d6352d515249cc4862118f086ce30b14b88d03ba17709082f40c20000135d0162df158ca0a49a2180f346d030e15409343e818c092832c0ce0000135c9ff2d995549f24982170f606e630715209283dc18a09603000cc0000135c3e12de956c9ee49621b8f346d430514c08ac38a15f08482d40a60000135bdd42d295189d24862118f046d2313156092c3d618d093830c0c00000135b7a82e915c49fe4a22238f986fa31b15c093c3e2189093030c0b4000))) else (if i < 197 then (if i < 195 then 0x138bbcf2e715a8a0a4a72220f8470231516089443c219409783240ca0000138b5e42c214a898a45e2008ea86902ea14908b439e17909083040c20000138afc82dc15549dc4912148f506f231315a09183b817608f82e40c80000138a9a02e995c0a0e49e2208f706f631915d093c3e419509903580d60000138a3bd2c194b89a847220d8f086b230615309303e0190093830c0cc00001389d822e795c8a2a4b22278fac716331164898040619b09783140d20000138975e2de15709fc49d21a8f5c6e031915c09383d418508a02c40ac000013891432da95509fe49c21f0f5c6de31015489103b818509703140b000001388b2c2db95789f649521a0f546e230f15509083b817908f02f80c2000013885192d915309d24842168f206d430415108e83b417508b83180d800001387f212cd14e09c048a2180f486da30d15109103ac18309403200d20000138791c2ce95049c448f21d0f386c82fb14808b43bc17109082f40c8000013872e52e71584a024a922a8fac70631b15c097c3ec18d09483440be00001386ce22d295349e249321b8f506e431615c09443d6188097833c0c4000013866c52de95689d848220e0ee06ac2fe15289103c418908e82dc0ae000013860c92cf14f89ac47220a0ecc6ac2f814a89083da18209003080b600001385aa92de9584a0049e2228f906f030c15c09603e419809a03180cc000013854c82c714d49c84822130f146dc30d15589303d818c09503040cc00001384ec92d014d49b64842100f306c830c15589183c418a09183040ce000013848a52e115609f849521c0f506f632815f09703e218d09a034c0cc0000138427c2e69590a164aa2238f8870c31a15c09583f018a09603000c600001383c6c2d194f89a848520d0f146ca30114e08f03ba17e09403080be0000138365d2d695109ae4772120f3c6d230315209103c217f08f82e80c0000013830562d5954c9ee4912148f1c6c0303152890c3c618509083180d2000013829ec303168ca664cc238102c74232d165094c3d018309a03380c6000013823e12d615149ca48b2128f106c22fa14808d43ae17c08e82e40b600001381dae2e41584a0449c2140edc6b22ff14c88f83bc18409282cc0ba000013817a52d295249cc4842178f586e231115b896c3ee19a09703380c2000013811ab2ce14f09b647d2128f386d430d15b095c3e219609303100d400001380b6e2e995b8a044ae2260fb471832115e094c3da17909103300c4000013805762ca14d89b048020d8ef06d230815809583ea18809083300ca0000137ff852c814c89b047f2130ee46ba2f314a89083d818b09083100ca0000137f95e2e515b8a1049f21a8f446da30b15289343d418d09603180bc0000137f37b2c4149498e47120b0ed46b82fc157095c3f019909b83180c80000137ed482e99604a244a62200fbc70e33116609b840c19d09c03500c00000137e7182e29598a124b22280f9471a32815f095c3e619e0a003440c80000137e0d32f2160ca3a4b62258fa46fc31515b893c3d2186096032c0cc0000137dabb2dd95889f449b2170f046c22fb14c88d83c617d09482fc0be0000137d4dc2c294d89ba47920d0f186bc2ff15008e83ac17408682d80a80000137cea72ee15bca1449e21e8f346d230615388d439816608982e80ae0000137c88d2dc1590a0a4a22218fc870c32b16689a03f618809a03240da0000137c2922cf14fc9c848a2148f0c6da316156895c3fc19509a034c0de0000137bc772dd95509dc4822120f206de30a15889643f419b09903200c20000137b67b2ca14d89aa47820d8ec46aa2f514a08c039617608902c40ba0000137b08a2c394d09b84732090ee86b02fc14988c83a217709183000c40000137aa942d114f09ac4772110f046d230915389103e018709403000cc0000137a4782de15409de49f2178f306cc30615609203d418208e02ec0c800001379e612d715289c848520c8eb86b2304159896c3e219609a83280ce0000137986b2c7950c9d64872108ef06c430b15208e83ba17f08c82ec0b2000013792732ca149498e4752038ec069a2f514608c03aa17809183140ce00001378c632dc154c9ea48f2188f3c6d630d15388fc3c018109182ec0c2000013786332ea15a8a204a321c8f586ea30f15689383f819109783140ca000013780272d515189e249621b8f606fc32616189503dc18808f02f00d000001377a1b2d015009bc4832188f706e031115a09383c818a09483400d60000137740b2d715249d04882120f0c6ba2fe14e08f83c017108902d40c200001376dde2e515d4a1249621a8f4c70432715e098040019809a03040c8000013767bb2d795389e44912128f1c6c830414888fc3ba17c08b02f40b6000013761b32d2150c9ac48120d8f006bc2f814b88c83a017708d82f40c000001375bb92c914cc9bc47a20f0ed46b62fd14d09003c418d08c83080b8000013755a32d795649e04932158efc6cc2f614688b03ae17c09082f40a800001374f972d895509dc48f2140ef06b02f014808d03a617508902a80a6000013749592ef95d8a284b22238f806f031c15c89643e818809783280bc0000137436e2c394cc99446b2030ea067e2de142087c39016f08e83080c600001373d642d915389ce4872158f146d2310155891c3c818308d02ec0c0000 else (if i < 196 then 0x13a3fdc2dd15549d84902150f5c6f8317156894c3f218f09803180b8000013a39b12e0957c9f649821c0f6871432115909283da18208c82e80d0000013a33b12d414fc9be47b2110ec86a82fc14d08f43cc187097833c0c6000013a2da52d415149e248b21b0f606ec31c15b896c3f2192095834c0d2000013a275f2ee9600a424b92280f9070631d15d898840419f09a830c0d4000013a21582cd14cc9a44772060ed86922dc14688b43a017309083240c8000013a1b572cd150c9c847e2108ef46b230615389443ca18709583200c0000013a15562cf15249d64892140f1c6d430a15388f43aa16e08402c00ba000013a0f332db15249fa49621c8f8070831c15e094c3d417f08d02f00b2000013a09532bf147897845a1ff0e586802de13e087038215a082028809a000013a034a2d415089bc47d2128f0c6c230515509443d4185090830c0c00000139fd5c2c514a49944662028eb86942e8142887c39e17508f82e80ae0000139f7222e195649ec49721b0f486ea30d15409243da18608e82e80b00000139f1392c194a499e4702070ed46a62ed14b88e83c018309002f00a80000139eb282d91578a024962178f546e630615789683ea19109683180c80000139e50c2db156c9f449a2188f246d831815d09603ee18d09803380ca0000139def22e015749ea4922118ef06b82f814c08e03b617408a02d80b20000139d8bf2e215849f848d2118efc6c82fa15289183c417809183140b20000139d28f2ea9604a384b42288fc070632716009783fc19a09b03200c60000139cc6e2e495a8a0c4a52200f746f631715989543c618a09203180b40000139c63c2e295849f449521b8f6c70a32216189503ee19209883240ce0000139c00f2e315a49fe49b21c0f7070031615b894c3f819809503140c00000139ba162cd14e499c4682038ebc6a42f714a08c03ac16f08c82d00a80000139b40b2cf15449e649221b0f506ee316158090c3ca17e09082dc0aa0000139adec2dc95409da48f21b0f706fa31315b09583e619309a03340c40000139a7fc2c894c09a846a20a0edc6a22e9141088839016b08e02e00b40000139a2232bb147497e4692050e8468e2f0141889838616c08082940aa00001399c1f2d395089d247f2118eb869a2f014b88e03b017f09203100b0000013996162d3153c9d84892140f106c22fa14808e43b817508b03000bc000013990172d094f49ce4872110f106ce31115609003c617c08d83280be00001398a1c2cc15149ca48220b0ef86cc2fd15309143de18708b82dc0b0000013983e22ee15eca3c4b12278fcc72432315d89543cc18108e82c80b800001397de22cb14e49aa4712098ed86b830714f09143ce17c08e03000bc000013977f32cf94fc9b647a20c8ed46922e214288c03a016f08a02880a0000013971e22dd955c9ea49d21d0f4c6e0309156093c3d619909503100c200001396bb02e815c8a304b922d0fa872233316b09ec4441b709d83300ce000013965982d815289e648e2160f346dc30c15589103c217b09082fc0d000001395f812df95749ee4982180f2c6d62fa14b88fc3c417c089030c0b2000013959942cc14e49a04782090ec86a02e614788c83a017f09603100c4000013953972d115189c848b2150f006ce303153092039e17609002f40c000001394d7e2da95309d849621d0f6870232316589bc3fe1a40a183540ce000013947362f69620a3c4b222a0fc870032616289703ee18f09482fc0d2000013940f52e995c8a164aa2230fac71232415d09583ea19309c03380ca00001393abb2f015c8a364b22220f8c712327168896c4121a109903440ba000013934b52cf94d49be47920c0f046aa2f414508e03a217708d031c0c200001392eaa2d4951c9dc48d2158f3c6ca2f714b88f83a617808602d80b0000013928be2c4949899046e20a0ee06bc30015209103ce18509183100c6000013922e12bf147497e45d1fd0e646842e4143087c38816e08a02c00a400001391cd72d395209b847f20c0ed469a2e914a08cc3c418d09683200ce000013916d72d715109d448c2128f086de2fe151890c3ae17b08e02f40bc000013910d52d315109c648720f8f406e030315089303d418e095030c0ba00001390acb2d695249d448e2138f3c6e6308153090c39c17908d02f40ca000013904b42d815309c24812140f0c6ce30614e08d43b018708e82f00b80000138fec02cc94e099a4692038e946782e313f88a039616908902d40b60000138f8722f21610a364b72278fbc6fc31515509403e218a09483240d20000138f26b2d094fc9ba4782140f486e630c153091c3be17808d03040ca0000138ec452de958ca024a221e0f806f432015f09443e8193093831c0c00000138e6412d3152c9cc4862120eec6c02f314a08e03b218209483240d00000138e02c2d995449e449021b8f206e030a15889383e619009002f00cc0000138da1a2dc15609ea4902198f346dc30a158095c3e019109783580ce0000138d41b2d215149d448b2150f106b82ff14988cc3c217908d82f00ba0000138ce2f2c914ec9ba4792100ee46982e414908e43a817808f82dc0be0000138c7f72ee95d0a284ab2268fa070c30a15509143aa18009283280c60000138c1fb2cd94cc9ae46d20a0eb86822e614488bc39a16d08782bc098000 else 0x13bc4202cb94d89b647e2100edc6ba30014e88dc3a417108682cc0b0000013bbdf72eb15f8a2a4aa2280fc472c32b164899c406197099033c0dc000013bb7ea2d4951c9ba47d2120f186d430515789403d4189094033c0be000013bb1d62dd157c9e24922118f146e430f155093c3de18c09603080be000013babc52d895349f249121a8f386bc2fd15309483e018c08d82e80ba000013ba5a52e0955c9ec49421b0f8070c32815c89343ea19709703380b6000013b9f6a2e995aca0049f2218f546fe32215d09743e419009082f00ba000013b994f2dd95909f64a321c0f546f231815b89443dc188092831c0de000013b932a2dc955c9e24972190f346c630114e08f03d017f090031c0ca000013b8d3a2c994d49884692040e9868c2ec14888c83be18208d82bc0a4000013b87372d095089b447e20b0ef06b630715088f83b017508c02dc0b6000013b81362cf14e49bc4832108f2c6c830414e88f83b218209302e00b0000013b7b142db95609ea49321a0f546ea30c15589243ce18608f830c0cc000013b74fd2d9953c9d24852158f1c6cc30b15489143d418809083140ca000013b6ef52d295109b647920d0f086bc2fd14688b839616c08a82f00b4000013b68c92de15689f448d2160f286d630215309203cc18409183000c2000013b62842ef15eca384b72290fa471a33216e09ac40c1a609b83480e2000013b5c622e615d4a0c4a92258fc071a32815e09683da18a09703280cc000013b56332e715849f24882108f086cc30115189303e0188098030c0be000013b503b2d495509ea4902110f086ca2fd15108dc3aa17508f82e00bc000013b4a1a2e01590a084a52228fa471631a16089883ee19b09b83500da000013b43f82da9574a104a42228f8870831a15b09383d6185093833c0d8000013b3e122c094889724541fb0e4c6762e414b08dc3a617308902c80b8000013b380d2d015049d44882130f306ca305150891c3e2190098032c0d6000013b323a2bb94a498e4682050ed06a22f114708e83aa16b08882f80cc000013b2c0f2e4159ca124ad2240f946f831615b89303da18b091832c0c0000013b26112d715489ea4922178f806f431915e09603e018f09902dc0a0000013b1fea2e795b4a144a821f8f686ee31715a09443d8196095835c0d2000013b19cd2dc15749fc4912168f486d430615209103d618f09502fc0ae000013b13cc2cf14fc9c24832140ed86b0304156893c3d218a09483140dc000013b0db82d415449e24932188f246c830214a88f83ca18809502e80b4000013b07b22d115249d648e2168f146c8305156895c3f418e094033c0c2000013b01a12d695009ca4832158f0c6c82fd14d08f03da19309c03240c2000013afba82cf95049c64882160f2c6d830e15509343e618d097832c0ce000013af58b2d915549cc48a2110f206c42fe15309103d818509083200c6000013aef662df155c9e44872140f546e0310154891c3ba17108502c00b8000013ae96b2d094ec9a64792080ed86a82fc14d08f03b617808e03140c2000013ae34c2db15889f449821a0f1c6d830615388f83a616d08882d40c2000013add3c2d895009d248b2160f406d030014e89103ce18909403140bc000013ad70f2e295bca0649f21c0f486da306154091c3d6186092032c0d2000013ad1122cd14e89b04772048eb86942e514308903b618109083140b8000013acb102d014e89a84842118f006c430915188d83a817908f82f40b8000013ac4f22db95789e448a20f0ee86c02fe152890c3cc18108c02e40c6000013abf3d2aa94149624662068edc6a62e814988fc3c418f099835c0da000013ab90e2e19584a144a521f0f0c6be30815589303c418a09202f40bc000013ab30b2d715749fa49121c0f4c6d030615309203ce17d08b83100ca000013aacf72d5951c9cc48c2148f186c22fe14c88fc3c018108f830c0be000013aa6e62dc95409f04952188f406d02ff15108fc3b618009402f40ce000013aa0de2d615349dc4882190f306ea31015709443ca190091030c0c6000013a9aca2d7953c9e44982198f546ec31a15d89683d6190096832c0d0000013a94af2da952c9e848e2158f4c6d630e15209043b617e08c82dc0b2000013a8eab2d115149c247720d0ed46ac2f914b08d039a16e08683040b4000013a88832e795b8a0a49b2210f9c73433c16b89b44201ab0a4037c0ec000013a82822d715389de4922190f5c6ea31715589143c617e08d03040b0000013a7c502ef95d0a3c4bc2270fac71231e15989203ec18c09603340e2000013a76572cd94e89bc4852080eec6ae2fb14d08fc3b218008e02e40c0000013a70312e395aca0a4a021f0f706e230b15308fc3d418108d02f80c6000013a6a392cc94a49b047d20b8f006d030215188f83b417c09002f80ba000013a64452cb95009aa47c2128f046bc30515108f43b817309083080c2000013a5e152e615bca1e4a72248fa070232a16189804141a1096032c0ca000013a580e2d415249d64862170f506ea31515809643e819309b032c0d0000013a520d2cf14f09b44822160f106d631215889503e618e09382fc0c2000013a4bff2d495649f04922180f646e031b15b89483c618509083280c8000013a45fe2cc14d09b047020b8ef46b02f414d88f43d418008f83200d2000)) else (if i < 199 then (if i < 198 then 0x13d48c12ca14f89a847220a8eb06982ef14308a037416208802d00a6000013d42ae2d5952c9de48e21a8f5c6f831e15d89783e2183092831c0d2000013d3c872e01578a0a49b21a8f546ea30615609043b2183091831c0ca000013d36482ed95e0a2c4ac22a0ff073233216509a83f618c09683080b2000013d30352d895389c648020e8ef46b42fc14e88fc3cc18308f82ec0a6000013d2a082e0156c9ea49b21b8f586e431415c89783d619509903340ce000013d240f2c814e09bc4832160f1c6cc2fd14d09143c017408882e80c2000013d1de72de15749e849b21f0f8871432215c89383de18308f03040bc000013d17bf2e615a8a0049f2258fc470c32416289803fe19209503340d4000013d11d62c594c89a647920d8ee06c82fe14e890c3ce18c09703040be000013d0b922ec15eca2e4bb22c8ff4720327167099440419a09a02ec0c0000013d05802dc15709fe49521c8f406e0317160898440219409a83380d8000013cff742d6952c9de48c20f0eec6ca31515709343d8187098834c0c8000013cf95e2d695289cc48320f8efc6b830315689483ca17c09003080c0000013cf3432e09578a0e4a22210f686de31115288fc3a217408a03040c0000013ced252df95a0a0a49f2220fa070e31115809083c818209583180c8000013ce7272d015149b84892138ef86bc30415309103a817908e82f80c0000013ce1342cb94ec9b447720e0f0c6c42f214c88dc3be17508b82e00c2000013cdb402cd14d89b247620e8f146e031a15a09403d219309703480d8000013cd5352d495309e648d2140f106b62f414b89043ce19d09683100bc000013ccf6e2b8946897645f1fe8e646782e614108c83b419109c83240ba000013cc97d2c994cc9b04862140f4c6d230915909403e0193096031c0ca000013cc3572de955c9f849d21a0f4c6de30e156893c3e418a09683240d2000013cbd482dc15309ea49921d8f606e030d15089103ce17f09303100c8000013cb6fb2f0963ca504bf22d8fd473033216a09a83f019c09d03500d2000013cb0f52d395349e248e2190f586ee32116009583de18a09903240d2000013caa9f2f7960ca2e4b1229100473833216a89a440e19e09903340ce000013ca4bb2c294b89964601fd8e7868c2e714708c439216a09083040aa000013c9ebe2d195309da49921e8f586e232516689b040a19709703380e2000013c98b72d094fc9d04942108f046ca31415a09243da18b08c82d80ae000013c92bb2cf94e09b447f20b0eb46ac2fa14708dc3ba17f08f83080d6000013c8caa2d615289d24842168f406c030815609203c817d08f82f40c4000013c868a2dc15389ee49421b8f746d030d15209043a817909103380dc000013c80742d895689f84ac2288fb070831915b09403e819a09b03040c4000013c7a562da95449d649321c8f546f231315a09643d8182093831c0ce000013c74492d695509ee49821a0f386e2310154892c3e618f09383000b6000013c6e442d214e49b04702028ea86b22ee14b88d03b017908d02f80b6000013c683f2d315049c64822110f546d031015808c83ac16908382d80ae000013c623f2d215149bc48420f8efc6ba2f514888d03b817b09103140ac000013c5c3f2d3150c9c247b2128ef86b42f314f08c83b017b08e82d80bc000013c560b2ee95c8a264ad2250fa071633216309703f218a09283080d6000013c4fe62e1954c9d44922198f5c6fc31c16209703e418809103080c8000013c49f22cb14e09b647e2050ea86a02ee14c88cc3a817509182dc0ba000013c440b2cb14cc9a847e2170f446e030a15408f83c218509102f00bc000013c3dc72f59628a5a4c8232100073c339168897c3f4190098033c0de000013c37b72d8156c9e84942188f506e830f15689243de18c093830c0ca000013c31972d915709e448f2188f506e831e15809383ce18a09683240c4000013c2b832d9153c9ea4872110ee06b62f614c89183cc18909d038c0d0000013c25642de15609ee48b2148f206cc30315389043c618008f03080bc000013c1f2a2ed95c4a3e4c222d8fd470c31c15b89843fa19309c832c0b0000013c19102d915409d248a2190f3c6e630e15909583e819409c83440de000013c131b2cd95009c64782108ef46a42e6142887437a16d08302f00ba000013c0d0f2d4952c9c84812140f006aa2f615108cc3a416a08983000b2000013c07032d795549f24982198f306e631015709283c617408e83000c2000013c01062cc94dc99c47720c0edc6aa2f114508d43ac17908982f80b8000013bfaca2e915b4a024a42238f84708328166899440219c09a03400d4000013bf4c72d7153c9e44912178f446f230e15709183c618709102fc0b8000013bee8f2ea15e0a144af2288fe071432a162896c3f619009a033c0ba000013be89b2c894989a247720b8ef06ba2fb14888fc3c218809283240bc000013be28d2d815389d44812128f146d630a157094c3e218b09703300c2000013bdc722dc15509d247b20d0ee06ac2fb15008f83b618108b82d40ba000013bd6302f4964ca5e4c222f8fb471832216389c04261a609d03500e8000013bd0092e515749f249921b0f106d630415689503de18d09083180b6000013bca1f2c794c09944712060e9c68e2e814288a03a217d09182fc0c6000 else 0x13ecbf32e895b4a244ad2280f9870e31a15d09543f019009303100bc000013ec5cf2e515eca224af21c0f206c02fd14c88a83a017b08d82fc0ce000013ebfc22d694e49b647c2120f086c030815488fc3be17608c831c0be000013eb9bc2cc14dc9a447220a0ebc6ae2f214e08f439c17608c030c0c8000013eb3ad2dc95689fc49c21a0f386cc30d15389283d0191094830c0ba000013ead972d8950c9c24872130ef46ba2fe15209243d219309883540ca000013ea7b52bf949098445a1fb8e786882e114108883a016d08c02c00b2000013ea1ac2d094e89aa47720a8ecc6a82f014708fc3c218f09482e80be000013e9b7d2e395709f849e2208f946fc31615b094c3e018e09083080d0000013e954d2eb95c8a004982200f586de30715b894c3f419509a83300c4000013e8f372d8954c9c848020c0f0c6d2306150090c3b817c08c02c409c000013e894c2c6948898046a2048ea46a82fe14a08e03c818708f83240d4000013e83422d895449d24832148f306d430e15409083de19009b83380ba000013e7d412cf15289d849921a8f506d831015909603e019009402f40c6000013e774b2ce94f09b846e2050ec869e2ed14108903a417308b02ec0b2000013e71292da15249d448e2120f046d030f159094c3e418f09583240e0000013e6b0a2df15509ec49921a0f306d4310156894c3e218909883440ce000013e65012d094e49a047b20e0ef46c22f614708bc3a817408f02f00aa000013e5ef12da15409e44962190f386d031315b89683fc19809583480d2000013e58d12e4158c9fc49c2220f7c6fc31f16209743e819009683340c8000013e52a42e215709da47f2130f306e0307153892c3ca17808a83100c0000013e4c9e2d7153c9ec48e2158ef46ce2ff14d89083c618c09c03180c2000013e468b2da955c9f049821b8f8470c32215e897c3e818c09a03600d2000013e407b2da95389ba47b20e8ec06b42f514a08dc3b817e08f83340c2000013e3a6b2d995349e24992188f006ce31115b894c3e419809383180c2000013e343d2e31564a0049e21d0f446ea30d155090c3d818509383000c0000013e2e482cb14dc9a64772070ed46ac30014f08d439e16f08882b00a8000013e28402d194f49ce4842170f186de30f154892c3d618109102f80a6000013e22392d915449ee49721f8f8870032615d89383c818709303080b6000013e1c482c894b09a24712080ec86962e714588d03bc17a09003080cc000013e164a2cc95089c44842120f0c6b82f114b88ec3b018009283240be000013e10272db95589fc49921b0f686fc31b15609283ce18909103200d6000013e0a232d094f09c247920e8f146ba30415289143ce17508e03280ce000013e03f22e415649ec49d2208f706e630f15689203e2188098832c0b6000013dfdfd2ce14f49b24672078e8c6922ec14988a03ac17708b83080c8000013df80a2c914909a24702050e906982f114708b43a816a08682d80b2000013df1fd2d995409d449321d8f686f831a15f09983fe1a209d03340e2000013debff2d1151c9d048520d8f086b830115088f03a016d08b831c0ba000013de5f32d615109da4892168f2c6c22ff15308f03ca17908e832c0ca000013ddff32d0151c9c248c2128f1c6d230215809343f018d09683340d0000013dda282b7143c94e44c1f38e3866a2ce13c086437e15d08282b40b2000013dd4132dd15409d449a21b0f5c6d4304151891c3da18908e03140c4000013dcdef2e2955c9da4882138f106c02f714a08c03a017408d02d80ca000013dc7f92cc94cc9b847b2108ef86b42eb14388a83a818009603180c0000013dc1fe2d015109b247620a8ec86a02f114888f03ba18809183140c6000013dbbd82e415749f84982190f2c6f231115789403de18008f82d00b2000013db5f82c014a098846e2088ec86962ec142889838816408382e40ba000013dafd72db15549f649921c8f386ca30615208f83d618a09183100c8000013da9b52de1558a0e4a52258fb871633316489643fa19609b83480d0000013da3792ee15d8a1a4aa2268fb471033416689704021a209f83480c2000013d9d872cf15189d048720f0f286c430a15909343be17d09083280c6000013d97692de15809f849e21f8f686fc319158095c3d018909083040da000013d914a2df95609e248921c8f686f031715609103b817f08b02d80ba000013d8b522cb14d09a047220b0f006ac2ed14588dc3b417d08f83000c2000013d855e2ca14c09a846c2038eac67e2e313d08a438c16d08e02e40b2000013d7f392e1158ca0a4962198f586e830115208f03e018509303080ba000013d79282d315189e648e2118f046ba2fc15109183dc18f098832c0ce000013d73002df152c9e64922158efc6aa2f914e88f03ac17208903040b8000013d6d0b2c3148c9864672010ea069e2ed14808cc38c17008702d00b6000013d66f82d715309a446c20a8ee469e2f414788fc3c018508f82cc0bc000013d60e32d795309da49421a8f586f031715d09643f219809202f00e0000013d5adf2d014ec9b448120f8ed86ca2f914408c43a217a08e02e00aa000013d54c82dc95889ea48c2170f186c430814d88d83ac17a08a02d40c0000013d4ebe2d395289de48720d0ee46c02ff15089043aa17b09483240c8000) else (if i < 200 then 0x14050692c714b499447920f0f086ba30915009103c218509803140d600001404a482e71584a0049f2170f346de31b15609483e818c09402fc0ba0000140445a2c994dc9b24792168f646e831115808ec3ae17d09003340d400001403e392e01590a104a12238f5c6e431115189243da18008c82ec0ba0000140386d2ba148c9a046b2100f046b030115309343da18d09583100cc0000140326d2ce950c9d048520c8ef86c02f714c08e83ac17308602c80b800001402c6b2d495409f649b21c8f6070031d154891c3ca17b08d02d00b6000014026562db1578a0649421b0f446d830915289103b817808d03100bc000014020362dd95409e64942120f206de30e15009043bc17408b029c0a000001401a312d114e49c047d2080ed46b02f714c887c38617208f83140ba000014014342c994a49884682008e7868a2e414608e439a17209282f80bc00001400e242cf94f89c447820b8ee06b22f914a08a439c16708702e40aa000014008142d6155ca044a22200f886f430e15289183d218208f02e80be000014001fd2d315049ba4782130f246d830c14f89043b4178091030c0be000013ffbef2d8150c9c247b2120f2c6d230515208f03a817408a82dc0a8000013ff6002c1948c98445f2028ec068c2fb14b88f83c0188091831c0ce000013fefe52da15309d84872158f086c230214a089039e17508602c80c0000013fe9ef2ce15049d448320e8f006ae2f714688c039a17608882e80ae000013fe3c52e315989fa49421c8f546ea314157093c3d618009083100c0000013fdd892ef15eca2c4b322c100074c34617689ec4221ac0a503840cc000013fd7902cb94c89b647b20f8ef86c630415089283ca18609783140b8000013fd17c2d795309d24912168f186bc2f314f08e03a617709103140c4000013fcb7f2ce94e49ae47720f0ee06cc30614e88e03b617508e82e80d6000013fc57d2cf952c9d647e2118f006b02f014308c839216508a02cc0b0000013fbf702d614fc9ac4732060eac6b82f014d88e03ac17d09002dc0b4000013fb93b2ee95e4a304b022d8fc871a329164899c3ec19809c83600d8000013fb33b2d995549de4922198f446ea31515989483d418108f82f80a8000013fad3c2d81558a0449b2190f546f630c15a89483dc19709983340d2000013fa7052ef15c8a184a52258fac70c31415709243e819409983400d4000013fa0d82e2957c9fa49b21a8f286d8311156890c3ce18509202fc0b8000013f9ad62d095149c047c20d8efc6b62f214a09043c217208902f40ba000013f94ac2e11580a0a4ac2218f906fe31d15f89403da18a09383340cc000013f8e9d2d995349bc4802150ee06c02fc14e091c3c818c09883200bc000013f88832db9588a004992200f746f031915a893c3d018d09683200d0000013f82422f395fca424b8231100c74c33e16b099c4081af0a4835c0e0000013f7c332d3151c9c648520f8f106d02f814e88e83be18409603000c6000013f76072e29584a084a621c8f6870832416409783f018e09403040d4000013f6fd22e815e4a2c4a621e0f5c6ec31615e89583ec1a009c03340c8000013f69c12da152c9e048a2178f306f230a15489283d018e094834c0ce000013f63902e895b8a0c49d21e0f806f231e15b097c3f419809783080d4000013f5d742da95389e44922130f346c82fc15189003ca18309183140bc000013f57782ce950c9c248220d0ee86aa2f814b89103b217108a02d00bc000013f51652dd15509f449c2208f746f031316309783ec19009503040d8000013f4b5b2db950c9be47c2118edc6bc2fa14e88d83ae17108d03100c6000013f45702ce94e09a847b20c0f046ac2fc15189143c217d08c03040ca000013f3f592da154c9f849e2200f5c6ee30b159091c3d818e09603180c2000013f39332e1155c9da49221d0f746e430e155093c3ba17f08b02e00a0000013f33472ca14c49a447520a8ed46b030215389043b817808903040bc000013f2d132e915b4a0849f2188f286ca2fe14f08f83ba17908f02e40c2000013f271b2c514889964692030e846b42ef141888038216e08a02d40ca000013f20fa2de951c9b447e2118f206e631a15789383e818809183080c8000013f1b1e2ba14809784592008e806842e914508a83ae17308c83000ba000013f15322c594ac99e46b2068ed06aa2f814e08f03d618208e82f80b0000013f0f172db15689d849621d0f386da30915108f43b818008e02b00bc000013f08ec2e495e8a184b32278f9c71c32c161897c40419809783140be000013f02e12d395209d64842108f306ea30815509083ac18809383180cc000013efc992f395f8a204a72258fa471032c16809a841819f09e83440de000013ef6782d615109d04892108ee46aa2f514a88b83ba17e08c02e80c4000013ef0712d295389d448821b8f206e231015609203e418709483280c8000013eea552dc95509da4892130f406d430d15288fc3be17f08f02f40b8000013ee44b2d395089bc48020c0ee86b22fd14d88f83c218708e03280c0000013ede4b2d395049b848420d8f146d430415509303d018008f02fc0d0000013ed83a2d914f89b047c20f8f086c62fa14c89043d4187091832c0c0000013ed22d2cd951c9c24892158f006c0307157893c3e418a090031c0b8000 else 0x141b61500000000000000000000000000000000000000000003140c60000141b0122d195089e44942198f0c6c230215108e83b417a09082e40c00000141aa1b2cd14dc9b44772080ec46a22fd151090c3ac17f08d83000c80000141a4112d615289c648b2110eec6a82f514b09083c617708c82e40b600001419df12df15709e649320f8ef06b02eb14688d03b417608d82f40ac000014197b32ef95f0a364ad2250fb871232916209884121a309d83380ce0000141916c2f3160ca3a4c122f900c73e34216889c03fe19b096831c0c200001418b3d2e59594a084a42218f706f831815709543d819309083280d6000014185352d095209b847020a0ec06a22f314308b438817008c02e00b800001417f432c714c89b04802070ea86962f714c08d43b817a08702ec0aa000014179092ec15cca104ad2250f946f6317158097040019d09b83400c8000014172f02da95509ea48d2150f2c6d830314d88e43b817708883280c800001416cf62cc94bc9964712070ebc69a2ee14888d039617108a82f00b0000014166e92cf94f499e47820a0edc6b02f414a08dc3c617808702b40aa000014160f42c694e09c447920e0ee46a42f714888e43ba18009103100c600001415af42ce15009d248e2178f1c6c030c15189143be17908902e00b8000014154cc2e395a8a0849621b8f486d030215208f43a816f08c82fc0c200001414ec72d814f09cc48b2150f246d230e15c09083c8183098832c0ca000014148c32cd14a498c4732078ed46bc2f915109203ba18008f03100c8000014142cd2ca14ac98246c2098eb46982e6144889839417108882d00b600001413cdf2ca14b898c46c20d8ef86b82f914d09043d218709182e40ac000014136b92df15909f449521a0f80700312160899c3ec18909483300d0000014130b02d895449f849f2228f586ce30e14e88e43d2186097033c0c800001412abb2d015249d04852148f2c6c42fa14f891c3ba18209183000b8000014124b62d715589ea48b2180f686da30715408f03b217d08a82d00b400001411eb92c3949c9944782110eec6b02fa15009103c418108d02f40b2000014118852e6956ca084a22228f646d631815909503ca18909283300cc0000141126e2d314e49b247a20e0ef46c830014f892c3bc18209282e00ac00001410c4a2e4159ca0e4a82230f8070632e163897c3f818e09583440c80000141061e2e215489ea4912150f006d430114f09103d418d09703340c4000014100122da15349f249f2168f206bc2ff14c08cc3b618208c02e80cc0000140f9db2e895d8a204b52288fcc72a331168899040a1a309a03600de0000140f3c52e195609e04932190f646e4315156096840219809c03200d60000140edb32dc157ca0048d2180f2c6dc30b159895c3e418a093832c0ba0000140e79a2df15889ec4922158f186ba2f114708c439617008802ec0c20000140e18b2da15049c847920a8edc6a02fc14688d83cc18709103180bc0000140db8d2d915409e048c2160f506d430114e08e43a016808182b80aa0000140d5872da95349de4902178f246d830314f89203ca18809282ec0b40000140cf592e615b0a124a722a8fc471832615f89903e218108f82cc0b20000140c9552d295089b848a2130f346dc30b14f08e83ba17f09082f80b80000140c3352db153c9dc4922168f2c6cc30e15609543e219109182ec0b20000140bd3d2c714bc99e4672048e9469c2e914308bc398175091030c0be0000140b7372d7952c9ca47820b0efc6c830515889403da18d09003100ca0000140b11f2d5952c9de49621c8f646e231815c09583d417e08c02e00b40000140ab152cf14f49ba47d20e0f006dc30a15208ec3c018308f02f40c80000140a5192ce151c9de4902148f206b22fd14b88f43b217a08a82d80b800001409f0e2d795049a84652000e6c68a2e013c88bc3a217008982cc0ae000014098fc2d695249c647d20b0ec06a82fb14e09143d019709983200cc000014092ee2dc1564a084a02178f3c6dc31315989303fa18f09703200bc00001408cec2d1952c9d247e20e0ee86aa2f615109103bc18208f83180c6000014086c62e0154c9e449621c8f846fc32315e09403e418708f82ec0b6000014080c22d114f899c4732090ecc68e2ee14988d43b417d09083280c800001407a792f215f8a224a12210f9070a31d16209944161a80a403600ec000014074692d9152c9d44892140f306ec317159096041819e099036c0e400001406e6e2ca95009cc48b2138f286ce2fb15189303e218909003340c20000140682e2f515e4a1e4af2288fc871c33016909ec4201a309c834c0cc000014062472ca14bc9a84842110ee86b62f614e88d03a817708b02f00ce00001405c342da15289ec48d21f0f386e230115008ec3b618608f02f80ae0000140564e2c4148898e4662020e986962ed14b08e83cc18109182fc0ce000))))))))

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



private theorem b192670 : covered 192670 192770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192770 : covered 192770 192871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192871 : covered 192871 192971 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192971 : covered 192971 193071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193071 : covered 193071 193171 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193171 : covered 193171 193272 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193272 : covered 193272 193372 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193372 : covered 193372 193473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193473 : covered 193473 193573 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193573 : covered 193573 193674 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193674 : covered 193674 193774 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193774 : covered 193774 193875 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193875 : covered 193875 193975 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b193975 : covered 193975 194076 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194076 : covered 194076 194176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194176 : covered 194176 194277 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194277 : covered 194277 194377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194377 : covered 194377 194478 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194478 : covered 194478 194578 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194578 : covered 194578 194678 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194678 : covered 194678 194778 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194778 : covered 194778 194879 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194879 : covered 194879 194979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b194979 : covered 194979 195080 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195080 : covered 195080 195180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195180 : covered 195180 195281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195281 : covered 195281 195381 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195381 : covered 195381 195482 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195482 : covered 195482 195582 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195582 : covered 195582 195683 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195683 : covered 195683 195783 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195783 : covered 195783 195884 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195884 : covered 195884 195984 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b195984 : covered 195984 196085 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196085 : covered 196085 196185 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196185 : covered 196185 196285 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196285 : covered 196285 196385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196385 : covered 196385 196486 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196486 : covered 196486 196586 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196586 : covered 196586 196687 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196687 : covered 196687 196787 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196787 : covered 196787 196888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196888 : covered 196888 196988 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b196988 : covered 196988 197089 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197089 : covered 197089 197189 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197189 : covered 197189 197290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197290 : covered 197290 197390 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197390 : covered 197390 197491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197491 : covered 197491 197591 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197591 : covered 197591 197692 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197692 : covered 197692 197792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197792 : covered 197792 197893 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197893 : covered 197893 197993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b197993 : covered 197993 198094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198094 : covered 198094 198194 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198194 : covered 198194 198295 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198295 : covered 198295 198395 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198395 : covered 198395 198496 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198496 : covered 198496 198596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198596 : covered 198596 198697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198697 : covered 198697 198797 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198797 : covered 198797 198898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198898 : covered 198898 198998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b198998 : covered 198998 199099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199099 : covered 199099 199199 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199199 : covered 199199 199300 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199300 : covered 199300 199400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199400 : covered 199400 199500 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199500 : covered 199500 199600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199600 : covered 199600 199701 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199701 : covered 199701 199801 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199801 : covered 199801 199902 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b199902 : covered 199902 200002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200002 : covered 200002 200103 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200103 : covered 200103 200203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200203 : covered 200203 200304 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200304 : covered 200304 200404 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200404 : covered 200404 200505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200505 : covered 200505 200605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200605 : covered 200605 200706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200706 : covered 200706 200806 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200806 : covered 200806 200907 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b200907 : covered 200907 201007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201007 : covered 201007 201108 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201108 : covered 201108 201208 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201208 : covered 201208 201309 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201309 : covered 201309 201409 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201409 : covered 201409 201510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201510 : covered 201510 201610 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201610 : covered 201610 201711 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201711 : covered 201711 201811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201811 : covered 201811 201912 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b201912 : covered 201912 202012 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202012 : covered 202012 202113 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202113 : covered 202113 202213 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202213 : covered 202213 202314 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202314 : covered 202314 202414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202414 : covered 202414 202515 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202515 : covered 202515 202615 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202615 : covered 202615 202715 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202715 : covered 202715 202815 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202815 : covered 202815 202916 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b202916 : covered 202916 203016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203016 : covered 203016 203117 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203117 : covered 203117 203217 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203217 : covered 203217 203318 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203318 : covered 203318 203418 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203418 : covered 203418 203519 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203519 : covered 203519 203619 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203619 : covered 203619 203720 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203720 : covered 203720 203820 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203820 : covered 203820 203921 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b203921 : covered 203921 204021 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204021 : covered 204021 204122 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204122 : covered 204122 204222 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204222 : covered 204222 204323 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204323 : covered 204323 204423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204423 : covered 204423 204524 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204524 : covered 204524 204624 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204624 : covered 204624 204725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204725 : covered 204725 204825 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204825 : covered 204825 204926 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b204926 : covered 204926 205026 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205026 : covered 205026 205127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205127 : covered 205127 205227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205227 : covered 205227 205328 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205328 : covered 205328 205428 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205428 : covered 205428 205529 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205529 : covered 205529 205629 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b205629 : covered 205629 205730 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 192670 205730 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b192670 b192770) (joinCoverage b192871 b192971)) (joinCoverage (joinCoverage b193071 b193171) (joinCoverage b193272 b193372))) (joinCoverage (joinCoverage (joinCoverage b193473 b193573) (joinCoverage b193674 b193774)) (joinCoverage (joinCoverage b193875 b193975) (joinCoverage b194076 b194176)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b194277 b194377) (joinCoverage b194478 b194578)) (joinCoverage (joinCoverage b194678 b194778) (joinCoverage b194879 b194979))) (joinCoverage (joinCoverage (joinCoverage b195080 b195180) (joinCoverage b195281 b195381)) (joinCoverage (joinCoverage b195482 b195582) (joinCoverage b195683 b195783))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b195884 b195984) (joinCoverage b196085 b196185)) (joinCoverage (joinCoverage b196285 b196385) (joinCoverage b196486 b196586))) (joinCoverage (joinCoverage (joinCoverage b196687 b196787) (joinCoverage b196888 b196988)) (joinCoverage (joinCoverage b197089 b197189) (joinCoverage b197290 b197390)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b197491 b197591) (joinCoverage b197692 b197792)) (joinCoverage (joinCoverage b197893 b197993) (joinCoverage b198094 b198194))) (joinCoverage (joinCoverage (joinCoverage b198295 b198395) (joinCoverage b198496 b198596)) (joinCoverage (joinCoverage b198697 b198797) (joinCoverage b198898 (joinCoverage b198998 b199099))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b199199 b199300) (joinCoverage b199400 b199500)) (joinCoverage (joinCoverage b199600 b199701) (joinCoverage b199801 b199902))) (joinCoverage (joinCoverage (joinCoverage b200002 b200103) (joinCoverage b200203 b200304)) (joinCoverage (joinCoverage b200404 b200505) (joinCoverage b200605 b200706)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b200806 b200907) (joinCoverage b201007 b201108)) (joinCoverage (joinCoverage b201208 b201309) (joinCoverage b201409 b201510))) (joinCoverage (joinCoverage (joinCoverage b201610 b201711) (joinCoverage b201811 b201912)) (joinCoverage (joinCoverage b202012 b202113) (joinCoverage b202213 b202314))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b202414 b202515) (joinCoverage b202615 b202715)) (joinCoverage (joinCoverage b202815 b202916) (joinCoverage b203016 b203117))) (joinCoverage (joinCoverage (joinCoverage b203217 b203318) (joinCoverage b203418 b203519)) (joinCoverage (joinCoverage b203619 b203720) (joinCoverage b203820 b203921)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b204021 b204122) (joinCoverage b204222 b204323)) (joinCoverage (joinCoverage b204423 b204524) (joinCoverage b204624 b204725))) (joinCoverage (joinCoverage (joinCoverage b204825 b204926) (joinCoverage b205026 b205127)) (joinCoverage (joinCoverage b205227 b205328) (joinCoverage b205428 (joinCoverage b205529 b205629))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 192670 ≤ index 370000000/512 := by decide +kernel
private theorem starting_value : fast 370000000=19818405 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 370000000=19818405) (n : ℕ) (low : 370000000≤n) (bound : n≤395000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=370000000
    · rw [first,anchor]
      exact starting_value
    · have past : 370000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤395000000 by omega)
        have within : index n / 512 < 205730 := by omega
        have lower : index 370000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤395000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ370000000To395000000
