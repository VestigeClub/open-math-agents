import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ500000000To525000000

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




private def radical : ℕ := 0x2cc08efbd164c50975d87750decd199452bf6b8ae51d590d9e84170f2002b458a555955db45f9c436e877c6ebbd4e708819a6184b104de9db1a3db596804e6711a9d6c4c57e7bbde95b3b4e60083ae1331391372d24a377300fb25169c0905e5f973a3cb5d37f92fca359aacf69e8d6180eace1e97aec8d30f18398b4218f034fa428da2413162d12f1b44dbed20e30137d2ee7071abd26307bec942d47c0775f7409920bbbda6f491151ced9778bb9531402141dc76c7549732e072bc78a7333b11d0d92831cb06b351e743e3ad8c296bb704e54780005dfe6e5f1e7da57352385a86b645cb46b80ba234c35f976687c6274b7577eddb5098d604b0fd6e6d83b79cebf5c80e3ec53ca8862ee93f364e1f316454afc1ff731a136739434794ba13d25089d60f8e4cdd3fe4c34f3c66d763eb75de29d474485c077a0d0a2bcca643bd2b03873f93a9f6e40f527db7819cd95a4d13f51ac8e6f3d11ad4cd17a4457fa2730412ce7e96dfa16e004ee7a3bffe0e1f97be793a35adf5d73ec5a759a30f3117757377e9e6bfa1da9768acd6abf35247443841571c8b7cd7ff7c73c864b0c9e9ca1a48234e8a32489c2801a1709bd3d21310cdd0d9a42cb37f71ef23f2f237cda22a66c9feabe995d7263d21e8a9826b084825cc6569d4e1bc8705510932de2616b5c02e3d774ddef371c97f022bdc059e1f503ba350ca401bb608f56c584e815f5cf97cb90e91562e9223fb8784835dbfbb17b16a3905611aeca86acec7b024d18c621656343ffcb78551f54546b94646b20164921dbc4d0589c40502e54052e9c855171d1f203fe6a0c4f7fcae8566838e885eb7f83f2c562338396f13315e42a7447c4b2af27a81f8f40dad4996506072b7175db27e40371b1b3ed7325294d3a154a8918dcc98bac6f3432deb584b136810c13132d4d1167d9caa6978a9482f0d09e4aefb182187570f699c363a5a8d07f4ad1e78a48c532cd9bb1cc9d406b243f117fd7d336717742b1f463817ba4741f1037c956b265c8b959472c527abb7f3bda56278b7c08f9509c4f14aca7405f378fb1de56978cb65792214ec2d88ea9a72c3e6aad4cf7c534b1314fcb43d6b70f56c5f41eec4e679cc08e3633cc0db908ca44b1194c245c9cb7c9c525310934178221c4222a0b0953ac292916777a2f07043d36e03e8cb5d3d1cad1af31b9d326f0830e74fe0a3a6ec051a04dee51dd4da72b783d8e5650fe3a48ab4b8a61519f458e8af0ec13297caf1e11fed8a6a61df49f8bc97f4377db417036132840337811f0d6a43c995a1e756dcfa22be596f609b810624f8d116f96f728c67602f7ddf4476c82f2cf8b3f00a3b2de9c3c0ced79033a163eb808114280f65ed9d788031554d8d6cae4e61f5fa39c97b58cc91303ac6f700ac5acaf8ddb6478d4a8f0197167079f0c76f50ba5276b2834e87af60bed5461b944d8aa5f82cd3bdf4fe58394b1a7043ee7846dc131ba1d0bb6540b3968675b51f27532fa9659d744f5d64fb906f19f4cd4105496848a75934c4c4ecda18d4636ceb65e89b6082658d6881b3d1d06e6c9d8aca1a257e42be85da9df3ce61e5958679d05fede41727e3a6cd51c873a27e3a50ee56a43556ddeaa5a08268f9b8c797f3ffd2971d80db4cb0223bc4e826caf6350f095d9f6b2b1923731f048e7f1cdfc88d9bdc4ae0e9bc95e18bbe6b99359c4fe1258e8303cb0ffdc037cdcf89d48423c7cb73429dd46c22d0886962c2bdd454bb23085c3c5d609221d03356f65289058637b180f3b817a2a7bf56647b12eebe5a58dd63e37620b8b7bd06e952ad2c2743f26c2493056cef1869c17e6e2d923c156fcdd6ec06cef80e90866f6912b2333b9161d8b25765abfd7ce1aaece017d43ea786483c416037a5938d1f3a0983dc280d9f4dca18f5bf3127036a345f4ca527eab92f056603c01986cb9415bd4150e1737071842fc7a26d6b568aa3e556cdd3b0bc117881dfb6295333fe03c101335fc3326c10cd0aee47386a1c1c3f0fb9a0218114a98cc552d9e335c5750aca23eb96dc3629ca345d6b91f9fd43ac4e1a0e4afb9fad2f18fa2e22e2ad8c0cf4d2514114e5cef6070e8f7306f78754dcf4c64f4fde8f899e7abbba1ac7880733a80b8c9bd3075d7525ffe14286e513fde6f5fd8390628a2e4c14a50d456a5850e58592fc6610f911f08d36affb04a34b53ae164a2f46d620165e24b5e96b78bfaaa9a1723aa81718e30e0faf00d5d232118780f3438cfa56f426e5ccd932dba32dd74fb4f04aef7c9ea62d073b43e24043687b1469b9f4dc2b19306c9ed80c447f28ec4f1558bd1684cf636c71b63142dc862fe9282b32bc85294d7b024c60b685bf4cf86aa1fcdad37d137db8935fe31255dfd5400e9ae59bc55df3979e8487ab9bc1867221c9f0eb6420fabe7550b9c9be966aba02619ed2fb3fc7398762f2aeb81da3aae4d5453ede428d5fa0f95a0b7c981873b94f35b805fd0b46b18de56b82ad119e3d2655045fe1b0d5e90aa00acad06849117e9a8815c89df4441b05678c1700c1cc549accb9479ad45c85d467088568c9459533876c5121d194684308daae602945518ab7e15d771aae58ecace572b77c69219abb2e16919b7a9d5154c0240eddd480d8c826a7deba1eb27fd59d162835a1bcc7fefe853899ad7e7da67bf5d130a1721db3aa1728799d9ee4e68387845150129d6e465279d1311c974b2c7760b9e5698e252f66fd61a92e661636715a2e9e3e2cf0a292be24516adf2df12fd7bff0f7a629cb22e7c80e8436c36da611bc12f9fa16fb39f4380232a27a4e9a1f2cb0375f14b1468c30a40b614551894775a315811caed9528760c752c95416c20f4f07cf7bf3f776530a360385f8b977a1c40442e3be84ad689ac45d1bc4726bc6bc9056c36cceca3146ec5c4879afbe9a9d19d78978cbdac6614a5ae84935de5bb2fdfbb306e293575417a9853eb36c13c7b43f9a82de81d838078da5745665691a912148b757f5d62f88048e11d9e3bbeeab0abf7ac5ecf9d6cd1b7dbdc2a2f96a069899b10a40b33593057a149cfa1f6a50ce838125a913fdb2069443af0d3cc4da8ec5107541db94229376a757e32f0d696f05ac9c62e3cb76e365a76bb58c007790ea3c13517327895146d261fd270127a8bb886f07f724b74dc5fce46c18450bc34da493badfc32947ee98842d550a21c626dd6bde8326a79bc15a90f02a827a83834d4fdabfeae764f4e46a377b7ddbf150e6fc76759e400662e5e85538263b6f8420a57e88d6e6228c276790978fe5ac2595971e3250333788092ec7cfebfec97835d5779ed14710fb64dd67546d38d7eeda1126c699a376ac0df44ed8d032c74623247b3ab84232e679156b7f20fe4b4138b5c2141991001234414877c7dd3db0737fda8f9eb6fd08eb1f80d4624c71ce7397dea0a0a243e082b4d392a5420afee1e8f0a94a4f5e7076b0ff170567c01f4d67aca8e016785a9492ea00a07b6415836fa3359e43a9b37097e317206e56cb1cc79cb755ccf267d29d3ad437aed25073176167459a7bf5c0a443b613b45b55852eb0851ff8a0b7531aa286686f546d414e7b329b01936ada46b0efe111b1f9893f631ab641130fd836cd7bf7732d7408d88350c41a28713dad2bb1fbb49ac9d496e29af3901d7269aba6690116f786d900aab7cf80187ee2d1a58d8a4acfe22bc979938f1205eda602cc6ee5df8aabdefeb26c7bc9834441e406166e9d62ddd0d70de7c91ea9c218919ca05048bcc74b498426e59c80897f412f243d47fe728ca1d897d1e59823ee203256044f78de06c8d461d5413d871a55be6cf8727a681df9e64c8114205317995844a7644348a3c2daa844db9a5fe3b894d5593afaa5a3ccdcd1838f9af4ed67fa4528d40cb7ee463a9a1fda4732e2006d2738ee471ff6f1e16018446352176bc94b5750fa51bbf6a444ecd25235bd5fffd68d24cc6b613c68e9534f7c3b7aec4762e8342c731c5b7888faeb8aacbbad5ef52d9a1960f3a633f88cf3632e61f2e93bad5307f993c8b119d46101b8983df76c730ec01ac5ba77f0c55c578d15c1ac7bd794988d58b6a657c96f6cb51894354a480c48d4c0a9bec057e8e734eac450992c528a735ecb56adb70bd76a7a5cd7755f9033516de36379533dab015f52a4332d7dc04ebe9c1b1f84ba8dca7b0330480e165bb07d9a0a99ce3642d41a0a2ce8e9547a17747c0dd8625a2448c56e043e4c9f839052346023963614e3423ac29109bbc38d43fcd487cb02e70c49b14776c71abadc835a27a0553ee586e7bef5b0163eaf077335426c7cc6e09823171e4b22308a98ae394314c66872a2bd5cf9916daee906fb80d39632a9ab5eae161ac06bf01b4eabf6e8d73100fdaa429de5c270ba729bd4c7a417255eb55e5f16ec665532d8f2e6ea75f63b5dc3c3bc6eed71baaf1dda739e7f7ac458065691f854a4326c9d558e52aa70bc8744b0cc825e664113c6cf069abbc85f7a130543a6d05f5279d22d9f5205f9bc79534206544623649f82ce3477a253ee00969c5670d5fe4d1ea622e636d03a0d8e86db163b93537d58ca8651a15fc2b61e467ae945f9a13e82d3c354236c7731068bb2681f1da30f3789f75e934bcf4d91932b4b6786b693ae4003c5c3eda1e1287c9b4da84d9c8babbfd4f7d5adc14ab04d4ea1a471b1e6eeda4c4e15bc25a98d497a52840b74c59fb6a47f78c08f9f71d1d8d36327f5bab866be1963dafbf76615d533300bfeb5d2b1777dccf3d7916758edba8956da163a00abdb36ed6b4f0bb2de46d63a43478050085e5eb11d6b44a7826cc95e58026531c95a4bc8854fa022cf5f59295f6010752e70fc320024895c7077944eddaaa78d6cf15579c6e2ad524ad955c0f299295cc9f4c82d996a6515a92e6d1af359a6ec54e0422679abf19941e6c75d730788e9776093a036e92ee490caefd0fca9fa4df686deb8a6d200ad7eb4a8562bc9f3f9365fb7156fc3c562d44e03e4ca33cd5be6c2d7757489cb2aaf403ef407c185deceeb84ecd6ac9b1353d6b4bbcad7ad252aaf552c40e1e34ef2ef4aa7c8548f6b90335e2c36bfb1859aa2e1051ae4613b7201d7423b76912e018519328c620f1203acf07374bd27d37b00f9c6bcc849490dfb3000fe79ea74d3738ef08bb711e28445a55595ad84066bc38cda20b60ef8d08b28cc1b4d22865116d3cf438e3b8e11aab1991044b0cf241734bee8874fff5000cca104b0923fb1fbe9aee41e730b2c3b823850de2d44475513b773e4a0f59ba4c66362002ade69a1dfc708a7e6a7f079fa13f6d98b4cd4e654d44b2c41fc8ac2e2a117cc65fa0536b2376913da7e6c038e23de70562b3250282d65d4a8547dc1ac607939b6b2b86b7805887d024d767e122b9875469b09532663d3be58142160c8d60804fc0e998ce88e2d677c3f8068f0f299ed43b03e0acee05ae2be43a1f2108e211058b454fdbd7d2fcacb87f442938d278533415eea1f50381e833c46d891274405c4e230642f3f78fb4ea5728a40f4dfaeab366bc4dadd3ccd223b7eacc30b5109c675290934b214d78991dae3ecc8403a969b6f80298bf3a8fde20f235e3140e8795200c5f53a57418a71d0de38cf5949838aa0a97eb61c5bdf3b11d9de044fbbb8da982424de8eedeaa2f04f5b18c5ddc85a4a5b208ae25fe65931dca9dfd2d278c235b0eb844372ef19ddac00ca663bfc16c94b988ca586cbe0950816c90d79cfb8bd80bb84cbf3af63f072b96af37323ac6c98a1ec366fe417c9a2756

private def light (n : ℕ) : Bool :=
  if n≤151 then decide n.Prime else n.gcd 8627209774233240431623188626544191544816225903687700891564804750810154197851655157362112747789971982951943289690774984828562603780001360174419748328584232052816331406456102618328128950857189333333217935399039885261005462721003520000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤22912) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 151 = 8627209774233240431623188626544191544816225903687700891564804750810154197851655157362112747789971982951943289690774984828562603780001360174419748328584232052816331406456102618328128950857189333333217935399039885261005462721003520000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 151 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤22912 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 44 := by unfold smallValid; decide +kernel

private theorem sp44 : smallValid 44 45 := by unfold smallValid; decide +kernel

private theorem sp89 : smallValid 89 45 := by unfold smallValid; decide +kernel

private theorem sp134 : smallValid 134 45 := by unfold smallValid; decide +kernel

private theorem sp179 : smallValid 179 44 := by unfold smallValid; decide +kernel

private theorem sp223 : smallValid 223 45 := by unfold smallValid; decide +kernel

private theorem sp268 : smallValid 268 45 := by unfold smallValid; decide +kernel

private theorem sp313 : smallValid 313 45 := by unfold smallValid; decide +kernel

private theorem sp358 : smallValid 358 44 := by unfold smallValid; decide +kernel

private theorem sp402 : smallValid 402 45 := by unfold smallValid; decide +kernel

private theorem sp447 : smallValid 447 45 := by unfold smallValid; decide +kernel

private theorem sp492 : smallValid 492 45 := by unfold smallValid; decide +kernel

private theorem sp537 : smallValid 537 44 := by unfold smallValid; decide +kernel

private theorem sp581 : smallValid 581 45 := by unfold smallValid; decide +kernel

private theorem sp626 : smallValid 626 45 := by unfold smallValid; decide +kernel

private theorem sp671 : smallValid 671 45 := by unfold smallValid; decide +kernel

private theorem sp716 : smallValid 716 44 := by unfold smallValid; decide +kernel

private theorem sp760 : smallValid 760 45 := by unfold smallValid; decide +kernel

private theorem sp805 : smallValid 805 45 := by unfold smallValid; decide +kernel

private theorem sp850 : smallValid 850 45 := by unfold smallValid; decide +kernel

private theorem sp895 : smallValid 895 44 := by unfold smallValid; decide +kernel

private theorem sp939 : smallValid 939 45 := by unfold smallValid; decide +kernel

private theorem sp984 : smallValid 984 45 := by unfold smallValid; decide +kernel

private theorem sp1029 : smallValid 1029 45 := by unfold smallValid; decide +kernel

private theorem sp1074 : smallValid 1074 44 := by unfold smallValid; decide +kernel

private theorem sp1118 : smallValid 1118 45 := by unfold smallValid; decide +kernel

private theorem sp1163 : smallValid 1163 45 := by unfold smallValid; decide +kernel

private theorem sp1208 : smallValid 1208 45 := by unfold smallValid; decide +kernel

private theorem sp1253 : smallValid 1253 44 := by unfold smallValid; decide +kernel

private theorem sp1297 : smallValid 1297 45 := by unfold smallValid; decide +kernel

private theorem sp1342 : smallValid 1342 45 := by unfold smallValid; decide +kernel

private theorem sp1387 : smallValid 1387 45 := by unfold smallValid; decide +kernel

private theorem sp1432 : smallValid 1432 44 := by unfold smallValid; decide +kernel

private theorem sp1476 : smallValid 1476 45 := by unfold smallValid; decide +kernel

private theorem sp1521 : smallValid 1521 45 := by unfold smallValid; decide +kernel

private theorem sp1566 : smallValid 1566 45 := by unfold smallValid; decide +kernel

private theorem sp1611 : smallValid 1611 44 := by unfold smallValid; decide +kernel

private theorem sp1655 : smallValid 1655 45 := by unfold smallValid; decide +kernel

private theorem sp1700 : smallValid 1700 45 := by unfold smallValid; decide +kernel

private theorem sp1745 : smallValid 1745 45 := by unfold smallValid; decide +kernel

private theorem sp1790 : smallValid 1790 44 := by unfold smallValid; decide +kernel

private theorem sp1834 : smallValid 1834 45 := by unfold smallValid; decide +kernel

private theorem sp1879 : smallValid 1879 45 := by unfold smallValid; decide +kernel

private theorem sp1924 : smallValid 1924 45 := by unfold smallValid; decide +kernel

private theorem sp1969 : smallValid 1969 44 := by unfold smallValid; decide +kernel

private theorem sp2013 : smallValid 2013 45 := by unfold smallValid; decide +kernel

private theorem sp2058 : smallValid 2058 45 := by unfold smallValid; decide +kernel

private theorem sp2103 : smallValid 2103 45 := by unfold smallValid; decide +kernel

private theorem sp2148 : smallValid 2148 44 := by unfold smallValid; decide +kernel

private theorem sp2192 : smallValid 2192 45 := by unfold smallValid; decide +kernel

private theorem sp2237 : smallValid 2237 45 := by unfold smallValid; decide +kernel

private theorem sp2282 : smallValid 2282 45 := by unfold smallValid; decide +kernel

private theorem sp2327 : smallValid 2327 44 := by unfold smallValid; decide +kernel

private theorem sp2371 : smallValid 2371 45 := by unfold smallValid; decide +kernel

private theorem sp2416 : smallValid 2416 45 := by unfold smallValid; decide +kernel

private theorem sp2461 : smallValid 2461 45 := by unfold smallValid; decide +kernel

private theorem sp2506 : smallValid 2506 44 := by unfold smallValid; decide +kernel

private theorem sp2550 : smallValid 2550 45 := by unfold smallValid; decide +kernel

private theorem sp2595 : smallValid 2595 45 := by unfold smallValid; decide +kernel

private theorem sp2640 : smallValid 2640 45 := by unfold smallValid; decide +kernel

private theorem sp2685 : smallValid 2685 44 := by unfold smallValid; decide +kernel

private theorem sp2729 : smallValid 2729 45 := by unfold smallValid; decide +kernel

private theorem sp2774 : smallValid 2774 45 := by unfold smallValid; decide +kernel

private theorem sp2819 : smallValid 2819 45 := by unfold smallValid; decide +kernel

private theorem sp2864 : smallValid 2864 44 := by unfold smallValid; decide +kernel

private theorem sp2908 : smallValid 2908 45 := by unfold smallValid; decide +kernel

private theorem sp2953 : smallValid 2953 45 := by unfold smallValid; decide +kernel

private theorem sp2998 : smallValid 2998 45 := by unfold smallValid; decide +kernel

private theorem sp3043 : smallValid 3043 44 := by unfold smallValid; decide +kernel

private theorem sp3087 : smallValid 3087 45 := by unfold smallValid; decide +kernel

private theorem sp3132 : smallValid 3132 45 := by unfold smallValid; decide +kernel

private theorem sp3177 : smallValid 3177 45 := by unfold smallValid; decide +kernel

private theorem sp3222 : smallValid 3222 44 := by unfold smallValid; decide +kernel

private theorem sp3266 : smallValid 3266 45 := by unfold smallValid; decide +kernel

private theorem sp3311 : smallValid 3311 45 := by unfold smallValid; decide +kernel

private theorem sp3356 : smallValid 3356 45 := by unfold smallValid; decide +kernel

private theorem sp3401 : smallValid 3401 44 := by unfold smallValid; decide +kernel

private theorem sp3445 : smallValid 3445 45 := by unfold smallValid; decide +kernel

private theorem sp3490 : smallValid 3490 45 := by unfold smallValid; decide +kernel

private theorem sp3535 : smallValid 3535 45 := by unfold smallValid; decide +kernel

private theorem sp3580 : smallValid 3580 44 := by unfold smallValid; decide +kernel

private theorem sp3624 : smallValid 3624 45 := by unfold smallValid; decide +kernel

private theorem sp3669 : smallValid 3669 45 := by unfold smallValid; decide +kernel

private theorem sp3714 : smallValid 3714 45 := by unfold smallValid; decide +kernel

private theorem sp3759 : smallValid 3759 44 := by unfold smallValid; decide +kernel

private theorem sp3803 : smallValid 3803 45 := by unfold smallValid; decide +kernel

private theorem sp3848 : smallValid 3848 45 := by unfold smallValid; decide +kernel

private theorem sp3893 : smallValid 3893 45 := by unfold smallValid; decide +kernel

private theorem sp3938 : smallValid 3938 44 := by unfold smallValid; decide +kernel

private theorem sp3982 : smallValid 3982 45 := by unfold smallValid; decide +kernel

private theorem sp4027 : smallValid 4027 45 := by unfold smallValid; decide +kernel

private theorem sp4072 : smallValid 4072 45 := by unfold smallValid; decide +kernel

private theorem sp4117 : smallValid 4117 44 := by unfold smallValid; decide +kernel

private theorem sp4161 : smallValid 4161 45 := by unfold smallValid; decide +kernel

private theorem sp4206 : smallValid 4206 45 := by unfold smallValid; decide +kernel

private theorem sp4251 : smallValid 4251 45 := by unfold smallValid; decide +kernel

private theorem sp4296 : smallValid 4296 44 := by unfold smallValid; decide +kernel

private theorem sp4340 : smallValid 4340 45 := by unfold smallValid; decide +kernel

private theorem sp4385 : smallValid 4385 45 := by unfold smallValid; decide +kernel

private theorem sp4430 : smallValid 4430 45 := by unfold smallValid; decide +kernel

private theorem sp4475 : smallValid 4475 44 := by unfold smallValid; decide +kernel

private theorem sp4519 : smallValid 4519 45 := by unfold smallValid; decide +kernel

private theorem sp4564 : smallValid 4564 45 := by unfold smallValid; decide +kernel

private theorem sp4609 : smallValid 4609 45 := by unfold smallValid; decide +kernel

private theorem sp4654 : smallValid 4654 44 := by unfold smallValid; decide +kernel

private theorem sp4698 : smallValid 4698 45 := by unfold smallValid; decide +kernel

private theorem sp4743 : smallValid 4743 45 := by unfold smallValid; decide +kernel

private theorem sp4788 : smallValid 4788 45 := by unfold smallValid; decide +kernel

private theorem sp4833 : smallValid 4833 44 := by unfold smallValid; decide +kernel

private theorem sp4877 : smallValid 4877 45 := by unfold smallValid; decide +kernel

private theorem sp4922 : smallValid 4922 45 := by unfold smallValid; decide +kernel

private theorem sp4967 : smallValid 4967 45 := by unfold smallValid; decide +kernel

private theorem sp5012 : smallValid 5012 44 := by unfold smallValid; decide +kernel

private theorem sp5056 : smallValid 5056 45 := by unfold smallValid; decide +kernel

private theorem sp5101 : smallValid 5101 45 := by unfold smallValid; decide +kernel

private theorem sp5146 : smallValid 5146 45 := by unfold smallValid; decide +kernel

private theorem sp5191 : smallValid 5191 44 := by unfold smallValid; decide +kernel

private theorem sp5235 : smallValid 5235 45 := by unfold smallValid; decide +kernel

private theorem sp5280 : smallValid 5280 45 := by unfold smallValid; decide +kernel

private theorem sp5325 : smallValid 5325 45 := by unfold smallValid; decide +kernel

private theorem sp5370 : smallValid 5370 44 := by unfold smallValid; decide +kernel

private theorem sp5414 : smallValid 5414 45 := by unfold smallValid; decide +kernel

private theorem sp5459 : smallValid 5459 45 := by unfold smallValid; decide +kernel

private theorem sp5504 : smallValid 5504 45 := by unfold smallValid; decide +kernel

private theorem sp5549 : smallValid 5549 44 := by unfold smallValid; decide +kernel

private theorem sp5593 : smallValid 5593 45 := by unfold smallValid; decide +kernel

private theorem sp5638 : smallValid 5638 45 := by unfold smallValid; decide +kernel

private theorem sp5683 : smallValid 5683 45 := by unfold smallValid; decide +kernel

private theorem sp5728 : smallValid 5728 44 := by unfold smallValid; decide +kernel

private theorem sp5772 : smallValid 5772 45 := by unfold smallValid; decide +kernel

private theorem sp5817 : smallValid 5817 45 := by unfold smallValid; decide +kernel

private theorem sp5862 : smallValid 5862 45 := by unfold smallValid; decide +kernel

private theorem sp5907 : smallValid 5907 44 := by unfold smallValid; decide +kernel

private theorem sp5951 : smallValid 5951 45 := by unfold smallValid; decide +kernel

private theorem sp5996 : smallValid 5996 45 := by unfold smallValid; decide +kernel

private theorem sp6041 : smallValid 6041 45 := by unfold smallValid; decide +kernel

private theorem sp6086 : smallValid 6086 44 := by unfold smallValid; decide +kernel

private theorem sp6130 : smallValid 6130 45 := by unfold smallValid; decide +kernel

private theorem sp6175 : smallValid 6175 45 := by unfold smallValid; decide +kernel

private theorem sp6220 : smallValid 6220 45 := by unfold smallValid; decide +kernel

private theorem sp6265 : smallValid 6265 44 := by unfold smallValid; decide +kernel

private theorem sp6309 : smallValid 6309 45 := by unfold smallValid; decide +kernel

private theorem sp6354 : smallValid 6354 45 := by unfold smallValid; decide +kernel

private theorem sp6399 : smallValid 6399 45 := by unfold smallValid; decide +kernel

private theorem sp6444 : smallValid 6444 44 := by unfold smallValid; decide +kernel

private theorem sp6488 : smallValid 6488 45 := by unfold smallValid; decide +kernel

private theorem sp6533 : smallValid 6533 45 := by unfold smallValid; decide +kernel

private theorem sp6578 : smallValid 6578 45 := by unfold smallValid; decide +kernel

private theorem sp6623 : smallValid 6623 44 := by unfold smallValid; decide +kernel

private theorem sp6667 : smallValid 6667 45 := by unfold smallValid; decide +kernel

private theorem sp6712 : smallValid 6712 45 := by unfold smallValid; decide +kernel

private theorem sp6757 : smallValid 6757 45 := by unfold smallValid; decide +kernel

private theorem sp6802 : smallValid 6802 44 := by unfold smallValid; decide +kernel

private theorem sp6846 : smallValid 6846 45 := by unfold smallValid; decide +kernel

private theorem sp6891 : smallValid 6891 45 := by unfold smallValid; decide +kernel

private theorem sp6936 : smallValid 6936 45 := by unfold smallValid; decide +kernel

private theorem sp6981 : smallValid 6981 44 := by unfold smallValid; decide +kernel

private theorem sp7025 : smallValid 7025 45 := by unfold smallValid; decide +kernel

private theorem sp7070 : smallValid 7070 45 := by unfold smallValid; decide +kernel

private theorem sp7115 : smallValid 7115 45 := by unfold smallValid; decide +kernel

private theorem sp7160 : smallValid 7160 44 := by unfold smallValid; decide +kernel

private theorem sp7204 : smallValid 7204 45 := by unfold smallValid; decide +kernel

private theorem sp7249 : smallValid 7249 45 := by unfold smallValid; decide +kernel

private theorem sp7294 : smallValid 7294 45 := by unfold smallValid; decide +kernel

private theorem sp7339 : smallValid 7339 44 := by unfold smallValid; decide +kernel

private theorem sp7383 : smallValid 7383 45 := by unfold smallValid; decide +kernel

private theorem sp7428 : smallValid 7428 45 := by unfold smallValid; decide +kernel

private theorem sp7473 : smallValid 7473 45 := by unfold smallValid; decide +kernel

private theorem sp7518 : smallValid 7518 44 := by unfold smallValid; decide +kernel

private theorem sp7562 : smallValid 7562 45 := by unfold smallValid; decide +kernel

private theorem sp7607 : smallValid 7607 45 := by unfold smallValid; decide +kernel

private theorem sp7652 : smallValid 7652 45 := by unfold smallValid; decide +kernel

private theorem sp7697 : smallValid 7697 44 := by unfold smallValid; decide +kernel

private theorem sp7741 : smallValid 7741 45 := by unfold smallValid; decide +kernel

private theorem sp7786 : smallValid 7786 45 := by unfold smallValid; decide +kernel

private theorem sp7831 : smallValid 7831 45 := by unfold smallValid; decide +kernel

private theorem sp7876 : smallValid 7876 44 := by unfold smallValid; decide +kernel

private theorem sp7920 : smallValid 7920 45 := by unfold smallValid; decide +kernel

private theorem sp7965 : smallValid 7965 45 := by unfold smallValid; decide +kernel

private theorem sp8010 : smallValid 8010 45 := by unfold smallValid; decide +kernel

private theorem sp8055 : smallValid 8055 44 := by unfold smallValid; decide +kernel

private theorem sp8099 : smallValid 8099 45 := by unfold smallValid; decide +kernel

private theorem sp8144 : smallValid 8144 45 := by unfold smallValid; decide +kernel

private theorem sp8189 : smallValid 8189 45 := by unfold smallValid; decide +kernel

private theorem sp8234 : smallValid 8234 44 := by unfold smallValid; decide +kernel

private theorem sp8278 : smallValid 8278 45 := by unfold smallValid; decide +kernel

private theorem sp8323 : smallValid 8323 45 := by unfold smallValid; decide +kernel

private theorem sp8368 : smallValid 8368 45 := by unfold smallValid; decide +kernel

private theorem sp8413 : smallValid 8413 44 := by unfold smallValid; decide +kernel

private theorem sp8457 : smallValid 8457 45 := by unfold smallValid; decide +kernel

private theorem sp8502 : smallValid 8502 45 := by unfold smallValid; decide +kernel

private theorem sp8547 : smallValid 8547 45 := by unfold smallValid; decide +kernel

private theorem sp8592 : smallValid 8592 44 := by unfold smallValid; decide +kernel

private theorem sp8636 : smallValid 8636 45 := by unfold smallValid; decide +kernel

private theorem sp8681 : smallValid 8681 45 := by unfold smallValid; decide +kernel

private theorem sp8726 : smallValid 8726 45 := by unfold smallValid; decide +kernel

private theorem sp8771 : smallValid 8771 44 := by unfold smallValid; decide +kernel

private theorem sp8815 : smallValid 8815 45 := by unfold smallValid; decide +kernel

private theorem sp8860 : smallValid 8860 45 := by unfold smallValid; decide +kernel

private theorem sp8905 : smallValid 8905 45 := by unfold smallValid; decide +kernel

private theorem sp8950 : smallValid 8950 44 := by unfold smallValid; decide +kernel

private theorem sp8994 : smallValid 8994 45 := by unfold smallValid; decide +kernel

private theorem sp9039 : smallValid 9039 45 := by unfold smallValid; decide +kernel

private theorem sp9084 : smallValid 9084 45 := by unfold smallValid; decide +kernel

private theorem sp9129 : smallValid 9129 44 := by unfold smallValid; decide +kernel

private theorem sp9173 : smallValid 9173 45 := by unfold smallValid; decide +kernel

private theorem sp9218 : smallValid 9218 45 := by unfold smallValid; decide +kernel

private theorem sp9263 : smallValid 9263 45 := by unfold smallValid; decide +kernel

private theorem sp9308 : smallValid 9308 44 := by unfold smallValid; decide +kernel

private theorem sp9352 : smallValid 9352 45 := by unfold smallValid; decide +kernel

private theorem sp9397 : smallValid 9397 45 := by unfold smallValid; decide +kernel

private theorem sp9442 : smallValid 9442 45 := by unfold smallValid; decide +kernel

private theorem sp9487 : smallValid 9487 44 := by unfold smallValid; decide +kernel

private theorem sp9531 : smallValid 9531 45 := by unfold smallValid; decide +kernel

private theorem sp9576 : smallValid 9576 45 := by unfold smallValid; decide +kernel

private theorem sp9621 : smallValid 9621 45 := by unfold smallValid; decide +kernel

private theorem sp9666 : smallValid 9666 44 := by unfold smallValid; decide +kernel

private theorem sp9710 : smallValid 9710 45 := by unfold smallValid; decide +kernel

private theorem sp9755 : smallValid 9755 45 := by unfold smallValid; decide +kernel

private theorem sp9800 : smallValid 9800 45 := by unfold smallValid; decide +kernel

private theorem sp9845 : smallValid 9845 44 := by unfold smallValid; decide +kernel

private theorem sp9889 : smallValid 9889 45 := by unfold smallValid; decide +kernel

private theorem sp9934 : smallValid 9934 45 := by unfold smallValid; decide +kernel

private theorem sp9979 : smallValid 9979 45 := by unfold smallValid; decide +kernel

private theorem sp10024 : smallValid 10024 44 := by unfold smallValid; decide +kernel

private theorem sp10068 : smallValid 10068 45 := by unfold smallValid; decide +kernel

private theorem sp10113 : smallValid 10113 45 := by unfold smallValid; decide +kernel

private theorem sp10158 : smallValid 10158 45 := by unfold smallValid; decide +kernel

private theorem sp10203 : smallValid 10203 44 := by unfold smallValid; decide +kernel

private theorem sp10247 : smallValid 10247 45 := by unfold smallValid; decide +kernel

private theorem sp10292 : smallValid 10292 45 := by unfold smallValid; decide +kernel

private theorem sp10337 : smallValid 10337 45 := by unfold smallValid; decide +kernel

private theorem sp10382 : smallValid 10382 44 := by unfold smallValid; decide +kernel

private theorem sp10426 : smallValid 10426 45 := by unfold smallValid; decide +kernel

private theorem sp10471 : smallValid 10471 45 := by unfold smallValid; decide +kernel

private theorem sp10516 : smallValid 10516 45 := by unfold smallValid; decide +kernel

private theorem sp10561 : smallValid 10561 44 := by unfold smallValid; decide +kernel

private theorem sp10605 : smallValid 10605 45 := by unfold smallValid; decide +kernel

private theorem sp10650 : smallValid 10650 45 := by unfold smallValid; decide +kernel

private theorem sp10695 : smallValid 10695 45 := by unfold smallValid; decide +kernel

private theorem sp10740 : smallValid 10740 44 := by unfold smallValid; decide +kernel

private theorem sp10784 : smallValid 10784 45 := by unfold smallValid; decide +kernel

private theorem sp10829 : smallValid 10829 45 := by unfold smallValid; decide +kernel

private theorem sp10874 : smallValid 10874 45 := by unfold smallValid; decide +kernel

private theorem sp10919 : smallValid 10919 44 := by unfold smallValid; decide +kernel

private theorem sp10963 : smallValid 10963 45 := by unfold smallValid; decide +kernel

private theorem sp11008 : smallValid 11008 45 := by unfold smallValid; decide +kernel

private theorem sp11053 : smallValid 11053 45 := by unfold smallValid; decide +kernel

private theorem sp11098 : smallValid 11098 44 := by unfold smallValid; decide +kernel

private theorem sp11142 : smallValid 11142 45 := by unfold smallValid; decide +kernel

private theorem sp11187 : smallValid 11187 45 := by unfold smallValid; decide +kernel

private theorem sp11232 : smallValid 11232 45 := by unfold smallValid; decide +kernel

private theorem sp11277 : smallValid 11277 44 := by unfold smallValid; decide +kernel

private theorem sp11321 : smallValid 11321 45 := by unfold smallValid; decide +kernel

private theorem sp11366 : smallValid 11366 45 := by unfold smallValid; decide +kernel

private theorem sp11411 : smallValid 11411 45 := by unfold smallValid; decide +kernel

private theorem sp11456 : smallValid 11456 44 := by unfold smallValid; decide +kernel

private theorem sp11500 : smallValid 11500 45 := by unfold smallValid; decide +kernel

private theorem sp11545 : smallValid 11545 45 := by unfold smallValid; decide +kernel

private theorem sp11590 : smallValid 11590 45 := by unfold smallValid; decide +kernel

private theorem sp11635 : smallValid 11635 44 := by unfold smallValid; decide +kernel

private theorem sp11679 : smallValid 11679 45 := by unfold smallValid; decide +kernel

private theorem sp11724 : smallValid 11724 45 := by unfold smallValid; decide +kernel

private theorem sp11769 : smallValid 11769 45 := by unfold smallValid; decide +kernel

private theorem sp11814 : smallValid 11814 44 := by unfold smallValid; decide +kernel

private theorem sp11858 : smallValid 11858 45 := by unfold smallValid; decide +kernel

private theorem sp11903 : smallValid 11903 45 := by unfold smallValid; decide +kernel

private theorem sp11948 : smallValid 11948 45 := by unfold smallValid; decide +kernel

private theorem sp11993 : smallValid 11993 44 := by unfold smallValid; decide +kernel

private theorem sp12037 : smallValid 12037 45 := by unfold smallValid; decide +kernel

private theorem sp12082 : smallValid 12082 45 := by unfold smallValid; decide +kernel

private theorem sp12127 : smallValid 12127 45 := by unfold smallValid; decide +kernel

private theorem sp12172 : smallValid 12172 44 := by unfold smallValid; decide +kernel

private theorem sp12216 : smallValid 12216 45 := by unfold smallValid; decide +kernel

private theorem sp12261 : smallValid 12261 45 := by unfold smallValid; decide +kernel

private theorem sp12306 : smallValid 12306 45 := by unfold smallValid; decide +kernel

private theorem sp12351 : smallValid 12351 44 := by unfold smallValid; decide +kernel

private theorem sp12395 : smallValid 12395 45 := by unfold smallValid; decide +kernel

private theorem sp12440 : smallValid 12440 45 := by unfold smallValid; decide +kernel

private theorem sp12485 : smallValid 12485 45 := by unfold smallValid; decide +kernel

private theorem sp12530 : smallValid 12530 44 := by unfold smallValid; decide +kernel

private theorem sp12574 : smallValid 12574 45 := by unfold smallValid; decide +kernel

private theorem sp12619 : smallValid 12619 45 := by unfold smallValid; decide +kernel

private theorem sp12664 : smallValid 12664 45 := by unfold smallValid; decide +kernel

private theorem sp12709 : smallValid 12709 44 := by unfold smallValid; decide +kernel

private theorem sp12753 : smallValid 12753 45 := by unfold smallValid; decide +kernel

private theorem sp12798 : smallValid 12798 45 := by unfold smallValid; decide +kernel

private theorem sp12843 : smallValid 12843 45 := by unfold smallValid; decide +kernel

private theorem sp12888 : smallValid 12888 44 := by unfold smallValid; decide +kernel

private theorem sp12932 : smallValid 12932 45 := by unfold smallValid; decide +kernel

private theorem sp12977 : smallValid 12977 45 := by unfold smallValid; decide +kernel

private theorem sp13022 : smallValid 13022 45 := by unfold smallValid; decide +kernel

private theorem sp13067 : smallValid 13067 44 := by unfold smallValid; decide +kernel

private theorem sp13111 : smallValid 13111 45 := by unfold smallValid; decide +kernel

private theorem sp13156 : smallValid 13156 45 := by unfold smallValid; decide +kernel

private theorem sp13201 : smallValid 13201 45 := by unfold smallValid; decide +kernel

private theorem sp13246 : smallValid 13246 44 := by unfold smallValid; decide +kernel

private theorem sp13290 : smallValid 13290 45 := by unfold smallValid; decide +kernel

private theorem sp13335 : smallValid 13335 45 := by unfold smallValid; decide +kernel

private theorem sp13380 : smallValid 13380 45 := by unfold smallValid; decide +kernel

private theorem sp13425 : smallValid 13425 44 := by unfold smallValid; decide +kernel

private theorem sp13469 : smallValid 13469 45 := by unfold smallValid; decide +kernel

private theorem sp13514 : smallValid 13514 45 := by unfold smallValid; decide +kernel

private theorem sp13559 : smallValid 13559 45 := by unfold smallValid; decide +kernel

private theorem sp13604 : smallValid 13604 44 := by unfold smallValid; decide +kernel

private theorem sp13648 : smallValid 13648 45 := by unfold smallValid; decide +kernel

private theorem sp13693 : smallValid 13693 45 := by unfold smallValid; decide +kernel

private theorem sp13738 : smallValid 13738 45 := by unfold smallValid; decide +kernel

private theorem sp13783 : smallValid 13783 44 := by unfold smallValid; decide +kernel

private theorem sp13827 : smallValid 13827 45 := by unfold smallValid; decide +kernel

private theorem sp13872 : smallValid 13872 45 := by unfold smallValid; decide +kernel

private theorem sp13917 : smallValid 13917 45 := by unfold smallValid; decide +kernel

private theorem sp13962 : smallValid 13962 44 := by unfold smallValid; decide +kernel

private theorem sp14006 : smallValid 14006 45 := by unfold smallValid; decide +kernel

private theorem sp14051 : smallValid 14051 45 := by unfold smallValid; decide +kernel

private theorem sp14096 : smallValid 14096 45 := by unfold smallValid; decide +kernel

private theorem sp14141 : smallValid 14141 44 := by unfold smallValid; decide +kernel

private theorem sp14185 : smallValid 14185 45 := by unfold smallValid; decide +kernel

private theorem sp14230 : smallValid 14230 45 := by unfold smallValid; decide +kernel

private theorem sp14275 : smallValid 14275 45 := by unfold smallValid; decide +kernel

private theorem sp14320 : smallValid 14320 44 := by unfold smallValid; decide +kernel

private theorem sp14364 : smallValid 14364 45 := by unfold smallValid; decide +kernel

private theorem sp14409 : smallValid 14409 45 := by unfold smallValid; decide +kernel

private theorem sp14454 : smallValid 14454 45 := by unfold smallValid; decide +kernel

private theorem sp14499 : smallValid 14499 44 := by unfold smallValid; decide +kernel

private theorem sp14543 : smallValid 14543 45 := by unfold smallValid; decide +kernel

private theorem sp14588 : smallValid 14588 45 := by unfold smallValid; decide +kernel

private theorem sp14633 : smallValid 14633 45 := by unfold smallValid; decide +kernel

private theorem sp14678 : smallValid 14678 44 := by unfold smallValid; decide +kernel

private theorem sp14722 : smallValid 14722 45 := by unfold smallValid; decide +kernel

private theorem sp14767 : smallValid 14767 45 := by unfold smallValid; decide +kernel

private theorem sp14812 : smallValid 14812 45 := by unfold smallValid; decide +kernel

private theorem sp14857 : smallValid 14857 44 := by unfold smallValid; decide +kernel

private theorem sp14901 : smallValid 14901 45 := by unfold smallValid; decide +kernel

private theorem sp14946 : smallValid 14946 45 := by unfold smallValid; decide +kernel

private theorem sp14991 : smallValid 14991 45 := by unfold smallValid; decide +kernel

private theorem sp15036 : smallValid 15036 44 := by unfold smallValid; decide +kernel

private theorem sp15080 : smallValid 15080 45 := by unfold smallValid; decide +kernel

private theorem sp15125 : smallValid 15125 45 := by unfold smallValid; decide +kernel

private theorem sp15170 : smallValid 15170 45 := by unfold smallValid; decide +kernel

private theorem sp15215 : smallValid 15215 44 := by unfold smallValid; decide +kernel

private theorem sp15259 : smallValid 15259 45 := by unfold smallValid; decide +kernel

private theorem sp15304 : smallValid 15304 45 := by unfold smallValid; decide +kernel

private theorem sp15349 : smallValid 15349 45 := by unfold smallValid; decide +kernel

private theorem sp15394 : smallValid 15394 44 := by unfold smallValid; decide +kernel

private theorem sp15438 : smallValid 15438 45 := by unfold smallValid; decide +kernel

private theorem sp15483 : smallValid 15483 45 := by unfold smallValid; decide +kernel

private theorem sp15528 : smallValid 15528 45 := by unfold smallValid; decide +kernel

private theorem sp15573 : smallValid 15573 44 := by unfold smallValid; decide +kernel

private theorem sp15617 : smallValid 15617 45 := by unfold smallValid; decide +kernel

private theorem sp15662 : smallValid 15662 45 := by unfold smallValid; decide +kernel

private theorem sp15707 : smallValid 15707 45 := by unfold smallValid; decide +kernel

private theorem sp15752 : smallValid 15752 44 := by unfold smallValid; decide +kernel

private theorem sp15796 : smallValid 15796 45 := by unfold smallValid; decide +kernel

private theorem sp15841 : smallValid 15841 45 := by unfold smallValid; decide +kernel

private theorem sp15886 : smallValid 15886 45 := by unfold smallValid; decide +kernel

private theorem sp15931 : smallValid 15931 44 := by unfold smallValid; decide +kernel

private theorem sp15975 : smallValid 15975 45 := by unfold smallValid; decide +kernel

private theorem sp16020 : smallValid 16020 45 := by unfold smallValid; decide +kernel

private theorem sp16065 : smallValid 16065 45 := by unfold smallValid; decide +kernel

private theorem sp16110 : smallValid 16110 44 := by unfold smallValid; decide +kernel

private theorem sp16154 : smallValid 16154 45 := by unfold smallValid; decide +kernel

private theorem sp16199 : smallValid 16199 45 := by unfold smallValid; decide +kernel

private theorem sp16244 : smallValid 16244 45 := by unfold smallValid; decide +kernel

private theorem sp16289 : smallValid 16289 44 := by unfold smallValid; decide +kernel

private theorem sp16333 : smallValid 16333 45 := by unfold smallValid; decide +kernel

private theorem sp16378 : smallValid 16378 45 := by unfold smallValid; decide +kernel

private theorem sp16423 : smallValid 16423 45 := by unfold smallValid; decide +kernel

private theorem sp16468 : smallValid 16468 44 := by unfold smallValid; decide +kernel

private theorem sp16512 : smallValid 16512 45 := by unfold smallValid; decide +kernel

private theorem sp16557 : smallValid 16557 45 := by unfold smallValid; decide +kernel

private theorem sp16602 : smallValid 16602 45 := by unfold smallValid; decide +kernel

private theorem sp16647 : smallValid 16647 44 := by unfold smallValid; decide +kernel

private theorem sp16691 : smallValid 16691 45 := by unfold smallValid; decide +kernel

private theorem sp16736 : smallValid 16736 45 := by unfold smallValid; decide +kernel

private theorem sp16781 : smallValid 16781 45 := by unfold smallValid; decide +kernel

private theorem sp16826 : smallValid 16826 44 := by unfold smallValid; decide +kernel

private theorem sp16870 : smallValid 16870 45 := by unfold smallValid; decide +kernel

private theorem sp16915 : smallValid 16915 45 := by unfold smallValid; decide +kernel

private theorem sp16960 : smallValid 16960 45 := by unfold smallValid; decide +kernel

private theorem sp17005 : smallValid 17005 44 := by unfold smallValid; decide +kernel

private theorem sp17049 : smallValid 17049 45 := by unfold smallValid; decide +kernel

private theorem sp17094 : smallValid 17094 45 := by unfold smallValid; decide +kernel

private theorem sp17139 : smallValid 17139 45 := by unfold smallValid; decide +kernel

private theorem sp17184 : smallValid 17184 44 := by unfold smallValid; decide +kernel

private theorem sp17228 : smallValid 17228 45 := by unfold smallValid; decide +kernel

private theorem sp17273 : smallValid 17273 45 := by unfold smallValid; decide +kernel

private theorem sp17318 : smallValid 17318 45 := by unfold smallValid; decide +kernel

private theorem sp17363 : smallValid 17363 44 := by unfold smallValid; decide +kernel

private theorem sp17407 : smallValid 17407 45 := by unfold smallValid; decide +kernel

private theorem sp17452 : smallValid 17452 45 := by unfold smallValid; decide +kernel

private theorem sp17497 : smallValid 17497 45 := by unfold smallValid; decide +kernel

private theorem sp17542 : smallValid 17542 44 := by unfold smallValid; decide +kernel

private theorem sp17586 : smallValid 17586 45 := by unfold smallValid; decide +kernel

private theorem sp17631 : smallValid 17631 45 := by unfold smallValid; decide +kernel

private theorem sp17676 : smallValid 17676 45 := by unfold smallValid; decide +kernel

private theorem sp17721 : smallValid 17721 44 := by unfold smallValid; decide +kernel

private theorem sp17765 : smallValid 17765 45 := by unfold smallValid; decide +kernel

private theorem sp17810 : smallValid 17810 45 := by unfold smallValid; decide +kernel

private theorem sp17855 : smallValid 17855 45 := by unfold smallValid; decide +kernel

private theorem sp17900 : smallValid 17900 44 := by unfold smallValid; decide +kernel

private theorem sp17944 : smallValid 17944 45 := by unfold smallValid; decide +kernel

private theorem sp17989 : smallValid 17989 45 := by unfold smallValid; decide +kernel

private theorem sp18034 : smallValid 18034 45 := by unfold smallValid; decide +kernel

private theorem sp18079 : smallValid 18079 44 := by unfold smallValid; decide +kernel

private theorem sp18123 : smallValid 18123 45 := by unfold smallValid; decide +kernel

private theorem sp18168 : smallValid 18168 45 := by unfold smallValid; decide +kernel

private theorem sp18213 : smallValid 18213 45 := by unfold smallValid; decide +kernel

private theorem sp18258 : smallValid 18258 44 := by unfold smallValid; decide +kernel

private theorem sp18302 : smallValid 18302 45 := by unfold smallValid; decide +kernel

private theorem sp18347 : smallValid 18347 45 := by unfold smallValid; decide +kernel

private theorem sp18392 : smallValid 18392 45 := by unfold smallValid; decide +kernel

private theorem sp18437 : smallValid 18437 44 := by unfold smallValid; decide +kernel

private theorem sp18481 : smallValid 18481 45 := by unfold smallValid; decide +kernel

private theorem sp18526 : smallValid 18526 45 := by unfold smallValid; decide +kernel

private theorem sp18571 : smallValid 18571 45 := by unfold smallValid; decide +kernel

private theorem sp18616 : smallValid 18616 44 := by unfold smallValid; decide +kernel

private theorem sp18660 : smallValid 18660 45 := by unfold smallValid; decide +kernel

private theorem sp18705 : smallValid 18705 45 := by unfold smallValid; decide +kernel

private theorem sp18750 : smallValid 18750 45 := by unfold smallValid; decide +kernel

private theorem sp18795 : smallValid 18795 44 := by unfold smallValid; decide +kernel

private theorem sp18839 : smallValid 18839 45 := by unfold smallValid; decide +kernel

private theorem sp18884 : smallValid 18884 45 := by unfold smallValid; decide +kernel

private theorem sp18929 : smallValid 18929 45 := by unfold smallValid; decide +kernel

private theorem sp18974 : smallValid 18974 44 := by unfold smallValid; decide +kernel

private theorem sp19018 : smallValid 19018 45 := by unfold smallValid; decide +kernel

private theorem sp19063 : smallValid 19063 45 := by unfold smallValid; decide +kernel

private theorem sp19108 : smallValid 19108 45 := by unfold smallValid; decide +kernel

private theorem sp19153 : smallValid 19153 44 := by unfold smallValid; decide +kernel

private theorem sp19197 : smallValid 19197 45 := by unfold smallValid; decide +kernel

private theorem sp19242 : smallValid 19242 45 := by unfold smallValid; decide +kernel

private theorem sp19287 : smallValid 19287 45 := by unfold smallValid; decide +kernel

private theorem sp19332 : smallValid 19332 44 := by unfold smallValid; decide +kernel

private theorem sp19376 : smallValid 19376 45 := by unfold smallValid; decide +kernel

private theorem sp19421 : smallValid 19421 45 := by unfold smallValid; decide +kernel

private theorem sp19466 : smallValid 19466 45 := by unfold smallValid; decide +kernel

private theorem sp19511 : smallValid 19511 44 := by unfold smallValid; decide +kernel

private theorem sp19555 : smallValid 19555 45 := by unfold smallValid; decide +kernel

private theorem sp19600 : smallValid 19600 45 := by unfold smallValid; decide +kernel

private theorem sp19645 : smallValid 19645 45 := by unfold smallValid; decide +kernel

private theorem sp19690 : smallValid 19690 44 := by unfold smallValid; decide +kernel

private theorem sp19734 : smallValid 19734 45 := by unfold smallValid; decide +kernel

private theorem sp19779 : smallValid 19779 45 := by unfold smallValid; decide +kernel

private theorem sp19824 : smallValid 19824 45 := by unfold smallValid; decide +kernel

private theorem sp19869 : smallValid 19869 44 := by unfold smallValid; decide +kernel

private theorem sp19913 : smallValid 19913 45 := by unfold smallValid; decide +kernel

private theorem sp19958 : smallValid 19958 45 := by unfold smallValid; decide +kernel

private theorem sp20003 : smallValid 20003 45 := by unfold smallValid; decide +kernel

private theorem sp20048 : smallValid 20048 44 := by unfold smallValid; decide +kernel

private theorem sp20092 : smallValid 20092 45 := by unfold smallValid; decide +kernel

private theorem sp20137 : smallValid 20137 45 := by unfold smallValid; decide +kernel

private theorem sp20182 : smallValid 20182 45 := by unfold smallValid; decide +kernel

private theorem sp20227 : smallValid 20227 44 := by unfold smallValid; decide +kernel

private theorem sp20271 : smallValid 20271 45 := by unfold smallValid; decide +kernel

private theorem sp20316 : smallValid 20316 45 := by unfold smallValid; decide +kernel

private theorem sp20361 : smallValid 20361 45 := by unfold smallValid; decide +kernel

private theorem sp20406 : smallValid 20406 44 := by unfold smallValid; decide +kernel

private theorem sp20450 : smallValid 20450 45 := by unfold smallValid; decide +kernel

private theorem sp20495 : smallValid 20495 45 := by unfold smallValid; decide +kernel

private theorem sp20540 : smallValid 20540 45 := by unfold smallValid; decide +kernel

private theorem sp20585 : smallValid 20585 44 := by unfold smallValid; decide +kernel

private theorem sp20629 : smallValid 20629 45 := by unfold smallValid; decide +kernel

private theorem sp20674 : smallValid 20674 45 := by unfold smallValid; decide +kernel

private theorem sp20719 : smallValid 20719 45 := by unfold smallValid; decide +kernel

private theorem sp20764 : smallValid 20764 44 := by unfold smallValid; decide +kernel

private theorem sp20808 : smallValid 20808 45 := by unfold smallValid; decide +kernel

private theorem sp20853 : smallValid 20853 45 := by unfold smallValid; decide +kernel

private theorem sp20898 : smallValid 20898 45 := by unfold smallValid; decide +kernel

private theorem sp20943 : smallValid 20943 44 := by unfold smallValid; decide +kernel

private theorem sp20987 : smallValid 20987 45 := by unfold smallValid; decide +kernel

private theorem sp21032 : smallValid 21032 45 := by unfold smallValid; decide +kernel

private theorem sp21077 : smallValid 21077 45 := by unfold smallValid; decide +kernel

private theorem sp21122 : smallValid 21122 44 := by unfold smallValid; decide +kernel

private theorem sp21166 : smallValid 21166 45 := by unfold smallValid; decide +kernel

private theorem sp21211 : smallValid 21211 45 := by unfold smallValid; decide +kernel

private theorem sp21256 : smallValid 21256 45 := by unfold smallValid; decide +kernel

private theorem sp21301 : smallValid 21301 44 := by unfold smallValid; decide +kernel

private theorem sp21345 : smallValid 21345 45 := by unfold smallValid; decide +kernel

private theorem sp21390 : smallValid 21390 45 := by unfold smallValid; decide +kernel

private theorem sp21435 : smallValid 21435 45 := by unfold smallValid; decide +kernel

private theorem sp21480 : smallValid 21480 44 := by unfold smallValid; decide +kernel

private theorem sp21524 : smallValid 21524 45 := by unfold smallValid; decide +kernel

private theorem sp21569 : smallValid 21569 45 := by unfold smallValid; decide +kernel

private theorem sp21614 : smallValid 21614 45 := by unfold smallValid; decide +kernel

private theorem sp21659 : smallValid 21659 44 := by unfold smallValid; decide +kernel

private theorem sp21703 : smallValid 21703 45 := by unfold smallValid; decide +kernel

private theorem sp21748 : smallValid 21748 45 := by unfold smallValid; decide +kernel

private theorem sp21793 : smallValid 21793 45 := by unfold smallValid; decide +kernel

private theorem sp21838 : smallValid 21838 44 := by unfold smallValid; decide +kernel

private theorem sp21882 : smallValid 21882 45 := by unfold smallValid; decide +kernel

private theorem sp21927 : smallValid 21927 45 := by unfold smallValid; decide +kernel

private theorem sp21972 : smallValid 21972 45 := by unfold smallValid; decide +kernel

private theorem sp22017 : smallValid 22017 44 := by unfold smallValid; decide +kernel

private theorem sp22061 : smallValid 22061 45 := by unfold smallValid; decide +kernel

private theorem sp22106 : smallValid 22106 45 := by unfold smallValid; decide +kernel

private theorem sp22151 : smallValid 22151 45 := by unfold smallValid; decide +kernel

private theorem sp22196 : smallValid 22196 44 := by unfold smallValid; decide +kernel

private theorem sp22240 : smallValid 22240 45 := by unfold smallValid; decide +kernel

private theorem sp22285 : smallValid 22285 45 := by unfold smallValid; decide +kernel

private theorem sp22330 : smallValid 22330 45 := by unfold smallValid; decide +kernel

private theorem sp22375 : smallValid 22375 44 := by unfold smallValid; decide +kernel

private theorem sp22419 : smallValid 22419 45 := by unfold smallValid; decide +kernel

private theorem sp22464 : smallValid 22464 45 := by unfold smallValid; decide +kernel

private theorem sp22509 : smallValid 22509 45 := by unfold smallValid; decide +kernel

private theorem sp22554 : smallValid 22554 44 := by unfold smallValid; decide +kernel

private theorem sp22598 : smallValid 22598 45 := by unfold smallValid; decide +kernel

private theorem sp22643 : smallValid 22643 45 := by unfold smallValid; decide +kernel

private theorem sp22688 : smallValid 22688 45 := by unfold smallValid; decide +kernel

private theorem sp22733 : smallValid 22733 45 := by unfold smallValid; decide +kernel

private theorem sp22778 : smallValid 22778 45 := by unfold smallValid; decide +kernel

private theorem sp22823 : smallValid 22823 45 := by unfold smallValid; decide +kernel

private theorem sp22868 : smallValid 22868 45 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤22912) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 22913 := (joinSmall (lo:=0) (a:=11456) (b:=11457) (joinSmall (lo:=0) (a:=5728) (b:=5728) (joinSmall (lo:=0) (a:=2864) (b:=2864) (joinSmall (lo:=0) (a:=1432) (b:=1432) (joinSmall (lo:=0) (a:=716) (b:=716) (joinSmall (lo:=0) (a:=358) (b:=358) (joinSmall (lo:=0) (a:=179) (b:=179) (joinSmall (lo:=0) (a:=89) (b:=90) (joinSmall (lo:=0) (a:=44) (b:=45) sp0 sp44) (joinSmall (lo:=89) (a:=45) (b:=45) sp89 sp134)) (joinSmall (lo:=179) (a:=89) (b:=90) (joinSmall (lo:=179) (a:=44) (b:=45) sp179 sp223) (joinSmall (lo:=268) (a:=45) (b:=45) sp268 sp313))) (joinSmall (lo:=358) (a:=179) (b:=179) (joinSmall (lo:=358) (a:=89) (b:=90) (joinSmall (lo:=358) (a:=44) (b:=45) sp358 sp402) (joinSmall (lo:=447) (a:=45) (b:=45) sp447 sp492)) (joinSmall (lo:=537) (a:=89) (b:=90) (joinSmall (lo:=537) (a:=44) (b:=45) sp537 sp581) (joinSmall (lo:=626) (a:=45) (b:=45) sp626 sp671)))) (joinSmall (lo:=716) (a:=358) (b:=358) (joinSmall (lo:=716) (a:=179) (b:=179) (joinSmall (lo:=716) (a:=89) (b:=90) (joinSmall (lo:=716) (a:=44) (b:=45) sp716 sp760) (joinSmall (lo:=805) (a:=45) (b:=45) sp805 sp850)) (joinSmall (lo:=895) (a:=89) (b:=90) (joinSmall (lo:=895) (a:=44) (b:=45) sp895 sp939) (joinSmall (lo:=984) (a:=45) (b:=45) sp984 sp1029))) (joinSmall (lo:=1074) (a:=179) (b:=179) (joinSmall (lo:=1074) (a:=89) (b:=90) (joinSmall (lo:=1074) (a:=44) (b:=45) sp1074 sp1118) (joinSmall (lo:=1163) (a:=45) (b:=45) sp1163 sp1208)) (joinSmall (lo:=1253) (a:=89) (b:=90) (joinSmall (lo:=1253) (a:=44) (b:=45) sp1253 sp1297) (joinSmall (lo:=1342) (a:=45) (b:=45) sp1342 sp1387))))) (joinSmall (lo:=1432) (a:=716) (b:=716) (joinSmall (lo:=1432) (a:=358) (b:=358) (joinSmall (lo:=1432) (a:=179) (b:=179) (joinSmall (lo:=1432) (a:=89) (b:=90) (joinSmall (lo:=1432) (a:=44) (b:=45) sp1432 sp1476) (joinSmall (lo:=1521) (a:=45) (b:=45) sp1521 sp1566)) (joinSmall (lo:=1611) (a:=89) (b:=90) (joinSmall (lo:=1611) (a:=44) (b:=45) sp1611 sp1655) (joinSmall (lo:=1700) (a:=45) (b:=45) sp1700 sp1745))) (joinSmall (lo:=1790) (a:=179) (b:=179) (joinSmall (lo:=1790) (a:=89) (b:=90) (joinSmall (lo:=1790) (a:=44) (b:=45) sp1790 sp1834) (joinSmall (lo:=1879) (a:=45) (b:=45) sp1879 sp1924)) (joinSmall (lo:=1969) (a:=89) (b:=90) (joinSmall (lo:=1969) (a:=44) (b:=45) sp1969 sp2013) (joinSmall (lo:=2058) (a:=45) (b:=45) sp2058 sp2103)))) (joinSmall (lo:=2148) (a:=358) (b:=358) (joinSmall (lo:=2148) (a:=179) (b:=179) (joinSmall (lo:=2148) (a:=89) (b:=90) (joinSmall (lo:=2148) (a:=44) (b:=45) sp2148 sp2192) (joinSmall (lo:=2237) (a:=45) (b:=45) sp2237 sp2282)) (joinSmall (lo:=2327) (a:=89) (b:=90) (joinSmall (lo:=2327) (a:=44) (b:=45) sp2327 sp2371) (joinSmall (lo:=2416) (a:=45) (b:=45) sp2416 sp2461))) (joinSmall (lo:=2506) (a:=179) (b:=179) (joinSmall (lo:=2506) (a:=89) (b:=90) (joinSmall (lo:=2506) (a:=44) (b:=45) sp2506 sp2550) (joinSmall (lo:=2595) (a:=45) (b:=45) sp2595 sp2640)) (joinSmall (lo:=2685) (a:=89) (b:=90) (joinSmall (lo:=2685) (a:=44) (b:=45) sp2685 sp2729) (joinSmall (lo:=2774) (a:=45) (b:=45) sp2774 sp2819)))))) (joinSmall (lo:=2864) (a:=1432) (b:=1432) (joinSmall (lo:=2864) (a:=716) (b:=716) (joinSmall (lo:=2864) (a:=358) (b:=358) (joinSmall (lo:=2864) (a:=179) (b:=179) (joinSmall (lo:=2864) (a:=89) (b:=90) (joinSmall (lo:=2864) (a:=44) (b:=45) sp2864 sp2908) (joinSmall (lo:=2953) (a:=45) (b:=45) sp2953 sp2998)) (joinSmall (lo:=3043) (a:=89) (b:=90) (joinSmall (lo:=3043) (a:=44) (b:=45) sp3043 sp3087) (joinSmall (lo:=3132) (a:=45) (b:=45) sp3132 sp3177))) (joinSmall (lo:=3222) (a:=179) (b:=179) (joinSmall (lo:=3222) (a:=89) (b:=90) (joinSmall (lo:=3222) (a:=44) (b:=45) sp3222 sp3266) (joinSmall (lo:=3311) (a:=45) (b:=45) sp3311 sp3356)) (joinSmall (lo:=3401) (a:=89) (b:=90) (joinSmall (lo:=3401) (a:=44) (b:=45) sp3401 sp3445) (joinSmall (lo:=3490) (a:=45) (b:=45) sp3490 sp3535)))) (joinSmall (lo:=3580) (a:=358) (b:=358) (joinSmall (lo:=3580) (a:=179) (b:=179) (joinSmall (lo:=3580) (a:=89) (b:=90) (joinSmall (lo:=3580) (a:=44) (b:=45) sp3580 sp3624) (joinSmall (lo:=3669) (a:=45) (b:=45) sp3669 sp3714)) (joinSmall (lo:=3759) (a:=89) (b:=90) (joinSmall (lo:=3759) (a:=44) (b:=45) sp3759 sp3803) (joinSmall (lo:=3848) (a:=45) (b:=45) sp3848 sp3893))) (joinSmall (lo:=3938) (a:=179) (b:=179) (joinSmall (lo:=3938) (a:=89) (b:=90) (joinSmall (lo:=3938) (a:=44) (b:=45) sp3938 sp3982) (joinSmall (lo:=4027) (a:=45) (b:=45) sp4027 sp4072)) (joinSmall (lo:=4117) (a:=89) (b:=90) (joinSmall (lo:=4117) (a:=44) (b:=45) sp4117 sp4161) (joinSmall (lo:=4206) (a:=45) (b:=45) sp4206 sp4251))))) (joinSmall (lo:=4296) (a:=716) (b:=716) (joinSmall (lo:=4296) (a:=358) (b:=358) (joinSmall (lo:=4296) (a:=179) (b:=179) (joinSmall (lo:=4296) (a:=89) (b:=90) (joinSmall (lo:=4296) (a:=44) (b:=45) sp4296 sp4340) (joinSmall (lo:=4385) (a:=45) (b:=45) sp4385 sp4430)) (joinSmall (lo:=4475) (a:=89) (b:=90) (joinSmall (lo:=4475) (a:=44) (b:=45) sp4475 sp4519) (joinSmall (lo:=4564) (a:=45) (b:=45) sp4564 sp4609))) (joinSmall (lo:=4654) (a:=179) (b:=179) (joinSmall (lo:=4654) (a:=89) (b:=90) (joinSmall (lo:=4654) (a:=44) (b:=45) sp4654 sp4698) (joinSmall (lo:=4743) (a:=45) (b:=45) sp4743 sp4788)) (joinSmall (lo:=4833) (a:=89) (b:=90) (joinSmall (lo:=4833) (a:=44) (b:=45) sp4833 sp4877) (joinSmall (lo:=4922) (a:=45) (b:=45) sp4922 sp4967)))) (joinSmall (lo:=5012) (a:=358) (b:=358) (joinSmall (lo:=5012) (a:=179) (b:=179) (joinSmall (lo:=5012) (a:=89) (b:=90) (joinSmall (lo:=5012) (a:=44) (b:=45) sp5012 sp5056) (joinSmall (lo:=5101) (a:=45) (b:=45) sp5101 sp5146)) (joinSmall (lo:=5191) (a:=89) (b:=90) (joinSmall (lo:=5191) (a:=44) (b:=45) sp5191 sp5235) (joinSmall (lo:=5280) (a:=45) (b:=45) sp5280 sp5325))) (joinSmall (lo:=5370) (a:=179) (b:=179) (joinSmall (lo:=5370) (a:=89) (b:=90) (joinSmall (lo:=5370) (a:=44) (b:=45) sp5370 sp5414) (joinSmall (lo:=5459) (a:=45) (b:=45) sp5459 sp5504)) (joinSmall (lo:=5549) (a:=89) (b:=90) (joinSmall (lo:=5549) (a:=44) (b:=45) sp5549 sp5593) (joinSmall (lo:=5638) (a:=45) (b:=45) sp5638 sp5683))))))) (joinSmall (lo:=5728) (a:=2864) (b:=2864) (joinSmall (lo:=5728) (a:=1432) (b:=1432) (joinSmall (lo:=5728) (a:=716) (b:=716) (joinSmall (lo:=5728) (a:=358) (b:=358) (joinSmall (lo:=5728) (a:=179) (b:=179) (joinSmall (lo:=5728) (a:=89) (b:=90) (joinSmall (lo:=5728) (a:=44) (b:=45) sp5728 sp5772) (joinSmall (lo:=5817) (a:=45) (b:=45) sp5817 sp5862)) (joinSmall (lo:=5907) (a:=89) (b:=90) (joinSmall (lo:=5907) (a:=44) (b:=45) sp5907 sp5951) (joinSmall (lo:=5996) (a:=45) (b:=45) sp5996 sp6041))) (joinSmall (lo:=6086) (a:=179) (b:=179) (joinSmall (lo:=6086) (a:=89) (b:=90) (joinSmall (lo:=6086) (a:=44) (b:=45) sp6086 sp6130) (joinSmall (lo:=6175) (a:=45) (b:=45) sp6175 sp6220)) (joinSmall (lo:=6265) (a:=89) (b:=90) (joinSmall (lo:=6265) (a:=44) (b:=45) sp6265 sp6309) (joinSmall (lo:=6354) (a:=45) (b:=45) sp6354 sp6399)))) (joinSmall (lo:=6444) (a:=358) (b:=358) (joinSmall (lo:=6444) (a:=179) (b:=179) (joinSmall (lo:=6444) (a:=89) (b:=90) (joinSmall (lo:=6444) (a:=44) (b:=45) sp6444 sp6488) (joinSmall (lo:=6533) (a:=45) (b:=45) sp6533 sp6578)) (joinSmall (lo:=6623) (a:=89) (b:=90) (joinSmall (lo:=6623) (a:=44) (b:=45) sp6623 sp6667) (joinSmall (lo:=6712) (a:=45) (b:=45) sp6712 sp6757))) (joinSmall (lo:=6802) (a:=179) (b:=179) (joinSmall (lo:=6802) (a:=89) (b:=90) (joinSmall (lo:=6802) (a:=44) (b:=45) sp6802 sp6846) (joinSmall (lo:=6891) (a:=45) (b:=45) sp6891 sp6936)) (joinSmall (lo:=6981) (a:=89) (b:=90) (joinSmall (lo:=6981) (a:=44) (b:=45) sp6981 sp7025) (joinSmall (lo:=7070) (a:=45) (b:=45) sp7070 sp7115))))) (joinSmall (lo:=7160) (a:=716) (b:=716) (joinSmall (lo:=7160) (a:=358) (b:=358) (joinSmall (lo:=7160) (a:=179) (b:=179) (joinSmall (lo:=7160) (a:=89) (b:=90) (joinSmall (lo:=7160) (a:=44) (b:=45) sp7160 sp7204) (joinSmall (lo:=7249) (a:=45) (b:=45) sp7249 sp7294)) (joinSmall (lo:=7339) (a:=89) (b:=90) (joinSmall (lo:=7339) (a:=44) (b:=45) sp7339 sp7383) (joinSmall (lo:=7428) (a:=45) (b:=45) sp7428 sp7473))) (joinSmall (lo:=7518) (a:=179) (b:=179) (joinSmall (lo:=7518) (a:=89) (b:=90) (joinSmall (lo:=7518) (a:=44) (b:=45) sp7518 sp7562) (joinSmall (lo:=7607) (a:=45) (b:=45) sp7607 sp7652)) (joinSmall (lo:=7697) (a:=89) (b:=90) (joinSmall (lo:=7697) (a:=44) (b:=45) sp7697 sp7741) (joinSmall (lo:=7786) (a:=45) (b:=45) sp7786 sp7831)))) (joinSmall (lo:=7876) (a:=358) (b:=358) (joinSmall (lo:=7876) (a:=179) (b:=179) (joinSmall (lo:=7876) (a:=89) (b:=90) (joinSmall (lo:=7876) (a:=44) (b:=45) sp7876 sp7920) (joinSmall (lo:=7965) (a:=45) (b:=45) sp7965 sp8010)) (joinSmall (lo:=8055) (a:=89) (b:=90) (joinSmall (lo:=8055) (a:=44) (b:=45) sp8055 sp8099) (joinSmall (lo:=8144) (a:=45) (b:=45) sp8144 sp8189))) (joinSmall (lo:=8234) (a:=179) (b:=179) (joinSmall (lo:=8234) (a:=89) (b:=90) (joinSmall (lo:=8234) (a:=44) (b:=45) sp8234 sp8278) (joinSmall (lo:=8323) (a:=45) (b:=45) sp8323 sp8368)) (joinSmall (lo:=8413) (a:=89) (b:=90) (joinSmall (lo:=8413) (a:=44) (b:=45) sp8413 sp8457) (joinSmall (lo:=8502) (a:=45) (b:=45) sp8502 sp8547)))))) (joinSmall (lo:=8592) (a:=1432) (b:=1432) (joinSmall (lo:=8592) (a:=716) (b:=716) (joinSmall (lo:=8592) (a:=358) (b:=358) (joinSmall (lo:=8592) (a:=179) (b:=179) (joinSmall (lo:=8592) (a:=89) (b:=90) (joinSmall (lo:=8592) (a:=44) (b:=45) sp8592 sp8636) (joinSmall (lo:=8681) (a:=45) (b:=45) sp8681 sp8726)) (joinSmall (lo:=8771) (a:=89) (b:=90) (joinSmall (lo:=8771) (a:=44) (b:=45) sp8771 sp8815) (joinSmall (lo:=8860) (a:=45) (b:=45) sp8860 sp8905))) (joinSmall (lo:=8950) (a:=179) (b:=179) (joinSmall (lo:=8950) (a:=89) (b:=90) (joinSmall (lo:=8950) (a:=44) (b:=45) sp8950 sp8994) (joinSmall (lo:=9039) (a:=45) (b:=45) sp9039 sp9084)) (joinSmall (lo:=9129) (a:=89) (b:=90) (joinSmall (lo:=9129) (a:=44) (b:=45) sp9129 sp9173) (joinSmall (lo:=9218) (a:=45) (b:=45) sp9218 sp9263)))) (joinSmall (lo:=9308) (a:=358) (b:=358) (joinSmall (lo:=9308) (a:=179) (b:=179) (joinSmall (lo:=9308) (a:=89) (b:=90) (joinSmall (lo:=9308) (a:=44) (b:=45) sp9308 sp9352) (joinSmall (lo:=9397) (a:=45) (b:=45) sp9397 sp9442)) (joinSmall (lo:=9487) (a:=89) (b:=90) (joinSmall (lo:=9487) (a:=44) (b:=45) sp9487 sp9531) (joinSmall (lo:=9576) (a:=45) (b:=45) sp9576 sp9621))) (joinSmall (lo:=9666) (a:=179) (b:=179) (joinSmall (lo:=9666) (a:=89) (b:=90) (joinSmall (lo:=9666) (a:=44) (b:=45) sp9666 sp9710) (joinSmall (lo:=9755) (a:=45) (b:=45) sp9755 sp9800)) (joinSmall (lo:=9845) (a:=89) (b:=90) (joinSmall (lo:=9845) (a:=44) (b:=45) sp9845 sp9889) (joinSmall (lo:=9934) (a:=45) (b:=45) sp9934 sp9979))))) (joinSmall (lo:=10024) (a:=716) (b:=716) (joinSmall (lo:=10024) (a:=358) (b:=358) (joinSmall (lo:=10024) (a:=179) (b:=179) (joinSmall (lo:=10024) (a:=89) (b:=90) (joinSmall (lo:=10024) (a:=44) (b:=45) sp10024 sp10068) (joinSmall (lo:=10113) (a:=45) (b:=45) sp10113 sp10158)) (joinSmall (lo:=10203) (a:=89) (b:=90) (joinSmall (lo:=10203) (a:=44) (b:=45) sp10203 sp10247) (joinSmall (lo:=10292) (a:=45) (b:=45) sp10292 sp10337))) (joinSmall (lo:=10382) (a:=179) (b:=179) (joinSmall (lo:=10382) (a:=89) (b:=90) (joinSmall (lo:=10382) (a:=44) (b:=45) sp10382 sp10426) (joinSmall (lo:=10471) (a:=45) (b:=45) sp10471 sp10516)) (joinSmall (lo:=10561) (a:=89) (b:=90) (joinSmall (lo:=10561) (a:=44) (b:=45) sp10561 sp10605) (joinSmall (lo:=10650) (a:=45) (b:=45) sp10650 sp10695)))) (joinSmall (lo:=10740) (a:=358) (b:=358) (joinSmall (lo:=10740) (a:=179) (b:=179) (joinSmall (lo:=10740) (a:=89) (b:=90) (joinSmall (lo:=10740) (a:=44) (b:=45) sp10740 sp10784) (joinSmall (lo:=10829) (a:=45) (b:=45) sp10829 sp10874)) (joinSmall (lo:=10919) (a:=89) (b:=90) (joinSmall (lo:=10919) (a:=44) (b:=45) sp10919 sp10963) (joinSmall (lo:=11008) (a:=45) (b:=45) sp11008 sp11053))) (joinSmall (lo:=11098) (a:=179) (b:=179) (joinSmall (lo:=11098) (a:=89) (b:=90) (joinSmall (lo:=11098) (a:=44) (b:=45) sp11098 sp11142) (joinSmall (lo:=11187) (a:=45) (b:=45) sp11187 sp11232)) (joinSmall (lo:=11277) (a:=89) (b:=90) (joinSmall (lo:=11277) (a:=44) (b:=45) sp11277 sp11321) (joinSmall (lo:=11366) (a:=45) (b:=45) sp11366 sp11411)))))))) (joinSmall (lo:=11456) (a:=5728) (b:=5729) (joinSmall (lo:=11456) (a:=2864) (b:=2864) (joinSmall (lo:=11456) (a:=1432) (b:=1432) (joinSmall (lo:=11456) (a:=716) (b:=716) (joinSmall (lo:=11456) (a:=358) (b:=358) (joinSmall (lo:=11456) (a:=179) (b:=179) (joinSmall (lo:=11456) (a:=89) (b:=90) (joinSmall (lo:=11456) (a:=44) (b:=45) sp11456 sp11500) (joinSmall (lo:=11545) (a:=45) (b:=45) sp11545 sp11590)) (joinSmall (lo:=11635) (a:=89) (b:=90) (joinSmall (lo:=11635) (a:=44) (b:=45) sp11635 sp11679) (joinSmall (lo:=11724) (a:=45) (b:=45) sp11724 sp11769))) (joinSmall (lo:=11814) (a:=179) (b:=179) (joinSmall (lo:=11814) (a:=89) (b:=90) (joinSmall (lo:=11814) (a:=44) (b:=45) sp11814 sp11858) (joinSmall (lo:=11903) (a:=45) (b:=45) sp11903 sp11948)) (joinSmall (lo:=11993) (a:=89) (b:=90) (joinSmall (lo:=11993) (a:=44) (b:=45) sp11993 sp12037) (joinSmall (lo:=12082) (a:=45) (b:=45) sp12082 sp12127)))) (joinSmall (lo:=12172) (a:=358) (b:=358) (joinSmall (lo:=12172) (a:=179) (b:=179) (joinSmall (lo:=12172) (a:=89) (b:=90) (joinSmall (lo:=12172) (a:=44) (b:=45) sp12172 sp12216) (joinSmall (lo:=12261) (a:=45) (b:=45) sp12261 sp12306)) (joinSmall (lo:=12351) (a:=89) (b:=90) (joinSmall (lo:=12351) (a:=44) (b:=45) sp12351 sp12395) (joinSmall (lo:=12440) (a:=45) (b:=45) sp12440 sp12485))) (joinSmall (lo:=12530) (a:=179) (b:=179) (joinSmall (lo:=12530) (a:=89) (b:=90) (joinSmall (lo:=12530) (a:=44) (b:=45) sp12530 sp12574) (joinSmall (lo:=12619) (a:=45) (b:=45) sp12619 sp12664)) (joinSmall (lo:=12709) (a:=89) (b:=90) (joinSmall (lo:=12709) (a:=44) (b:=45) sp12709 sp12753) (joinSmall (lo:=12798) (a:=45) (b:=45) sp12798 sp12843))))) (joinSmall (lo:=12888) (a:=716) (b:=716) (joinSmall (lo:=12888) (a:=358) (b:=358) (joinSmall (lo:=12888) (a:=179) (b:=179) (joinSmall (lo:=12888) (a:=89) (b:=90) (joinSmall (lo:=12888) (a:=44) (b:=45) sp12888 sp12932) (joinSmall (lo:=12977) (a:=45) (b:=45) sp12977 sp13022)) (joinSmall (lo:=13067) (a:=89) (b:=90) (joinSmall (lo:=13067) (a:=44) (b:=45) sp13067 sp13111) (joinSmall (lo:=13156) (a:=45) (b:=45) sp13156 sp13201))) (joinSmall (lo:=13246) (a:=179) (b:=179) (joinSmall (lo:=13246) (a:=89) (b:=90) (joinSmall (lo:=13246) (a:=44) (b:=45) sp13246 sp13290) (joinSmall (lo:=13335) (a:=45) (b:=45) sp13335 sp13380)) (joinSmall (lo:=13425) (a:=89) (b:=90) (joinSmall (lo:=13425) (a:=44) (b:=45) sp13425 sp13469) (joinSmall (lo:=13514) (a:=45) (b:=45) sp13514 sp13559)))) (joinSmall (lo:=13604) (a:=358) (b:=358) (joinSmall (lo:=13604) (a:=179) (b:=179) (joinSmall (lo:=13604) (a:=89) (b:=90) (joinSmall (lo:=13604) (a:=44) (b:=45) sp13604 sp13648) (joinSmall (lo:=13693) (a:=45) (b:=45) sp13693 sp13738)) (joinSmall (lo:=13783) (a:=89) (b:=90) (joinSmall (lo:=13783) (a:=44) (b:=45) sp13783 sp13827) (joinSmall (lo:=13872) (a:=45) (b:=45) sp13872 sp13917))) (joinSmall (lo:=13962) (a:=179) (b:=179) (joinSmall (lo:=13962) (a:=89) (b:=90) (joinSmall (lo:=13962) (a:=44) (b:=45) sp13962 sp14006) (joinSmall (lo:=14051) (a:=45) (b:=45) sp14051 sp14096)) (joinSmall (lo:=14141) (a:=89) (b:=90) (joinSmall (lo:=14141) (a:=44) (b:=45) sp14141 sp14185) (joinSmall (lo:=14230) (a:=45) (b:=45) sp14230 sp14275)))))) (joinSmall (lo:=14320) (a:=1432) (b:=1432) (joinSmall (lo:=14320) (a:=716) (b:=716) (joinSmall (lo:=14320) (a:=358) (b:=358) (joinSmall (lo:=14320) (a:=179) (b:=179) (joinSmall (lo:=14320) (a:=89) (b:=90) (joinSmall (lo:=14320) (a:=44) (b:=45) sp14320 sp14364) (joinSmall (lo:=14409) (a:=45) (b:=45) sp14409 sp14454)) (joinSmall (lo:=14499) (a:=89) (b:=90) (joinSmall (lo:=14499) (a:=44) (b:=45) sp14499 sp14543) (joinSmall (lo:=14588) (a:=45) (b:=45) sp14588 sp14633))) (joinSmall (lo:=14678) (a:=179) (b:=179) (joinSmall (lo:=14678) (a:=89) (b:=90) (joinSmall (lo:=14678) (a:=44) (b:=45) sp14678 sp14722) (joinSmall (lo:=14767) (a:=45) (b:=45) sp14767 sp14812)) (joinSmall (lo:=14857) (a:=89) (b:=90) (joinSmall (lo:=14857) (a:=44) (b:=45) sp14857 sp14901) (joinSmall (lo:=14946) (a:=45) (b:=45) sp14946 sp14991)))) (joinSmall (lo:=15036) (a:=358) (b:=358) (joinSmall (lo:=15036) (a:=179) (b:=179) (joinSmall (lo:=15036) (a:=89) (b:=90) (joinSmall (lo:=15036) (a:=44) (b:=45) sp15036 sp15080) (joinSmall (lo:=15125) (a:=45) (b:=45) sp15125 sp15170)) (joinSmall (lo:=15215) (a:=89) (b:=90) (joinSmall (lo:=15215) (a:=44) (b:=45) sp15215 sp15259) (joinSmall (lo:=15304) (a:=45) (b:=45) sp15304 sp15349))) (joinSmall (lo:=15394) (a:=179) (b:=179) (joinSmall (lo:=15394) (a:=89) (b:=90) (joinSmall (lo:=15394) (a:=44) (b:=45) sp15394 sp15438) (joinSmall (lo:=15483) (a:=45) (b:=45) sp15483 sp15528)) (joinSmall (lo:=15573) (a:=89) (b:=90) (joinSmall (lo:=15573) (a:=44) (b:=45) sp15573 sp15617) (joinSmall (lo:=15662) (a:=45) (b:=45) sp15662 sp15707))))) (joinSmall (lo:=15752) (a:=716) (b:=716) (joinSmall (lo:=15752) (a:=358) (b:=358) (joinSmall (lo:=15752) (a:=179) (b:=179) (joinSmall (lo:=15752) (a:=89) (b:=90) (joinSmall (lo:=15752) (a:=44) (b:=45) sp15752 sp15796) (joinSmall (lo:=15841) (a:=45) (b:=45) sp15841 sp15886)) (joinSmall (lo:=15931) (a:=89) (b:=90) (joinSmall (lo:=15931) (a:=44) (b:=45) sp15931 sp15975) (joinSmall (lo:=16020) (a:=45) (b:=45) sp16020 sp16065))) (joinSmall (lo:=16110) (a:=179) (b:=179) (joinSmall (lo:=16110) (a:=89) (b:=90) (joinSmall (lo:=16110) (a:=44) (b:=45) sp16110 sp16154) (joinSmall (lo:=16199) (a:=45) (b:=45) sp16199 sp16244)) (joinSmall (lo:=16289) (a:=89) (b:=90) (joinSmall (lo:=16289) (a:=44) (b:=45) sp16289 sp16333) (joinSmall (lo:=16378) (a:=45) (b:=45) sp16378 sp16423)))) (joinSmall (lo:=16468) (a:=358) (b:=358) (joinSmall (lo:=16468) (a:=179) (b:=179) (joinSmall (lo:=16468) (a:=89) (b:=90) (joinSmall (lo:=16468) (a:=44) (b:=45) sp16468 sp16512) (joinSmall (lo:=16557) (a:=45) (b:=45) sp16557 sp16602)) (joinSmall (lo:=16647) (a:=89) (b:=90) (joinSmall (lo:=16647) (a:=44) (b:=45) sp16647 sp16691) (joinSmall (lo:=16736) (a:=45) (b:=45) sp16736 sp16781))) (joinSmall (lo:=16826) (a:=179) (b:=179) (joinSmall (lo:=16826) (a:=89) (b:=90) (joinSmall (lo:=16826) (a:=44) (b:=45) sp16826 sp16870) (joinSmall (lo:=16915) (a:=45) (b:=45) sp16915 sp16960)) (joinSmall (lo:=17005) (a:=89) (b:=90) (joinSmall (lo:=17005) (a:=44) (b:=45) sp17005 sp17049) (joinSmall (lo:=17094) (a:=45) (b:=45) sp17094 sp17139))))))) (joinSmall (lo:=17184) (a:=2864) (b:=2865) (joinSmall (lo:=17184) (a:=1432) (b:=1432) (joinSmall (lo:=17184) (a:=716) (b:=716) (joinSmall (lo:=17184) (a:=358) (b:=358) (joinSmall (lo:=17184) (a:=179) (b:=179) (joinSmall (lo:=17184) (a:=89) (b:=90) (joinSmall (lo:=17184) (a:=44) (b:=45) sp17184 sp17228) (joinSmall (lo:=17273) (a:=45) (b:=45) sp17273 sp17318)) (joinSmall (lo:=17363) (a:=89) (b:=90) (joinSmall (lo:=17363) (a:=44) (b:=45) sp17363 sp17407) (joinSmall (lo:=17452) (a:=45) (b:=45) sp17452 sp17497))) (joinSmall (lo:=17542) (a:=179) (b:=179) (joinSmall (lo:=17542) (a:=89) (b:=90) (joinSmall (lo:=17542) (a:=44) (b:=45) sp17542 sp17586) (joinSmall (lo:=17631) (a:=45) (b:=45) sp17631 sp17676)) (joinSmall (lo:=17721) (a:=89) (b:=90) (joinSmall (lo:=17721) (a:=44) (b:=45) sp17721 sp17765) (joinSmall (lo:=17810) (a:=45) (b:=45) sp17810 sp17855)))) (joinSmall (lo:=17900) (a:=358) (b:=358) (joinSmall (lo:=17900) (a:=179) (b:=179) (joinSmall (lo:=17900) (a:=89) (b:=90) (joinSmall (lo:=17900) (a:=44) (b:=45) sp17900 sp17944) (joinSmall (lo:=17989) (a:=45) (b:=45) sp17989 sp18034)) (joinSmall (lo:=18079) (a:=89) (b:=90) (joinSmall (lo:=18079) (a:=44) (b:=45) sp18079 sp18123) (joinSmall (lo:=18168) (a:=45) (b:=45) sp18168 sp18213))) (joinSmall (lo:=18258) (a:=179) (b:=179) (joinSmall (lo:=18258) (a:=89) (b:=90) (joinSmall (lo:=18258) (a:=44) (b:=45) sp18258 sp18302) (joinSmall (lo:=18347) (a:=45) (b:=45) sp18347 sp18392)) (joinSmall (lo:=18437) (a:=89) (b:=90) (joinSmall (lo:=18437) (a:=44) (b:=45) sp18437 sp18481) (joinSmall (lo:=18526) (a:=45) (b:=45) sp18526 sp18571))))) (joinSmall (lo:=18616) (a:=716) (b:=716) (joinSmall (lo:=18616) (a:=358) (b:=358) (joinSmall (lo:=18616) (a:=179) (b:=179) (joinSmall (lo:=18616) (a:=89) (b:=90) (joinSmall (lo:=18616) (a:=44) (b:=45) sp18616 sp18660) (joinSmall (lo:=18705) (a:=45) (b:=45) sp18705 sp18750)) (joinSmall (lo:=18795) (a:=89) (b:=90) (joinSmall (lo:=18795) (a:=44) (b:=45) sp18795 sp18839) (joinSmall (lo:=18884) (a:=45) (b:=45) sp18884 sp18929))) (joinSmall (lo:=18974) (a:=179) (b:=179) (joinSmall (lo:=18974) (a:=89) (b:=90) (joinSmall (lo:=18974) (a:=44) (b:=45) sp18974 sp19018) (joinSmall (lo:=19063) (a:=45) (b:=45) sp19063 sp19108)) (joinSmall (lo:=19153) (a:=89) (b:=90) (joinSmall (lo:=19153) (a:=44) (b:=45) sp19153 sp19197) (joinSmall (lo:=19242) (a:=45) (b:=45) sp19242 sp19287)))) (joinSmall (lo:=19332) (a:=358) (b:=358) (joinSmall (lo:=19332) (a:=179) (b:=179) (joinSmall (lo:=19332) (a:=89) (b:=90) (joinSmall (lo:=19332) (a:=44) (b:=45) sp19332 sp19376) (joinSmall (lo:=19421) (a:=45) (b:=45) sp19421 sp19466)) (joinSmall (lo:=19511) (a:=89) (b:=90) (joinSmall (lo:=19511) (a:=44) (b:=45) sp19511 sp19555) (joinSmall (lo:=19600) (a:=45) (b:=45) sp19600 sp19645))) (joinSmall (lo:=19690) (a:=179) (b:=179) (joinSmall (lo:=19690) (a:=89) (b:=90) (joinSmall (lo:=19690) (a:=44) (b:=45) sp19690 sp19734) (joinSmall (lo:=19779) (a:=45) (b:=45) sp19779 sp19824)) (joinSmall (lo:=19869) (a:=89) (b:=90) (joinSmall (lo:=19869) (a:=44) (b:=45) sp19869 sp19913) (joinSmall (lo:=19958) (a:=45) (b:=45) sp19958 sp20003)))))) (joinSmall (lo:=20048) (a:=1432) (b:=1433) (joinSmall (lo:=20048) (a:=716) (b:=716) (joinSmall (lo:=20048) (a:=358) (b:=358) (joinSmall (lo:=20048) (a:=179) (b:=179) (joinSmall (lo:=20048) (a:=89) (b:=90) (joinSmall (lo:=20048) (a:=44) (b:=45) sp20048 sp20092) (joinSmall (lo:=20137) (a:=45) (b:=45) sp20137 sp20182)) (joinSmall (lo:=20227) (a:=89) (b:=90) (joinSmall (lo:=20227) (a:=44) (b:=45) sp20227 sp20271) (joinSmall (lo:=20316) (a:=45) (b:=45) sp20316 sp20361))) (joinSmall (lo:=20406) (a:=179) (b:=179) (joinSmall (lo:=20406) (a:=89) (b:=90) (joinSmall (lo:=20406) (a:=44) (b:=45) sp20406 sp20450) (joinSmall (lo:=20495) (a:=45) (b:=45) sp20495 sp20540)) (joinSmall (lo:=20585) (a:=89) (b:=90) (joinSmall (lo:=20585) (a:=44) (b:=45) sp20585 sp20629) (joinSmall (lo:=20674) (a:=45) (b:=45) sp20674 sp20719)))) (joinSmall (lo:=20764) (a:=358) (b:=358) (joinSmall (lo:=20764) (a:=179) (b:=179) (joinSmall (lo:=20764) (a:=89) (b:=90) (joinSmall (lo:=20764) (a:=44) (b:=45) sp20764 sp20808) (joinSmall (lo:=20853) (a:=45) (b:=45) sp20853 sp20898)) (joinSmall (lo:=20943) (a:=89) (b:=90) (joinSmall (lo:=20943) (a:=44) (b:=45) sp20943 sp20987) (joinSmall (lo:=21032) (a:=45) (b:=45) sp21032 sp21077))) (joinSmall (lo:=21122) (a:=179) (b:=179) (joinSmall (lo:=21122) (a:=89) (b:=90) (joinSmall (lo:=21122) (a:=44) (b:=45) sp21122 sp21166) (joinSmall (lo:=21211) (a:=45) (b:=45) sp21211 sp21256)) (joinSmall (lo:=21301) (a:=89) (b:=90) (joinSmall (lo:=21301) (a:=44) (b:=45) sp21301 sp21345) (joinSmall (lo:=21390) (a:=45) (b:=45) sp21390 sp21435))))) (joinSmall (lo:=21480) (a:=716) (b:=717) (joinSmall (lo:=21480) (a:=358) (b:=358) (joinSmall (lo:=21480) (a:=179) (b:=179) (joinSmall (lo:=21480) (a:=89) (b:=90) (joinSmall (lo:=21480) (a:=44) (b:=45) sp21480 sp21524) (joinSmall (lo:=21569) (a:=45) (b:=45) sp21569 sp21614)) (joinSmall (lo:=21659) (a:=89) (b:=90) (joinSmall (lo:=21659) (a:=44) (b:=45) sp21659 sp21703) (joinSmall (lo:=21748) (a:=45) (b:=45) sp21748 sp21793))) (joinSmall (lo:=21838) (a:=179) (b:=179) (joinSmall (lo:=21838) (a:=89) (b:=90) (joinSmall (lo:=21838) (a:=44) (b:=45) sp21838 sp21882) (joinSmall (lo:=21927) (a:=45) (b:=45) sp21927 sp21972)) (joinSmall (lo:=22017) (a:=89) (b:=90) (joinSmall (lo:=22017) (a:=44) (b:=45) sp22017 sp22061) (joinSmall (lo:=22106) (a:=45) (b:=45) sp22106 sp22151)))) (joinSmall (lo:=22196) (a:=358) (b:=359) (joinSmall (lo:=22196) (a:=179) (b:=179) (joinSmall (lo:=22196) (a:=89) (b:=90) (joinSmall (lo:=22196) (a:=44) (b:=45) sp22196 sp22240) (joinSmall (lo:=22285) (a:=45) (b:=45) sp22285 sp22330)) (joinSmall (lo:=22375) (a:=89) (b:=90) (joinSmall (lo:=22375) (a:=44) (b:=45) sp22375 sp22419) (joinSmall (lo:=22464) (a:=45) (b:=45) sp22464 sp22509))) (joinSmall (lo:=22554) (a:=179) (b:=180) (joinSmall (lo:=22554) (a:=89) (b:=90) (joinSmall (lo:=22554) (a:=44) (b:=45) sp22554 sp22598) (joinSmall (lo:=22643) (a:=45) (b:=45) sp22643 sp22688)) (joinSmall (lo:=22733) (a:=90) (b:=90) (joinSmall (lo:=22733) (a:=45) (b:=45) sp22733 sp22778) (joinSmall (lo:=22823) (a:=45) (b:=45) sp22823 sp22868)))))))))
  have good : (List.range 22913).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 525000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 22912 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 22912 := by
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


private def packet (i : ℕ) : ℕ := (if i < 134 then (if i < 67 then (if i < 33 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else 0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0 else 0) else (if i < 11 then 0 else 0)) else (if i < 14 then (if i < 13 then 0 else 0) else (if i < 15 then 0 else 0)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0 else 0) else (if i < 19 then 0 else 0)) else (if i < 22 then (if i < 21 then 0 else 0) else (if i < 23 then 0 else 0))) else (if i < 28 then (if i < 26 then (if i < 25 then 0 else 0) else (if i < 27 then 0 else 0)) else (if i < 30 then (if i < 29 then 0 else 0) else (if i < 31 then 0 else (if i < 32 then 0 else 0)))))) else (if i < 50 then (if i < 41 then (if i < 37 then (if i < 35 then (if i < 34 then 0 else 0) else (if i < 36 then 0 else 0)) else (if i < 39 then (if i < 38 then 0 else 0) else (if i < 40 then 0 else 0))) else (if i < 45 then (if i < 43 then (if i < 42 then 0 else 0) else (if i < 44 then 0 else 0)) else (if i < 47 then (if i < 46 then 0 else 0) else (if i < 48 then 0 else (if i < 49 then 0 else 0))))) else (if i < 58 then (if i < 54 then (if i < 52 then (if i < 51 then 0 else 0) else (if i < 53 then 0 else 0)) else (if i < 56 then (if i < 55 then 0 else 0) else (if i < 57 then 0 else 0))) else (if i < 62 then (if i < 60 then (if i < 59 then 0 else 0) else (if i < 61 then 0 else 0)) else (if i < 64 then (if i < 63 then 0 else 0) else (if i < 65 then 0 else (if i < 66 then 0 else 0))))))) else (if i < 100 then (if i < 83 then (if i < 75 then (if i < 71 then (if i < 69 then (if i < 68 then 0 else 0) else (if i < 70 then 0 else 0)) else (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else 0))) else (if i < 79 then (if i < 77 then (if i < 76 then 0 else 0) else (if i < 78 then 0 else 0)) else (if i < 81 then (if i < 80 then 0 else 0) else (if i < 82 then 0 else 0)))) else (if i < 91 then (if i < 87 then (if i < 85 then (if i < 84 then 0 else 0) else (if i < 86 then 0 else 0)) else (if i < 89 then (if i < 88 then 0 else 0) else (if i < 90 then 0 else 0))) else (if i < 95 then (if i < 93 then (if i < 92 then 0 else 0) else (if i < 94 then 0 else 0)) else (if i < 97 then (if i < 96 then 0 else 0) else (if i < 98 then 0 else (if i < 99 then 0 else 0)))))) else (if i < 117 then (if i < 108 then (if i < 104 then (if i < 102 then (if i < 101 then 0 else 0) else (if i < 103 then 0 else 0)) else (if i < 106 then (if i < 105 then 0 else 0) else (if i < 107 then 0 else 0))) else (if i < 112 then (if i < 110 then (if i < 109 then 0 else 0) else (if i < 111 then 0 else 0)) else (if i < 114 then (if i < 113 then 0 else 0) else (if i < 115 then 0 else (if i < 116 then 0 else 0))))) else (if i < 125 then (if i < 121 then (if i < 119 then (if i < 118 then 0 else 0) else (if i < 120 then 0 else 0)) else (if i < 123 then (if i < 122 then 0 else 0) else (if i < 124 then 0 else 0))) else (if i < 129 then (if i < 127 then (if i < 126 then 0 else 0) else (if i < 128 then 0 else 0)) else (if i < 131 then (if i < 130 then 0 else 0) else (if i < 132 then 0 else (if i < 133 then 0 else 0)))))))) else (if i < 201 then (if i < 167 then (if i < 150 then (if i < 142 then (if i < 138 then (if i < 136 then (if i < 135 then 0 else 0) else (if i < 137 then 0 else 0)) else (if i < 140 then (if i < 139 then 0 else 0) else (if i < 141 then 0 else 0))) else (if i < 146 then (if i < 144 then (if i < 143 then 0 else 0) else (if i < 145 then 0 else 0)) else (if i < 148 then (if i < 147 then 0 else 0) else (if i < 149 then 0 else 0)))) else (if i < 158 then (if i < 154 then (if i < 152 then (if i < 151 then 0 else 0) else (if i < 153 then 0 else 0)) else (if i < 156 then (if i < 155 then 0 else 0) else (if i < 157 then 0 else 0))) else (if i < 162 then (if i < 160 then (if i < 159 then 0 else 0) else (if i < 161 then 0 else 0)) else (if i < 164 then (if i < 163 then 0 else 0) else (if i < 165 then 0 else (if i < 166 then 0 else 0)))))) else (if i < 184 then (if i < 175 then (if i < 171 then (if i < 169 then (if i < 168 then 0 else 0) else (if i < 170 then 0 else 0)) else (if i < 173 then (if i < 172 then 0 else 0) else (if i < 174 then 0 else 0))) else (if i < 179 then (if i < 177 then (if i < 176 then 0 else 0) else (if i < 178 then 0 else 0)) else (if i < 181 then (if i < 180 then 0 else 0) else (if i < 182 then 0 else (if i < 183 then 0 else 0))))) else (if i < 192 then (if i < 188 then (if i < 186 then (if i < 185 then 0 else 0) else (if i < 187 then 0 else 0)) else (if i < 190 then (if i < 189 then 0 else 0) else (if i < 191 then 0 else 0))) else (if i < 196 then (if i < 194 then (if i < 193 then 0 else 0) else (if i < 195 then 0 else 0)) else (if i < 198 then (if i < 197 then 0 else 0) else (if i < 199 then 0 else (if i < 200 then 0 else 0))))))) else (if i < 234 then (if i < 217 then (if i < 209 then (if i < 205 then (if i < 203 then (if i < 202 then 0 else 0) else (if i < 204 then 0 else 0)) else (if i < 207 then (if i < 206 then 0 else 0) else (if i < 208 then 0 else 0))) else (if i < 213 then (if i < 211 then (if i < 210 then 0 else 0) else (if i < 212 then 0 else 0)) else (if i < 215 then (if i < 214 then 0 else 0) else (if i < 216 then 0 else 0)))) else (if i < 225 then (if i < 221 then (if i < 219 then (if i < 218 then 0 else 0) else (if i < 220 then 0 else 0)) else (if i < 223 then (if i < 222 then 0 else 0) else (if i < 224 then 0 else 0))) else (if i < 229 then (if i < 227 then (if i < 226 then 0 else 0) else (if i < 228 then 0 else 0)) else (if i < 231 then (if i < 230 then 0 else 0) else (if i < 232 then 0 else (if i < 233 then 0 else 0)))))) else (if i < 251 then (if i < 242 then (if i < 238 then (if i < 236 then (if i < 235 then 0 else 0) else (if i < 237 then 0 else 0)) else (if i < 240 then (if i < 239 then 0 else 0) else (if i < 241 then 0 else 0))) else (if i < 246 then (if i < 244 then (if i < 243 then 0 else 0) else (if i < 245 then 0 else 0)) else (if i < 248 then (if i < 247 then 0 else 0) else (if i < 249 then 0 else (if i < 250 then 0 else 0))))) else (if i < 259 then (if i < 255 then (if i < 253 then (if i < 252 then 0 else 0) else (if i < 254 then 0 else 0x19329882d615449e84882118ef86b82ef14608e43b017508a02b809c000019323b62bb142495844b1f10dfc65c2be135082c36a15e08282ec0c800001931dae2d895309c647c2108f1c6c030115688ec3aa18009283140c2000019317b92cb94b49b24702070eb069a2f014788ac3ba17609002f00da000019311d52c1145496645c2000e846842ec14788b83ac17308c02d40ba00001930bdc2cd94f89b047820d8f006d230515288e03be17508782c40ac000019305e62d315089d848f2178f486de30d158094c3e219909e03540d60000192ffec2ca94c89904652040eac6902ee14708bc39816a085829c0b20000192f9d82e09588a0a49e21e8f586dc30d15789283d818909483140c00000192f41a2ba14409624511f68e3866e2de142889c39c17008382fc0bc0000192ee142d295489ec4922170f186ae2f814508c43a417708f83240d20000192e8352c2947c9864602008e6466e2e314908c43a817c08d02f40b40000192e2222dc15649f649321c0f6870431f15b096840419209403200c40000192dc372ca14b89a446f2070edc6a22fc15289143d417808d82b00a00000192d6392ce95009be48220c8f046c030a15b09683fc197095832c0be0000192d0112dd155c9f64902158f086b82fd14c89083c218c09703100c60000192ca0a2d095089bc46c2058ea06982e2143889c39216b08902dc0be0000192c4322b9143096c45c1ff8e8c6922ea14808e03ac17308a82dc0ac0000192be3a2cc94c09a046a20f8f146c830615209083c018908f82f80c00000192b8392cd95009c648120e8ee86b830b15589243d818009302f80c80000192b2392d4951c9d64832150f1c6ca30d15a89403d818c092832c0c00000192ac282d5952c9d848e2160f046ca30014a88d83c818609803300c20000192a6402ca94c09c44852140ef46b02fa14d08e83b417a08802bc0c40000192a03f2d215449d44912160ee869e2ed14888dc3ba17308902c00b800001929a4b2ca15009b247d2070ed46a62f714e88fc3c018609483040c20000192945f2c794a89a247b2098ecc6b42fc14f092c3d018008e83100c000001928e2f2ea15aca1a4a12218fa86f831615a093c3e219309883400c8000019288522bf146097646a2088ec06b42f714888c039616a08902f409c0000192825c2cb94cc9c64892188f386ca30615189243cc18809083280c800001927c512d115109c848020e8f2c6e431515d89403d218208f02e40ce0000192764e2cb94d099046e2060e9868e2e8145088839817c09283180ce0000192704d2d615349e449021d8f6c6f031115809183d418709503100c800001926a1f2e715a0a0849e2198f8070431d16309803ec18509202f00bc000019264192d795609dc48d2148f286c82fe15589443ca17808a03080b400001925e192c715049b848b2180f446f431915408f43ac18108f834c0e0000019258252c514b49b046e2070e7c6842dd139887c38217108a03200d0000019252202d295109d647b20f0ed86ac30214f891c3c017f08d02fc0ba00001924c042db15349e848b2150f386f031515889483ea18a09083280e80000192460d2c3148498c4612010e7c68a2e514d090c3ce18709683200c2000019240292c414d49b648220f0ef06a62f114608c838016608582dc0ae00001923a2c2d0951c9e448f2148f246c630a15709443e619b09e035c0ee0000192344d2c294b099c46f20a0ee06a62f614d88f83cc18909382fc0d600001922e5e2cb14ec9ac47320b0ef46c830915989343e818d09983340d6000019228542d495049c64852130f006c030114f88fc3c218108d031c0da0000192224d2d094f89ae4772100ef06c630a155893c3de17f09002f00c000001921c3b2db15409e84902190f286be30315809543ec19a09883500e0000019216352d815409d649521a8f4c6e230715188f43bc18608f02c80b0000019210462cd14d49b246d2080ec06a22f414588a038e16808882dc0bc00001920a622c6149098e47420a8ef86d030214e88ec3b018609583000b2000019204712c794d098c46620b0eb46922ef14b08f03b217608e83140c40000191fe992c094a09a64742058e8c6922eb14608d43a016c08602cc0a40000191f88c2d294ec9a646c20b8f286da30d15309243ca18a095830c0b80000191f2912cb94f49be4872140f1c6d430c15609243c617f09183200ca0000191eca52c894b09984602028eb469c2f114b88c83ca19009803340c80000191e6af2c994ec9bc47b20f0f246c6300154090c3c217a08d82c00b60000191e09e2dc95509e84a121e0f806f231115b094c3f61a009a83100cc0000191dac22c194b897e45e1fc8e6068a2e014588bc3a217208c02cc0b80000191d4932e31594a024a32200f686ec31715c09503dc18409303240ba0000191ce8b2d094dc9c44912130f106d630714e88e03c017c09383140c80000191c88e2ca14909824672040ec46b630014e890c3c616e08382d40c00000191c2792d495249d048721b0f586de30615288f83b4186092030c0d80000191bc9e2bf948499647c20c0eec6c42fb14e89003ca19509b833c0c60000191b6ae2c6948c9864621ff8ec06a82f814c08fc3a617608f02e00b60000191b0aa2d69544a0049921b8f4c70431815d09603e418d09a83280d0000)) else (if i < 257 then (if i < 256 then 0x194a7b72ce150c9b848020f0f186de31115689083cc18c09503280ba0000194a1cf2c4948c9924622010ea06742dc13e086c38216308803040c000001949bf72c2949898045f1fe0e886942e614588b83ae17308d02dc0a8000019495e42d514fc9a446e2040e786842e114908fc3ae17708b02e80b2000019490042c314909a247320d0ef86ba2fe14f89083b618408a83080c4000019489c12ee9604a284a52210fbc72633016589b441c1a009883400d0000019483b32da15249d048320c8ee86c030615009283ce17608e831c0ce00001947dd02c414c89a84792098ef06ae2fc14e09083c818e090030c0c40000194778b2f19634a4e4c7232901873a33216a899040619309803200d8000019471752dc954c9f649221a0f386e2306155091c3cc18609082d80ba00001946b712d6954c9e448b2138f246c22ee14a09083c8191092032c0ce000019465892c714c098e46c2088ec06a62f014a88e43d018b096830c0bc00001945fca2b0942095244e1fb0e786802df13c886838c16b08902dc0b6000019459e82c194bc9a246a2028ebc6982e3140887839616c08c02dc0b00000194540f2ba14409704561ff8e7c68a2e214688e43b617e093032c0cc00001944e242c6149898e46c2088ef46b430014a88cc38e17408a02cc0a80000194482b2ca14cc9a24682060ef06c02ff14f09283d2188096831c0d00000194422e2cb14ec9b24782088eec6a22e313e889c39417808f02ec0b200001943c492c4148c98e4662048ea069a2fb15609183e419b09c83400d80000194364b2d1150c9be4862148f446e231615a895c3e418f09382ec0b20000194306e2c394b89a047720b8eec6c22fc15189103b219009082e80c000001942a7c2ca14cc9a04782110edc69c2eb14588d03a816c08502b40a8000019424812c994bc9a048020d0ec86b22ec14388c03b417d08b82d80b800001941e972ca14b898a4692060ecc6922f314a88f43d018209783240d4000019418b62c0947099e47620b8ef06ce31015809583d619409a03300d4000019412b42d314ec99647020c0ef06b830a154890c3ba17b09503180c800001940c932df157c9f249c21e8f446e230d15389203ba17908d02cc0b8000019406732e015449dc49521a8f106d2305152890c3c818709383240be000019400762cd94e89b047e2140f1c6c62fd14a88f83b417b08f02f80aa0000193fa842c494cc9a247320a8ed46ae300157091c3d819109783300ca0000193f4832d115289e04832118f186da31215789183cc17d08e82f80c00000193ee8e2cb94d099846e2090ed069e2f014288ac37e16d08c02e80ac0000193e86c2df959ca004a12228fb070231615409183de18508e83040b20000193e2872c694b89b64792118f0c6be2fd14d88e43b617e08d82ec0b00000193dcab2c094b499c46c1ff0e786982ea14a88dc3b417808a82d40be0000193d6b32d095289d047d2118ed86bc2fb153892c3e219b09603200ca0000193d0b72cd14b09b24752088ee86a82fd15108ec3c418009182f80c20000193cab32cd14f09a24772050ec86842e314108ac39a16a08682c00b40000193c4d22c014a498e4642088eb06982e614708cc3c217809303240be0000193bed22d094f89a847a2110f1c6da30b15709483f619009703080b80000193b8e02c314989a04722058ec86a02f314e88c43ae18008b82e00c40000193b2dc2d1952c9c64872150ef46be30314f89003b017a08f831c0ba0000193ad092b814509624542028e946902ee14a08e43b817c092831c0c40000193a6fc2d815449d247c2070e9c6822e414688c83a216f08902e40c00000193a1002d194fc9c048920e8f106e030d155090839e17308702d40b600001939ae62db156c9e84942188f446e030915489403dc19109903600c8000019395042c494f49bc47f2130ef46bc30715309203c217b08e03000c000001938edd2e295a4a184a02240fa072233616809803fa19609c83440ce000019388ce2d295609cc4852150f146de30715609403e218e09a03440d2000019382e32cf94f89c64812128f246d230214f09043a818109583040cc00001937cc52da15789ee49821c0f446de30414b88b83a617808e02e40aa000019376d42c994949864581fc0e8469e2e914908e03b417908f02f40c6000019370b92d995409e849e21b8f486da30f16109403de192094030c0cc00001936aca2c214ac99c4772050eac6a42f114888b03a017308e830c0dc000019364fd2bd94589824682090eb06a82fb14d08f03bc18209002f80c000001935eea2d695349d84812138f006b030314e89483d818f09783400e4000019358f62cf14f49d048d2188f106da30f15689503f419a09a03300dc0000193532a2bc144898446f2050eac6902f414c08e43da19409c83140b600001934d532c294989844562058ea46a22f314b08dc3b417908c82e80c2000019347582cf95149c647720e8efc69a2ed14988c83c218b09503100ba0000193415c2cc14f49b44852138f086ba2f514908943b618008b02c80b600001933b7f2c2949098c45f1fe0e886a02f314d89043c218109283140ba000019335642dc15349ce48820e0ed86bc2fe14a88dc3b016708882bc0a200001932f922ba144496645b1fc8e7868a2f114988f03aa17d09283140b6000 else 0x196266c2c2949898045d2008e706782e314488dc3b817808602c80ac000019620932ba145c9744602040ea46862f214a08f43b217c08e02e80ba00001961aa02cc14e89a247f2098ed86b22fb14a88c039817308882e00d4000019614d02b9144c96645d1fa8e6467e2e414688bc39c17108d82e00c200001960ed92cf14d09a84662018ea46902e6145089c3a016808802a4096000019608ee2c614d89b24772088ee06ae2fb14a08d43c417908f83240d4000019602e92cf15009d248d2158ef46b830414f09043bc17608c03000b40000195fd032c294c09b247c20a0edc69c2fc15289303ca19109902f40cc0000195f7132c894bc9a847e20b8f146d030a15c09683ea182093030c0ba0000195f11f2cd150499c47920f8edc6a62f814888a439e17a08c02f00ba0000195eaed2e615aca1e4a12248f9470431d15f09583d418108e03080c80000195e4f72c814e49c247d2098eec6c231115789403ee18c09403040ba0000195df012c214a89a247720d0edc69c2ee14c88d43a817f09483100c40000195d8f72d415149d048221a0f406e230615389203c417b08782dc0c00000195d2dd2d795709ea4a021f0f746dc30515789383ca18809003040c00000195ccf52c114849884662058eb06a82f314d88d439e17508d02f80c20000195c71f2bc14789b047d20f0f1c6dc307155894c3e619609883280da0000195c1482b8148098046d2078ec46a82ee14808c039816608802ec0b60000195bb3a2d315309e648e2138f046de31215108d83a617208a02d40bc0000195b5252d7152c9e449e2218f9071631f161898440619909503200be0000195af212ce14dc9ca4932138f006ca30915509143cc18209382fc0ce0000195a9272c894dc9d048d2160f446da30415108fc3a217108c02f80a40000195a30a2da15209cc47f2130f346dc30a14e88fc3ba17d08802a009e00001959d052cf94f89c24872108ee46ae30414e89183cc17a09102e40b2000019597232bf946898c4662040ec06962ef14408c83aa16d08c02f40b80000195914f2c0147c9844652048eb468c2ea14788d43be17908f02fc0b600001958b6d2c594909a646f2008e8c6762ed14788b03a417508b02ec0b40000195857e2c914cc9a047320b8ec86ac302153093c3d417908d02f40ba00001957f6b2db955c9c648320c8ed46a82e614908d03b217b08e02e40ac0000195796e2d095049aa4812120f146c830615089103e419109883280c6000019573992b994349544551f88e806842e314408b439e17509103040c200001956d942d195149d84842110f046b82f714b88e43ae18408e82f80c6000019567912d295149c448921a8f446d430a15d09543f219009883040b00000195619c2cb94f09c44892140f506e830914d88e43a817708902e80b400001955b972d3150c9b647720a0ec86b02f314a88cc3b818308d02e80c0000019555b42be94ac99046f2098ec86b02f914e090c3be17b09002fc0be00001954f822eb95a8a1e4a42218f786f431f15d89543dc18b09203000aa000019549922c614a497c4662008e6c68c2e514788d03b618709283240a8000019543802d695149ca49421a0f4470032215d89303ce18f09503040ce00001953d7f2ce14b09904541fc8e8868e2ec14288b838616c08c830c0ce000019537a92bd14a097445c2008e9c69a2e714508d43a017908982dc0ba000019531a72ce14d49ba4752130ed86b62fe14c88f03ac17a08d82f40b600001952bc42c214ac9a047820e0eec6a62f014708f83cc18009583300ce000019525b42db151c9ce4862148f546f630f15509483f419009b83540e400001951fe22be947c99645e2000e606622cd136086c38c15f08782d40b4000019519f02bf949498a46c2030ee46b62fe14b08dc3ce187093031c0d2000019514052c994bc9b447420b0ef06bc30215688f439e17908a02bc0b000001950ddd2dc9588a0a4a82238fac71c32c16009603f218709083180b6000019507cf2d615309d64872130f186c22f914c08e03c8186092832c0d0000019501e22c894d09ac48020b8f006c230615409103da185096032c0c60000194fbbb2e315789ea49a21f8f606ec31415809283c8183094832c0be0000194f5cd2c3149c98c4662020e8c67e2e11440878388169085830c0bc0000194efa02e315a8a264a721d8f486e231a153893c3ba17e093832c0be0000194e9992d914f49ba47820b0ec06a030214d08d03ca18609102e40d40000194e3992d595349d048421b8f5c6f431715b09803ec18e09983240c20000194ddb52c2145897c4682038ec86b02f014888ac3b217c08d830c0be0000194d7bc2ce94e49b847d20b8ed86bc2f414d89103e018d09583280ca0000194d1c72d114e09ac47520d0f046c431115989543ee18c09303140ce0000194cbd52c7149c9a047a20c0eb86aa2f014708d43a818108d830409e0000194c5dd2cf14d899e47c20b0ecc6a82f714988d83b817508f03080ba0000194bfdf2d595249c048c2118f0c6cc30715989583f019709b832c0c40000194b9cd2d695049ae47520c8eec6a02f014b88dc3bc17a08e82dc0d40000194b3c52cd94ec9c048120e8f106ce30714f89283dc18809103040c00000194adba2d295289ec49b2190f506dc309155890c3c217b08e03080c0000) else (if i < 258 then 0x197a5b12c1949098846b2060ed86b82fd14d08fc3c818909182fc0be00001979fd12c514b09944732078edc69a2ee142888837015d08582b80b4000019799d92ce94e49b24782098ed86b02f714d08e03b817f09003040b0000019793e32cd94d09bc4872128f1c6c4300152892c3d4184091031c0c600001978dd32d494fc9c04812170f486d230215489583f418e08e03140d0000019787d92c994c49b04722090ee46b02f215009083d418108c82e00ae000019781d82ca149c9a24662000e886922f114888dc3ba18709503240c200001977c0a2b6944496044f1f80e5c6882e014408c03ac17108502dc0c6000019776022d094f09be4842110ed46a62fb15189343f018909503280d8000019770232be149098446b2010e906822e4147089c39217308682dc0a400001976a202d094e49c047e20c0f006e030e15b89503f419f09d03300c2000019763ec2ec15cca1e4ab2238f6470232316189683de18809102ec0c400001975e0b2c3948897c46b2048ed46ba2f914a08d43ac17008502e80c00000197581a2cb94b498846f2060ee46ae2f914f89043ac17608e02e80a6000019751fd2df15749f44a32220f6070232015f095c3ea18809002ec0b400001974c1c2c414cc99647320e0ef06be2f114508e43b017b08f03340c6000019745fe2de154c9e649a2170f206c82fc15209243cc18509203180bc00001973fff2ca94d49964672070ed46b030015689083b818309203300ca00001973a1a2c214889844652048ed06b630315189003b817c08802e40a6000019734232cd14b098e4742070eb86b22f514a08c83a616f08702fc0c400001972e2b2d014f49be48620e8f006be30214b88c83ae17b08d83140d8000019728572be14a49a047120a8ea869e2f414908e43cc17e08f02e00c0000019722442dd159c9e84912168f486e031115309343ca18809203040ce00001971c2d2de156c9e04902190f306da30d15488f03aa17d091030c0b80000197163a2cb94f09ae47820d0f086d631415a09683ce18909483140b00000197102e2d595289b647f2120ef86a42eb14988c039e16a08802d80ba00001970a052e315a8a0849f21f8f486d230115408f43ba17808982e00b8000019704062ce94f89c84892138f386dc30d15689403da18509083100b40000196fe062c814f49c84892198f446ca30a156890c3cc18809503400d40000196f8162c714e89ca4802108f046ca2fd14988e43b417709103100cc0000196f23b2c2149098846a20d8ec46ac2f214b08e83be17608f03140b20000196ec462cc94b49a04692058ed46ae2f814b08fc3bc181093831c0c80000196e6682c314a89924662040e986a22e114508bc39e17e08d02f00b80000196e0542d495149d449921b0f406d831415c09603cc18f094830c0cc0000196da4d2d195109c04792090ec06822e714308a43aa17908b82d80ba0000196d4462d014e09b248220d8ecc6b42fc14a09003ca19609683040ca0000196ce3f2d395109c848d2180f5c6fe31615989283ce18109083140cc0000196c8502cb14d09ae4712068ebc69e2e613f087837816408602cc0a60000196c2312d695349e64922170f646e031415e09543e418709283180c20000196bc4a2c594bc99e47020f8f146d42f614808e83c2185095833c0e20000196b63c2d5152c9ce49221e0f6c6f831815889303da18e09303080be0000196b02f2d8156c9f04982190f206dc30515308ec3c217508d02f40b80000196aa332cc94d49b447d2078ef06be30414d88e03a017608d02fc0c00000196a3f72ec95b4a204a02218f786fe31e15e89843f61a109c03500ca00001969de12e295809fa49221d0f346d231215789583ee1a009d03440d6000019697de2d415149d04832100f346cc30b15609143c017d09303100ce000019691eb2d095089b447a2090ed869a2fa14c88d03c818008d82fc0c400001968bfd2c994cc9ac4742098ed86aa2fb14d08ec3a2175092031c0c0000019686332b8145c9664521fa0e6c6862e814808ec3cc17008e02fc0b800001967ffe2df95809fa4902150f286c2306157893c3d018f09883200c600001967a0d2d014f89b247a20b0ebc6a42f514e08f83c217c08d831c0ae0000196741c2cd94e49be4832128f006e030c15b09343d018a09683400cc00001966e642ae942495e44b1fc0e6c6842e614288bc39817d08f02dc0ac000019668742c794dc99c4712070eb46a42f014908ec3b017709382f40b00000196627b2cd14e49c648621c0f286be30a15609283d619009703340d400001965c652da95709d64882108f086d830f15409143d618f097832c0c6000019656752c6949498e4692018e9469e2f714c08e83ac18609103240d0000019650762d4954c9cc47b2108f086be30214f091c3c618b091030c0c000001964a652d915409e649c21d8f506fe31c158093c3ea18c09283000d00000196444c2da15449cc48320b8ec86ac2f214608d03b017308e82d00b800001963e2a2e2958c9f44962188f186dc2f814b89003b818308f03000ce000019638472c314ac9864612020eb06a02f914a08d03a017708e02e80c6000019632372d815309e24932170f186c62f614988e83c018c09683380da00001962c532c314b89ac47420f0ef86c230215189183cc17f08e83080b8000 else 0x19924992d9155c9f248f2170f046c42f914a88d839a17908f83200ce00001991eae2c694c49b04792110efc6ac2f415009043b017e08f82e00c0000019918b22d014e89b646a2080edc6ae2fa15309203ba17f08d82d00b80000199129b2dc95509de48c2150f186c430215209103c617609083100d200001990ca42cf950c9bc4962198f546f031715889483dc18008f83100c2000019906962d715249c247f20f0f346d631515c09443c818309182e40c2000019900912d3151c9c847d20c0eec69e2f614f89083cc17d08682c00b20000198fa8d2cd14e09be47b20b8ee86bc2f014808c43c018308e02e40ba0000198f4bb2be14949924602028eb46902de13c088439017608c02dc0cc0000198eeee2b894409744592000eb06ae2df14808d83b417908802b80ac0000198e8e12d415489e84872138f2c6d830415409383de18e09603180d40000198e2e52cb94e49ca4812100eb869a2f014908d83ca18408d82e80be0000198dcf42c914d09b84752098edc69a2f514b88e03b017a09283140b80000198d6fb2d1150c9d047e2120f0c6b22fe14d09003c418109002f00bc0000198d0f82d295289d248b2140ef06cc30314f88dc3b018209282f80c60000198cad52d995549e649c21f0f846f231615809283d418609403200c00000198c4ba2df9554a024ab2218fa871a32f16589c440e1aa09e83500e20000198becc2c994c89b64842110f386e231515389383d818909383100bc0000198b8db2c694c89ac47220b8ec86a22f314808f83b618009403100b40000198b2f62c514c09b247520c8ec86ba2f614d08dc3b418509002e40ac0000198acf82d2151c9c64862168f386d631215609203e218b09c036c0d80000198a6f02d615149c64852140f006c42f214788bc3b816d08a02d80aa0000198a0c92e1157c9da48f2140f186c630915609083cc189092031c0d000001989abb2d1951c9b24822110f146e031015a092c3be18409583440d2000019894c22d014e89b847620b8f006c42ff14608c03a017c08e83100bc00001988eb52cf15189d64922168f586ea30f15409483de18a09603180c4000019888e32bf14849864692030e9c6882e614808c839e17008902d00ae000019882db2d3152c9c247f20f8edc6bc2ff14c88f43b6180091031c0ce00001987ce62cc94d89aa47920b8ed06b02fc14b88d43ae17708b82f80bc000019876e62d314e499c46920a8ed06aa30215309103c017208782b40ba0000198710b2bf14789744681ff8e986a82f314d09043c017808e02f00bc00001986b272c394989944612030eb86a02f014d88f83be17708e83200b60000198651b2d395389dc48c2168f406e030f15809343c618a09683180ca00001985f1a2d315309d248e2160f286dc31615389243c617c09583080d0000019859162d415109d44892118f086b42f5152892c3de188095833c0d2000019853082d395149be48a20e0ef06bc2f714988e43a016708802b00ac00001984d3d2ba942c96645d2000e946862df142889838c15f08882e80d40000198472f2d6952c9c848921b0f486e030f15989483ca17408782c40c0000019841552be149897645e1f98e446762df142089c39c17908f02ec0ac00001983b462d615209d248b2180f306d630215489143c818409002e00b2000019835512cd15209ae47920e8ef06c0305153092c3c817c08d82d40c000001982f2a2e095649e648a2178f4c6e4308158893c3ee18d09503500ce000019829292d1952c9e449221b0f806e031315f09783e019209683300ca0000198234f2c0949c98a46820d8ef46c630315889303d418909282cc0b200001981d262df956c9f249521c0f6c6f8311157093c3b418008f82dc0c20000198170d2d895549d04842108efc6cc30615709603d618f09983140c4000019810fa2d114fc9d848f21b0f606fc32b16309b03fa19009783200c400001980af42d194ec9ae47a2128f086c230614e09083c818609303400d4000019805112c1949899446d2088ed46a62ea14408c03a217708f03040ca0000197ff062d9956c9e04892130f006b22fc15309243c618609603200cc0000197f9122c314c099c4712020e7c6842e514408a039c17b08b02e80b60000197f3002dd95549de48b2190f3c6d830614e08d83b617408a02f80c80000197ed152cc14bc9ae47420e8f0c6c230a15289303da18909183180ca0000197e72d2c5148098646f2040ec06a02ea14b08f43bc17a08c82c80b40000197e13c2c814cc9b24752048ea868e2e814188a038c17608983100c60000197db482d195049ba47e20f0ef46c030614f09083c618108d03080c40000197d56f2b8944497a4602028e8068c2eb14688f43b617d09203240d20000197cf6e2cd14dc9be48320f0f006b02fe14e890c3c617f08d82f40b60000197c97e2c994cc9ba47d20c8ed86a22ee14788d839e16d08c02d80a60000197c36b2d695409d04952200f606e431015789543de18d09083040c20000197bd5e2d315109be4892110f206d630715489303d618c09283280c00000197b7592d7954c9f649321a8f746f231a15609103be17508b83040bc0000197b15e2cf95149c84952160f646ec31115088f83b417908e83000c40000197ab952b6944497245d2058ea068c2dd13b888c37216008302b80ba000))) else (if i < 263 then (if i < 261 then (if i < 260 then 0x19aa2822c114ac9b048620c0ecc6982e314408dc3a017508d82e40b4000019a9c892c994d49904601fa0e7c6822cf13a887c38616008582a80a0000019a969a2c994e89bc47e2150f206ce30315389383ec19a099033c0d8000019a90982cd14f09c64812160f2c6c830514d08f43be18508f82fc0b6000019a8aa72ca94dc9b647a20e0f106ce30c15408f43d017f09303240be000019a84a72c994e09ac47f2110efc6ce2fb15209043d218808f03080bc000019a7ea12cb94ec9b447f2108ee86ae30515489183bc17f09483180ce000019a789f2d4153c9dc48e2188f386e830515408fc3bc18308f831c0c6000019a72ba2c614c09ac46f20c0ee06b82fa14708c83b218809483340dc000019a6cf42b494249684571fe0e806982fd14889043b617c08e03180c4000019a67152bc945898046f20a0ee46a02ed14608d03b417a08c83100ba000019a61342c494b899a4692028eb469a2f114c08f03b817408c02e40b2000019a5b3f2d094ec9c24812100ee06b82ff14a08e03c218009102f00a0000019a55792b4142094e4431ef8e246682e914588b03a017508702dc0c0000019a4f6d2d095089ce4892150f2c6d630014f08ec3c617b09183100b8000019a49752cd14e49a046a2020ea469e2f514b89083ba17d09182f00a6000019a438f2c614c89ba47d20a0ee06b42ff15009203cc18609282ec0cc000019a3d8c2d195009c448d2188f286da30915608fc3bc18009003040c0000019a37812d795209ea4952180f446ec31c15989403c818509182f40b4000019a318d2cb14f49c04882128f0c6b42f814c08fc3ce18909503180ba000019a2b942c714dc9b447d20c8edc6b02ec14588a03a216808782dc0be000019a25912d214f09ba47f2108f186da31115989183d418409403240c2000019a1fa12c514ac99847720b0ef46b830014f08e83be18509082fc0c4000019a19c82b994809784672048ecc6aa2f914e89303d0187098833c0cc000019a13d92c694b49a44772078f046d030415088fc3ba18009102f00ac000019a0dd22d094fc9a84652080ecc6a42f5155092c3d218609083040bc000019a07b32e01588a0c49a2220fac70432515b89543ea18e09703580e2000019a01c42c694ac99447620d0ef06c430815289043d818409503280cc0000199fb992e995c4a1c4af2268f906fc31c15f89843e018d08f02dc0c20000199f5b52bf945897a4601ff8e8068a2e614608c439e16f08902d80d00000199efd22c214c49a24792138e9c6902df13f88ac3a217308902e80aa0000199e9ce2d615309c64842118f046bc2f614688bc39e17b08e03100b60000199e3cd2d495209c64842168f0c6ca30214a88f43ba17308702ac0ac0000199dde82c014749844541fd8e8068a2ed14608b03a417e08a03000b80000199d7f22d014f49b847b20b8ed06ba30814f88e83a617008c02fc0cc0000199d1ed2ce94d89c84822100f206d030e15a09483dc18909503240ce0000199cc0f2be148497a45a1fa0e586802eb14508a03a018209403140c20000199c60b2d114dc9b247220d8ef06c02fe14c89103bc17908d83080b80000199bfef2d715549de49921c8f506f431115c09503e218d09483280ce0000199b9f42cc14d89c048f2150f406ce30c15708f43c418008d830c0be0000199b3fa2cd14e49bc4722078ee86c42fc15008f83ba17508b02f40bc0000199adcb2e6959ca0a4a121c0f386d430215509183be17908c030c0d00000199a8052b1943095a44d1f20e2865c2d6141085838416408a02c009c0000199a22e2bc147498646b2058ed46a82fc15189083b616e08902d80ac00001999c822a913f094a44a1f80e546722d513e888839417108f02c00a60000199966c2d5153c9f049921d8f6c6ec31415489043be18109002f80ba0000199907f2ce152c9ba47820c0ef46942e414088903a617308882d009e00001998a5a2e0157c9e24872118f106c62f915189043d4189094830c0b2000019984822bf145496a44d1f60e4467c2dd14508cc39817408b02c40bc00001997eb62ba14409764622050ea869a2e914808d83c017509103180c2000019978e22c314b09944612028ea86922e714a88cc39816c08682ec0c6000019972ca2d9154c9ea4a221d8f6c6d831115e89343e218b09103080d800001996cb22d795349e24942160f386e42fe14e891c3c417a08e83000c8000019966b82d6154c9e847f2100f086ba2ff152890c3b818208f02d40dc000019960eb2b714549724571ff8ea06982f214c88f83b8182090830c0cc00001995ae32cd94f09ba4892140f1c6ca31415309343e218c09382f80c0000019954ed2c814c49a046c2078edc6c630515289143c618509502f40d200001994ef52d215189b647f20f0efc6c6300151891c3ca18c09283140b8000019948cf2e19598a164ac2218f5c70032415b893c3e619009682f40a8000019942cd2d595589f84912188f006bc30314e08e43be17809003040cc00001993cc72d5151c9c047b20e0ef86ac2ff14c88d83c217e08c02c80b2000019936d52c894c89a24662060e946942e614308b838216708702d80ba000019930ca2d9152c9cc49221c0f286d430c15909283d817c09083080d200001992aae2de95809f44992168f4c6f831515809583f419309782e40b0000 else 0x19c21a92ce94cc9a847720e0f206d6306154091c3de18b09182fc0bc000019c1bd22b9945495e4501fe0e946902dd14388b83a216e08b02a80a2000019c15d32d195449d24892128f386de30015809303d018308e03040c6000019c0fb62e215849fc4a62260f646e831115909643f2199096033c0d0000019c09bb2cd14ec9d048120e0eec6a62fd14988e039e17a08d82f00ce000019c03b52d415109c247d20c0ef86ca30715609303d818609603280c8000019bfda52d415449cc4872138f306ea30d15889183de18709202dc0c4000019bf7ba2c3948098a4621ff0e8c68a2d813b084436e16108882a80bc000019bf1cc2cc14e89a24692090ea86aa2f014d88d83ac18308f83040c4000019bebe82bf148c9844672048e986b630715009043e419009083100be000019be61e2ba945897c46820c0ecc6a62fc14b09083b017308982c40a4000019bdff82df15609e649c21e8f746f230e15289243d418509703340ca000019bd9ec2d915309d848c2178f346da30f157892c3d818f09883340c6000019bd3ec2d4951c9e049021a0f106c430315209003c017c08a82fc0b0000019bce212b6146897a45c1ff8e8c6682d413b084c37c15d08202c80ae000019bc8152da95409e04812110f106ec31415c896c3e218e09303280d6000019bc2032d915489e648f2160f306ce30e15a89403e018908f83140be000019bbc062d115449d84962178f406d030215009103be17c08e82e40a2000019bb6092d114e499646b20e0eec6a62f114988f83c018109283100d2000019bb00c2cf14e89ba47820b8ee86ba2fb15208f83c418109502f40c0000019baa042d6152c9da48c21b0f4c6d82ff14f08f03b017508903000b8000019ba4312b9145096a44c1f90ea469a2eb14908dc3a217708b82d80b0000019b9e092de95889e249021d8f5c6e630815609503dc18e09383280c6000019b98152cd950c9cc4852150f3c6de30f159091c3cc187095831c0d0000019b922a2c814b499c47520a0ed46cc30114b88bc3a017308d02e80ba000019b8c1f2d0950c9da4952190f486ee31815709183ce17f08a82c40b8000019b85f02e9959ca104a02238fa470832215b09443e218e09503340d8000019b80242b5140095244e1f68e306542d714008b039a17708b83140d0000019b7a1f2cf14c898c4652010ea86982ed14508b43b417308d02e40ba000019b74232cf14ec9c44772080eac66e2e314408d03b817c08d02d00bc000019b6e6f2ae942095444d1fa0e746702ea14808d039c16c08a83000b0000019b68842c394a49a047020b0ee46c230715809283ca18a08f83080c2000019b62902cc14d49a247620c8ee46b22f314a08ec3ba18809703240bc000019b5c6c2e015449dc4862138f146b02f514f89043c618808f82e80be000019b56672d615049cc4772110f206e230b15788dc3be17908a82e00bc000019b50602d395009c248521a8f306d630815208f83ac17e091830c0ac000019b4a5c2d215049c848a2168f306d830b15389183da18c09783140d4000019b445d2d114f49c04852100ef86b42fe14e090c3ce18008b82d80b2000019b3e452e515849fa4a621c8f406de30115289303c017c08c02d80bc000019b382f2d795489ce4912170f386de31115f09583e0192094832c0ce000019b324c2ca14b09aa47520b8eb869c2e313f08a039616808903000c4000019b2c192e915b8a1a4aa2228f906f6317153893c3c217f08e82e80be000019b26142d194f49b24892180f406e030614b08dc3ac181091030c0c0000019b20012d215149c64822138f046d230715208e83cc184090830c0bc000019b19f32d715109cc4832108edc6c630414d08e43a616e09003280c4000019b13ed2d8952c9d24842158f2c6d430115388ec3b417708902d80c0000019b0e012c6149c99e46b2070ec86b02e914488c039c16908682d00bc000019b080d2ca94ec9bc47e2100ee46b430315889543ea19909d83600d4000019b01e62e915bca1a4ae22b0f986f831a15b09483f219609182fc0bc000019afc012c314ac98c47120b0f006be304154891c3d618309282ec0ca000019af5c82e815d8a304aa2218f7c6e631415909643ec19009903480d0000019aeff92bc14509644531f78e686742e3144887037015808002e40c2000019aea142c4948497c45a2000e9469c2f014988e83b818608e03000ba000019ae4362c5149c99047820f0ef86ba2ee14c88e03b617d08e03140be000019ade4a2c814ac99a4662070eb869e2fa14b890c3c017d08d02f00c2000019ad8342db956c9ee4982138f146be2f514a88e83bc18a095832c0d6000019ad2412c815009bc47e20e0ef06c42fd15189543da19809d831c0c4000019acc162e29598a124aa2208f786dc30e15489083c418209403140c0000019ac6242d094f89c44882188f286d230015108e03ce17b08f030c0cc000019ac0432cb94d899c46a2030e9869a2f714a88fc3d017909082f00b6000019aba0f2e995b0a224a321b8f286ce30914e88e43a817108d02fc0c0000019ab4332c394709844591fc8e5c67a2de13f086c37616508802ec0d2000019aae372cd14f89b047a2110f186c82fe15408f03d618f09803180be000019aa8612be94849924702088eb46a22f514a89143dc18408e83040cc000) else (if i < 262 then 0x19d9f8b2c714ac98846e20d0ecc6962ea14388a039016a08682fc0b4000019d99972c694a499a47620a0ecc68e2f114588c83ac17e08d830c0ca000019d93a52c794a098046f20d0ee06ba2f314808dc3c218a08f02fc0b6000019d8daf2c994d49be47120c8ecc6c42fd14d08ec3b617a08e82ec0cc000019d87c52c1149099647920b8ed46a830315409503cc18e095030c0bc000019d81dc2c3949c98a45f1f90e806822dd14088ac39416f08c02e80bc000019d7bcd2d995709ea48d2180f046ae30115089083d018009082f80b8000019d75f22bd14689644571fd0e6c6982eb14a08b03a617308702e00b4000019d6fe52d715449c64872178f246d430415a09403c218208e02ec0b6000019d69e32c894d89c448920e8f006c430615489003e019409703240ca000019d63fd2c1947098c46e2098ec46982eb14688c83ae16b08782c80aa000019d5deb2dc154c9e448b2190f046b62f514d88e83ae17508702cc0a6000019d57fc2c894b49a04792070ebc6922ea142886c37a16b08582a00b6000019d520d2ca94e49b247520a8ee46be30615809083b018408a03080b8000019d4be62dd157c9e649d21d0f4c6e231d15f89543da18c09583100ce000019d45f82cd94dc9c64842128f286b8303152090c3b817208a02d40ae000019d401d2bc14749744662070ebc6962ee14608c43cc17608b02f80c6000019d3a202cf94d89be4842118f246d030c15789343f219509783280ce000019d34222cd14e89c247e20e8f046bc2f314908f03d418609103400c8000019d2e3c2bf946497a45e1fc0e4c67a2e914488c03a017608902a009e000019d28502c494ac9a046f2088ef06c830614a88d83a016508882d00c4000019d224b2d6152c9d04852100ed06a62f614a08dc3a617108e02cc0c4000019d1c552d115049b84872138f306d230014e88d43b017508b02e80ba000019d16692c4949899647020c8ed86a82f814b88f43c218209283040d2000019d10682d195189d248c2180f586fa31815e09843e618e08f82fc0d0000019d0a622d6954c9d84912138f186ce2fe15189043c218709383340cc000019d04912bf14c099046d2060ebc6b62fc14e88e83ba17408a82f00ac000019cfe732de15609f04932198f586e8321162096c3de18c092030c0cc000019cf88c2c894b89a64682108ef06c430b15309203c018309403440da000019cf29a2cb14e89b648520f0ee06b42f014c08d43aa17e09002f40b6000019cec992d195089be47420d0ee46b82ea14688c839a16408582c80ca000019ce6b92c0149c97a45a2018e906742db137088839616e08182b40ac000019ce0a82d795349ca47f2118ed86c230415208f43ba18008f83000c2000019cdace2c494a89984611fd8e846a02f3144089c39417508c02dc0c4000019cd4d72ce14e89b647b2098ec06ac2f514f09003cc18209183080b6000019ccee82c894e89ca4912150f286ea30f15689143b218108f83080ca000019cc8f52ca15049ba47720e0ea469e2fc14d89083b617c08b02fc0c8000019cc31f2b6145498045f2010ea06962f414a88c43ae18509103280d2000019cbd2c2c994c49b647b2118eec6be30014e09103ac18008e83080c8000019cb73c2c714c89aa47120a0edc6ba2ff14f08d83aa17208f02fc0bc000019cb1342d395189b447e20f8ed86be30215108d43aa17a08982e40ba000019cab122e395b4a1c49f21f0f746e631015b09683d618209002f40a8000019ca5202c714c09a246c2080ee06c22f814f08f83d618908d82e40ba000019c9f452c2948497e4601fe0e986962eb14308b83a817c08f82ec0ba000019c99472cf14d89ae4792110ee46c630914d89083bc17909103080c4000019c93512ce15009ae47620e8ec06862e713f888c37c17108902e40b4000019c8d632c914f89ac47c20b8ee86a22f514588b839615d08382f00c0000019c87862be149099a4712098ea86902e013e88883a617708c82f40bc000019c817d2d3952c9d248020a0ee46c2300151092c3d618709003200d4000019c7b8b2c814d09ae46e2050ec46aa2fe14e89283da18909003040b8000019c75942c794d89b047220e8ecc6b02f314d89103b817508a82d40b2000019c6f882d815509f248e20f0ed46982e814b88c43bc17808e82e40ca000019c69782d514f89aa47820f8f186d02fe15688f83ac18509183180c0000019c63552de15789e44902128f106cc30b151894c3e618b097030c0d0000019c5d5b2cf14e49b448a2100f0c6d830715689403e018f09883080d6000019c57552d195249d248020d0f006bc30214c88ec3c418209703380d0000019c51802b9146497a4632038ea068e2f114b08bc3a016c08b02f40c0000019c4b822cb14e49b047a20a8ed86ae2ed14b08d83a017408882d40c2000019c45652d915349e04902178f0c6d830f15689243c017f08e82cc0ca000019c3f962bc14589784652008ea86a230014c08e03a817608b83100c0000019c39892ca14fc9c64842108eec6b02ff15088e83a617808c02d40bc000019c33902c894d89ca47f2100ee46c830c15309003be184094831c0bc000019c2d8b2ce14ec9a647c20b8ee46a22f915089003ac17808d02e00c6000019c27b22bf946898046a20a0ee06aa2f014688e03aa17208c82f00ce000 else 0x19f1f1f2c714d09ae46f2058eb469a2ff14d08ec3b417f09102f40c0000019f19372c414b49804632088ec46b02f914c08e43aa17108a02f40be000019f132c2d815609e849c2190f406d430214e08f83ca17a094830c0cc000019f0d2b2d2951c9c24892188f606ec31e15d893c3de18e09482e40c6000019f070d2db9594a1e4b62268f886fc31c16009843f419c09f03500de000019f010f2d595009c44822128f186d430a14e88f03b217e08d02bc0ae000019efb2c2bf147c97e4631fe0e8868a2da14288e439c17e092830c0ae000019ef52d2cb14a499646b1fd0e846a02f214c88c43a217508a82d80b6000019eef492c494a099646d2068eb46b82ee14488b436e16208702b80aa000019ee9182e895a0a224a22208f306d831015409003c217908a02f80d2000019ee3502b9947097c4571fd0e646702dd14408bc3a417c08f82e40b8000019edd4b2d095109d248520e8f046b42fe14788ec3b617d08c82dc0c4000019ed76e2bf146097245c2018e7c67e2e113a885c37015307c02a0092000019ed1622d595509e048f21d0f346de31115a89583dc18008d830c0c4000019ecb662cf94f89c048220a0edc69c2f814a08dc3b017f08d02ec0b2000019ec5592da1554a0049721c0f9070a32315f09643d0190093831c0c6000019ebf582d215149da47f2138f0c6d830114f89143ca17d09483140cc000019eb9672c3947c98045b1fa8e886982f414d08f83b217a08b03180c2000019eb36d2d715209cc48e2198f386e231415309303ca179090030c0c2000019ead7c2cc14ec99e4702078ed86be2fd15309383e818508a02fc0ce000019ea7562e21588a284b02260f986fa325160094c3ea18809183000d6000019ea13a2e015549f048b2118ebc6982f114e88ec3c0178091031c0b2000019e9b2a2d915589ee48f2140f086de30015289043aa17808f02ec0aa000019e952b2d1150c9b047720c8ef86c430015408f43c617d09183400ce000019e8f2b2ce94e89a44752080f006c030815589103be17c09103300cc000019e89192da15289ce47d2080eb46962e814a08d03bc18609183240be000019e831d2ce95409d048c2140f306d630815b09303ca18809082f80bc000019e7d152d9952c9d448c2170f446d830c15189143c418509283080b2000019e76e32dd958ca0449f2150f246d2308156893c3de18e09683340c4000019e70ed2cd95009c24792120f486dc30315409183d018809483240d0000019e6ab52ef95dca344b52238f6c6fc32415b09303de19209603040b6000019e64c72ce14f49c047420c8ef06bc2fd14e88fc3de18309203140b0000019e5eee2bc947497645c1fb8e7c6802d614788b439016408602c40a0000019e58de2dc95349ee4992218f246cc31015709243d218909683240b2000019e52d72d295589ec49721a8f906ee31415308f83aa17008602d40a8000019e4ce12ca94e09a247320c8ee06aa2f314988d43a818008c82e80ce000019e47082bf147c98045f1fb8e8868c2ed14588b438616408902b80ba000019e41122ce94e09aa47920d8f086c42fc14f08f43c017d09882f00c4000019e3b292c394b09ac46f2068ea469e2ea14708ec3be17108c82e40be000019e353b2c714ac98c4682050ed06a42e9142887c37216808602f00ba000019e2f362d794fc9d04902160f346ea31e15e09483fe1a209c03480e0000019e29242d915309c64812120f306d830214d88c43a818109182fc0b8000019e235d2b514209544501fc0e6066e2d813b086c39a17a08f03200d2000019e1d712c514a898646720d0f086bc30515689183c017a092830c0c2000019e17812c9147c98445e1fe8e586702dc140088038016808802b40b6000019e11682d795489da4812130f386c230715489303cc18508f02c40ba000019e0b792c994d49aa47d20e0ef86922ed143088038416408582c00a6000019e057a2d295209d648b2190f586f632215b894c3fe19a09d03400d2000019dff9a2c394c89c24892120ec06ac2fc14e88e438a17408882ec0a6000019df9842d915509d648c2180f246dc31215e896c3e818b09403040c2000019df35d2e115709dc4942128f206d230815409183ca17b08d83140d0000019ded642cb94c09ae4672078ea86a02e414b08b83a817208782bc0b6000019de78b2bb14709844631ff8ea46782dc14808dc3b817e08b03080b4000019de16e2dd956c9da48120d0f006a42f214888c839416908282a809e000019ddb632d315189c847e20b8ecc6aa2f714808e83b217308982ec0b8000019dd57b2c614a099647c20d8efc6cc30c154091c3ca18609783400da000019dcf812c914e09c047e20b8f006cc2fe14e09083b218409003080c0000019dc9712d215089b84832158f286e831d15d09743e019008902c80b4000019dc3822cd94f49ac47120c8f046a82f214788a83a217b08d02e40b4000019dbd892cc14f09ba47b20f8ef86b630915208e43a416708002e80be000019db7982c394609764531fc0e4466e2de14088b03b417b08c02f00c2000019db1992cc94ec9ba48f2150f1c6c830415189303d018b09282e80ba000019dab7d2d915349be47620a0ee46b22f914b08c83ae17908e02fc0b6000019da5702d695349d24842170ef86b22f414708b83a017008e82f80c6000)) else (if i < 265 then (if i < 264 then 0x1a09e632c814c49be4822118f146ca30715189043be18a09203200cc00001a098532db15449f849521d0f8c702320164099c3f619b09b032c0ce00001a0924a2d515149c84862128f346ea31315c89643de18a09682f40cc00001a08c492ce150c9bc47f20e8efc6ae2fd150091c3d418e09683240ce00001a086362d915609f049721b0f706fc32016109683e819109503340d600001a0806e2b7143495a4551ff0e686662dc13e087438015e08602a40b600001a07a792c714c49b847920d8ed46a62f314888bc3a616808782e00ac00001a074852c814b098c45e2028e986ac2f114988cc3aa17b08f830c0b600001a06e8f2d19550a0249521c0f486e031115709383de19209183040c400001a068902cc95009c447c2128efc6c630415689403d018809803280c400001a062902d094e49bc47b2098ec86ac2f614608c438c16c08582a80a600001a05cad2c114649804632040ec06c831315c895c3f218c095831c0ba00001a0567d2eb95d8a184b72280f8470633016509a441c19f09803140be00001a0505b2db95709f249421e0f446f030315288d43b217b09002e80ae00001a04a7a2be14689684652028eec6d2307150091c3ca18a08b02d80bc00001a0447b2cd150c9ba4842100ec86aa2ea14908b439617908d03000ba00001a03ea02be148898e46520d0ed46a22f114408b83a617409203000c000001a038a92c814f09a046f2050e9868e2e9143088c38e16d08682dc0b600001a032d22b8941c95044d1f90e506562ce138086c372155078826c0a000001a02cba2db15589e248c20d8ec86ac2fc15088ec3b417e08e02e00aa00001a026962e115a0a1a4a52210f606fe31915809103de18b09803300b400001a020af2c515089c248620f0ee46b22fb15189203ba18108c82d40b400001a01aad2c814dc9a247d2098ec469e2e9147889439616708802e40bc00001a014a62d715189d24862120f046aa2f314808c43b217d09403380d400001a00ec52c4949098c4702088ec86a42f0144888838a16e08702cc09e00001a008bc2d795689fc4a021e0f646f230c14f090c3cc185091831c0c200001a002b82d895189d448d2168eec6d030015309083b017408e82e80bc000019ffcd72bf946c96e4541fc0e706802ed145889439a16808982d00cc000019ff6f62bd14509644591fb0e646662de13e084837c15f08a82a80b0000019ff0f12d695309fc49e21a8f3c6ea31515489303b818108f03040b0000019feadf2d595289c848a2180f206de306152092c3d4186094831c0d4000019fe4dc2c914e89b246a2038eb06a42f614d88e03c218508e02f80be000019fdf0c2b9144896845a1fc8e906722e013d088038616708682b40b2000019fd8f82d895549e44892160f046b030214d88e03a618109002c00b0000019fd2ff2ce954c9ce4842128ef86c630215289103ce17e08c02d40ae000019fccd62e895e4a384b822a8fa471032e165097c3fe19009a033c0c0000019fc6d82d495249de49821a0f746fa31e15d09503dc18408f030c0c2000019fc0e22c614989a847920c0f086d030c15388f03b617008d83140e8000019fbaf32cb94cc9a045e1f90e446762d9142088838016208382ac0aa000019fb4db2dd15389f24972198f386d830e15409383dc18d096832c0c8000019faebd2e215609de4902160f086b62f414a08e03b616508382a80a8000019fa8ad2d895209c04782080ecc6a82fd14d89043b818109403380e6000019fa2992d295489ea49c21a0f686ee31915f097c3e619109483080ce000019f9cb42c414b499246e2078ed06a42fa14a88d03b018608d82e80d0000019f96b02cd14f499c4662068ea86aa2fe15209183c418309102ec0c4000019f90cd2c6149899c4662038e786762d013d885c36415f08182940a2000019f8ac52d195189d44962150f1c6d2312153891c3bc17d08b02e40b6000019f84c52ce95149c64822100f286e030d14f89043ba18209303040c0000019f7ec52ce94d09b447c2128f3c6dc30c14e88f83be17c08d02fc0c4000019f78de2c314a89aa48020e8ecc6b22f314c09043c617e08c030c0c0000019f72ea2ca14ac9ac47120b8eec6b42fa14e89043bc17d09102fc0cc000019f6cdd2dc95b4a1e4af2250fd472c32f16509a440a1a109d833c0cc000019f66c62e015849fc49e21a0f406e630a155891c3d218b092832c0ce000019f60c02d294fc9c44892148eec6b62fd15189143ce18209003000b6000019f5ae52c1146096a45f1fc8e6c66e2e514808b838a16f08c02f40c8000019f54f92c494989824622020e7467c2dd14488a839817908902dc0b8000019f4f052cc14d89aa4802108f006c62ff14908bc3a417608782d00a8000019f48cb2e815c8a384ca2310fe471c32a16789c04441bd0a903940da000019f42ee2c4149c97c45c1fd0e7468e2ec14608bc3ac17f08d82ec0c0000019f3cce2da952c9d447e20e8f046c42ff15409383d018209383180c6000019f36c82d2152c9da48320b8ee86a02ed14908c83ac17d08e02c00b4000019f30ef2b714609864632080eb46b02f614a88dc3bc17508b02ec0c8000019f2b032c3948097844b1f78e746862e714288d03bc18008f02e40b2000019f250d2d015089ba47c2130f286de2ff15008ec3c017b09083040b0000 else 0x1a21cc22c294a49a84762080ed069e2f214808d43c217e08c02f80c200001a216d42c814d49a44752070eac6ae2fe14c09143d818609603380c600001a210c12d415049c847d2120f386da30515289103d818c09903300e400001a20ac52cd14d49a245f2058e906802df13e888839416308c82d00b800001a204c52ce94dc9b447c20c8ef06b62ff152890c3bc17708802f00c000001a1febf2d014f09c447e2130f286d430a15609543f818909483300c200001a1f90e2aa93f49484521fe8e7867e2e114488a43aa16c08782d40aa00001a1f31c2c594b89a047320b8ed46922e814088a43a216e08782b40a000001a1ed112d095149e64892118ef06c02ff14d08f43c218a08c82f40ce00001a1e70b2d315189bc47920b8ef46c630315008e83bc18609202fc0ba00001a1e1082d214f89d04912168f246ca30915288e43be18708f82f40c600001a1db172c9149499a46d2090edc6a02e814488bc39216e08802e00c200001a1d5262c794a099646f2070eac6aa2f314988e03c417d08e02f40c800001a1cef12ec960ca464b52230fa070a31d15509303c818a094831c0bc00001a1c8f72cc95189c84922100f186b02fb14508983b417109083100c400001a1c30c2c594a49904742078ec06a82f214408b839417a08f03180c000001a1bd192cb14d49b647820c8ebc6a230315289143da18608b03000b800001a1b7252c814b498c4632080ed86a62ee14688a839e16f08b02f40c200001a1b1272ca14ec9cc48320f8ed06a22f514888dc3c017e08c82c40a400001a1ab2a2d095189b447520a0ef46c030714f08ec3ba18509103000b600001a1a5182d695249ea49521b8f6c6f431415809403ec18908e83040c600001a19f452b8945096e45e1fd8e6c6762e2142889439816a08982d40aa00001a199562c994a098a46a2088ed46a82fb15389503d218b09283240c600001a193732c3945896e44d1fc8e806882e413e087437e16708202980aa00001a18d6d2d415009ac4852138ef46b62fd14c89183ac17708982dc09c00001a187b22b9947896844f1f88e6c6822f214808943aa17408f03180c600001a181a22d615249cc4882140ee86a42f214b08e43ce17f08f83140c200001a17ba22d115149b847620d8edc69c2fb155891c3c818509403380c000001a175c92bb947096e4632018e7c68a2f214908a83a817608982e00ba00001a16fe62bf14689844652000e9c68a2de14588d43bc18808e82f40bc00001a16a032ba94589724592010e906802e013f88b839416e08782d809e00001a163ea2df157c9f249e2298f8c70832215d09743e419209703480b600001a15dec2c994ec9ac4712090eac6942f014208a83a617d08b030c0cc00001a157fc2c894fc9c847c20a8eec6c230815009083da18c09283040cc00001a152092cb14e09b04772110ed06b42fe14a88a03aa17608c02f00c200001a14c3f2b694609764612048e8c6942df13f888438a16508602d40a800001a146372d595349e248a2170f286ce30715309103de18b09583140c000001a140252d114fc9d047f2118ef06b02fb15609183c418509382f80bc00001a13a1e2d4153c9d848e2178f506da30715509183bc17d09182f00c600001a134012de156ca084962190f586f0317158094c3e618d09503040c200001a12dfd2cf15089e44972168f3c6f031115709403ba17808c82d80ac00001a128012cf95189ba47a2088ee86c630e14f08c03ba16f08902c80ae00001a121d22e815e4a464b22270fb471e33616989dc40c19809203140c200001a11be72c614a09b84772088eb06ba2f8150090c3be18809503180ce00001a115fe2c214b09a247b20c0ec869c2f314a09003c818709083240c000001a10fef2da15589de48d21a8f306e631615a89583e418c09683140b400001a10a0f2c394a099a46f2058ebc6902e614788c439c17808a82e80c000001a1041f2c794fc9be47720e8efc6be30014f88e03ba17608c831c0c200001a0fe0d2d915389ce4912120efc6b430415189003ba17e09282fc0ba00001a0f81b2c514a499a46c2028ea069a2e914488c03be17608d83000be00001a0f21f2d014f49c248120c8f0c6c2309156095c3f019409883180bc00001a0ec4a2be946097245f2030ea46962ed143088039017508c02ec0ba00001a0e6672c494bc97c45c2070ed069c2ed14788c439e17108702fc0c600001a0e0532db95549f64882140f1c6e631315f89a83f819309603000b600001a0da312de15749fa4942190f546f631915c89503e6185092032c0cc00001a0d40e2e595b8a0c49821c0f8070c32216109683f419e09703400d400001a0ce052d615709ea4992200f9070632315e09603e018a094031c0ca00001a0c7fe2d195049b046e2090eec6a82f714b88fc3b417e08d82e80ae00001a0c2062d294e89c84862100ec469c2e314588d03ac17a08f02f00c800001a0bc162c614e49b24712060eb86a22fb15288f83aa17708e02e40c400001a0b60a2cf95089dc4912128f046c030114b08e43b818809002f40c400001a0affe2d595409d24812168f246ca30c15288f03ce18209103180c600001a0aa522a693e49424441fa8e506642d613d885038016808a83140b000001a0a4542cf14f49b247c2058eb86962ee142888c38216c08902f40bc000) else (if i < 266 then 0x1a39b3b2b6146896e45d2020e646802e214488d83aa17c08f02e80b400001a395252d895009d04842108f086dc31215a895c3f219409302f80b800001a38f462c214809804662048e946822e113d88a439816b08c82f40c000001a389472d1152c9e048a21c0f8070a31c15f09783f218d09583080b400001a3833a2d115189d64942168f186ce2fe14f89103c218b09483140ba00001a37d2e2d095009ce4912160f446cc30715309343cc18709803400d800001a377302d3952c9d248b2170f6471232c162896c3e6188091030c0d600001a371312d615109d44822110f006c630315489243c818609683580d800001a36b472c7949c9aa47320b0ee46c02ff158892c3d817f09102fc0d600001a365272e095789e84942168f206ba30815489103bc17d08c82d40b400001a35f2e2c814c49ba47c2098ed46c02f714f89043be18609102f80bc00001a359492c594849764561fe0e546622e714b88ec3b417909282f80ba00001a353402d9154c9c64882140ef86b82fa14f89203c018209003100ba00001a34d4a2cf94ec9c64842128f006b22fe14d88e83ca18c09283340d800001a347562c994e89b84772090eb46a42ff15189183da18e09382e80ba00001a341232ef95b0a0e4962198f246ca30115289343e418a09383240d200001a33af82e3159c9f64a421f0f4c6e231215909543e418c09703240d200001a335192c1949c98645c1fd8eb068c2e214488dc3ba17e09103000be00001a32ef52e595aca1a4b02238f706f431615b09143b018208f02f80dc00001a3292b2b6143c96e4581fe8e7c67e2e414588a03a417808d82e00b600001a3232b2d114c89c64802148f286e230514f08f83d218309103080c200001a31d442c294a099e4682050eb06942e714688ac39a17a08b82f00ca00001a317492cf15089aa47820c0ef46ae2ed14988c039c16d08983000cc00001a3116e2c4946896e4621fb0e7467e2e514688f83c017c08e82cc0be00001a30b892c514a499a4782040ee46c22fe14a08f03ae17b09102fc0b600001a305922cb14b49b84812100f306ca2fc15189203b217909002e40c200001a2ffa42c914dc9ca4792148f146ba2fb15209103d618908e82f80b400001a2f9ac2d195089c447e2128f0c6f231815e09603f019309683280b800001a2f3c72cc14e89ba4732090e9c68e2e3143087438016a08602d00ae00001a2edba2db95489e848920f0ef46b02f714d88cc3a017f09803480cc00001a2e7d22c594a09a046c2088ee06b82f214788c43a016b08682d40b200001a2e2002ba945c97a46a20b8ed06a02f914c88f83a617708c02e00b800001a2dc042d295189dc4862158f086d030314d88e83b017d08802f40b000001a2d61b2ca94cc99645c2060ebc6a42f015088c83ae17208702d00a800001a2d0082da955c9e448c2170f086c430815489103d818b09683100be00001a2ca2b2bf148097e4632030ecc6982fd14e89003ae17708983000a800001a2c4492c3149c98a45e2040ea469c2ed14608bc38c16408882980a800001a2be2a2e4158ca024a42228f7c6fc31b15b89283e019009503240d800001a2b8022da955c9f048b2160f306ea313156096c3f218f09683000ba00001a2b2172cc94f49c648220f0f0c6b62ff14a88f03c4182092032c0c000001a2abef2dc957c9fa4922178f046ce31315689583f819909a03240ca00001a2a5e12d4952c9da49121d0f5c6e430815409003b817708c03000be00001a29fc72e115889fe49c21e8f5c71032d16689b040619c09803240ce00001a29a162b0142896c4581fe0e5c6702e614308a438e16a08783180c400001a2940a2d615409f04942168f6c6f432015a89403de18d09883200d800001a28dfb2d395109c04722070ed86a42fd15689103ec18c08f83280c000001a287f42d295309da4942198f6070c335167098c40819f09c03200de00001a282072cd14f89be4752078eec6aa2f214a08ac39e17308d83180be00001a27c172c214849a246f2058edc6b830414e88ec3ba16a08a029c0bc00001a275e82e89594a0049a2170f206c630115008c03a817708c02d80b600001a2700a2bf949098e4672008e986822e614708bc3b218009382ec0c800001a26a022d695449dc48720e0f046ca30815a09483da18509202ec0ba00001a263f42d3153c9dc49221b8f686f430f157892c3da19509583240cc00001a25de42d915389d448220a0f0c6a830014d08d039e16408502cc0b000001a258122b714349444491f58e2066c2de14388b03a817908f02e80ba00001a2520b2d2955ca0049a21b0f306f231615d894c3d418e09702f80c400001a24c3f2b494149644571fe8e946942fb14a08f43d218008e03180c600001a2465e2c294889924612050eb46c0307152093c3de19009583180c800001a240742c394a898846720b0ee06b82f414b88fc3c217f09203080a800001a23a6d2db15389ce4852100f246ca30515289083ba18208e830c0c000001a234902c2149499a46c2058ec06902eb14a08cc3b618709183040be00001a22ebb2bb148098e4702110f086d030f15509183bc18009482f40c200001a228b02cd94cc99c47020f8ed86a82eb144089038e17508f83040b400001a222a02d9953c9d24852180f386ce2f714808ec3ba17d09202f00d8000 else (if i < 267 then 0x1a519c92c614c899a46b2068eb06ac2fc14f89103ea19a09603440d200001a513d02c914f49b447d20f8eec6c230314f09403cc18309102f40c000001a50dd52ce14e49c64872158f286d030115388f83b817f09083300ca00001a507ea2c594b897a4602030e7067c2dc143089c38c16408102a40aa00001a501fa2cd14e49a446720d0eb869c2ee14e88e03b8179090830c0c000001a4fc262c114309664531f90e5c66e2d7141887838c17208902d40c200001a4f6202d415409d847f20c8f006c030a15009083d018d09483200c400001a4eff22e515b0a104aa2210fa070431c15789183d218f097031c0d000001a4ea142c594b899e45d2020ea467c2e314308c439c17608a82dc0b600001a4e4242c894b498447320d8ee46a42e8141089039a17808a82e80be00001a4de212d995589ee4942240fac71231915b09743f219309d835c0d200001a4d8252cd14e49b047b2098ea86ac2f714a08d83b817308e02d80b600001a4d22b2cf95049c248220e8ee86b02ff15088dc3c4184092030c0be00001a4cc432c914ac99c4712078e886822de14188c83a417308d02e00b000001a4c64e2d095289d448d2198f486e6317156890c3aa17d09403200c200001a4c02d2dd15549ee4982198f406d030a15609443ee19a09983300c400001a4ba002e615bca0e4aa2258f8070231f15989383d418b09203180d000001a4b3f52d5953c9d848e21a0f346d830b15188e03ac17708c82f80d000001a4adfe2cc15149d04922190f4c6da30214e08d03a017109082d80c200001a4a80b2ca94d09ac4712090eb468c2e614808e43b016908302bc0a200001a4a22e2ba945c98045a1fc8e5c67c2e914908d43ac17c08f83000b400001a49c4a2c1949499846e20a8ef06ce2fd15209103cc18809683280de00001a4963d2d1952c9ce4802138f2c6dc305157091c3be18109403100b600001a4904e2c994ec99e4712088ee069c2f214d090c3d618709182fc0c200001a48a832b4943097c45a2050f086d231015309183ba18509383080c000001a4849e2c914f09be47b2140f106b630314f89283c617908982d40b600001a47ea62d414f49a647620c8f0c6c02ff14b88c43a817508b82f00c200001a478912d815189d448d20e8f246ca30715309203cc18009303340c600001a472ab2c294a899a46d2078ecc6b62f914788c43a817308c02c809c00001a46c902dc95449ee4962198f3c6d830715789243ee199092030c0c200001a466972ce95149c84842160f386cc30615489343cc187090030c0d200001a4609e2d394f49b24702088ec46a62f814d88e83b217d09002cc0a000001a45a912d3150c9cc48120c8edc6a62f115288ec3ba17b08f83100be00001a454842d895549f04902108eb86a22f414508cc3aa18008d02f00c200001a44e7e2d095109c247f20c8ed86ac2f915289203ca18d09803580d800001a448622db954c9f049a21a8f346c830614d08ec3aa17e09002cc0b400001a442722c494a89764531fe0e706782df146889038c17108902d00b800001a43c9e2b794449744632030ea86a62ee14788c43b018509803480cc00001a436b42c614b49a64742060e9c6c42fd14c08e83ca18709183140d400001a430a92d514f09c048320d0eec6be2fc14d08b83be18909503000ce00001a42ae12b9944496e4581fd8e686762e1146887839816f08302ac0aa00001a424fa2c814b499e46e2050ed06a22e9145089039a17209083080d000001a41f2b2bb143c97e4622018ec86982ee145089439a17008a82cc0ac00001a4190a2dc15249da4952180f5c6d030515389243ca18c096031c0ce00001a413272c194809684511fb8e8c68e2ec14a88a039617408802e00c400001a40d172d8155c9d248c21b0f506da30b15289143ce17e09083000c400001a4075b2b7941094c4461f18e1463c2c413a087439a17208c82e80b000001a401552d195209e44902178f1c6d030115189043b817d09783340d600001a3fb6d2c194cc9a846a2068eb46922e614888a837c15e08482e00c000001a3f5662d695389de4832168f206d630514e08ec3c219009483140b000001a3ef762c994f09b847e20a0eec6ba2fb14a88c83a017208902dc0c400001a3e9722d0951c9cc48a2140f046d42f914c08d83ac178091030c0c800001a3e3732cf14fc9b447920a0ef46b830515089343b418309182d40be00001a3dd792ca14d89a04732068eb86b62f014808e43a417b08e83100c200001a3d7462ea95bca0049c2188f606e631115a09443f619a09803200c800001a3d1542c914d09bc47420c8ed46bc2f414a08ec3ba18609703200d400001a3cb402db957c9ee49e21b8f506f631e161897c3e218e09603240c600001a3c5392d415289d447b20b0ec06a42f214e08d439017309002f00d000001a3bf322ce95009d04902120f286e831015008e83be18208b82fc0c400001a3b9132df155ca0e4a82240fa06fe32516289a441819d09c83540d600001a3b3122d115149c247520d0ee06b2306153891c3ce18409583300c600001a3ad292c1148898045d1ff8e8467e2e614308a838a16308602840a200001a3a7002e995b4a124a62238fa470031915a89343e618e098834c0dc00001a3a1092cb14dc9b447e2108f246ce315159094c3e618a09182d00be000 else 0x1a525b300015149ba47d2098ef86aa2ec14508d03ae16e08582c40ac00001a51fab2d615509f649c21c8f686f831215d09583fc18e08f83140ca000)))))))))

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



private theorem b260353 : covered 260353 260419 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260419 : covered 260419 260486 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260486 : covered 260486 260553 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260553 : covered 260553 260620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260620 : covered 260620 260686 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260686 : covered 260686 260753 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260753 : covered 260753 260820 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260820 : covered 260820 260887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260887 : covered 260887 260953 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b260953 : covered 260953 261020 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261020 : covered 261020 261087 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261087 : covered 261087 261154 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261154 : covered 261154 261220 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261220 : covered 261220 261287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261287 : covered 261287 261354 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261354 : covered 261354 261421 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261421 : covered 261421 261487 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261487 : covered 261487 261554 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261554 : covered 261554 261621 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261621 : covered 261621 261688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261688 : covered 261688 261754 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261754 : covered 261754 261821 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261821 : covered 261821 261888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261888 : covered 261888 261955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b261955 : covered 261955 262021 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262021 : covered 262021 262088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262088 : covered 262088 262155 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262155 : covered 262155 262222 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262222 : covered 262222 262288 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262288 : covered 262288 262355 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262355 : covered 262355 262422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262422 : covered 262422 262489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262489 : covered 262489 262555 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262555 : covered 262555 262622 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262622 : covered 262622 262689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262689 : covered 262689 262756 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262756 : covered 262756 262822 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262822 : covered 262822 262889 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262889 : covered 262889 262956 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b262956 : covered 262956 263023 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263023 : covered 263023 263089 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263089 : covered 263089 263156 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263156 : covered 263156 263223 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263223 : covered 263223 263290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263290 : covered 263290 263356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263356 : covered 263356 263423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263423 : covered 263423 263490 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263490 : covered 263490 263557 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263557 : covered 263557 263623 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263623 : covered 263623 263690 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263690 : covered 263690 263757 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263757 : covered 263757 263824 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263824 : covered 263824 263890 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263890 : covered 263890 263957 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b263957 : covered 263957 264024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264024 : covered 264024 264091 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264091 : covered 264091 264157 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264157 : covered 264157 264224 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264224 : covered 264224 264291 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264291 : covered 264291 264358 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264358 : covered 264358 264424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264424 : covered 264424 264491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264491 : covered 264491 264558 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264558 : covered 264558 264625 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264625 : covered 264625 264692 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264692 : covered 264692 264759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264759 : covered 264759 264826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264826 : covered 264826 264893 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264893 : covered 264893 264959 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b264959 : covered 264959 265026 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265026 : covered 265026 265093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265093 : covered 265093 265160 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265160 : covered 265160 265226 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265226 : covered 265226 265293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265293 : covered 265293 265360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265360 : covered 265360 265427 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265427 : covered 265427 265493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265493 : covered 265493 265560 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265560 : covered 265560 265627 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265627 : covered 265627 265694 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265694 : covered 265694 265760 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265760 : covered 265760 265827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265827 : covered 265827 265894 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265894 : covered 265894 265961 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b265961 : covered 265961 266027 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266027 : covered 266027 266094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266094 : covered 266094 266161 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266161 : covered 266161 266228 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266228 : covered 266228 266294 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266294 : covered 266294 266361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266361 : covered 266361 266428 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266428 : covered 266428 266495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266495 : covered 266495 266561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266561 : covered 266561 266628 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266628 : covered 266628 266695 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266695 : covered 266695 266762 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266762 : covered 266762 266828 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266828 : covered 266828 266895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266895 : covered 266895 266962 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b266962 : covered 266962 267029 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267029 : covered 267029 267095 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267095 : covered 267095 267162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267162 : covered 267162 267229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267229 : covered 267229 267296 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267296 : covered 267296 267362 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267362 : covered 267362 267429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267429 : covered 267429 267496 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267496 : covered 267496 267563 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267563 : covered 267563 267629 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267629 : covered 267629 267696 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267696 : covered 267696 267763 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267763 : covered 267763 267830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267830 : covered 267830 267896 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267896 : covered 267896 267963 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b267963 : covered 267963 268030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268030 : covered 268030 268097 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268097 : covered 268097 268163 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268163 : covered 268163 268230 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268230 : covered 268230 268297 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268297 : covered 268297 268364 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268364 : covered 268364 268430 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268430 : covered 268430 268497 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268497 : covered 268497 268564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268564 : covered 268564 268631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268631 : covered 268631 268697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268697 : covered 268697 268764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268764 : covered 268764 268831 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268831 : covered 268831 268898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268898 : covered 268898 268964 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b268964 : covered 268964 269031 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269031 : covered 269031 269098 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269098 : covered 269098 269165 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269165 : covered 269165 269231 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269231 : covered 269231 269298 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269298 : covered 269298 269365 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269365 : covered 269365 269432 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269432 : covered 269432 269498 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269498 : covered 269498 269565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269565 : covered 269565 269632 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269632 : covered 269632 269699 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269699 : covered 269699 269765 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269765 : covered 269765 269832 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269832 : covered 269832 269899 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269899 : covered 269899 269966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b269966 : covered 269966 270032 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270032 : covered 270032 270099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270099 : covered 270099 270166 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270166 : covered 270166 270233 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270233 : covered 270233 270299 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270299 : covered 270299 270366 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270366 : covered 270366 270433 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270433 : covered 270433 270500 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270500 : covered 270500 270566 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270566 : covered 270566 270633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270633 : covered 270633 270700 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270700 : covered 270700 270767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270767 : covered 270767 270833 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270833 : covered 270833 270900 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270900 : covered 270900 270967 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b270967 : covered 270967 271034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271034 : covered 271034 271100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271100 : covered 271100 271167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271167 : covered 271167 271234 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271234 : covered 271234 271301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271301 : covered 271301 271367 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271367 : covered 271367 271434 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271434 : covered 271434 271501 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271501 : covered 271501 271568 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271568 : covered 271568 271634 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271634 : covered 271634 271701 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271701 : covered 271701 271768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271768 : covered 271768 271835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271835 : covered 271835 271901 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271901 : covered 271901 271968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b271968 : covered 271968 272035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272035 : covered 272035 272102 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272102 : covered 272102 272168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272168 : covered 272168 272235 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272235 : covered 272235 272302 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272302 : covered 272302 272369 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272369 : covered 272369 272435 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272435 : covered 272435 272502 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272502 : covered 272502 272569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272569 : covered 272569 272636 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272636 : covered 272636 272702 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272702 : covered 272702 272769 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272769 : covered 272769 272836 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272836 : covered 272836 272903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272903 : covered 272903 272969 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b272969 : covered 272969 273036 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273036 : covered 273036 273103 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273103 : covered 273103 273170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273170 : covered 273170 273237 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273237 : covered 273237 273304 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273304 : covered 273304 273371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b273371 : covered 273371 273438 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 260353 273438 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b260353 (joinCoverage b260419 b260486)) (joinCoverage b260553 (joinCoverage b260620 b260686))) (joinCoverage (joinCoverage b260753 (joinCoverage b260820 b260887)) (joinCoverage b260953 (joinCoverage b261020 b261087)))) (joinCoverage (joinCoverage (joinCoverage b261154 (joinCoverage b261220 b261287)) (joinCoverage b261354 (joinCoverage b261421 b261487))) (joinCoverage (joinCoverage b261554 (joinCoverage b261621 b261688)) (joinCoverage b261754 (joinCoverage b261821 b261888))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b261955 (joinCoverage b262021 b262088)) (joinCoverage b262155 (joinCoverage b262222 b262288))) (joinCoverage (joinCoverage b262355 (joinCoverage b262422 b262489)) (joinCoverage b262555 (joinCoverage b262622 b262689)))) (joinCoverage (joinCoverage (joinCoverage b262756 (joinCoverage b262822 b262889)) (joinCoverage b262956 (joinCoverage b263023 b263089))) (joinCoverage (joinCoverage b263156 (joinCoverage b263223 b263290)) (joinCoverage (joinCoverage b263356 b263423) (joinCoverage b263490 b263557)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b263623 (joinCoverage b263690 b263757)) (joinCoverage b263824 (joinCoverage b263890 b263957))) (joinCoverage (joinCoverage b264024 (joinCoverage b264091 b264157)) (joinCoverage b264224 (joinCoverage b264291 b264358)))) (joinCoverage (joinCoverage (joinCoverage b264424 (joinCoverage b264491 b264558)) (joinCoverage b264625 (joinCoverage b264692 b264759))) (joinCoverage (joinCoverage b264826 (joinCoverage b264893 b264959)) (joinCoverage b265026 (joinCoverage b265093 b265160))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b265226 (joinCoverage b265293 b265360)) (joinCoverage b265427 (joinCoverage b265493 b265560))) (joinCoverage (joinCoverage b265627 (joinCoverage b265694 b265760)) (joinCoverage b265827 (joinCoverage b265894 b265961)))) (joinCoverage (joinCoverage (joinCoverage b266027 (joinCoverage b266094 b266161)) (joinCoverage b266228 (joinCoverage b266294 b266361))) (joinCoverage (joinCoverage b266428 (joinCoverage b266495 b266561)) (joinCoverage (joinCoverage b266628 b266695) (joinCoverage b266762 b266828))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b266895 (joinCoverage b266962 b267029)) (joinCoverage b267095 (joinCoverage b267162 b267229))) (joinCoverage (joinCoverage b267296 (joinCoverage b267362 b267429)) (joinCoverage b267496 (joinCoverage b267563 b267629)))) (joinCoverage (joinCoverage (joinCoverage b267696 (joinCoverage b267763 b267830)) (joinCoverage b267896 (joinCoverage b267963 b268030))) (joinCoverage (joinCoverage b268097 (joinCoverage b268163 b268230)) (joinCoverage b268297 (joinCoverage b268364 b268430))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b268497 (joinCoverage b268564 b268631)) (joinCoverage b268697 (joinCoverage b268764 b268831))) (joinCoverage (joinCoverage b268898 (joinCoverage b268964 b269031)) (joinCoverage b269098 (joinCoverage b269165 b269231)))) (joinCoverage (joinCoverage (joinCoverage b269298 (joinCoverage b269365 b269432)) (joinCoverage b269498 (joinCoverage b269565 b269632))) (joinCoverage (joinCoverage b269699 (joinCoverage b269765 b269832)) (joinCoverage (joinCoverage b269899 b269966) (joinCoverage b270032 b270099)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b270166 (joinCoverage b270233 b270299)) (joinCoverage b270366 (joinCoverage b270433 b270500))) (joinCoverage (joinCoverage b270566 (joinCoverage b270633 b270700)) (joinCoverage b270767 (joinCoverage b270833 b270900)))) (joinCoverage (joinCoverage (joinCoverage b270967 (joinCoverage b271034 b271100)) (joinCoverage b271167 (joinCoverage b271234 b271301))) (joinCoverage (joinCoverage b271367 (joinCoverage b271434 b271501)) (joinCoverage b271568 (joinCoverage b271634 b271701))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b271768 (joinCoverage b271835 b271901)) (joinCoverage b271968 (joinCoverage b272035 b272102))) (joinCoverage (joinCoverage b272168 (joinCoverage b272235 b272302)) (joinCoverage b272369 (joinCoverage b272435 b272502)))) (joinCoverage (joinCoverage (joinCoverage b272569 (joinCoverage b272636 b272702)) (joinCoverage b272769 (joinCoverage b272836 b272903))) (joinCoverage (joinCoverage b272969 (joinCoverage b273036 b273103)) (joinCoverage (joinCoverage b273170 b273237) (joinCoverage b273304 b273371))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 260353 ≤ index 500000000/512 := by decide +kernel
private theorem starting_value : fast 500000000=26355867 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 500000000=26355867) (n : ℕ) (low : 500000000≤n) (bound : n≤525000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=500000000
    · rw [first,anchor]
      exact starting_value
    · have past : 500000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤525000000 by omega)
        have within : index n / 512 < 273438 := by omega
        have lower : index 500000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤525000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ500000000To525000000
