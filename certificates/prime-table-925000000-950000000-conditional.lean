import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ925000000To950000000

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




private def radical : ℕ := 0xa226673aa46411ae20fc42d6c5d9e15aa8868e4a864987914e1d40101f322bfb28f9155186714b5ec622794bbfb9b745d6029958347d86e139e1086339edaca2cb7f58ecae949662add77724fed83ee71e8e63d6596e70ce8ee064b439e8b667f56c217febb19374284cf2f11fb8ad82db72db57c94cfd16219b6256bdf9bac336b105792460589fc4ed767a2e277e6ba4913429b6a09247d1b4e8e36435e19fca5447b96af4ad72b2000743cc9cb67ce34164e10c93c53477bd94c2180ab300092d8de6bc126196cf5d5aff8d82cf343353b521f1caa66039abee21d4441dff55934199b5c9efd5637f6dece60f0c1b7edbab3c8de7bb98018d437087ad98589af55c032f8d2a2c87df63c971c10efc47df02fdaa04c9693545c82e892e69c011d6a803befdf2e6cd0d1fabfdc4ed011bbc6f2e7f9e4ed2b7257609c076aa466787055e8a96da7e78fe4083250b8b6764437f745835ec4e8f7bfdc2dac08403dc841d515eeb0db8824a49a02fa7b123f4e7535b0f382acbda99688922589329df978345ca8d667f6c6857d7bf4a3d745fff9c892a052caea2eb968fcc845bc96a5c27593e02075f953cd77accdbb78b82a9d7da02c66ec7d6cc51c49ef0f2cba624ef1f345905bfead8047bfe9864bb3112c66b0bd40043000bde68bfe69ec243fdcefcdbe8bc9160dab1f76ecddf75321734be28d0bc6325ce3e6af68292fef7e35c590d42c6e1518a5c3bf05fa220c2d29fe14dff0069855604c04425458a86b1ae0377ce884beda6da31fe7b6c05333b9dd6dc4ee5caf695c0304f72cd33eccade6fce1009de13ebd8a14a3bf75a91d5295783342493c102c29abe0a4ccdbecec4a1733b8064b0ee216890bb51589c04229ebe2fe37db64fb74484b5daeff68998740186c30b2e3e3cee5236e236dd1b89c0653f7c01b1bf9b2bf078403ebcca70828b735bb2c5796caa530654683428a1b4e3e387808ba4641163e6f0d5e418bded75f5fbc77632b6e8aba6542bb2944dcb09707b7a3a40b1909d68904f1021a105492231bbf4e5f5888e28ec7efbef351cdf2add1d2c5d99465b013ee9ad23109bbc25485fd77b0635e765ae7e96c836cc18af54920100717aa97e84fbff96c7de804ddc8059d17f2795061592cb60a933a305a24236b7f42aa5ea487808d345742f19fe7c4765791162ecaf96f7e7b0e21e3fc4ee895d7dbbe6ad88281a724350711bc8bd591e990a871713781f319fc8fee833f8aeca9d7b48e4a2e3a3d34491176b53a3856513b7756e61aba5710f5baedb1e6d9a91283d8841180d92e8d7f280b100ea1e7657e4fec7faa0bca86956f0720c84afb320659bfd3db0690a419d0e0c65d6f2c51caf032cac99ec5bac846cfedd24d16f16e797a31fcaf7c6ccc65dbdd1b61c8a6c6498b8bc8e77849e3c8cb996c4fd38e8f44b343e2eb8ba65d681a21b4a55165bbe74a81c410e5f55a1e604ebeb9a1e58eb9bf911342156919492ca15e1cfb707517aae277d65edc1272f8de77941b94d1043581fe34ed8ad7c7544e16b904c895df19fac04aa16478b1ecad198ebce8f7711a45bda1955b3c693c1a308656e990d30272b26bc276cdebabbcbc4d335e6e53fd0c87c8d877011fcfa19ad76baa137c46f5bb475c19abfc4892719d7b2bcb653704de14a47f8a5ee970e5f304738496982e0f30ca413e720c19e4e96b6952b4d38b5efe001a5910481a82ff20d506938ea07229be1520bb81f39bc1409e632f837151ae7a6772e226e5d1ad092d126f7786454f8ef9d8149d48db5f74b5ccf7a5b2f5135d439e7eca465077ee95d4765a48e165d1619c94a994e084a4fa7f5e30a923d174e56b7aa51e469b1dbc2c1c72f0706e683b842b06df15bdadfcf1452ab7315832c3a0f47a862bc9cfc550e9f245b76eac8cc622058e69315ddc8f1f381b852fc5fd0f4644c7a3ba4978c51a0b3b72d0951e90b94023360e0e5d613602611a68d2776da26cf6fae3e056ecdcf7a2837a7b4bf75ccb8afd89af858f68ff93987a7b55bda364486d9e79a616d9b8ce3f17d6f2a4de59a9d753f3c941f27b39284a66a2107bc72345442d5b1de2620d887af7e666dbbe111784b166b85d05c65d8305829bc2599bc504848c39570478298d0f7ef2f80c9dacaab4f565cd893176243d9497c31ff951d05a7ab4b9ea1f992d0d214f63256e62fdba39777f2af0a92a72a3d70418bfbbf9844eb04f388256bfe8538e40eb1396e1348cb1c5d9bfff09617074d77dbeba451b15e70ef6ae95d840c32916d2ed591518141e19bdd5b80f8bd7725619e370cdea3172a46f6f3ac62d2cb0e3a47c8f40d535d85ddbccff372f2fc5743cc1612d746b2add58dc311d91b8cdb36b8a0a545ab1c847454314ee98086b7e2d1198bd8165b6c44c48cbea30feb2b55a9974496b58945ee50dda9ed5a5abe95b2e61cda5c7904b3df452da3d1035cc6915fc0fcdef80478427bf554e1a75e75f35834d5266611ce9d14a44995ef83151f4376f058f306d4db828e6fa8c960e1991c36c7de2423f40a0f2ee72f3e520ccc34d9c6893f98ec85b2e042eba128baf124fd1f10b73635e1841fd9bd09cd5843395ba5b068447482e1e3608d341bae86ac531533ade7e12e0e77efde23621811d17b5486eae137922d322ae2ec443fb94d7d963dc0dd1e63e456e96b864df17760b646fa6f4e6cb29696e96e0f06b494b2191ab8e4c3da8fa980430a1e91328f4fa732cc857cb3b1f971678dc537eaf848e83486ef62936fe45e754411953b5bf16bc3994b8ce58aa78e54741f365aa1594efe0cf3ac5752d0dc420ea10f1d0eaed2d7d98f0884330d85de564911a04e8ad1f14e036b565a65bd0fa8d50ac56a91b5275b9e1c753b97253c489f568be45df809468d4aa4e8f4d8c4dc05617bcbdd6a517857d384855eca9fb8668e2f557cd451704c1484a4c0377baa2648c18e82b09baaff32c4e88f6b52939388e5e507fa73d6be201308e5c80e77273a2c4f869a03cc7176ac0f3ff6976dac2a152ef4997a4fdb16985c372619de4e4d83499314ae96892719f9cf5c2e24fd1c42f115869911740f38c6361497d728564aa03b93ac698de50ed134943c9b606c7ea395bd000f721ba0d6bc2f30d6e79f17d84377a6b6bfd84c881895a1da854ddc5bc8e1934fe02d27e24622bdf6477fd7d6ee27da3822ce49cba8fa5cda77fd4dc82d921be16eb1d6c63a90985f6d2ad22f79ca892fe7592970124dffac0cd4ce015498957c3c93d29bca21294af9b5d6a8a6e40b2938a0f27bf599feff771181aff3c8c21324169e10db8b56d8d8e82471d580d2214b74172a2f231bfde2051c2e98f44cc930e0c72d537f44c90c498119e78a479ab8384d3cebf1e62acbb334ca44d897c82fe92ddec4fa6dabe9b9f81d3503bd0a2ba09d4fc8fc01436ba33cfb94eae30f4dcc15d43a38ae48992a91f75f04872c37345e9b45974de3440d93332806c9e21ec7aa1ff7dfb1048c2001fc3eb5a7da206010dd923072a015d323a618babeba29edb648da43bce21148d9cc3d7cd092c6fb815620e2edcdf150a8027be4fe5943580132c596bcbb8bbda64f9562fd20a28e5056b6ac8a2061b491e04a95133c010b80d463c600bac25efce511a1173cee2d85d53f6e800028b9700255ec08ac19b6de8e7638dd67ba304e81908cc22e5f195d301a0e75fd83842e69521b3b6537f940b3a4d70f5bec8ecc54dd9ab1a489537e5526750c3e79a74d7fcfe7f9897038f3c1088774ce99d659cdc4610ee45489452ea68756b9e72672fe6ba2e87408f2c1763ec1d099ec0c302bc899a09a118f08968b903b0e4a6833e641f282062862d661cbbd3ae11a55c55a1f74e692bbbcbc57cee2ce6182f2d7e1ff353fa480c5d9300e5a48d5a1efac33e62b7712f731c64b39d823031ee1bf74b7d8940d318d7eca8a85ac8d2f312d8011d4e7f8bda057a82a21ea9ef573a15480442b897eb967b0ea128995ebbf3b03fbe83f4e2a6ff9f150ef971a9d16abf0302069fd36dc8b20e7cdfdcb82df07114b5bf5c659229071628f7e5c54b800467150c5c26242bced9b9bf51520b32d5f387e7f94395a281c97801f2de289f42c2e06b0b087eb5e36b26eef94b428d403519e6e79d5dc54dd4c75ed551fa32d0fdba944afde1789c3abc15553d0bb1294f9075ca1695aee82a1ece8b2bcfc7ef7ad96d8ecac688d70ea0635b9bc2294114f0c0afd4829bfe141ce772f4ea8bd343e7c71e0a886a557b58d5a56d8399be3391906377aef9deea143133140fc8b0c5ac362fdcc06d62882f3d9904ec4fec6915f7aa3f14ee8b21c05dc5c77963c60367cc7d2425ba6859a1d12d15f42ea8db49a90748ddc9c4aa557cb6400b90e7936455c4a71ecb32b0a9a76b32614609f3fe4c9c2729ef5da0641357d22ca30514549fa89cbe4d122e3b38963d2c9138cf2be89aeb63d5f72167b4c7683d694d158bb7e814a492cccc37d550f4dd5b2fba219e2de7c032272f042950a33fca99518aad9ae6241a4e3213bedddfb2c888ac9a53e1c34b5335f3c9b7d07797216661755d940c01895f21a5461fef2b07c2184982b45ceec0aadac6c9b61b082f0b42d22a3b0890be5661f1a4ebb1da051ce2e603ac164eafdc11cc563bf55415d19785e60f9ed89632899128c4fb16477cda634835f54d3318b48afdbee6feedddbda7dfe5664b6d7f6c934d9d9069e65d4dc9cefb7b23f37b6df9e188cf6cf3162f27bee2e6a2566be65cc56dbede24f82cdd4572d4aa81d11daee6bd59ab3e11e61362d5b75ab2cecef90ee42c90a28547717b44fb493d6665926d9d289f14a0592f2970bd22499f643552ff4d6182651965cf56575491918f5ef5b7bfdaeeac388144189838e58ca373fd948cdb72d88c4fbae4c59327db5b968d4182bad5b62f5bf600448d218825fd0f232c769bd6e7b9308e96e8f3fac12c898e3d0c4286ad4e519d7720610f390fc4fc9a8c6ff8372b342fb5d15eadb7f9118efcfd5cb660b971c4563b9ae9bb822ce14c0450ec4a9f4cb4375b2b0da31941117d9b61e80c50ee0e76b915d3f60fe4b02b2782af35911cbd62872f67c8f39f9dbad1b3d1c2ee0dd6dfe8046ef096bb4415c09827c96aa0afbbf87407c09bb4f07a19deab3cd3c14eb16839adf57c4ae0bbd68128b7b7cd25429a71516bad3176a5fbe31aef0439a8c05f1c9dc9904dfd89109d6dff34e818b40e3f557b2157b0c738c9d49a33bb2355873d40bcc8f0d2dce0f9b333fa09326b7526923bc10c7073b0f5966bfb1743b40938db65d1aaafc397a835ceb018916a9589190ef1855a7cf64c06410a5a2f9a8257ba5a21c64e64a37682a447429abaccd153938757dce6ca1da86bd147d0e7d65bd889eb81f7ddd5fc7a8fa23d30cc3e8ff15d8d60e241d4316fccc89c566f7d960d1de984c5e5c08a0252b5ac7072900d5ce36f71b11bd7809d7967932936c22c52d6a7d166710a3350be3bbc11b7b17e1e84d87a2736165ec58b9c008b0e7e24b6aeda474e5e95629f8b30ee26581f145a582b4ffb440a3b707684b24ddd6a57d92a3e35d82dd9854291c1d0158e63d48b09cba11389e7ae30d9e10f60dbdb68e7d0bd6bc4a384655908e803b6ad492a9682e9dfae933dc6eedd35d662e8a856beaadf7c3b202e5f50798d4cd792b9aae00b4ccbe86b55d05111f2b110cd5d15b06418f921fc778ca8885dd2fd9ea085372ad9de4f4ef12132a06917b80c1a262b95558b83e9135b0a2a7f0533ab32490689cfe67c326ac624a09d49cd58292b0600e20c22fc80d34c28c04703e6efa0d521da3d6f0371c18e6d2bc91c917e1832c62d1e16e4f3bbd42f1c3c4cf036d01fba1fffaf2e86ef084b92674d5384cf2a2bb3136add2a5e23c09bf0e8aa6fe7fcea0e6c1de27f1b4f165f06e95a696361d19f122c31f78d1cc41179e216866c950f21b4428fd9a7d4cad56af6640f30078fdfec711b097014c8fdf4300215860aab5ac4dea4d8e87bbc8618216e492fe39260ae4db819fb32363697f823d7a12a72035a53c7d55da797f137dd395e440c5c41719be3836d37a51046d0bdc99ee39c21e84ee218ef84e3d49afaf9ea34c9a74c41c814c3cb7559e07d4de12a61edb86d50c3e862e8258dc9dfbc3470472de22ff8bdb749e1991ed5773e847391177c40b3dd08df3fd9b45ab4c978137496158c4a4d816509765c5b9e06832773af5bebe16c7999064128fcc0fc284547d1ec6c8d23b95c00176c5381d7e3e0454d88700e6dc1d64078f88aeea505f4140bae6b5766f185b08734f2e982f8ffadce690546da6ee093affd5696e10309a48e19237b9ef278022cae93f530e35f958ca4f0ec5aff2fa1af3e1da7077e2e31b6ff7040ed59204317feed1c8cca1108cc07c5ecaf28c514f2d8c4f66589f93a716a556e976fce7a1ad17e24faa25186e74cbfb82d7903a6d56af9d1796f676c794921993392cbe82732d8bb29e44f8255a164e490c1807179fde06bdb64b088d043c5ddba47432a420651529f3a256ed3ba89a1bad02ca725ce59d48025ed77c050da58d6f85c7cdba68eff5d0f7011e5daba536019260617e61ccff7590879689431ea9cfc77d01da60383df9273dc89262c203995f7004d3bd1396d0de2c47bc632b1f2d0eceb2f05c454d43e5f13803c7cb351cde797e28c93f139af483e3b66bda579d0d8b25b874ba9b63cc19d24fbe83b0ea450845e0ef6dfef1372f1b40efcf2ebf913decaba6f7beee5f00e85c68abf3ebf0d4279c086abe4b83352492fe2e855203cff3a9a0cd84c6987cba479bb7f055e88eb471ca23ab429fa2c42c84609ee53ddcaf36388e9a98d5feb3676e9d7a5f01a0df5c54e2af6f7545ddb05865410580c0a5528835f771a0e15ec349561a98184091b830f352c276b2cf46d1b870dd5d3c57c6c78eaed7ba7356a68e888b8ec4e428455b1274a0ab707e1eb7d39d319ea3de66aa0fc387e840dc4dbe716155e17762cac91fc49105538e0dac6db72cdc20f09fc750f72b5571d1ac4deeb718518b9d0fdaca25c521b45d77629764d0efa07ff16b5059dde9ce3d0c51b6c617461508195d2b3f69f516d082d51cd3f07413627a799f9e2fc2381a12e09d5f1f6d795bd8a25310e3acacd4acae8bef22b9e0a1566344053c9b61b3cae0e7f0138dec7a6deccde0b0d5ad98ce71f23acbfd85e506330fc826bcdf3da3121d05abec2e7ebdf94133cf94f3480baa3096217ddbc682fa44b23ee51f0af7bc430cd7218179649a8162da7f15495c3327b2ad335a14dec047b70858d0f1354cd65827c5ddd894632fa2cfd8e7bac09069989877d36ea02593863bcf766dc59f668ead36503c35b5542a657849a91c3a8d73a9adea532d41dfb8fcf4797e08fe1daf07c25e36c81aa9c9bfc4ad29e942a701bfbbbed9db52d766c3a75200499d61f0e33f9fae18f41d72840fdd967a0d41e65e11918693da0e78a0b5bbeef70127e26ac808754c8ad26406efd4d148a2540f39b755fab1c2c9993847529413eb6c26cba5ab7c2890766f7f88af281d9498fd9c7235f718544434ce17186369f6084dbdb3349107d515b6d517dbab9637cf9bd2458bb64c8073e8137f339ee48a02f87d5ae7890b489b611ce618a77dbc68367add73c4c65b05ec8ff201b35e3baee45955ac86b4c02cf74245ce689bd4cb4b6731a1c7956934e15594cec8f03b007f95d861129728fba46f0b7c09ac708d86de297bd766a8c3fc66afceac55948c3080390ea

private def light (n : ℕ) : Bool :=
  if n≤175 then decide n.Prime else n.gcd 1124449491085736328304109938642204255210926338928074644824004638489082006275333290972493383366025810760784721148670387931016867466241864043097971934380608571667663656813479380532220559625623957805983663469624056384461365161184611811666936997356618263665919666081369067104501760000000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤30822) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 175 = 1124449491085736328304109938642204255210926338928074644824004638489082006275333290972493383366025810760784721148670387931016867466241864043097971934380608571667663656813479380532220559625623957805983663469624056384461365161184611811666936997356618263665919666081369067104501760000000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 175 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤30822 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 60 := by unfold smallValid; decide +kernel

private theorem sp60 : smallValid 60 60 := by unfold smallValid; decide +kernel

private theorem sp120 : smallValid 120 60 := by unfold smallValid; decide +kernel

private theorem sp180 : smallValid 180 60 := by unfold smallValid; decide +kernel

private theorem sp240 : smallValid 240 60 := by unfold smallValid; decide +kernel

private theorem sp300 : smallValid 300 60 := by unfold smallValid; decide +kernel

private theorem sp360 : smallValid 360 60 := by unfold smallValid; decide +kernel

private theorem sp420 : smallValid 420 61 := by unfold smallValid; decide +kernel

private theorem sp481 : smallValid 481 60 := by unfold smallValid; decide +kernel

private theorem sp541 : smallValid 541 60 := by unfold smallValid; decide +kernel

private theorem sp601 : smallValid 601 60 := by unfold smallValid; decide +kernel

private theorem sp661 : smallValid 661 61 := by unfold smallValid; decide +kernel

private theorem sp722 : smallValid 722 60 := by unfold smallValid; decide +kernel

private theorem sp782 : smallValid 782 60 := by unfold smallValid; decide +kernel

private theorem sp842 : smallValid 842 60 := by unfold smallValid; decide +kernel

private theorem sp902 : smallValid 902 61 := by unfold smallValid; decide +kernel

private theorem sp963 : smallValid 963 60 := by unfold smallValid; decide +kernel

private theorem sp1023 : smallValid 1023 60 := by unfold smallValid; decide +kernel

private theorem sp1083 : smallValid 1083 60 := by unfold smallValid; decide +kernel

private theorem sp1143 : smallValid 1143 60 := by unfold smallValid; decide +kernel

private theorem sp1203 : smallValid 1203 60 := by unfold smallValid; decide +kernel

private theorem sp1263 : smallValid 1263 60 := by unfold smallValid; decide +kernel

private theorem sp1323 : smallValid 1323 60 := by unfold smallValid; decide +kernel

private theorem sp1383 : smallValid 1383 61 := by unfold smallValid; decide +kernel

private theorem sp1444 : smallValid 1444 60 := by unfold smallValid; decide +kernel

private theorem sp1504 : smallValid 1504 60 := by unfold smallValid; decide +kernel

private theorem sp1564 : smallValid 1564 60 := by unfold smallValid; decide +kernel

private theorem sp1624 : smallValid 1624 61 := by unfold smallValid; decide +kernel

private theorem sp1685 : smallValid 1685 60 := by unfold smallValid; decide +kernel

private theorem sp1745 : smallValid 1745 60 := by unfold smallValid; decide +kernel

private theorem sp1805 : smallValid 1805 60 := by unfold smallValid; decide +kernel

private theorem sp1865 : smallValid 1865 61 := by unfold smallValid; decide +kernel

private theorem sp1926 : smallValid 1926 60 := by unfold smallValid; decide +kernel

private theorem sp1986 : smallValid 1986 60 := by unfold smallValid; decide +kernel

private theorem sp2046 : smallValid 2046 60 := by unfold smallValid; decide +kernel

private theorem sp2106 : smallValid 2106 60 := by unfold smallValid; decide +kernel

private theorem sp2166 : smallValid 2166 60 := by unfold smallValid; decide +kernel

private theorem sp2226 : smallValid 2226 60 := by unfold smallValid; decide +kernel

private theorem sp2286 : smallValid 2286 60 := by unfold smallValid; decide +kernel

private theorem sp2346 : smallValid 2346 61 := by unfold smallValid; decide +kernel

private theorem sp2407 : smallValid 2407 60 := by unfold smallValid; decide +kernel

private theorem sp2467 : smallValid 2467 60 := by unfold smallValid; decide +kernel

private theorem sp2527 : smallValid 2527 60 := by unfold smallValid; decide +kernel

private theorem sp2587 : smallValid 2587 61 := by unfold smallValid; decide +kernel

private theorem sp2648 : smallValid 2648 60 := by unfold smallValid; decide +kernel

private theorem sp2708 : smallValid 2708 60 := by unfold smallValid; decide +kernel

private theorem sp2768 : smallValid 2768 60 := by unfold smallValid; decide +kernel

private theorem sp2828 : smallValid 2828 61 := by unfold smallValid; decide +kernel

private theorem sp2889 : smallValid 2889 60 := by unfold smallValid; decide +kernel

private theorem sp2949 : smallValid 2949 60 := by unfold smallValid; decide +kernel

private theorem sp3009 : smallValid 3009 60 := by unfold smallValid; decide +kernel

private theorem sp3069 : smallValid 3069 60 := by unfold smallValid; decide +kernel

private theorem sp3129 : smallValid 3129 60 := by unfold smallValid; decide +kernel

private theorem sp3189 : smallValid 3189 60 := by unfold smallValid; decide +kernel

private theorem sp3249 : smallValid 3249 60 := by unfold smallValid; decide +kernel

private theorem sp3309 : smallValid 3309 61 := by unfold smallValid; decide +kernel

private theorem sp3370 : smallValid 3370 60 := by unfold smallValid; decide +kernel

private theorem sp3430 : smallValid 3430 60 := by unfold smallValid; decide +kernel

private theorem sp3490 : smallValid 3490 60 := by unfold smallValid; decide +kernel

private theorem sp3550 : smallValid 3550 61 := by unfold smallValid; decide +kernel

private theorem sp3611 : smallValid 3611 60 := by unfold smallValid; decide +kernel

private theorem sp3671 : smallValid 3671 60 := by unfold smallValid; decide +kernel

private theorem sp3731 : smallValid 3731 60 := by unfold smallValid; decide +kernel

private theorem sp3791 : smallValid 3791 61 := by unfold smallValid; decide +kernel

private theorem sp3852 : smallValid 3852 60 := by unfold smallValid; decide +kernel

private theorem sp3912 : smallValid 3912 60 := by unfold smallValid; decide +kernel

private theorem sp3972 : smallValid 3972 60 := by unfold smallValid; decide +kernel

private theorem sp4032 : smallValid 4032 60 := by unfold smallValid; decide +kernel

private theorem sp4092 : smallValid 4092 60 := by unfold smallValid; decide +kernel

private theorem sp4152 : smallValid 4152 60 := by unfold smallValid; decide +kernel

private theorem sp4212 : smallValid 4212 60 := by unfold smallValid; decide +kernel

private theorem sp4272 : smallValid 4272 61 := by unfold smallValid; decide +kernel

private theorem sp4333 : smallValid 4333 60 := by unfold smallValid; decide +kernel

private theorem sp4393 : smallValid 4393 60 := by unfold smallValid; decide +kernel

private theorem sp4453 : smallValid 4453 60 := by unfold smallValid; decide +kernel

private theorem sp4513 : smallValid 4513 61 := by unfold smallValid; decide +kernel

private theorem sp4574 : smallValid 4574 60 := by unfold smallValid; decide +kernel

private theorem sp4634 : smallValid 4634 60 := by unfold smallValid; decide +kernel

private theorem sp4694 : smallValid 4694 60 := by unfold smallValid; decide +kernel

private theorem sp4754 : smallValid 4754 61 := by unfold smallValid; decide +kernel

private theorem sp4815 : smallValid 4815 60 := by unfold smallValid; decide +kernel

private theorem sp4875 : smallValid 4875 60 := by unfold smallValid; decide +kernel

private theorem sp4935 : smallValid 4935 60 := by unfold smallValid; decide +kernel

private theorem sp4995 : smallValid 4995 60 := by unfold smallValid; decide +kernel

private theorem sp5055 : smallValid 5055 60 := by unfold smallValid; decide +kernel

private theorem sp5115 : smallValid 5115 60 := by unfold smallValid; decide +kernel

private theorem sp5175 : smallValid 5175 60 := by unfold smallValid; decide +kernel

private theorem sp5235 : smallValid 5235 61 := by unfold smallValid; decide +kernel

private theorem sp5296 : smallValid 5296 60 := by unfold smallValid; decide +kernel

private theorem sp5356 : smallValid 5356 60 := by unfold smallValid; decide +kernel

private theorem sp5416 : smallValid 5416 60 := by unfold smallValid; decide +kernel

private theorem sp5476 : smallValid 5476 61 := by unfold smallValid; decide +kernel

private theorem sp5537 : smallValid 5537 60 := by unfold smallValid; decide +kernel

private theorem sp5597 : smallValid 5597 60 := by unfold smallValid; decide +kernel

private theorem sp5657 : smallValid 5657 60 := by unfold smallValid; decide +kernel

private theorem sp5717 : smallValid 5717 61 := by unfold smallValid; decide +kernel

private theorem sp5778 : smallValid 5778 60 := by unfold smallValid; decide +kernel

private theorem sp5838 : smallValid 5838 60 := by unfold smallValid; decide +kernel

private theorem sp5898 : smallValid 5898 60 := by unfold smallValid; decide +kernel

private theorem sp5958 : smallValid 5958 60 := by unfold smallValid; decide +kernel

private theorem sp6018 : smallValid 6018 60 := by unfold smallValid; decide +kernel

private theorem sp6078 : smallValid 6078 60 := by unfold smallValid; decide +kernel

private theorem sp6138 : smallValid 6138 60 := by unfold smallValid; decide +kernel

private theorem sp6198 : smallValid 6198 61 := by unfold smallValid; decide +kernel

private theorem sp6259 : smallValid 6259 60 := by unfold smallValid; decide +kernel

private theorem sp6319 : smallValid 6319 60 := by unfold smallValid; decide +kernel

private theorem sp6379 : smallValid 6379 60 := by unfold smallValid; decide +kernel

private theorem sp6439 : smallValid 6439 61 := by unfold smallValid; decide +kernel

private theorem sp6500 : smallValid 6500 60 := by unfold smallValid; decide +kernel

private theorem sp6560 : smallValid 6560 60 := by unfold smallValid; decide +kernel

private theorem sp6620 : smallValid 6620 60 := by unfold smallValid; decide +kernel

private theorem sp6680 : smallValid 6680 61 := by unfold smallValid; decide +kernel

private theorem sp6741 : smallValid 6741 60 := by unfold smallValid; decide +kernel

private theorem sp6801 : smallValid 6801 60 := by unfold smallValid; decide +kernel

private theorem sp6861 : smallValid 6861 60 := by unfold smallValid; decide +kernel

private theorem sp6921 : smallValid 6921 61 := by unfold smallValid; decide +kernel

private theorem sp6982 : smallValid 6982 60 := by unfold smallValid; decide +kernel

private theorem sp7042 : smallValid 7042 60 := by unfold smallValid; decide +kernel

private theorem sp7102 : smallValid 7102 60 := by unfold smallValid; decide +kernel

private theorem sp7162 : smallValid 7162 61 := by unfold smallValid; decide +kernel

private theorem sp7223 : smallValid 7223 60 := by unfold smallValid; decide +kernel

private theorem sp7283 : smallValid 7283 60 := by unfold smallValid; decide +kernel

private theorem sp7343 : smallValid 7343 60 := by unfold smallValid; decide +kernel

private theorem sp7403 : smallValid 7403 61 := by unfold smallValid; decide +kernel

private theorem sp7464 : smallValid 7464 60 := by unfold smallValid; decide +kernel

private theorem sp7524 : smallValid 7524 60 := by unfold smallValid; decide +kernel

private theorem sp7584 : smallValid 7584 60 := by unfold smallValid; decide +kernel

private theorem sp7644 : smallValid 7644 61 := by unfold smallValid; decide +kernel

private theorem sp7705 : smallValid 7705 60 := by unfold smallValid; decide +kernel

private theorem sp7765 : smallValid 7765 60 := by unfold smallValid; decide +kernel

private theorem sp7825 : smallValid 7825 60 := by unfold smallValid; decide +kernel

private theorem sp7885 : smallValid 7885 60 := by unfold smallValid; decide +kernel

private theorem sp7945 : smallValid 7945 60 := by unfold smallValid; decide +kernel

private theorem sp8005 : smallValid 8005 60 := by unfold smallValid; decide +kernel

private theorem sp8065 : smallValid 8065 60 := by unfold smallValid; decide +kernel

private theorem sp8125 : smallValid 8125 61 := by unfold smallValid; decide +kernel

private theorem sp8186 : smallValid 8186 60 := by unfold smallValid; decide +kernel

private theorem sp8246 : smallValid 8246 60 := by unfold smallValid; decide +kernel

private theorem sp8306 : smallValid 8306 60 := by unfold smallValid; decide +kernel

private theorem sp8366 : smallValid 8366 61 := by unfold smallValid; decide +kernel

private theorem sp8427 : smallValid 8427 60 := by unfold smallValid; decide +kernel

private theorem sp8487 : smallValid 8487 60 := by unfold smallValid; decide +kernel

private theorem sp8547 : smallValid 8547 60 := by unfold smallValid; decide +kernel

private theorem sp8607 : smallValid 8607 61 := by unfold smallValid; decide +kernel

private theorem sp8668 : smallValid 8668 60 := by unfold smallValid; decide +kernel

private theorem sp8728 : smallValid 8728 60 := by unfold smallValid; decide +kernel

private theorem sp8788 : smallValid 8788 60 := by unfold smallValid; decide +kernel

private theorem sp8848 : smallValid 8848 60 := by unfold smallValid; decide +kernel

private theorem sp8908 : smallValid 8908 60 := by unfold smallValid; decide +kernel

private theorem sp8968 : smallValid 8968 60 := by unfold smallValid; decide +kernel

private theorem sp9028 : smallValid 9028 60 := by unfold smallValid; decide +kernel

private theorem sp9088 : smallValid 9088 61 := by unfold smallValid; decide +kernel

private theorem sp9149 : smallValid 9149 60 := by unfold smallValid; decide +kernel

private theorem sp9209 : smallValid 9209 60 := by unfold smallValid; decide +kernel

private theorem sp9269 : smallValid 9269 60 := by unfold smallValid; decide +kernel

private theorem sp9329 : smallValid 9329 61 := by unfold smallValid; decide +kernel

private theorem sp9390 : smallValid 9390 60 := by unfold smallValid; decide +kernel

private theorem sp9450 : smallValid 9450 60 := by unfold smallValid; decide +kernel

private theorem sp9510 : smallValid 9510 60 := by unfold smallValid; decide +kernel

private theorem sp9570 : smallValid 9570 61 := by unfold smallValid; decide +kernel

private theorem sp9631 : smallValid 9631 60 := by unfold smallValid; decide +kernel

private theorem sp9691 : smallValid 9691 60 := by unfold smallValid; decide +kernel

private theorem sp9751 : smallValid 9751 60 := by unfold smallValid; decide +kernel

private theorem sp9811 : smallValid 9811 60 := by unfold smallValid; decide +kernel

private theorem sp9871 : smallValid 9871 60 := by unfold smallValid; decide +kernel

private theorem sp9931 : smallValid 9931 60 := by unfold smallValid; decide +kernel

private theorem sp9991 : smallValid 9991 60 := by unfold smallValid; decide +kernel

private theorem sp10051 : smallValid 10051 61 := by unfold smallValid; decide +kernel

private theorem sp10112 : smallValid 10112 60 := by unfold smallValid; decide +kernel

private theorem sp10172 : smallValid 10172 60 := by unfold smallValid; decide +kernel

private theorem sp10232 : smallValid 10232 60 := by unfold smallValid; decide +kernel

private theorem sp10292 : smallValid 10292 61 := by unfold smallValid; decide +kernel

private theorem sp10353 : smallValid 10353 60 := by unfold smallValid; decide +kernel

private theorem sp10413 : smallValid 10413 60 := by unfold smallValid; decide +kernel

private theorem sp10473 : smallValid 10473 60 := by unfold smallValid; decide +kernel

private theorem sp10533 : smallValid 10533 61 := by unfold smallValid; decide +kernel

private theorem sp10594 : smallValid 10594 60 := by unfold smallValid; decide +kernel

private theorem sp10654 : smallValid 10654 60 := by unfold smallValid; decide +kernel

private theorem sp10714 : smallValid 10714 60 := by unfold smallValid; decide +kernel

private theorem sp10774 : smallValid 10774 61 := by unfold smallValid; decide +kernel

private theorem sp10835 : smallValid 10835 60 := by unfold smallValid; decide +kernel

private theorem sp10895 : smallValid 10895 60 := by unfold smallValid; decide +kernel

private theorem sp10955 : smallValid 10955 60 := by unfold smallValid; decide +kernel

private theorem sp11015 : smallValid 11015 61 := by unfold smallValid; decide +kernel

private theorem sp11076 : smallValid 11076 60 := by unfold smallValid; decide +kernel

private theorem sp11136 : smallValid 11136 60 := by unfold smallValid; decide +kernel

private theorem sp11196 : smallValid 11196 60 := by unfold smallValid; decide +kernel

private theorem sp11256 : smallValid 11256 61 := by unfold smallValid; decide +kernel

private theorem sp11317 : smallValid 11317 60 := by unfold smallValid; decide +kernel

private theorem sp11377 : smallValid 11377 60 := by unfold smallValid; decide +kernel

private theorem sp11437 : smallValid 11437 60 := by unfold smallValid; decide +kernel

private theorem sp11497 : smallValid 11497 61 := by unfold smallValid; decide +kernel

private theorem sp11558 : smallValid 11558 60 := by unfold smallValid; decide +kernel

private theorem sp11618 : smallValid 11618 60 := by unfold smallValid; decide +kernel

private theorem sp11678 : smallValid 11678 60 := by unfold smallValid; decide +kernel

private theorem sp11738 : smallValid 11738 60 := by unfold smallValid; decide +kernel

private theorem sp11798 : smallValid 11798 60 := by unfold smallValid; decide +kernel

private theorem sp11858 : smallValid 11858 60 := by unfold smallValid; decide +kernel

private theorem sp11918 : smallValid 11918 60 := by unfold smallValid; decide +kernel

private theorem sp11978 : smallValid 11978 61 := by unfold smallValid; decide +kernel

private theorem sp12039 : smallValid 12039 60 := by unfold smallValid; decide +kernel

private theorem sp12099 : smallValid 12099 60 := by unfold smallValid; decide +kernel

private theorem sp12159 : smallValid 12159 60 := by unfold smallValid; decide +kernel

private theorem sp12219 : smallValid 12219 61 := by unfold smallValid; decide +kernel

private theorem sp12280 : smallValid 12280 60 := by unfold smallValid; decide +kernel

private theorem sp12340 : smallValid 12340 60 := by unfold smallValid; decide +kernel

private theorem sp12400 : smallValid 12400 60 := by unfold smallValid; decide +kernel

private theorem sp12460 : smallValid 12460 61 := by unfold smallValid; decide +kernel

private theorem sp12521 : smallValid 12521 60 := by unfold smallValid; decide +kernel

private theorem sp12581 : smallValid 12581 60 := by unfold smallValid; decide +kernel

private theorem sp12641 : smallValid 12641 60 := by unfold smallValid; decide +kernel

private theorem sp12701 : smallValid 12701 60 := by unfold smallValid; decide +kernel

private theorem sp12761 : smallValid 12761 60 := by unfold smallValid; decide +kernel

private theorem sp12821 : smallValid 12821 60 := by unfold smallValid; decide +kernel

private theorem sp12881 : smallValid 12881 60 := by unfold smallValid; decide +kernel

private theorem sp12941 : smallValid 12941 61 := by unfold smallValid; decide +kernel

private theorem sp13002 : smallValid 13002 60 := by unfold smallValid; decide +kernel

private theorem sp13062 : smallValid 13062 60 := by unfold smallValid; decide +kernel

private theorem sp13122 : smallValid 13122 60 := by unfold smallValid; decide +kernel

private theorem sp13182 : smallValid 13182 61 := by unfold smallValid; decide +kernel

private theorem sp13243 : smallValid 13243 60 := by unfold smallValid; decide +kernel

private theorem sp13303 : smallValid 13303 60 := by unfold smallValid; decide +kernel

private theorem sp13363 : smallValid 13363 60 := by unfold smallValid; decide +kernel

private theorem sp13423 : smallValid 13423 61 := by unfold smallValid; decide +kernel

private theorem sp13484 : smallValid 13484 60 := by unfold smallValid; decide +kernel

private theorem sp13544 : smallValid 13544 60 := by unfold smallValid; decide +kernel

private theorem sp13604 : smallValid 13604 60 := by unfold smallValid; decide +kernel

private theorem sp13664 : smallValid 13664 60 := by unfold smallValid; decide +kernel

private theorem sp13724 : smallValid 13724 60 := by unfold smallValid; decide +kernel

private theorem sp13784 : smallValid 13784 60 := by unfold smallValid; decide +kernel

private theorem sp13844 : smallValid 13844 60 := by unfold smallValid; decide +kernel

private theorem sp13904 : smallValid 13904 61 := by unfold smallValid; decide +kernel

private theorem sp13965 : smallValid 13965 60 := by unfold smallValid; decide +kernel

private theorem sp14025 : smallValid 14025 60 := by unfold smallValid; decide +kernel

private theorem sp14085 : smallValid 14085 60 := by unfold smallValid; decide +kernel

private theorem sp14145 : smallValid 14145 61 := by unfold smallValid; decide +kernel

private theorem sp14206 : smallValid 14206 60 := by unfold smallValid; decide +kernel

private theorem sp14266 : smallValid 14266 60 := by unfold smallValid; decide +kernel

private theorem sp14326 : smallValid 14326 60 := by unfold smallValid; decide +kernel

private theorem sp14386 : smallValid 14386 61 := by unfold smallValid; decide +kernel

private theorem sp14447 : smallValid 14447 60 := by unfold smallValid; decide +kernel

private theorem sp14507 : smallValid 14507 60 := by unfold smallValid; decide +kernel

private theorem sp14567 : smallValid 14567 60 := by unfold smallValid; decide +kernel

private theorem sp14627 : smallValid 14627 61 := by unfold smallValid; decide +kernel

private theorem sp14688 : smallValid 14688 60 := by unfold smallValid; decide +kernel

private theorem sp14748 : smallValid 14748 60 := by unfold smallValid; decide +kernel

private theorem sp14808 : smallValid 14808 60 := by unfold smallValid; decide +kernel

private theorem sp14868 : smallValid 14868 61 := by unfold smallValid; decide +kernel

private theorem sp14929 : smallValid 14929 60 := by unfold smallValid; decide +kernel

private theorem sp14989 : smallValid 14989 60 := by unfold smallValid; decide +kernel

private theorem sp15049 : smallValid 15049 60 := by unfold smallValid; decide +kernel

private theorem sp15109 : smallValid 15109 61 := by unfold smallValid; decide +kernel

private theorem sp15170 : smallValid 15170 60 := by unfold smallValid; decide +kernel

private theorem sp15230 : smallValid 15230 60 := by unfold smallValid; decide +kernel

private theorem sp15290 : smallValid 15290 60 := by unfold smallValid; decide +kernel

private theorem sp15350 : smallValid 15350 61 := by unfold smallValid; decide +kernel

private theorem sp15411 : smallValid 15411 60 := by unfold smallValid; decide +kernel

private theorem sp15471 : smallValid 15471 60 := by unfold smallValid; decide +kernel

private theorem sp15531 : smallValid 15531 60 := by unfold smallValid; decide +kernel

private theorem sp15591 : smallValid 15591 60 := by unfold smallValid; decide +kernel

private theorem sp15651 : smallValid 15651 60 := by unfold smallValid; decide +kernel

private theorem sp15711 : smallValid 15711 60 := by unfold smallValid; decide +kernel

private theorem sp15771 : smallValid 15771 60 := by unfold smallValid; decide +kernel

private theorem sp15831 : smallValid 15831 61 := by unfold smallValid; decide +kernel

private theorem sp15892 : smallValid 15892 60 := by unfold smallValid; decide +kernel

private theorem sp15952 : smallValid 15952 60 := by unfold smallValid; decide +kernel

private theorem sp16012 : smallValid 16012 60 := by unfold smallValid; decide +kernel

private theorem sp16072 : smallValid 16072 61 := by unfold smallValid; decide +kernel

private theorem sp16133 : smallValid 16133 60 := by unfold smallValid; decide +kernel

private theorem sp16193 : smallValid 16193 60 := by unfold smallValid; decide +kernel

private theorem sp16253 : smallValid 16253 60 := by unfold smallValid; decide +kernel

private theorem sp16313 : smallValid 16313 61 := by unfold smallValid; decide +kernel

private theorem sp16374 : smallValid 16374 60 := by unfold smallValid; decide +kernel

private theorem sp16434 : smallValid 16434 60 := by unfold smallValid; decide +kernel

private theorem sp16494 : smallValid 16494 60 := by unfold smallValid; decide +kernel

private theorem sp16554 : smallValid 16554 60 := by unfold smallValid; decide +kernel

private theorem sp16614 : smallValid 16614 60 := by unfold smallValid; decide +kernel

private theorem sp16674 : smallValid 16674 60 := by unfold smallValid; decide +kernel

private theorem sp16734 : smallValid 16734 60 := by unfold smallValid; decide +kernel

private theorem sp16794 : smallValid 16794 61 := by unfold smallValid; decide +kernel

private theorem sp16855 : smallValid 16855 60 := by unfold smallValid; decide +kernel

private theorem sp16915 : smallValid 16915 60 := by unfold smallValid; decide +kernel

private theorem sp16975 : smallValid 16975 60 := by unfold smallValid; decide +kernel

private theorem sp17035 : smallValid 17035 61 := by unfold smallValid; decide +kernel

private theorem sp17096 : smallValid 17096 60 := by unfold smallValid; decide +kernel

private theorem sp17156 : smallValid 17156 60 := by unfold smallValid; decide +kernel

private theorem sp17216 : smallValid 17216 60 := by unfold smallValid; decide +kernel

private theorem sp17276 : smallValid 17276 61 := by unfold smallValid; decide +kernel

private theorem sp17337 : smallValid 17337 60 := by unfold smallValid; decide +kernel

private theorem sp17397 : smallValid 17397 60 := by unfold smallValid; decide +kernel

private theorem sp17457 : smallValid 17457 60 := by unfold smallValid; decide +kernel

private theorem sp17517 : smallValid 17517 60 := by unfold smallValid; decide +kernel

private theorem sp17577 : smallValid 17577 60 := by unfold smallValid; decide +kernel

private theorem sp17637 : smallValid 17637 60 := by unfold smallValid; decide +kernel

private theorem sp17697 : smallValid 17697 60 := by unfold smallValid; decide +kernel

private theorem sp17757 : smallValid 17757 61 := by unfold smallValid; decide +kernel

private theorem sp17818 : smallValid 17818 60 := by unfold smallValid; decide +kernel

private theorem sp17878 : smallValid 17878 60 := by unfold smallValid; decide +kernel

private theorem sp17938 : smallValid 17938 60 := by unfold smallValid; decide +kernel

private theorem sp17998 : smallValid 17998 61 := by unfold smallValid; decide +kernel

private theorem sp18059 : smallValid 18059 60 := by unfold smallValid; decide +kernel

private theorem sp18119 : smallValid 18119 60 := by unfold smallValid; decide +kernel

private theorem sp18179 : smallValid 18179 60 := by unfold smallValid; decide +kernel

private theorem sp18239 : smallValid 18239 61 := by unfold smallValid; decide +kernel

private theorem sp18300 : smallValid 18300 60 := by unfold smallValid; decide +kernel

private theorem sp18360 : smallValid 18360 60 := by unfold smallValid; decide +kernel

private theorem sp18420 : smallValid 18420 60 := by unfold smallValid; decide +kernel

private theorem sp18480 : smallValid 18480 61 := by unfold smallValid; decide +kernel

private theorem sp18541 : smallValid 18541 60 := by unfold smallValid; decide +kernel

private theorem sp18601 : smallValid 18601 60 := by unfold smallValid; decide +kernel

private theorem sp18661 : smallValid 18661 60 := by unfold smallValid; decide +kernel

private theorem sp18721 : smallValid 18721 61 := by unfold smallValid; decide +kernel

private theorem sp18782 : smallValid 18782 60 := by unfold smallValid; decide +kernel

private theorem sp18842 : smallValid 18842 60 := by unfold smallValid; decide +kernel

private theorem sp18902 : smallValid 18902 60 := by unfold smallValid; decide +kernel

private theorem sp18962 : smallValid 18962 61 := by unfold smallValid; decide +kernel

private theorem sp19023 : smallValid 19023 60 := by unfold smallValid; decide +kernel

private theorem sp19083 : smallValid 19083 60 := by unfold smallValid; decide +kernel

private theorem sp19143 : smallValid 19143 60 := by unfold smallValid; decide +kernel

private theorem sp19203 : smallValid 19203 61 := by unfold smallValid; decide +kernel

private theorem sp19264 : smallValid 19264 60 := by unfold smallValid; decide +kernel

private theorem sp19324 : smallValid 19324 60 := by unfold smallValid; decide +kernel

private theorem sp19384 : smallValid 19384 60 := by unfold smallValid; decide +kernel

private theorem sp19444 : smallValid 19444 60 := by unfold smallValid; decide +kernel

private theorem sp19504 : smallValid 19504 60 := by unfold smallValid; decide +kernel

private theorem sp19564 : smallValid 19564 60 := by unfold smallValid; decide +kernel

private theorem sp19624 : smallValid 19624 60 := by unfold smallValid; decide +kernel

private theorem sp19684 : smallValid 19684 61 := by unfold smallValid; decide +kernel

private theorem sp19745 : smallValid 19745 60 := by unfold smallValid; decide +kernel

private theorem sp19805 : smallValid 19805 60 := by unfold smallValid; decide +kernel

private theorem sp19865 : smallValid 19865 60 := by unfold smallValid; decide +kernel

private theorem sp19925 : smallValid 19925 61 := by unfold smallValid; decide +kernel

private theorem sp19986 : smallValid 19986 60 := by unfold smallValid; decide +kernel

private theorem sp20046 : smallValid 20046 60 := by unfold smallValid; decide +kernel

private theorem sp20106 : smallValid 20106 60 := by unfold smallValid; decide +kernel

private theorem sp20166 : smallValid 20166 61 := by unfold smallValid; decide +kernel

private theorem sp20227 : smallValid 20227 60 := by unfold smallValid; decide +kernel

private theorem sp20287 : smallValid 20287 60 := by unfold smallValid; decide +kernel

private theorem sp20347 : smallValid 20347 60 := by unfold smallValid; decide +kernel

private theorem sp20407 : smallValid 20407 60 := by unfold smallValid; decide +kernel

private theorem sp20467 : smallValid 20467 60 := by unfold smallValid; decide +kernel

private theorem sp20527 : smallValid 20527 60 := by unfold smallValid; decide +kernel

private theorem sp20587 : smallValid 20587 60 := by unfold smallValid; decide +kernel

private theorem sp20647 : smallValid 20647 61 := by unfold smallValid; decide +kernel

private theorem sp20708 : smallValid 20708 60 := by unfold smallValid; decide +kernel

private theorem sp20768 : smallValid 20768 60 := by unfold smallValid; decide +kernel

private theorem sp20828 : smallValid 20828 60 := by unfold smallValid; decide +kernel

private theorem sp20888 : smallValid 20888 61 := by unfold smallValid; decide +kernel

private theorem sp20949 : smallValid 20949 60 := by unfold smallValid; decide +kernel

private theorem sp21009 : smallValid 21009 60 := by unfold smallValid; decide +kernel

private theorem sp21069 : smallValid 21069 60 := by unfold smallValid; decide +kernel

private theorem sp21129 : smallValid 21129 61 := by unfold smallValid; decide +kernel

private theorem sp21190 : smallValid 21190 60 := by unfold smallValid; decide +kernel

private theorem sp21250 : smallValid 21250 60 := by unfold smallValid; decide +kernel

private theorem sp21310 : smallValid 21310 60 := by unfold smallValid; decide +kernel

private theorem sp21370 : smallValid 21370 60 := by unfold smallValid; decide +kernel

private theorem sp21430 : smallValid 21430 60 := by unfold smallValid; decide +kernel

private theorem sp21490 : smallValid 21490 60 := by unfold smallValid; decide +kernel

private theorem sp21550 : smallValid 21550 60 := by unfold smallValid; decide +kernel

private theorem sp21610 : smallValid 21610 61 := by unfold smallValid; decide +kernel

private theorem sp21671 : smallValid 21671 60 := by unfold smallValid; decide +kernel

private theorem sp21731 : smallValid 21731 60 := by unfold smallValid; decide +kernel

private theorem sp21791 : smallValid 21791 60 := by unfold smallValid; decide +kernel

private theorem sp21851 : smallValid 21851 61 := by unfold smallValid; decide +kernel

private theorem sp21912 : smallValid 21912 60 := by unfold smallValid; decide +kernel

private theorem sp21972 : smallValid 21972 60 := by unfold smallValid; decide +kernel

private theorem sp22032 : smallValid 22032 60 := by unfold smallValid; decide +kernel

private theorem sp22092 : smallValid 22092 61 := by unfold smallValid; decide +kernel

private theorem sp22153 : smallValid 22153 60 := by unfold smallValid; decide +kernel

private theorem sp22213 : smallValid 22213 60 := by unfold smallValid; decide +kernel

private theorem sp22273 : smallValid 22273 60 := by unfold smallValid; decide +kernel

private theorem sp22333 : smallValid 22333 61 := by unfold smallValid; decide +kernel

private theorem sp22394 : smallValid 22394 60 := by unfold smallValid; decide +kernel

private theorem sp22454 : smallValid 22454 60 := by unfold smallValid; decide +kernel

private theorem sp22514 : smallValid 22514 60 := by unfold smallValid; decide +kernel

private theorem sp22574 : smallValid 22574 61 := by unfold smallValid; decide +kernel

private theorem sp22635 : smallValid 22635 60 := by unfold smallValid; decide +kernel

private theorem sp22695 : smallValid 22695 60 := by unfold smallValid; decide +kernel

private theorem sp22755 : smallValid 22755 60 := by unfold smallValid; decide +kernel

private theorem sp22815 : smallValid 22815 61 := by unfold smallValid; decide +kernel

private theorem sp22876 : smallValid 22876 60 := by unfold smallValid; decide +kernel

private theorem sp22936 : smallValid 22936 60 := by unfold smallValid; decide +kernel

private theorem sp22996 : smallValid 22996 60 := by unfold smallValid; decide +kernel

private theorem sp23056 : smallValid 23056 61 := by unfold smallValid; decide +kernel

private theorem sp23117 : smallValid 23117 60 := by unfold smallValid; decide +kernel

private theorem sp23177 : smallValid 23177 60 := by unfold smallValid; decide +kernel

private theorem sp23237 : smallValid 23237 60 := by unfold smallValid; decide +kernel

private theorem sp23297 : smallValid 23297 60 := by unfold smallValid; decide +kernel

private theorem sp23357 : smallValid 23357 60 := by unfold smallValid; decide +kernel

private theorem sp23417 : smallValid 23417 60 := by unfold smallValid; decide +kernel

private theorem sp23477 : smallValid 23477 60 := by unfold smallValid; decide +kernel

private theorem sp23537 : smallValid 23537 61 := by unfold smallValid; decide +kernel

private theorem sp23598 : smallValid 23598 60 := by unfold smallValid; decide +kernel

private theorem sp23658 : smallValid 23658 60 := by unfold smallValid; decide +kernel

private theorem sp23718 : smallValid 23718 60 := by unfold smallValid; decide +kernel

private theorem sp23778 : smallValid 23778 61 := by unfold smallValid; decide +kernel

private theorem sp23839 : smallValid 23839 60 := by unfold smallValid; decide +kernel

private theorem sp23899 : smallValid 23899 60 := by unfold smallValid; decide +kernel

private theorem sp23959 : smallValid 23959 60 := by unfold smallValid; decide +kernel

private theorem sp24019 : smallValid 24019 61 := by unfold smallValid; decide +kernel

private theorem sp24080 : smallValid 24080 60 := by unfold smallValid; decide +kernel

private theorem sp24140 : smallValid 24140 60 := by unfold smallValid; decide +kernel

private theorem sp24200 : smallValid 24200 60 := by unfold smallValid; decide +kernel

private theorem sp24260 : smallValid 24260 60 := by unfold smallValid; decide +kernel

private theorem sp24320 : smallValid 24320 60 := by unfold smallValid; decide +kernel

private theorem sp24380 : smallValid 24380 60 := by unfold smallValid; decide +kernel

private theorem sp24440 : smallValid 24440 60 := by unfold smallValid; decide +kernel

private theorem sp24500 : smallValid 24500 61 := by unfold smallValid; decide +kernel

private theorem sp24561 : smallValid 24561 60 := by unfold smallValid; decide +kernel

private theorem sp24621 : smallValid 24621 60 := by unfold smallValid; decide +kernel

private theorem sp24681 : smallValid 24681 60 := by unfold smallValid; decide +kernel

private theorem sp24741 : smallValid 24741 61 := by unfold smallValid; decide +kernel

private theorem sp24802 : smallValid 24802 60 := by unfold smallValid; decide +kernel

private theorem sp24862 : smallValid 24862 60 := by unfold smallValid; decide +kernel

private theorem sp24922 : smallValid 24922 60 := by unfold smallValid; decide +kernel

private theorem sp24982 : smallValid 24982 61 := by unfold smallValid; decide +kernel

private theorem sp25043 : smallValid 25043 60 := by unfold smallValid; decide +kernel

private theorem sp25103 : smallValid 25103 60 := by unfold smallValid; decide +kernel

private theorem sp25163 : smallValid 25163 60 := by unfold smallValid; decide +kernel

private theorem sp25223 : smallValid 25223 60 := by unfold smallValid; decide +kernel

private theorem sp25283 : smallValid 25283 60 := by unfold smallValid; decide +kernel

private theorem sp25343 : smallValid 25343 60 := by unfold smallValid; decide +kernel

private theorem sp25403 : smallValid 25403 60 := by unfold smallValid; decide +kernel

private theorem sp25463 : smallValid 25463 61 := by unfold smallValid; decide +kernel

private theorem sp25524 : smallValid 25524 60 := by unfold smallValid; decide +kernel

private theorem sp25584 : smallValid 25584 60 := by unfold smallValid; decide +kernel

private theorem sp25644 : smallValid 25644 60 := by unfold smallValid; decide +kernel

private theorem sp25704 : smallValid 25704 61 := by unfold smallValid; decide +kernel

private theorem sp25765 : smallValid 25765 60 := by unfold smallValid; decide +kernel

private theorem sp25825 : smallValid 25825 60 := by unfold smallValid; decide +kernel

private theorem sp25885 : smallValid 25885 60 := by unfold smallValid; decide +kernel

private theorem sp25945 : smallValid 25945 61 := by unfold smallValid; decide +kernel

private theorem sp26006 : smallValid 26006 60 := by unfold smallValid; decide +kernel

private theorem sp26066 : smallValid 26066 60 := by unfold smallValid; decide +kernel

private theorem sp26126 : smallValid 26126 60 := by unfold smallValid; decide +kernel

private theorem sp26186 : smallValid 26186 61 := by unfold smallValid; decide +kernel

private theorem sp26247 : smallValid 26247 60 := by unfold smallValid; decide +kernel

private theorem sp26307 : smallValid 26307 60 := by unfold smallValid; decide +kernel

private theorem sp26367 : smallValid 26367 60 := by unfold smallValid; decide +kernel

private theorem sp26427 : smallValid 26427 61 := by unfold smallValid; decide +kernel

private theorem sp26488 : smallValid 26488 60 := by unfold smallValid; decide +kernel

private theorem sp26548 : smallValid 26548 60 := by unfold smallValid; decide +kernel

private theorem sp26608 : smallValid 26608 60 := by unfold smallValid; decide +kernel

private theorem sp26668 : smallValid 26668 61 := by unfold smallValid; decide +kernel

private theorem sp26729 : smallValid 26729 60 := by unfold smallValid; decide +kernel

private theorem sp26789 : smallValid 26789 60 := by unfold smallValid; decide +kernel

private theorem sp26849 : smallValid 26849 60 := by unfold smallValid; decide +kernel

private theorem sp26909 : smallValid 26909 61 := by unfold smallValid; decide +kernel

private theorem sp26970 : smallValid 26970 60 := by unfold smallValid; decide +kernel

private theorem sp27030 : smallValid 27030 60 := by unfold smallValid; decide +kernel

private theorem sp27090 : smallValid 27090 60 := by unfold smallValid; decide +kernel

private theorem sp27150 : smallValid 27150 60 := by unfold smallValid; decide +kernel

private theorem sp27210 : smallValid 27210 60 := by unfold smallValid; decide +kernel

private theorem sp27270 : smallValid 27270 60 := by unfold smallValid; decide +kernel

private theorem sp27330 : smallValid 27330 60 := by unfold smallValid; decide +kernel

private theorem sp27390 : smallValid 27390 61 := by unfold smallValid; decide +kernel

private theorem sp27451 : smallValid 27451 60 := by unfold smallValid; decide +kernel

private theorem sp27511 : smallValid 27511 60 := by unfold smallValid; decide +kernel

private theorem sp27571 : smallValid 27571 60 := by unfold smallValid; decide +kernel

private theorem sp27631 : smallValid 27631 61 := by unfold smallValid; decide +kernel

private theorem sp27692 : smallValid 27692 60 := by unfold smallValid; decide +kernel

private theorem sp27752 : smallValid 27752 60 := by unfold smallValid; decide +kernel

private theorem sp27812 : smallValid 27812 60 := by unfold smallValid; decide +kernel

private theorem sp27872 : smallValid 27872 61 := by unfold smallValid; decide +kernel

private theorem sp27933 : smallValid 27933 60 := by unfold smallValid; decide +kernel

private theorem sp27993 : smallValid 27993 60 := by unfold smallValid; decide +kernel

private theorem sp28053 : smallValid 28053 60 := by unfold smallValid; decide +kernel

private theorem sp28113 : smallValid 28113 60 := by unfold smallValid; decide +kernel

private theorem sp28173 : smallValid 28173 60 := by unfold smallValid; decide +kernel

private theorem sp28233 : smallValid 28233 60 := by unfold smallValid; decide +kernel

private theorem sp28293 : smallValid 28293 60 := by unfold smallValid; decide +kernel

private theorem sp28353 : smallValid 28353 61 := by unfold smallValid; decide +kernel

private theorem sp28414 : smallValid 28414 60 := by unfold smallValid; decide +kernel

private theorem sp28474 : smallValid 28474 60 := by unfold smallValid; decide +kernel

private theorem sp28534 : smallValid 28534 60 := by unfold smallValid; decide +kernel

private theorem sp28594 : smallValid 28594 61 := by unfold smallValid; decide +kernel

private theorem sp28655 : smallValid 28655 60 := by unfold smallValid; decide +kernel

private theorem sp28715 : smallValid 28715 60 := by unfold smallValid; decide +kernel

private theorem sp28775 : smallValid 28775 60 := by unfold smallValid; decide +kernel

private theorem sp28835 : smallValid 28835 61 := by unfold smallValid; decide +kernel

private theorem sp28896 : smallValid 28896 60 := by unfold smallValid; decide +kernel

private theorem sp28956 : smallValid 28956 60 := by unfold smallValid; decide +kernel

private theorem sp29016 : smallValid 29016 60 := by unfold smallValid; decide +kernel

private theorem sp29076 : smallValid 29076 60 := by unfold smallValid; decide +kernel

private theorem sp29136 : smallValid 29136 60 := by unfold smallValid; decide +kernel

private theorem sp29196 : smallValid 29196 60 := by unfold smallValid; decide +kernel

private theorem sp29256 : smallValid 29256 60 := by unfold smallValid; decide +kernel

private theorem sp29316 : smallValid 29316 61 := by unfold smallValid; decide +kernel

private theorem sp29377 : smallValid 29377 60 := by unfold smallValid; decide +kernel

private theorem sp29437 : smallValid 29437 60 := by unfold smallValid; decide +kernel

private theorem sp29497 : smallValid 29497 60 := by unfold smallValid; decide +kernel

private theorem sp29557 : smallValid 29557 61 := by unfold smallValid; decide +kernel

private theorem sp29618 : smallValid 29618 60 := by unfold smallValid; decide +kernel

private theorem sp29678 : smallValid 29678 60 := by unfold smallValid; decide +kernel

private theorem sp29738 : smallValid 29738 60 := by unfold smallValid; decide +kernel

private theorem sp29798 : smallValid 29798 61 := by unfold smallValid; decide +kernel

private theorem sp29859 : smallValid 29859 60 := by unfold smallValid; decide +kernel

private theorem sp29919 : smallValid 29919 60 := by unfold smallValid; decide +kernel

private theorem sp29979 : smallValid 29979 60 := by unfold smallValid; decide +kernel

private theorem sp30039 : smallValid 30039 61 := by unfold smallValid; decide +kernel

private theorem sp30100 : smallValid 30100 60 := by unfold smallValid; decide +kernel

private theorem sp30160 : smallValid 30160 60 := by unfold smallValid; decide +kernel

private theorem sp30220 : smallValid 30220 60 := by unfold smallValid; decide +kernel

private theorem sp30280 : smallValid 30280 61 := by unfold smallValid; decide +kernel

private theorem sp30341 : smallValid 30341 60 := by unfold smallValid; decide +kernel

private theorem sp30401 : smallValid 30401 60 := by unfold smallValid; decide +kernel

private theorem sp30461 : smallValid 30461 60 := by unfold smallValid; decide +kernel

private theorem sp30521 : smallValid 30521 61 := by unfold smallValid; decide +kernel

private theorem sp30582 : smallValid 30582 60 := by unfold smallValid; decide +kernel

private theorem sp30642 : smallValid 30642 60 := by unfold smallValid; decide +kernel

private theorem sp30702 : smallValid 30702 60 := by unfold smallValid; decide +kernel

private theorem sp30762 : smallValid 30762 61 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤30822) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 30823 := (joinSmall (lo:=0) (a:=15411) (b:=15412) (joinSmall (lo:=0) (a:=7705) (b:=7706) (joinSmall (lo:=0) (a:=3852) (b:=3853) (joinSmall (lo:=0) (a:=1926) (b:=1926) (joinSmall (lo:=0) (a:=963) (b:=963) (joinSmall (lo:=0) (a:=481) (b:=482) (joinSmall (lo:=0) (a:=240) (b:=241) (joinSmall (lo:=0) (a:=120) (b:=120) (joinSmall (lo:=0) (a:=60) (b:=60) sp0 sp60) (joinSmall (lo:=120) (a:=60) (b:=60) sp120 sp180)) (joinSmall (lo:=240) (a:=120) (b:=121) (joinSmall (lo:=240) (a:=60) (b:=60) sp240 sp300) (joinSmall (lo:=360) (a:=60) (b:=61) sp360 sp420))) (joinSmall (lo:=481) (a:=241) (b:=241) (joinSmall (lo:=481) (a:=120) (b:=121) (joinSmall (lo:=481) (a:=60) (b:=60) sp481 sp541) (joinSmall (lo:=601) (a:=60) (b:=61) sp601 sp661)) (joinSmall (lo:=722) (a:=120) (b:=121) (joinSmall (lo:=722) (a:=60) (b:=60) sp722 sp782) (joinSmall (lo:=842) (a:=60) (b:=61) sp842 sp902)))) (joinSmall (lo:=963) (a:=481) (b:=482) (joinSmall (lo:=963) (a:=240) (b:=241) (joinSmall (lo:=963) (a:=120) (b:=120) (joinSmall (lo:=963) (a:=60) (b:=60) sp963 sp1023) (joinSmall (lo:=1083) (a:=60) (b:=60) sp1083 sp1143)) (joinSmall (lo:=1203) (a:=120) (b:=121) (joinSmall (lo:=1203) (a:=60) (b:=60) sp1203 sp1263) (joinSmall (lo:=1323) (a:=60) (b:=61) sp1323 sp1383))) (joinSmall (lo:=1444) (a:=241) (b:=241) (joinSmall (lo:=1444) (a:=120) (b:=121) (joinSmall (lo:=1444) (a:=60) (b:=60) sp1444 sp1504) (joinSmall (lo:=1564) (a:=60) (b:=61) sp1564 sp1624)) (joinSmall (lo:=1685) (a:=120) (b:=121) (joinSmall (lo:=1685) (a:=60) (b:=60) sp1685 sp1745) (joinSmall (lo:=1805) (a:=60) (b:=61) sp1805 sp1865))))) (joinSmall (lo:=1926) (a:=963) (b:=963) (joinSmall (lo:=1926) (a:=481) (b:=482) (joinSmall (lo:=1926) (a:=240) (b:=241) (joinSmall (lo:=1926) (a:=120) (b:=120) (joinSmall (lo:=1926) (a:=60) (b:=60) sp1926 sp1986) (joinSmall (lo:=2046) (a:=60) (b:=60) sp2046 sp2106)) (joinSmall (lo:=2166) (a:=120) (b:=121) (joinSmall (lo:=2166) (a:=60) (b:=60) sp2166 sp2226) (joinSmall (lo:=2286) (a:=60) (b:=61) sp2286 sp2346))) (joinSmall (lo:=2407) (a:=241) (b:=241) (joinSmall (lo:=2407) (a:=120) (b:=121) (joinSmall (lo:=2407) (a:=60) (b:=60) sp2407 sp2467) (joinSmall (lo:=2527) (a:=60) (b:=61) sp2527 sp2587)) (joinSmall (lo:=2648) (a:=120) (b:=121) (joinSmall (lo:=2648) (a:=60) (b:=60) sp2648 sp2708) (joinSmall (lo:=2768) (a:=60) (b:=61) sp2768 sp2828)))) (joinSmall (lo:=2889) (a:=481) (b:=482) (joinSmall (lo:=2889) (a:=240) (b:=241) (joinSmall (lo:=2889) (a:=120) (b:=120) (joinSmall (lo:=2889) (a:=60) (b:=60) sp2889 sp2949) (joinSmall (lo:=3009) (a:=60) (b:=60) sp3009 sp3069)) (joinSmall (lo:=3129) (a:=120) (b:=121) (joinSmall (lo:=3129) (a:=60) (b:=60) sp3129 sp3189) (joinSmall (lo:=3249) (a:=60) (b:=61) sp3249 sp3309))) (joinSmall (lo:=3370) (a:=241) (b:=241) (joinSmall (lo:=3370) (a:=120) (b:=121) (joinSmall (lo:=3370) (a:=60) (b:=60) sp3370 sp3430) (joinSmall (lo:=3490) (a:=60) (b:=61) sp3490 sp3550)) (joinSmall (lo:=3611) (a:=120) (b:=121) (joinSmall (lo:=3611) (a:=60) (b:=60) sp3611 sp3671) (joinSmall (lo:=3731) (a:=60) (b:=61) sp3731 sp3791)))))) (joinSmall (lo:=3852) (a:=1926) (b:=1927) (joinSmall (lo:=3852) (a:=963) (b:=963) (joinSmall (lo:=3852) (a:=481) (b:=482) (joinSmall (lo:=3852) (a:=240) (b:=241) (joinSmall (lo:=3852) (a:=120) (b:=120) (joinSmall (lo:=3852) (a:=60) (b:=60) sp3852 sp3912) (joinSmall (lo:=3972) (a:=60) (b:=60) sp3972 sp4032)) (joinSmall (lo:=4092) (a:=120) (b:=121) (joinSmall (lo:=4092) (a:=60) (b:=60) sp4092 sp4152) (joinSmall (lo:=4212) (a:=60) (b:=61) sp4212 sp4272))) (joinSmall (lo:=4333) (a:=241) (b:=241) (joinSmall (lo:=4333) (a:=120) (b:=121) (joinSmall (lo:=4333) (a:=60) (b:=60) sp4333 sp4393) (joinSmall (lo:=4453) (a:=60) (b:=61) sp4453 sp4513)) (joinSmall (lo:=4574) (a:=120) (b:=121) (joinSmall (lo:=4574) (a:=60) (b:=60) sp4574 sp4634) (joinSmall (lo:=4694) (a:=60) (b:=61) sp4694 sp4754)))) (joinSmall (lo:=4815) (a:=481) (b:=482) (joinSmall (lo:=4815) (a:=240) (b:=241) (joinSmall (lo:=4815) (a:=120) (b:=120) (joinSmall (lo:=4815) (a:=60) (b:=60) sp4815 sp4875) (joinSmall (lo:=4935) (a:=60) (b:=60) sp4935 sp4995)) (joinSmall (lo:=5055) (a:=120) (b:=121) (joinSmall (lo:=5055) (a:=60) (b:=60) sp5055 sp5115) (joinSmall (lo:=5175) (a:=60) (b:=61) sp5175 sp5235))) (joinSmall (lo:=5296) (a:=241) (b:=241) (joinSmall (lo:=5296) (a:=120) (b:=121) (joinSmall (lo:=5296) (a:=60) (b:=60) sp5296 sp5356) (joinSmall (lo:=5416) (a:=60) (b:=61) sp5416 sp5476)) (joinSmall (lo:=5537) (a:=120) (b:=121) (joinSmall (lo:=5537) (a:=60) (b:=60) sp5537 sp5597) (joinSmall (lo:=5657) (a:=60) (b:=61) sp5657 sp5717))))) (joinSmall (lo:=5778) (a:=963) (b:=964) (joinSmall (lo:=5778) (a:=481) (b:=482) (joinSmall (lo:=5778) (a:=240) (b:=241) (joinSmall (lo:=5778) (a:=120) (b:=120) (joinSmall (lo:=5778) (a:=60) (b:=60) sp5778 sp5838) (joinSmall (lo:=5898) (a:=60) (b:=60) sp5898 sp5958)) (joinSmall (lo:=6018) (a:=120) (b:=121) (joinSmall (lo:=6018) (a:=60) (b:=60) sp6018 sp6078) (joinSmall (lo:=6138) (a:=60) (b:=61) sp6138 sp6198))) (joinSmall (lo:=6259) (a:=241) (b:=241) (joinSmall (lo:=6259) (a:=120) (b:=121) (joinSmall (lo:=6259) (a:=60) (b:=60) sp6259 sp6319) (joinSmall (lo:=6379) (a:=60) (b:=61) sp6379 sp6439)) (joinSmall (lo:=6500) (a:=120) (b:=121) (joinSmall (lo:=6500) (a:=60) (b:=60) sp6500 sp6560) (joinSmall (lo:=6620) (a:=60) (b:=61) sp6620 sp6680)))) (joinSmall (lo:=6741) (a:=482) (b:=482) (joinSmall (lo:=6741) (a:=241) (b:=241) (joinSmall (lo:=6741) (a:=120) (b:=121) (joinSmall (lo:=6741) (a:=60) (b:=60) sp6741 sp6801) (joinSmall (lo:=6861) (a:=60) (b:=61) sp6861 sp6921)) (joinSmall (lo:=6982) (a:=120) (b:=121) (joinSmall (lo:=6982) (a:=60) (b:=60) sp6982 sp7042) (joinSmall (lo:=7102) (a:=60) (b:=61) sp7102 sp7162))) (joinSmall (lo:=7223) (a:=241) (b:=241) (joinSmall (lo:=7223) (a:=120) (b:=121) (joinSmall (lo:=7223) (a:=60) (b:=60) sp7223 sp7283) (joinSmall (lo:=7343) (a:=60) (b:=61) sp7343 sp7403)) (joinSmall (lo:=7464) (a:=120) (b:=121) (joinSmall (lo:=7464) (a:=60) (b:=60) sp7464 sp7524) (joinSmall (lo:=7584) (a:=60) (b:=61) sp7584 sp7644))))))) (joinSmall (lo:=7705) (a:=3853) (b:=3853) (joinSmall (lo:=7705) (a:=1926) (b:=1927) (joinSmall (lo:=7705) (a:=963) (b:=963) (joinSmall (lo:=7705) (a:=481) (b:=482) (joinSmall (lo:=7705) (a:=240) (b:=241) (joinSmall (lo:=7705) (a:=120) (b:=120) (joinSmall (lo:=7705) (a:=60) (b:=60) sp7705 sp7765) (joinSmall (lo:=7825) (a:=60) (b:=60) sp7825 sp7885)) (joinSmall (lo:=7945) (a:=120) (b:=121) (joinSmall (lo:=7945) (a:=60) (b:=60) sp7945 sp8005) (joinSmall (lo:=8065) (a:=60) (b:=61) sp8065 sp8125))) (joinSmall (lo:=8186) (a:=241) (b:=241) (joinSmall (lo:=8186) (a:=120) (b:=121) (joinSmall (lo:=8186) (a:=60) (b:=60) sp8186 sp8246) (joinSmall (lo:=8306) (a:=60) (b:=61) sp8306 sp8366)) (joinSmall (lo:=8427) (a:=120) (b:=121) (joinSmall (lo:=8427) (a:=60) (b:=60) sp8427 sp8487) (joinSmall (lo:=8547) (a:=60) (b:=61) sp8547 sp8607)))) (joinSmall (lo:=8668) (a:=481) (b:=482) (joinSmall (lo:=8668) (a:=240) (b:=241) (joinSmall (lo:=8668) (a:=120) (b:=120) (joinSmall (lo:=8668) (a:=60) (b:=60) sp8668 sp8728) (joinSmall (lo:=8788) (a:=60) (b:=60) sp8788 sp8848)) (joinSmall (lo:=8908) (a:=120) (b:=121) (joinSmall (lo:=8908) (a:=60) (b:=60) sp8908 sp8968) (joinSmall (lo:=9028) (a:=60) (b:=61) sp9028 sp9088))) (joinSmall (lo:=9149) (a:=241) (b:=241) (joinSmall (lo:=9149) (a:=120) (b:=121) (joinSmall (lo:=9149) (a:=60) (b:=60) sp9149 sp9209) (joinSmall (lo:=9269) (a:=60) (b:=61) sp9269 sp9329)) (joinSmall (lo:=9390) (a:=120) (b:=121) (joinSmall (lo:=9390) (a:=60) (b:=60) sp9390 sp9450) (joinSmall (lo:=9510) (a:=60) (b:=61) sp9510 sp9570))))) (joinSmall (lo:=9631) (a:=963) (b:=964) (joinSmall (lo:=9631) (a:=481) (b:=482) (joinSmall (lo:=9631) (a:=240) (b:=241) (joinSmall (lo:=9631) (a:=120) (b:=120) (joinSmall (lo:=9631) (a:=60) (b:=60) sp9631 sp9691) (joinSmall (lo:=9751) (a:=60) (b:=60) sp9751 sp9811)) (joinSmall (lo:=9871) (a:=120) (b:=121) (joinSmall (lo:=9871) (a:=60) (b:=60) sp9871 sp9931) (joinSmall (lo:=9991) (a:=60) (b:=61) sp9991 sp10051))) (joinSmall (lo:=10112) (a:=241) (b:=241) (joinSmall (lo:=10112) (a:=120) (b:=121) (joinSmall (lo:=10112) (a:=60) (b:=60) sp10112 sp10172) (joinSmall (lo:=10232) (a:=60) (b:=61) sp10232 sp10292)) (joinSmall (lo:=10353) (a:=120) (b:=121) (joinSmall (lo:=10353) (a:=60) (b:=60) sp10353 sp10413) (joinSmall (lo:=10473) (a:=60) (b:=61) sp10473 sp10533)))) (joinSmall (lo:=10594) (a:=482) (b:=482) (joinSmall (lo:=10594) (a:=241) (b:=241) (joinSmall (lo:=10594) (a:=120) (b:=121) (joinSmall (lo:=10594) (a:=60) (b:=60) sp10594 sp10654) (joinSmall (lo:=10714) (a:=60) (b:=61) sp10714 sp10774)) (joinSmall (lo:=10835) (a:=120) (b:=121) (joinSmall (lo:=10835) (a:=60) (b:=60) sp10835 sp10895) (joinSmall (lo:=10955) (a:=60) (b:=61) sp10955 sp11015))) (joinSmall (lo:=11076) (a:=241) (b:=241) (joinSmall (lo:=11076) (a:=120) (b:=121) (joinSmall (lo:=11076) (a:=60) (b:=60) sp11076 sp11136) (joinSmall (lo:=11196) (a:=60) (b:=61) sp11196 sp11256)) (joinSmall (lo:=11317) (a:=120) (b:=121) (joinSmall (lo:=11317) (a:=60) (b:=60) sp11317 sp11377) (joinSmall (lo:=11437) (a:=60) (b:=61) sp11437 sp11497)))))) (joinSmall (lo:=11558) (a:=1926) (b:=1927) (joinSmall (lo:=11558) (a:=963) (b:=963) (joinSmall (lo:=11558) (a:=481) (b:=482) (joinSmall (lo:=11558) (a:=240) (b:=241) (joinSmall (lo:=11558) (a:=120) (b:=120) (joinSmall (lo:=11558) (a:=60) (b:=60) sp11558 sp11618) (joinSmall (lo:=11678) (a:=60) (b:=60) sp11678 sp11738)) (joinSmall (lo:=11798) (a:=120) (b:=121) (joinSmall (lo:=11798) (a:=60) (b:=60) sp11798 sp11858) (joinSmall (lo:=11918) (a:=60) (b:=61) sp11918 sp11978))) (joinSmall (lo:=12039) (a:=241) (b:=241) (joinSmall (lo:=12039) (a:=120) (b:=121) (joinSmall (lo:=12039) (a:=60) (b:=60) sp12039 sp12099) (joinSmall (lo:=12159) (a:=60) (b:=61) sp12159 sp12219)) (joinSmall (lo:=12280) (a:=120) (b:=121) (joinSmall (lo:=12280) (a:=60) (b:=60) sp12280 sp12340) (joinSmall (lo:=12400) (a:=60) (b:=61) sp12400 sp12460)))) (joinSmall (lo:=12521) (a:=481) (b:=482) (joinSmall (lo:=12521) (a:=240) (b:=241) (joinSmall (lo:=12521) (a:=120) (b:=120) (joinSmall (lo:=12521) (a:=60) (b:=60) sp12521 sp12581) (joinSmall (lo:=12641) (a:=60) (b:=60) sp12641 sp12701)) (joinSmall (lo:=12761) (a:=120) (b:=121) (joinSmall (lo:=12761) (a:=60) (b:=60) sp12761 sp12821) (joinSmall (lo:=12881) (a:=60) (b:=61) sp12881 sp12941))) (joinSmall (lo:=13002) (a:=241) (b:=241) (joinSmall (lo:=13002) (a:=120) (b:=121) (joinSmall (lo:=13002) (a:=60) (b:=60) sp13002 sp13062) (joinSmall (lo:=13122) (a:=60) (b:=61) sp13122 sp13182)) (joinSmall (lo:=13243) (a:=120) (b:=121) (joinSmall (lo:=13243) (a:=60) (b:=60) sp13243 sp13303) (joinSmall (lo:=13363) (a:=60) (b:=61) sp13363 sp13423))))) (joinSmall (lo:=13484) (a:=963) (b:=964) (joinSmall (lo:=13484) (a:=481) (b:=482) (joinSmall (lo:=13484) (a:=240) (b:=241) (joinSmall (lo:=13484) (a:=120) (b:=120) (joinSmall (lo:=13484) (a:=60) (b:=60) sp13484 sp13544) (joinSmall (lo:=13604) (a:=60) (b:=60) sp13604 sp13664)) (joinSmall (lo:=13724) (a:=120) (b:=121) (joinSmall (lo:=13724) (a:=60) (b:=60) sp13724 sp13784) (joinSmall (lo:=13844) (a:=60) (b:=61) sp13844 sp13904))) (joinSmall (lo:=13965) (a:=241) (b:=241) (joinSmall (lo:=13965) (a:=120) (b:=121) (joinSmall (lo:=13965) (a:=60) (b:=60) sp13965 sp14025) (joinSmall (lo:=14085) (a:=60) (b:=61) sp14085 sp14145)) (joinSmall (lo:=14206) (a:=120) (b:=121) (joinSmall (lo:=14206) (a:=60) (b:=60) sp14206 sp14266) (joinSmall (lo:=14326) (a:=60) (b:=61) sp14326 sp14386)))) (joinSmall (lo:=14447) (a:=482) (b:=482) (joinSmall (lo:=14447) (a:=241) (b:=241) (joinSmall (lo:=14447) (a:=120) (b:=121) (joinSmall (lo:=14447) (a:=60) (b:=60) sp14447 sp14507) (joinSmall (lo:=14567) (a:=60) (b:=61) sp14567 sp14627)) (joinSmall (lo:=14688) (a:=120) (b:=121) (joinSmall (lo:=14688) (a:=60) (b:=60) sp14688 sp14748) (joinSmall (lo:=14808) (a:=60) (b:=61) sp14808 sp14868))) (joinSmall (lo:=14929) (a:=241) (b:=241) (joinSmall (lo:=14929) (a:=120) (b:=121) (joinSmall (lo:=14929) (a:=60) (b:=60) sp14929 sp14989) (joinSmall (lo:=15049) (a:=60) (b:=61) sp15049 sp15109)) (joinSmall (lo:=15170) (a:=120) (b:=121) (joinSmall (lo:=15170) (a:=60) (b:=60) sp15170 sp15230) (joinSmall (lo:=15290) (a:=60) (b:=61) sp15290 sp15350)))))))) (joinSmall (lo:=15411) (a:=7706) (b:=7706) (joinSmall (lo:=15411) (a:=3853) (b:=3853) (joinSmall (lo:=15411) (a:=1926) (b:=1927) (joinSmall (lo:=15411) (a:=963) (b:=963) (joinSmall (lo:=15411) (a:=481) (b:=482) (joinSmall (lo:=15411) (a:=240) (b:=241) (joinSmall (lo:=15411) (a:=120) (b:=120) (joinSmall (lo:=15411) (a:=60) (b:=60) sp15411 sp15471) (joinSmall (lo:=15531) (a:=60) (b:=60) sp15531 sp15591)) (joinSmall (lo:=15651) (a:=120) (b:=121) (joinSmall (lo:=15651) (a:=60) (b:=60) sp15651 sp15711) (joinSmall (lo:=15771) (a:=60) (b:=61) sp15771 sp15831))) (joinSmall (lo:=15892) (a:=241) (b:=241) (joinSmall (lo:=15892) (a:=120) (b:=121) (joinSmall (lo:=15892) (a:=60) (b:=60) sp15892 sp15952) (joinSmall (lo:=16012) (a:=60) (b:=61) sp16012 sp16072)) (joinSmall (lo:=16133) (a:=120) (b:=121) (joinSmall (lo:=16133) (a:=60) (b:=60) sp16133 sp16193) (joinSmall (lo:=16253) (a:=60) (b:=61) sp16253 sp16313)))) (joinSmall (lo:=16374) (a:=481) (b:=482) (joinSmall (lo:=16374) (a:=240) (b:=241) (joinSmall (lo:=16374) (a:=120) (b:=120) (joinSmall (lo:=16374) (a:=60) (b:=60) sp16374 sp16434) (joinSmall (lo:=16494) (a:=60) (b:=60) sp16494 sp16554)) (joinSmall (lo:=16614) (a:=120) (b:=121) (joinSmall (lo:=16614) (a:=60) (b:=60) sp16614 sp16674) (joinSmall (lo:=16734) (a:=60) (b:=61) sp16734 sp16794))) (joinSmall (lo:=16855) (a:=241) (b:=241) (joinSmall (lo:=16855) (a:=120) (b:=121) (joinSmall (lo:=16855) (a:=60) (b:=60) sp16855 sp16915) (joinSmall (lo:=16975) (a:=60) (b:=61) sp16975 sp17035)) (joinSmall (lo:=17096) (a:=120) (b:=121) (joinSmall (lo:=17096) (a:=60) (b:=60) sp17096 sp17156) (joinSmall (lo:=17216) (a:=60) (b:=61) sp17216 sp17276))))) (joinSmall (lo:=17337) (a:=963) (b:=964) (joinSmall (lo:=17337) (a:=481) (b:=482) (joinSmall (lo:=17337) (a:=240) (b:=241) (joinSmall (lo:=17337) (a:=120) (b:=120) (joinSmall (lo:=17337) (a:=60) (b:=60) sp17337 sp17397) (joinSmall (lo:=17457) (a:=60) (b:=60) sp17457 sp17517)) (joinSmall (lo:=17577) (a:=120) (b:=121) (joinSmall (lo:=17577) (a:=60) (b:=60) sp17577 sp17637) (joinSmall (lo:=17697) (a:=60) (b:=61) sp17697 sp17757))) (joinSmall (lo:=17818) (a:=241) (b:=241) (joinSmall (lo:=17818) (a:=120) (b:=121) (joinSmall (lo:=17818) (a:=60) (b:=60) sp17818 sp17878) (joinSmall (lo:=17938) (a:=60) (b:=61) sp17938 sp17998)) (joinSmall (lo:=18059) (a:=120) (b:=121) (joinSmall (lo:=18059) (a:=60) (b:=60) sp18059 sp18119) (joinSmall (lo:=18179) (a:=60) (b:=61) sp18179 sp18239)))) (joinSmall (lo:=18300) (a:=482) (b:=482) (joinSmall (lo:=18300) (a:=241) (b:=241) (joinSmall (lo:=18300) (a:=120) (b:=121) (joinSmall (lo:=18300) (a:=60) (b:=60) sp18300 sp18360) (joinSmall (lo:=18420) (a:=60) (b:=61) sp18420 sp18480)) (joinSmall (lo:=18541) (a:=120) (b:=121) (joinSmall (lo:=18541) (a:=60) (b:=60) sp18541 sp18601) (joinSmall (lo:=18661) (a:=60) (b:=61) sp18661 sp18721))) (joinSmall (lo:=18782) (a:=241) (b:=241) (joinSmall (lo:=18782) (a:=120) (b:=121) (joinSmall (lo:=18782) (a:=60) (b:=60) sp18782 sp18842) (joinSmall (lo:=18902) (a:=60) (b:=61) sp18902 sp18962)) (joinSmall (lo:=19023) (a:=120) (b:=121) (joinSmall (lo:=19023) (a:=60) (b:=60) sp19023 sp19083) (joinSmall (lo:=19143) (a:=60) (b:=61) sp19143 sp19203)))))) (joinSmall (lo:=19264) (a:=1926) (b:=1927) (joinSmall (lo:=19264) (a:=963) (b:=963) (joinSmall (lo:=19264) (a:=481) (b:=482) (joinSmall (lo:=19264) (a:=240) (b:=241) (joinSmall (lo:=19264) (a:=120) (b:=120) (joinSmall (lo:=19264) (a:=60) (b:=60) sp19264 sp19324) (joinSmall (lo:=19384) (a:=60) (b:=60) sp19384 sp19444)) (joinSmall (lo:=19504) (a:=120) (b:=121) (joinSmall (lo:=19504) (a:=60) (b:=60) sp19504 sp19564) (joinSmall (lo:=19624) (a:=60) (b:=61) sp19624 sp19684))) (joinSmall (lo:=19745) (a:=241) (b:=241) (joinSmall (lo:=19745) (a:=120) (b:=121) (joinSmall (lo:=19745) (a:=60) (b:=60) sp19745 sp19805) (joinSmall (lo:=19865) (a:=60) (b:=61) sp19865 sp19925)) (joinSmall (lo:=19986) (a:=120) (b:=121) (joinSmall (lo:=19986) (a:=60) (b:=60) sp19986 sp20046) (joinSmall (lo:=20106) (a:=60) (b:=61) sp20106 sp20166)))) (joinSmall (lo:=20227) (a:=481) (b:=482) (joinSmall (lo:=20227) (a:=240) (b:=241) (joinSmall (lo:=20227) (a:=120) (b:=120) (joinSmall (lo:=20227) (a:=60) (b:=60) sp20227 sp20287) (joinSmall (lo:=20347) (a:=60) (b:=60) sp20347 sp20407)) (joinSmall (lo:=20467) (a:=120) (b:=121) (joinSmall (lo:=20467) (a:=60) (b:=60) sp20467 sp20527) (joinSmall (lo:=20587) (a:=60) (b:=61) sp20587 sp20647))) (joinSmall (lo:=20708) (a:=241) (b:=241) (joinSmall (lo:=20708) (a:=120) (b:=121) (joinSmall (lo:=20708) (a:=60) (b:=60) sp20708 sp20768) (joinSmall (lo:=20828) (a:=60) (b:=61) sp20828 sp20888)) (joinSmall (lo:=20949) (a:=120) (b:=121) (joinSmall (lo:=20949) (a:=60) (b:=60) sp20949 sp21009) (joinSmall (lo:=21069) (a:=60) (b:=61) sp21069 sp21129))))) (joinSmall (lo:=21190) (a:=963) (b:=964) (joinSmall (lo:=21190) (a:=481) (b:=482) (joinSmall (lo:=21190) (a:=240) (b:=241) (joinSmall (lo:=21190) (a:=120) (b:=120) (joinSmall (lo:=21190) (a:=60) (b:=60) sp21190 sp21250) (joinSmall (lo:=21310) (a:=60) (b:=60) sp21310 sp21370)) (joinSmall (lo:=21430) (a:=120) (b:=121) (joinSmall (lo:=21430) (a:=60) (b:=60) sp21430 sp21490) (joinSmall (lo:=21550) (a:=60) (b:=61) sp21550 sp21610))) (joinSmall (lo:=21671) (a:=241) (b:=241) (joinSmall (lo:=21671) (a:=120) (b:=121) (joinSmall (lo:=21671) (a:=60) (b:=60) sp21671 sp21731) (joinSmall (lo:=21791) (a:=60) (b:=61) sp21791 sp21851)) (joinSmall (lo:=21912) (a:=120) (b:=121) (joinSmall (lo:=21912) (a:=60) (b:=60) sp21912 sp21972) (joinSmall (lo:=22032) (a:=60) (b:=61) sp22032 sp22092)))) (joinSmall (lo:=22153) (a:=482) (b:=482) (joinSmall (lo:=22153) (a:=241) (b:=241) (joinSmall (lo:=22153) (a:=120) (b:=121) (joinSmall (lo:=22153) (a:=60) (b:=60) sp22153 sp22213) (joinSmall (lo:=22273) (a:=60) (b:=61) sp22273 sp22333)) (joinSmall (lo:=22394) (a:=120) (b:=121) (joinSmall (lo:=22394) (a:=60) (b:=60) sp22394 sp22454) (joinSmall (lo:=22514) (a:=60) (b:=61) sp22514 sp22574))) (joinSmall (lo:=22635) (a:=241) (b:=241) (joinSmall (lo:=22635) (a:=120) (b:=121) (joinSmall (lo:=22635) (a:=60) (b:=60) sp22635 sp22695) (joinSmall (lo:=22755) (a:=60) (b:=61) sp22755 sp22815)) (joinSmall (lo:=22876) (a:=120) (b:=121) (joinSmall (lo:=22876) (a:=60) (b:=60) sp22876 sp22936) (joinSmall (lo:=22996) (a:=60) (b:=61) sp22996 sp23056))))))) (joinSmall (lo:=23117) (a:=3853) (b:=3853) (joinSmall (lo:=23117) (a:=1926) (b:=1927) (joinSmall (lo:=23117) (a:=963) (b:=963) (joinSmall (lo:=23117) (a:=481) (b:=482) (joinSmall (lo:=23117) (a:=240) (b:=241) (joinSmall (lo:=23117) (a:=120) (b:=120) (joinSmall (lo:=23117) (a:=60) (b:=60) sp23117 sp23177) (joinSmall (lo:=23237) (a:=60) (b:=60) sp23237 sp23297)) (joinSmall (lo:=23357) (a:=120) (b:=121) (joinSmall (lo:=23357) (a:=60) (b:=60) sp23357 sp23417) (joinSmall (lo:=23477) (a:=60) (b:=61) sp23477 sp23537))) (joinSmall (lo:=23598) (a:=241) (b:=241) (joinSmall (lo:=23598) (a:=120) (b:=121) (joinSmall (lo:=23598) (a:=60) (b:=60) sp23598 sp23658) (joinSmall (lo:=23718) (a:=60) (b:=61) sp23718 sp23778)) (joinSmall (lo:=23839) (a:=120) (b:=121) (joinSmall (lo:=23839) (a:=60) (b:=60) sp23839 sp23899) (joinSmall (lo:=23959) (a:=60) (b:=61) sp23959 sp24019)))) (joinSmall (lo:=24080) (a:=481) (b:=482) (joinSmall (lo:=24080) (a:=240) (b:=241) (joinSmall (lo:=24080) (a:=120) (b:=120) (joinSmall (lo:=24080) (a:=60) (b:=60) sp24080 sp24140) (joinSmall (lo:=24200) (a:=60) (b:=60) sp24200 sp24260)) (joinSmall (lo:=24320) (a:=120) (b:=121) (joinSmall (lo:=24320) (a:=60) (b:=60) sp24320 sp24380) (joinSmall (lo:=24440) (a:=60) (b:=61) sp24440 sp24500))) (joinSmall (lo:=24561) (a:=241) (b:=241) (joinSmall (lo:=24561) (a:=120) (b:=121) (joinSmall (lo:=24561) (a:=60) (b:=60) sp24561 sp24621) (joinSmall (lo:=24681) (a:=60) (b:=61) sp24681 sp24741)) (joinSmall (lo:=24802) (a:=120) (b:=121) (joinSmall (lo:=24802) (a:=60) (b:=60) sp24802 sp24862) (joinSmall (lo:=24922) (a:=60) (b:=61) sp24922 sp24982))))) (joinSmall (lo:=25043) (a:=963) (b:=964) (joinSmall (lo:=25043) (a:=481) (b:=482) (joinSmall (lo:=25043) (a:=240) (b:=241) (joinSmall (lo:=25043) (a:=120) (b:=120) (joinSmall (lo:=25043) (a:=60) (b:=60) sp25043 sp25103) (joinSmall (lo:=25163) (a:=60) (b:=60) sp25163 sp25223)) (joinSmall (lo:=25283) (a:=120) (b:=121) (joinSmall (lo:=25283) (a:=60) (b:=60) sp25283 sp25343) (joinSmall (lo:=25403) (a:=60) (b:=61) sp25403 sp25463))) (joinSmall (lo:=25524) (a:=241) (b:=241) (joinSmall (lo:=25524) (a:=120) (b:=121) (joinSmall (lo:=25524) (a:=60) (b:=60) sp25524 sp25584) (joinSmall (lo:=25644) (a:=60) (b:=61) sp25644 sp25704)) (joinSmall (lo:=25765) (a:=120) (b:=121) (joinSmall (lo:=25765) (a:=60) (b:=60) sp25765 sp25825) (joinSmall (lo:=25885) (a:=60) (b:=61) sp25885 sp25945)))) (joinSmall (lo:=26006) (a:=482) (b:=482) (joinSmall (lo:=26006) (a:=241) (b:=241) (joinSmall (lo:=26006) (a:=120) (b:=121) (joinSmall (lo:=26006) (a:=60) (b:=60) sp26006 sp26066) (joinSmall (lo:=26126) (a:=60) (b:=61) sp26126 sp26186)) (joinSmall (lo:=26247) (a:=120) (b:=121) (joinSmall (lo:=26247) (a:=60) (b:=60) sp26247 sp26307) (joinSmall (lo:=26367) (a:=60) (b:=61) sp26367 sp26427))) (joinSmall (lo:=26488) (a:=241) (b:=241) (joinSmall (lo:=26488) (a:=120) (b:=121) (joinSmall (lo:=26488) (a:=60) (b:=60) sp26488 sp26548) (joinSmall (lo:=26608) (a:=60) (b:=61) sp26608 sp26668)) (joinSmall (lo:=26729) (a:=120) (b:=121) (joinSmall (lo:=26729) (a:=60) (b:=60) sp26729 sp26789) (joinSmall (lo:=26849) (a:=60) (b:=61) sp26849 sp26909)))))) (joinSmall (lo:=26970) (a:=1926) (b:=1927) (joinSmall (lo:=26970) (a:=963) (b:=963) (joinSmall (lo:=26970) (a:=481) (b:=482) (joinSmall (lo:=26970) (a:=240) (b:=241) (joinSmall (lo:=26970) (a:=120) (b:=120) (joinSmall (lo:=26970) (a:=60) (b:=60) sp26970 sp27030) (joinSmall (lo:=27090) (a:=60) (b:=60) sp27090 sp27150)) (joinSmall (lo:=27210) (a:=120) (b:=121) (joinSmall (lo:=27210) (a:=60) (b:=60) sp27210 sp27270) (joinSmall (lo:=27330) (a:=60) (b:=61) sp27330 sp27390))) (joinSmall (lo:=27451) (a:=241) (b:=241) (joinSmall (lo:=27451) (a:=120) (b:=121) (joinSmall (lo:=27451) (a:=60) (b:=60) sp27451 sp27511) (joinSmall (lo:=27571) (a:=60) (b:=61) sp27571 sp27631)) (joinSmall (lo:=27692) (a:=120) (b:=121) (joinSmall (lo:=27692) (a:=60) (b:=60) sp27692 sp27752) (joinSmall (lo:=27812) (a:=60) (b:=61) sp27812 sp27872)))) (joinSmall (lo:=27933) (a:=481) (b:=482) (joinSmall (lo:=27933) (a:=240) (b:=241) (joinSmall (lo:=27933) (a:=120) (b:=120) (joinSmall (lo:=27933) (a:=60) (b:=60) sp27933 sp27993) (joinSmall (lo:=28053) (a:=60) (b:=60) sp28053 sp28113)) (joinSmall (lo:=28173) (a:=120) (b:=121) (joinSmall (lo:=28173) (a:=60) (b:=60) sp28173 sp28233) (joinSmall (lo:=28293) (a:=60) (b:=61) sp28293 sp28353))) (joinSmall (lo:=28414) (a:=241) (b:=241) (joinSmall (lo:=28414) (a:=120) (b:=121) (joinSmall (lo:=28414) (a:=60) (b:=60) sp28414 sp28474) (joinSmall (lo:=28534) (a:=60) (b:=61) sp28534 sp28594)) (joinSmall (lo:=28655) (a:=120) (b:=121) (joinSmall (lo:=28655) (a:=60) (b:=60) sp28655 sp28715) (joinSmall (lo:=28775) (a:=60) (b:=61) sp28775 sp28835))))) (joinSmall (lo:=28896) (a:=963) (b:=964) (joinSmall (lo:=28896) (a:=481) (b:=482) (joinSmall (lo:=28896) (a:=240) (b:=241) (joinSmall (lo:=28896) (a:=120) (b:=120) (joinSmall (lo:=28896) (a:=60) (b:=60) sp28896 sp28956) (joinSmall (lo:=29016) (a:=60) (b:=60) sp29016 sp29076)) (joinSmall (lo:=29136) (a:=120) (b:=121) (joinSmall (lo:=29136) (a:=60) (b:=60) sp29136 sp29196) (joinSmall (lo:=29256) (a:=60) (b:=61) sp29256 sp29316))) (joinSmall (lo:=29377) (a:=241) (b:=241) (joinSmall (lo:=29377) (a:=120) (b:=121) (joinSmall (lo:=29377) (a:=60) (b:=60) sp29377 sp29437) (joinSmall (lo:=29497) (a:=60) (b:=61) sp29497 sp29557)) (joinSmall (lo:=29618) (a:=120) (b:=121) (joinSmall (lo:=29618) (a:=60) (b:=60) sp29618 sp29678) (joinSmall (lo:=29738) (a:=60) (b:=61) sp29738 sp29798)))) (joinSmall (lo:=29859) (a:=482) (b:=482) (joinSmall (lo:=29859) (a:=241) (b:=241) (joinSmall (lo:=29859) (a:=120) (b:=121) (joinSmall (lo:=29859) (a:=60) (b:=60) sp29859 sp29919) (joinSmall (lo:=29979) (a:=60) (b:=61) sp29979 sp30039)) (joinSmall (lo:=30100) (a:=120) (b:=121) (joinSmall (lo:=30100) (a:=60) (b:=60) sp30100 sp30160) (joinSmall (lo:=30220) (a:=60) (b:=61) sp30220 sp30280))) (joinSmall (lo:=30341) (a:=241) (b:=241) (joinSmall (lo:=30341) (a:=120) (b:=121) (joinSmall (lo:=30341) (a:=60) (b:=60) sp30341 sp30401) (joinSmall (lo:=30461) (a:=60) (b:=61) sp30461 sp30521)) (joinSmall (lo:=30582) (a:=120) (b:=121) (joinSmall (lo:=30582) (a:=60) (b:=60) sp30582 sp30642) (joinSmall (lo:=30702) (a:=60) (b:=61) sp30702 sp30762)))))))))
  have good : (List.range 30823).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 950000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 30822 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 30822 := by
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


private def packet (i : ℕ) : ℕ := (if i < 242 then (if i < 121 then (if i < 60 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0 else 0) else (if i < 10 then 0 else 0)) else (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else 0)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0 else (if i < 17 then 0 else 0)) else (if i < 20 then (if i < 19 then 0 else 0) else (if i < 21 then 0 else 0))) else (if i < 26 then (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else 0)) else (if i < 28 then (if i < 27 then 0 else 0) else (if i < 29 then 0 else 0))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then 0 else (if i < 32 then 0 else 0)) else (if i < 35 then (if i < 34 then 0 else 0) else (if i < 36 then 0 else 0))) else (if i < 41 then (if i < 39 then (if i < 38 then 0 else 0) else (if i < 40 then 0 else 0)) else (if i < 43 then (if i < 42 then 0 else 0) else (if i < 44 then 0 else 0)))) else (if i < 52 then (if i < 48 then (if i < 46 then 0 else (if i < 47 then 0 else 0)) else (if i < 50 then (if i < 49 then 0 else 0) else (if i < 51 then 0 else 0))) else (if i < 56 then (if i < 54 then (if i < 53 then 0 else 0) else (if i < 55 then 0 else 0)) else (if i < 58 then (if i < 57 then 0 else 0) else (if i < 59 then 0 else 0)))))) else (if i < 90 then (if i < 75 then (if i < 67 then (if i < 63 then (if i < 61 then 0 else (if i < 62 then 0 else 0)) else (if i < 65 then (if i < 64 then 0 else 0) else (if i < 66 then 0 else 0))) else (if i < 71 then (if i < 69 then (if i < 68 then 0 else 0) else (if i < 70 then 0 else 0)) else (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else 0)))) else (if i < 82 then (if i < 78 then (if i < 76 then 0 else (if i < 77 then 0 else 0)) else (if i < 80 then (if i < 79 then 0 else 0) else (if i < 81 then 0 else 0))) else (if i < 86 then (if i < 84 then (if i < 83 then 0 else 0) else (if i < 85 then 0 else 0)) else (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else 0))))) else (if i < 105 then (if i < 97 then (if i < 93 then (if i < 91 then 0 else (if i < 92 then 0 else 0)) else (if i < 95 then (if i < 94 then 0 else 0) else (if i < 96 then 0 else 0))) else (if i < 101 then (if i < 99 then (if i < 98 then 0 else 0) else (if i < 100 then 0 else 0)) else (if i < 103 then (if i < 102 then 0 else 0) else (if i < 104 then 0 else 0)))) else (if i < 113 then (if i < 109 then (if i < 107 then (if i < 106 then 0 else 0) else (if i < 108 then 0 else 0)) else (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else 0))) else (if i < 117 then (if i < 115 then (if i < 114 then 0 else 0) else (if i < 116 then 0 else 0)) else (if i < 119 then (if i < 118 then 0 else 0) else (if i < 120 then 0 else 0))))))) else (if i < 181 then (if i < 151 then (if i < 136 then (if i < 128 then (if i < 124 then (if i < 122 then 0 else (if i < 123 then 0 else 0)) else (if i < 126 then (if i < 125 then 0 else 0) else (if i < 127 then 0 else 0))) else (if i < 132 then (if i < 130 then (if i < 129 then 0 else 0) else (if i < 131 then 0 else 0)) else (if i < 134 then (if i < 133 then 0 else 0) else (if i < 135 then 0 else 0)))) else (if i < 143 then (if i < 139 then (if i < 137 then 0 else (if i < 138 then 0 else 0)) else (if i < 141 then (if i < 140 then 0 else 0) else (if i < 142 then 0 else 0))) else (if i < 147 then (if i < 145 then (if i < 144 then 0 else 0) else (if i < 146 then 0 else 0)) else (if i < 149 then (if i < 148 then 0 else 0) else (if i < 150 then 0 else 0))))) else (if i < 166 then (if i < 158 then (if i < 154 then (if i < 152 then 0 else (if i < 153 then 0 else 0)) else (if i < 156 then (if i < 155 then 0 else 0) else (if i < 157 then 0 else 0))) else (if i < 162 then (if i < 160 then (if i < 159 then 0 else 0) else (if i < 161 then 0 else 0)) else (if i < 164 then (if i < 163 then 0 else 0) else (if i < 165 then 0 else 0)))) else (if i < 173 then (if i < 169 then (if i < 167 then 0 else (if i < 168 then 0 else 0)) else (if i < 171 then (if i < 170 then 0 else 0) else (if i < 172 then 0 else 0))) else (if i < 177 then (if i < 175 then (if i < 174 then 0 else 0) else (if i < 176 then 0 else 0)) else (if i < 179 then (if i < 178 then 0 else 0) else (if i < 180 then 0 else 0)))))) else (if i < 211 then (if i < 196 then (if i < 188 then (if i < 184 then (if i < 182 then 0 else (if i < 183 then 0 else 0)) else (if i < 186 then (if i < 185 then 0 else 0) else (if i < 187 then 0 else 0))) else (if i < 192 then (if i < 190 then (if i < 189 then 0 else 0) else (if i < 191 then 0 else 0)) else (if i < 194 then (if i < 193 then 0 else 0) else (if i < 195 then 0 else 0)))) else (if i < 203 then (if i < 199 then (if i < 197 then 0 else (if i < 198 then 0 else 0)) else (if i < 201 then (if i < 200 then 0 else 0) else (if i < 202 then 0 else 0))) else (if i < 207 then (if i < 205 then (if i < 204 then 0 else 0) else (if i < 206 then 0 else 0)) else (if i < 209 then (if i < 208 then 0 else 0) else (if i < 210 then 0 else 0))))) else (if i < 226 then (if i < 218 then (if i < 214 then (if i < 212 then 0 else (if i < 213 then 0 else 0)) else (if i < 216 then (if i < 215 then 0 else 0) else (if i < 217 then 0 else 0))) else (if i < 222 then (if i < 220 then (if i < 219 then 0 else 0) else (if i < 221 then 0 else 0)) else (if i < 224 then (if i < 223 then 0 else 0) else (if i < 225 then 0 else 0)))) else (if i < 234 then (if i < 230 then (if i < 228 then (if i < 227 then 0 else 0) else (if i < 229 then 0 else 0)) else (if i < 232 then (if i < 231 then 0 else 0) else (if i < 233 then 0 else 0))) else (if i < 238 then (if i < 236 then (if i < 235 then 0 else 0) else (if i < 237 then 0 else 0)) else (if i < 240 then (if i < 239 then 0 else 0) else (if i < 241 then 0 else 0)))))))) else (if i < 363 then (if i < 302 then (if i < 272 then (if i < 257 then (if i < 249 then (if i < 245 then (if i < 243 then 0 else (if i < 244 then 0 else 0)) else (if i < 247 then (if i < 246 then 0 else 0) else (if i < 248 then 0 else 0))) else (if i < 253 then (if i < 251 then (if i < 250 then 0 else 0) else (if i < 252 then 0 else 0)) else (if i < 255 then (if i < 254 then 0 else 0) else (if i < 256 then 0 else 0)))) else (if i < 264 then (if i < 260 then (if i < 258 then 0 else (if i < 259 then 0 else 0)) else (if i < 262 then (if i < 261 then 0 else 0) else (if i < 263 then 0 else 0))) else (if i < 268 then (if i < 266 then (if i < 265 then 0 else 0) else (if i < 267 then 0 else 0)) else (if i < 270 then (if i < 269 then 0 else 0) else (if i < 271 then 0 else 0))))) else (if i < 287 then (if i < 279 then (if i < 275 then (if i < 273 then 0 else (if i < 274 then 0 else 0)) else (if i < 277 then (if i < 276 then 0 else 0) else (if i < 278 then 0 else 0))) else (if i < 283 then (if i < 281 then (if i < 280 then 0 else 0) else (if i < 282 then 0 else 0)) else (if i < 285 then (if i < 284 then 0 else 0) else (if i < 286 then 0 else 0)))) else (if i < 294 then (if i < 290 then (if i < 288 then 0 else (if i < 289 then 0 else 0)) else (if i < 292 then (if i < 291 then 0 else 0) else (if i < 293 then 0 else 0))) else (if i < 298 then (if i < 296 then (if i < 295 then 0 else 0) else (if i < 297 then 0 else 0)) else (if i < 300 then (if i < 299 then 0 else 0) else (if i < 301 then 0 else 0)))))) else (if i < 332 then (if i < 317 then (if i < 309 then (if i < 305 then (if i < 303 then 0 else (if i < 304 then 0 else 0)) else (if i < 307 then (if i < 306 then 0 else 0) else (if i < 308 then 0 else 0))) else (if i < 313 then (if i < 311 then (if i < 310 then 0 else 0) else (if i < 312 then 0 else 0)) else (if i < 315 then (if i < 314 then 0 else 0) else (if i < 316 then 0 else 0)))) else (if i < 324 then (if i < 320 then (if i < 318 then 0 else (if i < 319 then 0 else 0)) else (if i < 322 then (if i < 321 then 0 else 0) else (if i < 323 then 0 else 0))) else (if i < 328 then (if i < 326 then (if i < 325 then 0 else 0) else (if i < 327 then 0 else 0)) else (if i < 330 then (if i < 329 then 0 else 0) else (if i < 331 then 0 else 0))))) else (if i < 347 then (if i < 339 then (if i < 335 then (if i < 333 then 0 else (if i < 334 then 0 else 0)) else (if i < 337 then (if i < 336 then 0 else 0) else (if i < 338 then 0 else 0))) else (if i < 343 then (if i < 341 then (if i < 340 then 0 else 0) else (if i < 342 then 0 else 0)) else (if i < 345 then (if i < 344 then 0 else 0) else (if i < 346 then 0 else 0)))) else (if i < 355 then (if i < 351 then (if i < 349 then (if i < 348 then 0 else 0) else (if i < 350 then 0 else 0)) else (if i < 353 then (if i < 352 then 0 else 0) else (if i < 354 then 0 else 0))) else (if i < 359 then (if i < 357 then (if i < 356 then 0 else 0) else (if i < 358 then 0 else 0)) else (if i < 361 then (if i < 360 then 0 else 0) else (if i < 362 then 0 else 0))))))) else (if i < 423 then (if i < 393 then (if i < 378 then (if i < 370 then (if i < 366 then (if i < 364 then 0 else (if i < 365 then 0 else 0)) else (if i < 368 then (if i < 367 then 0 else 0) else (if i < 369 then 0 else 0))) else (if i < 374 then (if i < 372 then (if i < 371 then 0 else 0) else (if i < 373 then 0 else 0)) else (if i < 376 then (if i < 375 then 0 else 0) else (if i < 377 then 0 else 0)))) else (if i < 385 then (if i < 381 then (if i < 379 then 0 else (if i < 380 then 0 else 0)) else (if i < 383 then (if i < 382 then 0 else 0) else (if i < 384 then 0 else 0))) else (if i < 389 then (if i < 387 then (if i < 386 then 0 else 0) else (if i < 388 then 0 else 0)) else (if i < 391 then (if i < 390 then 0 else 0) else (if i < 392 then 0 else 0))))) else (if i < 408 then (if i < 400 then (if i < 396 then (if i < 394 then 0 else (if i < 395 then 0 else 0)) else (if i < 398 then (if i < 397 then 0 else 0) else (if i < 399 then 0 else 0))) else (if i < 404 then (if i < 402 then (if i < 401 then 0 else 0) else (if i < 403 then 0 else 0)) else (if i < 406 then (if i < 405 then 0 else 0) else (if i < 407 then 0 else 0)))) else (if i < 415 then (if i < 411 then (if i < 409 then 0 else (if i < 410 then 0 else 0)) else (if i < 413 then (if i < 412 then 0 else 0) else (if i < 414 then 0 else 0))) else (if i < 419 then (if i < 417 then (if i < 416 then 0 else 0) else (if i < 418 then 0 else 0)) else (if i < 421 then (if i < 420 then 0 else 0) else (if i < 422 then 0 else 0)))))) else (if i < 453 then (if i < 438 then (if i < 430 then (if i < 426 then (if i < 424 then 0 else (if i < 425 then 0 else 0)) else (if i < 428 then (if i < 427 then 0 else 0) else (if i < 429 then 0 else 0))) else (if i < 434 then (if i < 432 then (if i < 431 then 0 else 0) else (if i < 433 then 0 else 0)) else (if i < 436 then (if i < 435 then 0 else 0) else (if i < 437 then 0 else 0)))) else (if i < 445 then (if i < 441 then (if i < 439 then 0 else (if i < 440 then 0 else 0)) else (if i < 443 then (if i < 442 then 0 else 0) else (if i < 444 then 0 else 0))) else (if i < 449 then (if i < 447 then (if i < 446 then 0 else 0) else (if i < 448 then 0 else 0)) else (if i < 451 then (if i < 450 then 0 else 0) else (if i < 452 then 0 else 0))))) else (if i < 468 then (if i < 460 then (if i < 456 then (if i < 454 then 0 else (if i < 455 then 0 else 0)) else (if i < 458 then (if i < 457 then 0 else 0) else (if i < 459 then 0 else 0))) else (if i < 464 then (if i < 462 then (if i < 461 then 0 else 0) else (if i < 463 then 0 else 0)) else (if i < 466 then (if i < 465 then 0 else 0) else (if i < 467 then 0 else 0)))) else (if i < 476 then (if i < 472 then (if i < 470 then (if i < 469 then 0 else 0) else (if i < 471 then 0x2d1478f2c914b49ae48020e0ef06c030614d88d03b617908a02f80c800002d141d52b1942894e44a1f98e5c6782d5139887438816108582e40b600002d13c0a2b814409584511fd8e846802ec14508b439c16908902c80be00002d136362bf148c99e4742108ef06bc2ff15489343dc18c09883040cc00002d130762b7146497645f2000e986a62e814588d03ac179093030c0c200002d12aab2b6944895e45f20a0ee06ae2fa14c09003a817d08c82c40b800002d124e92ba942896445b2020e8c66a2e2144888c3aa17308902f00b200002d11ef82c594b89a24782098ea069a2e1142889439016e08f82c40ba00002d119132c014c098c47720e0ec86ac2fb143089c39217508e832c0c600002d113402bf949498e4672080ed86c02fc14b09083c418308f83040bc00002d10d492ca14e09b04782080eb46942ed14788bc3b617909583380cc00002d1077e2b2940094e4541fb0e7867e2e114708c839c16b08882fc0c600002d101b42b394349644451f38e646842ec14488a039216708702d00ba00002d0fbca2ca14cc9a64752100f046ce309152891c3b217d09182f40d800002d0f5e72c614c09a24652030e9c6942f114888dc3bc18909082fc0b400002d0f0182b5942495444b1f28e146502ce139089838e17708882f00bc00002d0ea412b6942c9704662030ee06a82f7152890c3cc18309083200bc00002d0e48a2aa93fc9504471f60e306462c7136084c37c15808502c80b800002d0dee42a313c09324301ee0dd46362c1133884036216808902f00c000002d0d9272b0141893c43c1ef0dd86422c413a085436a15c07f02c80b400002d0d3652b5942c9684521fd0e606822e114188a03a417008b82f80ce00002d0cd6d2c994f09c44812168f246b82f214c88e83bc18409282e80b200002d0c7af2b014209564511f70e186522d1140889438a17608b82d80b800002d0c1f02b113f893e4481f70e306682d813c085436616608402f40b600002d0bc032c7948c9724662080edc6ae2f815589383c618a08e03080e600002d0b65d2ab93dc94844b1f68e606642d314188a439616908a82f80c200002d0b0a62b093ec93443f1ea8dd063a2c6139083c36015b08082880a600002d0aaaa2d215109c447120b8eb869a2ea14888ac3aa17008f82fc0c800002d0a4e42b5942c95844e1fe8e9068a2ee14b08e03a818909103200c600002d09ef02cb14d099c46d2068ed068a2f014b08dc3ac17308f02ec0c400002d099242b894549664532020e6867a2d713d08843a217808b02f80b600002d0935b2b4945c97445d1fd8e9c6962eb14888c43a617708e82fc0c000002d08d672c914c09944632048e946842ea14b88f83be17c08782d00ac00002d0878a2ba948099446f2078eac69e2ef14e08f43ce18809683440d200002d0819e2ca14a499647220b0ec46b62f814f89003ca18209202fc0c200002d07bde2b3142c9624591fc8e646722e213f088437216108682c40b000002d0763a2a493bc91c4341eb8dc46262c3137887037c15b08382c40c600002d070822ad13e493243e1f18de06362bf134085c38616608702e80bc00002d06aa02c214689864692048ed46a02e914508b03a616c08b82f40b800002d064cd2be945498a4611ff0e886942e6146889c39416408902e00b200002d05f042b8141c95a4481f98e7068a2e8141889438a16908482d80b600002d059362bb94609904631ff8ea46882e414108a439016c08982ec0b400002d053762b714709804571fd8e9869e2fe14b08f43c217b08d82f80bc00002d04da82bb147097c4632050eb86962e8140887437c16208302a009600002d047d72b2143c96645c2000ec06b02f414388c43b418008c82c40a800002d042192ad14149604461f50e306522d313a085435815007e82a00b000002d03c432b6945c9644501f98e7c6742e314408e03a417108a82d80bc00002d036712b6943c96c44b1fa0e4467c2dc13e088437216508b82fc0b600002d030882c6149c99a4752068eb46902f214e88f03b218309282f80d000002d02ab02bc146c9844571fc8e546742cf135083037a15e08602c80be00002d024b12ce14f09b647f20b8f046ce30a15108d439817a08b82d40b000002d01ef52b5141894c4491fa0e6867a2e414088b439816e08902d809e00002d0192b2b2142896645d1fc0e7469a2f614b88d03b617d09403400c800002d013852ac13e892c4351f30e406662d2139085838216e08d02f00be00002d00dab2b8145897c4602018ea06a82fd14a88f03b218109103040c800002d007b52c915049b447420d8f006c42f314908c43b817a08e831c0c600002d002002af14149504471f58e4468e2ee14988cc3ac17008702e80ba00002cffc2c2bf948c96e4592018e9867a2d9139885837c16408a02f40ba00002cff66c2b214309584541f90e806822e714a08ac3a417308b82e40be00002cff0662d815249c847f20e0f106ba2f914d08d83ac17708c02e80ae00002cfeaa72b2941894a4451f58e686702d814688b039417808f83080c600002cfe4db2b5945496e45a1fc8e6065e2da141888839817508a03000cc00002cfdefd2c394949704571fc0e746802d113c886438c16b08502a80a000002cfd9432b1945496a45a2038eb86942e814308a439616b08902cc0b0000 else 0x2d2bae72c3948c98245d2028ea868c2ef14808cc3b417d08d02e80b200002d2b5242bc143496c4541fd0e846842eb14888b439816d08982bc0c400002d2af602b294109404471f58e046482d613a088c39416d08d03040c400002d2a9962b6144897a4652078ebc6982eb14808a03ae17808c82ec0c000002d2a3ac2c6149c99846d20b8eb06942ef14808c83aa17008a02dc0b000002d29dd62bd145497a46c1ff8e886862e214308cc3a417908d82c40b000002d2982c2a713b892a43b1ef0e3465c2dd13e888838a16f08c02e00a800002d292862a793b893c43f1f48e1064e2cf13b888838c16d08782bc0ac00002d28ca22c814d09a84702028e9c69e2e714288d43b017a09102e80bc00002d286eb2b113e89244341e98e006562cf13a884436415f08502c80ae00002d280f42ce14fc9c24752068eb06b42fb15189183b617608c02f00ba00002d27b402a993c89244441f70e306742db14488c03ae17508f82dc0ac00002d275712b614649844651fc8e746822e6146089439817a08e03180ac00002d26fc42aa941c95c4551fc8e7867c2de14388bc3ae17508782c80bc00002d26a092b094409664511f70e786822ed14688a839c16b09082cc0bc00002d2645b2af93ec9504551fa8e746742e614388b43a017e09102f80c800002d25eb12a793d092e4391ee0e1066e2df14108a039816b08902c80a600002d258d12c0146498245c1fd0e7069a2ee14b08e03bc18909503040bc00002d252f92bb944c9684601fe0e906862e514708cc3a017a08983140c600002d24d3e2b0941c9504471f90e846962f014c08cc3aa16f08a82c80c400002d2478f2a493c09244321ea0dd463e2cc13b887438216008502c80b000002d241bb2c314a89984661fd8e786a42ea14608d839a17609103000ca00002d23bd92c8148498e47120d0ef06be2fc14e88bc39a17008502e80bc00002d236012bd146c9764612050eac6982f614908dc3b818408e82e00ac00002d2302b2c014709804652070ee46c030715389203d818308d030c0da00002d22a492c714dc9b047e20f0f046c030515609203c617d08f82f80b600002d224712c0148c9864632070ef86ce31015309003aa17608a83080be00002d21e8f2bf148c9684591fc8e806a02f514888ac3b417a09203000ba00002d218e62a913ac93043f1f78e5c6762df13d085c39016608402ac09e00002d213002c694b49ac47220a0ec46bc30215089243c818609403040d000002d20d4b2af13e09484401f38e2465a2d213a885c38015f08682dc0c000002d2078e2b514349724561fb8e6c6902df14008bc3b416908202a00b000002d201b52c494a099647220c0ee86c22fc15109083b018509103100be00002d1fbd32c694e09ba48c2158f106d430415189103c018008e03000bc00002d1f6262a793d493843b1f68e7c68a2e414388c038a16b08902c80ae00002d1f0512ba946c9644551fa8e6867c2d813b086838a16a08702ec0bc00002d1ea802b7946c9964622018ec06aa2fb15089043b417808c02e00ae00002d1e4a92bc947c96c4632058ecc6ac2f214908ac39416708882b40b400002d1ded12ba94589884612028e946922f5147889c39216708182cc0b400002d1d8e32cb94dc9b44762098ee46be2ee14808cc3aa17f09403000b800002d1d32a2ad14209524451f60e2865a2de13f887037416307c82bc0b200002d1cd7a2a213ac9264331f08e0867e2dd142888839817208a82bc0b400002d1c7c72af941496444e1f50e4866a2dd140084036615e08402d00ac00002d1c2032ae93e892a42a1ea0dd06342bf132083c36e16008a82f40c400002d1bc122c894e49a646b2090ef86ba2f214a09043a416a08782dc0ac00002d1b6412b7146497445e2020ea469c30015489203d617f08d03000b800002d1b07f2b2940c93e43a1ef8e086622e214088a03b618409002e80ba00002d1aacf2ab141494a44f1f88e3c6662dd13d886837616108482e00c600002d1a5092b1143096845c2030e8c6ae2f714909183c617b08a82e80ba00002d19f1b2c694cc9ac47420d0eec6c630315088b438e17f08c82cc0a400002d199442bb94709824632008ea86ae2fd14d08e83be17e08f83000cc00002d193762bd14649684602040e9c68e2f415188fc3c217a08d82e80bc00002d18d912c514c49a44832140f2c6dc2ff15109103d018409083040c400002d187e42ab93ec94243e1f48e0866a2d713b88b439416e08a82ec0a800002d181f52c914e49be48c2170f306e632215b89583da184094830c0c800002d17bf62ce15109be47720c0f0c6c630015088f83c0181091830c0c000002d176312b9142095845f1fb0e7868a2f114a08ec3b618409703300cc00002d170482c794c49a848520f0f006b430815489283d218f093031c0d400002d16a712bc146496a4602018ea469e2f614988d43aa17608c82f00bc00002d164aa2bc147497a45f2020e906822ec14688ac39016a08682ac0b000002d15ef32ac93e09424451f60e7867a2dc13b086037c16808182ac09e00002d1592e2ae141093e4471f58e4c6882df13f08943a817408882c80ba00002d153592bd94889804581f98e6866e2dd13e889c38e16408602f00ae00002d14d792c094689784652010ea46842e013d885437616b08c02e00b6000)) else (if i < 474 then (if i < 473 then 0x2d42df12c414dc99847620d8ee06c22ff14d08dc3b617f08e82ec0be00002d428172b9947897a4692040e9868c2e614788b038a16c08b02f80c800002d422242c614bc9904692018e846b02f314688b43a617a08a02e80ce00002d41c6a2a793fc93e4481f88e2466a2df144889439217108802dc0a400002d4169f2b5144496a4561fe0e4466a2de14588ac39817208402cc0bc00002d410d72b214489764542000e6c68a2e014608c43b417a08e82f00c200002d40b082bb944c98246e2010e9c6962ee14808fc3c617f08f03100ba00002d4054d2ac940c9544481f88e4c68a2e313c085c39817908f82f40ce00002d3ff9b2aa13f494c4501fd0e6867e2e7141089838e16d08803040cc00002d3f9d82b594589764672088ee06b82f314c88f03c217808f83040c800002d3f4192af941896444f1f80e7067e2d913c084436a15207c02940ae00002d3ee392c094a49a247920d8eb869c2ee14d890c3ce18308c02f00c400002d3e8782ad93dc93e4421f30e386582d713c088038817309003280d600002d3e28f2c294ac98a46f2078ec468e2f814888cc3ba17a08582dc0c400002d3dc8e2d095149b84752108f046b02fd14f08f43aa16b08f02e00a200002d3d6aa2c414d49b247a2128ee46b22f314908cc3b818b09403280b200002d3d0f12a813b893644a1f38e4c67e2df14288b839a16c08802c80a000002d3cafb2ca14b49964712098eb469e2fa14888983b017c08c02e00bc00002d3c52c2b794609644501f50e406702e114108a83aa17a08e03000ae00002d3bf562ba146c98845f2020ebc6ac30414e08cc39e16c08f83100c200002d3b9952b5944c97c45f1fe8e6067e2e614608cc39017a08a82d40b200002d3b3e02ae93fc93243d1f78e246742de14108ac3a017108e82f40c400002d3adfe2c014b09864652068ea06902e714608cc3bc17608d03040c000002d3a82e2ba144897a46e2098ee46ac2fb14889183b417908882dc09e00002d3a2542bd146c9804592070e9c6b42f715009183d018e096832c0d600002d39c992af141093c4401f10e406782d9141889038616408b82f40bc00002d396e92a8143093c4401f38e406722d913e088839016808482d80ba00002d3915429b93708f641c1df0da06362bc132882c36c15a08482dc0ca00002d38b892bd94889864662010e8067c2e714d88d43ac17e09583080da00002d385de2a613a092c4381f40e4866e2d1137886838c17408702b80a000002d3802e2a613a892c43c1e70df06442d513e089039816c08f82fc0b600002d37a562bc948497a4551fd0e586662da13f889438a16208102ac0ba00002d374a02ab94189484591f88e506582cf13d889c3a017f09182ec0ac00002d36ecc2b3943094e4461f30e486522d714188ac3bc17208702f40c800002d369062b3940895644c1f80e4867e2de14308a438a16208682d00ba00002d3637a29893709164381f08e3064e2cc138887437c15408182a009200002d35d8e2c494b499a47720a8ecc6ae2eb14788a83aa17b08902d40ba00002d357c82af93e493a4461f28e186582ce136886437c16408602b00ba00002d352172a9940c94e45b1ff8e5c6782d513c089c39216808782c00b000002d34c4e2b3942895644f1f60e546882db14288a439a17608f830c0c000002d346a02ab93cc9204311f10e2c65e2d314308bc3b617808f83080c200002d340bd2c714c099646a2048ec86c230115509283d818409302f40dc00002d33af62b3943095a44d1f70e286542d713b089438816808402a80a800002d335122c3949c9924742088ec46ac2ff151893c3e418909603400d200002d32f382c094909924612048eac6962e7140888438a16808702dc09e00002d3296f2b314049304351ed8e086462cf13b887437a16e08a82f40ce00002d323bf2aa93e493043a1ea0df06382c5135884437616a08502ac0aa00002d31de82b9147897a45d1f78e686862e614408d43b817308782d00c800002d3181e2b8949099847820c0ef46b4306152090c3be18809803040ca00002d312392bf148898a4682030e8868a2e214308ac37c16808902d00c200002d30c672bb146096e45b1fe0e7869a2ef14808c03ae17308a02d40aa00002d306702ce94f49ac47120a8ec06a02f714f090c3d418709303100c600002d300ca2a693c493e44a1f30e106642d713d089439016908e03040c600002d2fae42bc94a099247420d8edc69c2fa14c88d03cc18609683280cc00002d2f51a2b4943c9404421f20e4467a2dc13f089039016d08b02dc0c000002d2ef322c114a899646b20a0eb46a42f214988e03ce18c09103040c200002d2e9752b3944c9744552000ea46962f814788bc39e16d08402b00aa00002d2e3a72b7147097a45e1fd0eb06942ec14d08ac3a416f08a02f00b600002d2dde42b3141c95a45c1fc0e5866e2e014008c039617608d02fc0c200002d2d80e2be148c98c46f20b0eec6c430215609303cc18709003000c800002d2d2512ae940494a4451f18e186522cc138084837c16a08882e00b400002d2cc7c2b8944c95845d1ff8ea869a2f214c08fc3c218109403400c200002d2c6992c094809864632078ee46b230315109083c018209003100c200002d2c0ce2b794389664512010e8c69a2f414908e03aa17108c03100dc000 else 0x2d5a20d2b2141895444b2000e686982f714a89183be18108e03080aa00002d59c672a493cc9264381f20e4c66c2d013f087c3ae17108983200c000002d596922b9945c9884742088e9c6942e714408b03a617309202f00ae00002d590b32bf94509644571fe0e546782e014408a439e16f08982dc0be00002d58adf2bb145c97e46e2078ec46a02f114c89003b2185092030c0c800002d584ee2c814f49bc4762100ef86aa2f914b08c03b417208782d00b200002d57f232af14149504541fe0e906802ee14808b43ae18109803380ae00002d5796f2b193f895244d1f80e4866e2d814208a83ac17608c02f40d800002d5739e2b9143496445b2028e906862e5146089c38c17208b02d40b800002d56dcf2b914709864752138f046c82f914f89103c018009083040ca00002d567f82bb947898245f2000eb06a62f514e88e83b217d091831c0c200002d5622b2b113e494a4421f70e4c6682d813f085c38816c08b82ec0b600002d55c612b6946896845a1ff8e9868e2ec14a08a039a17308b82c40ba00002d5569a2b1942c95444e1f60e486742e8143889439e17909003200c600002d550b42c2947c9a247820f0eec6aa2fd14e88bc39e17408e82ec0b600002d54aef2b3941493e43f1f00e186662d714388a43a817108f02f00c600002d5452f2b4140893a4441f28e1c64a2c7134883837816a08a82f40b400002d53f512c114a49884612040ebc6982f314b88d83b817809082f80b200002d539772c294a499e4732040e9869e2ef14508bc3ba17a08f82ec0bc00002d5338f2c2949c9a846f20c8ef86be303158892c3de18708d02e00c800002d52da92c214a898045f1fd8e4865c2cd136883c358158081029c0ae00002d527d72b8147095a4571ff8e746842e4140889038816f08902cc0ba00002d522002bf94709a446d20b0eb069a2f614c88e03ae16d08e82e40c000002d51c4a2a993d493c4421f40e686762e4145887c38215f08202b80a800002d5163e2cd95009c047d20a0ee06ae2fb14b88d03b216f08d82f00b600002d510a82a3138c9124261e60ddc6382c3132884837a16308682d80bc00002d50af22aa13b09304391e80de86502cf13a0838378163086829c09c00002d5051e2bb143c9684521fa0e886822e213e087c37e16d08882cc0a800002d4ff4f2b814609624571f80e706922f014508d43be18208b83080d000002d4f9802ba94489624541fc8e6c67a2db142089c38e17908b02ec0bc00002d4f3dc2a1139c91642c1e40de06562c4136884837016108282b80a600002d4eddc2d415309e248a2170f246e030414f09143be17d09003140c200002d4e82b2ad942494a4421f98e606542cd139887038217308982e00bc00002d4e2372cc14f49b44782118ee86c62fc14d88d83aa17408782d40c400002d4dc8c2ab13f49504431f50e4866e2e013f08a438616508482e80be00002d4d6952cb94d49b047f20e0ef46c6304154893c3d818a09803340c200002d4d0b72c494989a04792098ec86b02f814a88f03b817208602e80ba00002d4caf72b194149624581fa8e406662d714188b039e17508e83080c600002d4c54b2a4938492843f1f10e306582e0142889837416808302980a800002d4bf412d194f49ac47920e8eac6aa30014d08e83c417509003080ba00002d4b99e2a714009324361ee0df06402bc134084037016208302b009e00002d4b3db2af14189524611fe0e8c6782e814588a03aa17708c82e80ac00002d4ade22c814ec9ac4772088ed86b82fe14e89143c418109283240d000002d4a8182b7143496c4551fa0e546742e414188a83a417608a02e40b600002d4a2652ab93f094243b1ec8df06522c6131083837016008382c40ae00002d49c7f2c594b49a447120f8f106b62f914e08dc3c2184096033c0d200002d496b52b8145097c4682050eb06a42fd15088f43c218b09102d80b400002d490d92c194709784672040ec46b22f914d08b83aa17f090831c0ba00002d48afa2bd146497e45a1ff8e886942ec143889439817308682b80aa00002d4851b2bc94749764572010e886902eb14988e43ae17508c02e80c200002d47f692b094049484571fd8eac6a42ef14c89003be18109003100d800002d479752c714f09b047420b8ec06b42fa15309203d417908a02f00c200002d4738f2c694c89ac47d2100f106bc2fd14d090c3c818108e82d80ae00002d46dd42ab13f093e43f1ee0dfc6622d813d888838a16d08782d40b200002d468162a993f094a4431ef8e446722d813d089c3a416b08b82dc0b800002d462542b2942c96844a1f78e486622d913a086837216307e02880b400002d45c932b3142895c45e1fd0e9468e2e614388f43c018108d02f00b200002d456e82a9140494844b1f70e3c6602cd139886c37216708702c00b000002d4510f2ba94709824702058ed86be2f514c892c3de19509882fc0c800002d44b472b8145496c4601fa0e786742dd14408d438c17508a02d00c800002d445482ce14cc9b84822110f0c6d2308157092c3ca18a09703480c600002d43f652c2149498646920b0ef46ba30915308ec3be16b08682f00c200002d4399e2b5941493e4481fb0e606622cd134084438216d08902f40ac00002d433ce2b8941895c45b1fe8e7c68c2e2141887c37c16d08a82c40b8000) else (if i < 475 then 0x2d7165b2ca14cc9a247620e0f046ba30615609543d618809683340d800002d710822c0946495a44f1fe8e686882f514a08c43b817a092031c0cc00002d70a972c4949c9924681fe0e7068c2ed14908cc3a017708f83100d400002d704b02bf948098046a20d8ef86d22fe14d08e03b217908c02e40ca00002d6fed32bd946c9804682058e946a22e9145087838416608682a80ac00002d6f9142b093f894e4461f78e5067a2db13e889c39216007f829c0ac00002d6f3442bc148499a45d2040e9067a2e9143889839417108782ec0ba00002d6ed622be94a898646b2080eb069a2fe14b89083bc17f09383080ca00002d6e7712c894c89bc4862190f386bc30c152892c3c418c09283180ba00002d6e1af2b0941895a4511fb0e9c68c2e814788d03b818209083140b200002d6dbee2ad940896c45d1fe0e8c67e2dd14908c039817508b82f40ac00002d6d6252b5945c9624612020ebc6b02f014b09083c017b08e02c40ae00002d6d0362ca94fc9c04882118f386d4313157894c3f019009683240ce00002d6ca9629c13509144391ed8e246662da14088c039a16c08702c40b400002d6c4b52c394b499647820d8ef46c02fb14c08dc3aa17b08882c00c400002d6bed52c3147c97246b2088ef46a62f514b08dc3a617308b02e00c200002d6b9212ad140c9644541f90e6467e2db14388a83a417408b02dc0ca00002d6b3462bf94749924601ff8eac68e2ec13b889438616307f82a00a000002d6ad9a2a793f89384451f70e306482cf13b087436215b08482c40b800002d6a7bd2c094909784531ff8e9c6882f714608d03b617808f82fc0bc00002d6a1f22b4144097a4692090ebc6b22fd14e09083ac17409003040be00002d69c162c014649844722018e5c6782e3142087c39016907c82980a200002d696402bc944896444e1f80e446702dc14408b039016a08802b40b600002d690682b5145097045e2030e9869e2fc14d08f03a416b08582d40b600002d68a7c2c794bc9ae4832148f1c6e230f15809183d018009283140cc00002d684a22be94809944672060e6066a2cd13c886c38016608182bc0ae00002d67ee62a993e494244b1fc0e7869e2f814f88e83bc17508c03040bc00002d678f12c714a89884672078ecc6b02fe14b08f03c417d09383180be00002d673302b7143896445d2020e6c6802e7140087c37c15f081829c0ae00002d66d592bb945c97045b2028e906a22f914788bc3b818609183200c800002d6675c2ce14e89b44762080ecc6a02f214708d43a617b08d03140bc00002d661b52a713d092843e1f58e486642d313c089839416e08a82e80c400002d65bf92ba145097c4692008eb46a22ea14808d43b817208c82d80b600002d656072d315109d848d2178f0c6e231d15809283d418909082f00ba00002d650322bb943897045d1ff8ea868c2f514b88bc39e17708e02fc0b400002d64a302cf950c9c24812118f246e030f15588ec3aa18308f02e40ba00002d6444e2b9946c97645d2028e706822da13d088038616808a02f40ba00002d63e8b2b594489384501f88e746802e213f08a438a15f080829409e00002d638c22b4943495844f1f88e446802dd13f888c3ac18109203040b600002d633032b3146096c4641ff8e7c6942f014d092c3c018809382f80b600002d62d422b3942495444d1fb0e4865c2cf13d887438615d08782b40b600002d627812b1142896c4501f60e4c65e2d413a888038016e08c82d80b800002d621c12b494149504461fa8e5466a2e4145888839217a08e03000cc00002d61bf22b794489704541f70e6c6822e013e087438416308b02f00b800002d615f42ca14b49a646d1fe0e406562c5136084c38a16208582b80ac00002d610622a0137c90a42a1e38da06262bf132085436015c08182cc0aa00002d60a932b914309664581fe0e7c66a2c6130082c37816e08f02ec0ae00002d604ac2c314bc99846a20b8ea867a2e414b08f83b017d09082f40cc00002d5fee62b3142097045c1fc8e986842de141087038817508a02f80b400002d5f9032bf143c9804501fc8e7c6822e9149089c37c15f08182800a600002d5f34a2ab93dc94044a1fc0e706622d5140889439e16908782e80bc00002d5ed6d2c0949c9a84762070ed469c2fb15809103b617208c83080cc00002d5e7a52b9944495a44c1f50e3464e2cd136884036615408302a40aa00002d5e1d82b894209544561fa8e4c6702d1139082c37c17008b83000be00002d5dbfd2b9946c9944642040e8c6722ea14688e03ba17f08d03080b800002d5d61d2bb948c99646f2120edc6ae2f514a893c3c018609383040b800002d5d0462ba14449744642028ec06a02fc15488d83ba17608d03080bc00002d5ca722b8143896c44c1fb0e386722da13b886038216608902c80be00002d5c4a02b4944c96a4621fd8e906822e314508d83a417108602d40b200002d5beee2ab941095a4491f98ea068e2ea14488d438a16908882d00a800002d5b9482a213909264381ee0e106682c513b085438c16b08282c00a800002d5b3742b8945896845f2030eb46b42fb14888b039c17708c02b80a600002d5ada32bc94749684591fc8e6866c2da14388cc39e18009083040ba00002d5a7c72c014a897a4632048ec06922ea14708dc3cc18609183380d6000 else 0x2d88ac22b5144c9624551fe0e7467e2ea14809003c218909383240ca00002d884c72c614c499647720d0edc6c230415189203d817c08c83180c600002d87ee72c194a09904612058eb06902e114308d439c17008502bc0be00002d879162ba946098246420b0eb06ae2fd15088f03b817608c03140c800002d873522b4944896645c1fa0e706a62ff15289303d818a09782ec0b800002d86da92a593ac94043c1f18e106662d914088a039a17608a03140c000002d867c82c3948c97e4622040ebc6982f514a08c43b418009603140ca00002d861d62ca94b49a647020a8ee069a2f414a08a439816b08402b80ac00002d85c012bb947498c46c2090f046b42fe15309283d418d09182f40c600002d8564c2b194289444411f60e706742db13c88d03b217e09202f80be00002d850522cd94ec9c848620f8f146be2fc15209203ca18309103240d200002d84a872b694349644511fa8e586602d113d087839817608802fc0be00002d844bd2b6144c96c4581fc8e9469e2fa15189043c217e09603340e000002d83ee02be948497445d2038ecc69c2ec14308c839c16908802e80b000002d838fd2c5149497c45a1ff8e8c6862f215288fc3a817a08f02f40bc00002d833372b914749884642030e9868c2f114c88d03ae17c09282fc0bc00002d82d5b2c1148899647120a0ed46ac2f714889103d817f09003240d000002d8278c2b994349604501f88e7067c2e2143089c39216a087030c0c600002d821d12b4141894e4451f10e2066a2d213d887838416b08502d00c400002d81bc72d695349d848f2148f306d630915809203ba17f09183140c200002d816242a813dc92a43d1ef0e1064a2d313a084836e16808802d80ca00002d8103f2c894e89b447e20b0ee86be2f414908d43b017208a02e80ac00002d80a522c694c49ac4762048e8868a2e014188a83a217308c02f80c200002d804812b694649944661fc0e7468e2e714708dc3a0184096032c0ba00002d7fecf2aa13dc93243e1f58e5066e2dc13e087039016808982e00c000002d7f8dd2c314b899a4722080ed46a62f714b08d83aa18008c02ec0c000002d7f2eb2c6949097a45e2038e7867c2ee14908ac38e16108302b00b000002d7ed1c2b7144c95e4561ff0e606882eb14909043c017508b02ec0ac00002d7e7752a813c492042b1e70d9c6362c4133881c36015e08002840a800002d7e1c02aa93e494043f1f48e446542d1138085c38e16a08b02f40bc00002d7dbe22be94889984602018ec06a42f714908f03b418108b82d80ae00002d7d61b2b5943096644d1f10e2865e2d813e889438417308382d00b800002d7d0402b8944c97c4642050ea46a630315509203dc18708e82ec0c400002d7ca7f2b3141c94c43f1f20df86442cb137084437616208182d00b800002d7c48d2c894e89b647920d0ef46ce30715189043c617d09103180be00002d7bec52b594189464401f08e286582e213d086c37e16908803000b600002d7b8dd2c794c89964642020e9c6a62f615089203c818809182e40b400002d7b3202af142c9564441f78e6c66e2da140089838616b08882c40ae00002d7ad582b7141c9544541fd0e686882ef14809143bc18709603100c800002d7a7872bc945099245f1fd8e6067c2dc140089039416b08b02e00ca00002d7a1a62c394949a44712098eb869c2f914b08cc39616e08882d80a400002d79bd52c2147097c4682078ecc6882e114608883a617608d031c0da00002d795ef2c494b499e47320c8eec6c631115589203d818a09183080be00002d790252b413f89404491f08e186542d713e08983b816c08b82e40b600002d78a422c4949898046a1fe8e686882d8140088038216c08582c40a600002d784432c814dc9a647020c0ef46ae2fd14d09083d217c09003340c800002d77e642bf949499a46b2070eac6a22ea14588c03aa17e08f82e00b800002d778a42b8142096a4551f78e586862e414408a83b218008e031c0c800002d772f12ab93e492643f1f18e186582d513c888838215a081828c0ae00002d76d432aa13d49344351eb0de46502c1132082835615e07e028c0a800002d767842b1144495e44e1fb8e6c6842e113b885037816308582c40ae00002d761942c714a499846f20e8ec86a62ed146089039a17409002e00ca00002d75bd22ac13e09364461f70e706882e113e089c3a417008902ec0c400002d756162bb148c9984652030ea86902e9142889c39016c08902dc0ba00002d7501e2cb14ac99046e2068ebc6b030315889203ca181090034c0da00002d74a582b4141c9404401f40e486722e2144088436c15b08902e00d000002d744852bb146096445e2040ebc6902e7140086c36c15307d02940c600002d73ed62a893d092e4311ed0e4066e2da13a087c39616b08682e40b400002d739322a293ac9264301e58dd062c2c713a883c36415608002880a000002d733842a7940093a4421ec8dcc6442c4137086438416608902c80a400002d72dd92a613d093443e1ee8dfc64e2d7141087c39416a08a02f00c000002d727fc2bc14709924682058ec06a62f814e89003b017808b03100b600002d7225a2a313d892c4391ed0e1064c2c8138084035e15c08082c40c400002d71c4b2d395249de4882130f2c6ec31015789483ea18f09583240c2000))) else (if i < 480 then (if i < 478 then (if i < 477 then 0x2d9fdd62b614509884662060ea069c2ea14988b83b617508c02f80c200002d9f7e42c694e09ba48a2138f006ce30d15288ec3bc18709003000c400002d9f2332ae14089524451f80e446742df14508b839016f08682e40c000002d9ec4e2c514c499c46a2000eb86962f814d08ec39e16d08882dc0c000002d9e69a2af14149644571fa8e486602dd140089439617208c02ac0b800002d9e0f62a513c893a4451ee0e1464c2c613a087437a16708682d80b600002d9db2a2be144c9884612000e9c6902ec140889037416c08a02d00c600002d9d5462c694b09b647c20d8ee46bc2f714a88e43c017608982b00b400002d9cf562c514bc98645e1ff8e7469e2ea14788d43aa17c09182f40be00002d9c9872b6147097c4632010e806762d914188943a417508982e00b200002d9c3af2ba94649764672030e986802ea13f886837416508982d40bc00002d9bddb2c194b499a46b20c8ef06c430115089003be18009182ec0d400002d9b8112b4142896a4561fb8e7068e2e214708dc3b417909103140c200002d9b23f2c1146897a4571fd0e6867a2e314388c039617008782e80d000002d9ac672c0149099046c2050e946942eb14c08dc3b617e08b02d00a400002d9a6902c094a499047520a8f0c6d630815389183c4181092031c0c200002d9a0922cd94cc99a46c2060eb06a42ee14a88ec3b618608e02f40b400002d99af22a393b092042d1ef8e286642cf138084437016608602ec0be00002d994f72c314b89ae4712080ef06bc2fa153891c3cc18b09b03300de00002d98f342b5141894c44f1f98e7c69a2e914408ac39417c08902d40be00002d989812b4143c98445c2028ea86882eb14b08ec3b017808b82f80ca00002d983ba2b394449784622090eec6be2fe14c88f43be17f09002ec0de00002d97e182a3139090242f1ec8e106522d613f886c38216108102bc0ae00002d978342c4146498e4652020ec86ac2f114a08ec3b218509403200ca00002d972572be148097a45b1ff0e8469a2f514808a439216508902c40c400002d96c8c2b8146898c46e2048e8067a2ea14c08e83c018608f83300d400002d966c02ae141c9624551f98e4c65e2e613b889038816608982e40c400002d960ff2b1144c96044b1fe0e6c6842e8142089c39416e08982e00be00002d95b392b214109544451f30e306822e7144089438e16808602d00b600002d9558d2a313ac91c4321eb8dd06242bb12f886437016408502b80b600002d94fbb2be948098445c1fb0e5c6802e514508d83b418508f83140be00002d94a172a713989224361ee0e1c6702e8148888838416d08c83080c600002d9443e2c114749704541f58e7868e2e614408c43b817208a02dc0a000002d93e8f2ac942096644f1f38e446722e314708b83a417508a82d80b600002d9389a2d1152c9dc48a2120eec6b02f914d88f43b218108e83140bc00002d932db2b2942c9584491f98e5c6642c8133884838216d08a82f40b800002d92cfe2b9948498646c2070ebc6b82f2149889c38216908a82bc0a200002d927142c614c89b44732060eb06862e914c88dc3c017f08c02fc0ca00002d9214a2b494349644511fb8e7866c2d513c889838a16208702b80b400002d91b7a2c094749624541fe8e686722d413e089839016708382a40b000002d915b02b8945c97c4742090eec6be30715488fc3c0181091031c0d000002d90ff42ad93dc9364421f18e106602d813e885837816208382f40ba00002d90a3a2b413f89424481f58e606722ea14988d03b017308902cc09e00002d9046b2b5142496e4662000ea06a22f614b08cc3a217209103080c000002d8fecd2a193c091a4321ee0e1064c2c9135885037616108682d00ba00002d8f9112af940c9664531f70e246582bd135084c37816b08982e40ba00002d8f3502b5946096644e1fa8e606822e414288bc3a017508d83240cc00002d8ed852b5943c97246420b0ecc6b02ff14d09103c417f093031c0c400002d8e7782d915709fa4962150f406d630915008e83ac17608e83380c600002d8e1ad2ba145897445b1f98e686802e214588c438816308282a40b400002d8dbee2ae143c96445c1fc0e7067a2dc13d888c39417308982d80b400002d8d5f72d0152c9e048e2160efc6ca2fb14a88e43aa17708d03000d200002d8d0542a993f893c4381eb0df463e2c1133883837816108b03040b600002d8caa42a993c492c4331ef8de063c2c7135085037216008082cc0aa00002d8c4d22b714749884702088ec46b830515209083c217708902bc0ba00002d8bee62cb14d89c04892188f3c6c630515489403dc19009483100c600002d8b8e72cb94f49ca48620d8edc6ba2fb15089303da18b09383080c400002d8b3242b1941c95a44c1f70e5867e2dd14288c839c16508782c00b000002d8ad8f2a013889064281eb0de46402c5130883035615908102a40a200002d8a7cc2b093e09444361ea8dfc6602d013d085837616008102c40b800002d8a1f72ba147899a4662058eb068c2f814d09003b417d08f03000ba00002d89c0d2c314a099245e2020e746822e214088d839e16f08a82d40c800002d8966d2a793a89144331ed0e0c6482ce13f887037c15b08102b00b200002d890882c0948c9a64732088ec46a02ea14908f83b417f09082f40ae000 else 0x2db70b12ae140894a4511f28de863e2c9133885437815d08102cc0b600002db6afe2ab14249524421f50e486762db143889039617c08d02c80b600002db65102c894909824632040e986842e213f086c39216f08982dc0a600002db5f2f2c2947098a4682090ed86b830215a09803de18b09283040ba00002db596e2b2943c95644f1f88e7467e2e5141088c39816b08382ac0ca00002db53d02a393c093a4511f40e386502ce13b087037016108802d80b000002db4dfd2bb947898c46920a0ee86b02f614988b03a616e08482a80b200002db484b2ad141496a44d1fa0ea06942f2143888838216b08682d009400002db42ab2a493a493a4461f70e446842e113e886c37a16108682b00ae00002db3ccc2b9944497244e1fc0e746902e714508ac3a218208d03180b000002db37212af93f894c4411f18e4867c2db14108b838a16607f82a40b400002db315d2b814549604511f88e5066e2db14088a438a16508602b00a000002db2b862c214889684571f90e8c68c2e914388ac3ac17c08e02d80c000002db25e92a2138c90e42d1e68ddc6522d714008b439616a08402d40b600002db1fe02d815489e84912178f306d230a15709103c817f08d02ec0a600002db1a252ae93fc9524471f80e486462c8137883838017108802d40ac00002db14762aa13d093a43b1f08e2c6682e414608bc38e17608c02f80c400002db0e8a2c6949c9ac47b20f0f086be30114b88d03aa17608e03080ac00002db08a62bf94a498646d2020ebc6a22f214a88d83b617e08e83040c600002db02fa2a493b092c4391f10e286542c7137083436815f08482cc0a800002dafcfd2c914d89b047b2120f146ba2f914d08d43a817008a03080b000002daf74b2ad140893844d1fa8e6467a2e914888c43a417e09583240e600002daf18a2ab13c092442f1ef8e0c63e2c112d87f034615108102d40b200002daeba72c594c09ac4712070e9c68a2f614588a03a016f08c82e80b800002dae60629e13989284431f28e286442d013a085837815e08682c80b800002dae0542a913fc9504532018ee06b430515308ec3b617108982ec0bc00002dada7f2bd94709744621fe8e786822e014688e43ba17708f03040b400002dad49a2c614a098a4661fe0e6866c2e1142889c39616908582d00b800002dacec62b9942495e4571fe8e8c6882ed14989043ba17608882e40b800002dac8f02b6142094a43b1f10e386522d613d888438e16708502d00ba00002dac3182c514b89804642040ea86b42f014708d83ac17b08e82d40b400002dabd552b194289524491f30e1865c2d113f88a03aa17b08b02fc0c600002dab7952b594449564481fa0e6466a2e313f08b43be18809203140b600002dab1c92ba946496a4591fe0ea86aa30115409203d6190094833c0bc00002daabf52bb143c97444e1fa8e6c66a2dd13f0890396173093030c0c600002daa6062cd14fc9c047420b0eec6be30715008d839c17709183000c800002daa06a2a0939c91e4361ec8dd86462c8136085c37a16a08982c40b200002da9a822c5146c98245e2008e946862e014708d03aa16d08b82e00a600002da94a82be944c9824622018e906962ee14288d83ac17d09403000d200002da8ee12b9945097846d2088ea86a22f014708e03a017208882a40a200002da89362a893cc9424451f30e246562d513f88b839016c08882b00b000002da83502c194809a247c20b8ed069e2ed14608a438216508b82ec0b400002da7d892b1942c9484481f78e4c6802de14688c83b618409102e40c200002da77952c794a498c4642030ea867c2e7140089c3a417b08e03100bc00002da71bb2bb946c9764692048eb46922ee14a08d039e17908b83080c200002da6c082a593b094444e1f70e446722dc14188ac39416d08f03140b200002da66432b3141c9624591fc0e546702e213e08a039417308a82f80c400002da605f2c114a09864652040ea869a2f714e89003b417a09082fc0be00002da5a862ba144095c44e1f88e3c6682d614108943a217508582cc0b000002da54d92ad94109424511f90e6067a2e614308b839c17b08b02f80c600002da4f092b9145095c4401f70e4065a2d113a888037c15d08582a80b600002da49402b2141094c4461f60e8068e2ef14908b43a416608902d40b000002da43762b093e094c4541f80e6066e2db144889c3a018909683080c200002da3dc52a713a89224311ed8df06482d914088ac3a616e08903200c000002da37e62c0147c9744642040ee46b42ee14708b439417108682d80b000002da31dd2d5950c9ca48a2140f206be30515889183b818008f02f80bc00002da2c102b914609744611fe8e846a62f314a08cc3b017c08c82e40b800002da26502b214309664582030e8066e2dd14508d03b217208e82ec0bc00002da20732be949c98445b1fd8e7c68a2e714508c839816d08a82d80b400002da1aad2b0141c95a4561f90e506622d313d884037015e08602c80ae00002da14d12be94889824642060e9868a2dd14608dc3ba17208d83000b800002da0ef92b9946097a45f2070ec86b42fa15009303c618209182e40c200002da09582a713dc9324421f70e586802e0140889438e16d08b82c80a200002da03a32b314209644551fd0e546722d513e089439a17508d03180ce000) else (if i < 479 then 0x2dce4b22c794d49b246f20b8ee06bc2fe14e08ec3b016708c02ec0c600002dcdf012ac141494e4451fc0e546742e014308ac39e16e08d02f40a200002dcd9552a893c492a4481f98e506862e7140089038417208a82f80c400002dcd36e2c594889824672070eac6b22f814788d03be17208c030c0ca00002dccd812c814d09a847b20b8ee06cc30d15309383f419409783100d200002dcc7a22bf148499a4702078ec06a22f914d88fc3ba17c09183240c600002dcc1c52c514849884682048eac68a2da140088439817708e03140d800002dcbbd52c814a89904642008ec86822e714488b439817108502ec0be00002dcb5f82bd94949a64712098ed06b42ff14e890c3bc17d08782d80b800002dcb0262b9948499e46c2068ee46b82fd151890c3ca17f08d02e80ce00002dcaa6d2b0140c95845d2028edc6c02ff14a88c83bc17808c82e80ae00002dca4aa2b814389544501fa8e4c67a2d5137886437215e08102ec0bc00002dc9eda2ba94a09964712088ebc6be30014f08cc3ba18208e02e00c000002dc99192b194389624491f88e5c67e2db14388a839a16e08e03140c000002dc93232cc94d89bc47f2150f186bc30515089143c818109083380ce00002dc8d362ca94c89a246f2060edc6a42ed14c88c43aa17e08e03040bc00002dc87762b414009504501f98e506682cf138083c37815d08502cc0ac00002dc81992c414b09ac47d2108f146ac2f814c09003b217f08e02d80c800002dc7bef2a613f494c44f1f58e406642d113e089c396178090830c0ce00002dc76082c994ac99e4692050ebc69e2fa15189343d818c09303180b800002dc70432b6945c9744632018e786882ea14308c03a617408902e00ba00002dc6a972a813ec94444b1f78e446722e514108cc3bc16f08682e40b600002dc64bd2c214c89b647d2108ed86c8303150090c3c218208e82e00c200002dc5eef2be948896845d2018e9c68c2ea14888b83a017908f02ec0bc00002dc59392aa93cc9424411f38e4066c2d713b087438616c08902b80a800002dc538f2a793d491442d1eb0df465e2d913d087037616808b02fc0b000002dc4dbd2be145895a45d2010eac6982e714608e43c618409483340d200002dc48172a693d892843b1ef8e2866c2e1145088c37016507d02b80ac00002dc422d2c2147c9aa47a2098ed86962f314f08e83a616f08782e40bc00002dc3c412c494b89a84712088ef06a82f414788e43a417908982dc0a800002dc36702b3141494843f1ef0e246622cb139085037c16108182b80b200002dc309d2b9943093c4471f58e6066e2d813f88a038c16b08582b00c400002dc2aa62cd14dc9b447820c8f186c4308150891c3ca19509683240c800002dc24a12d995609ea4902180f446de30715709143e018609683400c800002dc1edc2b494289524501fe8e7867e2da140887c39016908882fc0bc00002dc19032bf947c9824692078ecc6c030514a88e83ac17a08f02f00b400002dc132b2bc146097a45b2010ea86822e314188b83a618309503040c400002dc0d492c1946c98446a2070e886702dc143089839416108202dc0bc00002dc07832b7143095c44d1f78e6c6722ce13f886838816908282c00aa00002dc01b92b6141c9464441ef8e2c6762e5146889839e16d08a02f40c400002dbfbdc2c214ac99e47b2088edc6ba30914d08f039a17008682d40ac00002dbf6342ac13f893843e1f18e2865a2d013c085c37a15d08282a40a200002dbf04a2c2149c99c46b2098ec06a22f714f08d83b417b09003000c800002dbea6e2be948098e4662028ec06a82f214a88ac39016c08a82ec0c200002dbe4ae2b2943095a44f1f78e4865e2de14288b83aa17708b83040b400002dbdedb2be94789784691ff8e5465e2d3139885437e15e08582e80b800002dbd9172b313e89364471f60e2c66a2d713b887c37015a07d82b00a200002dbd3222c894c09a24692028ea86a62f514409183b618708d02fc0b600002dbcd5c2b794389504551f90e5c6662e614788f03b217d08e82e40aa00002dbc77d2c414d89ba48621a0f206c8307157091c3c018409102f80cc00002dbc1aa2bb947c9824632020ea46802de140089c39a16c08d82d80c000002dbbbea2ba946c9704561fe0e846762e714108ac39617208982f40ba00002dbb63a2ab94089424471f08e3865e2d7141088837e16008282a80a400002dbb0832ad13c892e43f1ed8df46602cb13b886438216108802f00ba00002dbaab42ba944896644f1fc8e646662cf13e088c38c16b08782ac0a400002dba4bd2c594bc9a44712080ed06ae2ff15089003ca18809082f00c000002db9edd2be946095a4581fa0e5866a2e014588ac3b418108d02f80ba00002db99402a493a49224331ea8dfc63e2d514008f43ba17909103140ce00002db93592c694b099a46b2048eb06942f114c88b83b817b08c02f80b200002db8d952b8143897845b1fe8ea067e2e514a09043ae17709283100c600002db87c42b614449684612010eb069c2ee14e08f43cc19209a83400d000002db81fb2b4945898a4681fd8e8068a2ee14a08dc3b417c08e03080ca00002db7c0d2ca94e49b048120c8eec6ba2f914b08e83c017808c82c80aa00002db76632a913f494e44c1f78e706862f414288a039a17408982c40a6000 else 0x2de57be2b2941c9424491f68e3c6782dd141089838817508c02fc0ba00002de51f82b6143c98a46f20b0efc6b830e15b095c3dc18a09a83280ca00002de4c1a2c614e49944612000e8c6962f514c88dc3b817b08d82d80c600002de464d2bc147496645d1ff0e8868c2e1142888839817608982dc0c800002de406d2bf146498045e1ff8e6c6862eb13f88b438e16508882c40a600002de3a782c1149c9844642058eac6a22eb14888f83ae17d091030c0c400002de34bb2b393f89404421ea0df463c2bb137085837c16508802dc0ae00002de2ee52c594b49a24732058e946882db13f88c839617108682bc0b800002de29272b0140894444f1f98e5865e2d713a080c35815608182b00b000002de23442c2149498046920b0ef06c030914d08e83be18008f82e80d400002de1d6d2c0149499846c20d0ed46ac2ef14808d03b017708d02d80b600002de17b42ac942496244e1f90e5c69c2ee14988d03b016f08902e40b600002de11dc2ba146498446920a8ef46d430315389243ca187096833c0ce00002de0c202b3143c9584592018ea068e2e914608b03aa17308982dc0b200002de06452c0146096c4581ff8e706842e814288943a017708f031c0d000002de008f2b014109584491fa0e206642d0138086436a16c08902c40ca00002ddfadb2ae13f89464451f30e2063e2c813b089838016508582d00a600002ddf5082ba144099446c2068eac6c02f414708b839a17308a02f40ba00002ddef302c194ac99646e2080ed06bc30114f09143c418208e031c0be00002dde9442c494a09a447820a8ee06ae2f614b092c3f219009483280c400002dde38b2b414349564612028e946a42f614b88fc3d219209203040c200002ddddc92b2943c95a4562000e7466c2e9141089439417108782d80a000002ddd80d2ad13e492e4361f08e386782e814c08dc3b417b08c02ec0b200002ddd2252c494a49a64762050eb46a42e214909003ba17a09102fc0c200002ddcc772a793ac90e4391ee0e2465e2d1137885c37016608882bc09e00002ddc6b12b3945096245b1fe0e546842e014208a03a417f08e82fc0c200002ddc0e22be144c9684552008e706722dd14588bc38417108402d00bc00002ddbb132b9947096e4541f78e6c6802e9141886838216908d82e40c000002ddb52d2c1149499247620c0ecc6ae2f914a08c43b217808d83180ca00002ddaf7f2af140894e4441f60e5c6802e914788cc39e17908c02c40a400002dda9ea2a013a091a43e1f20e306522ce13c889438216a08702ec0b800002dda40f2c614e89c64862150f386d630315809443e219809683480c000002dd9e442b4942095444a1ef8e086382c512c07fc34e15107c82a409e00002dd988b2b5945c96444f1f60e186482ce138885437415d08502c80aa00002dd92a72c594ac99e4722060eb46a02de14208b03a617b09002fc0be00002dd8cf32aa13e09464511fc0e686742dc13f089438a16a08802d00be00002dd87022cf14e09b04842108ee86b42fd15589683e418b09183040be00002dd813a2b4143095e45c2000eb068c2e5143089c39216c08a02c80c200002dd7b452cd95209ca48420e0edc6ac2f014a88b439417708a02f00b800002dd75612c714d09b247e2120f146bc2f414f09183ec18408f02fc0ba00002dd6f872c1949098045a1fd0e886882e413d087c38a17308602c00ac00002dd69ce2b2140895644a1f50e5065c2cf137083435c15508082e40b200002dd64042b694389604571fb8e6c6602cd13d087c38c17108c82e40ae00002dd5e3c2af93fc95a4461fa8e506542c7134083c38217208982d40bc00002dd58612c314609604451f98e606882dd13e088037c15f084029c09c00002dd52a52b2142c9544401ee0e4465e2d3140089439e16d08902f80ca00002dd4cb42d094d899847220b8ee06b4300156095c3e218408f03080c200002dd46fd2ac93ec93e4441f60e2c66e2e514308b03b817d09203080b600002dd41302ba94789804622030ea468a2f015088f03d818009503200c600002dd3b792ad140494643a1f18e1865c2d213f088038816608802fc0ba00002dd359f2bb14849884642048eb46b230415009043ca17c08c82fc0ca00002dd2fa22cc94a498a4632018e886862dc13f088c39c17508882bc0ac00002dd29ea2af140893c4381ed0df862e2b5131081c35e15508102c00a200002dd24382a994089404491f60e486682e313c88ac39816a08a02ec0be00002dd1e432cc15049aa47a2060ecc6b22f414a88b03ae17608f83280dc00002dd186a2bc947897e45d2018e9867a2e314888b439c17509083040ca00002dd12c32a393b892843a1f18dfc65c2d713e085c36416008b02d40b000002dd0d0b2ac13fc94e44f1fd0e646862d713d087436c15e08702a40b400002dd075d2ae13fc93e4421ef8e246482d314088903a017508e03080c000002dd01742c794d09a448020f8efc6c62fd153093c3c0182095031c0d200002dcfbc32a793ec94844f1f60e346462cb136085437415d08302a40b400002dcf6162a5138c90642d1e78ddc63e2c0136888839817308d02ec0c200002dcf0582b0142c95644d1f88e2c6682df14308d039817208702dc0b400002dcea9c2b7148098646e2080ed069c2f914588d03ae18009002f80c8000)) else (if i < 482 then (if i < 481 then 0x2dfcb932b3943094c44c1f98e4c67a2e2142088838016508902d40aa00002dfc5c72b8945096c4551fb8e686802df13f089c39217308b02ec0b400002dfbfea2bb94549724642020ea46a430014808e43bc17a08982ec0b000002dfba182bf94949964752060ea86a62eb144889439017108602bc09c00002dfb4602ae140494c4411f48e286542cc13c088036c17008682e80c200002dfae8a2bb14789984792110f1c6d430015509203d417408a02e80bc00002dfa8922cd14c89a045f2040e906a02ef14b08d03a817008982ac0b000002dfa2a92c514a899446b20a0ec86a22f7145887c38a16808a02d40a200002df9cdc2b494409564501f60e7c6922de13f089838215f08882ec0b600002df97292a913e89384441f38e3465e2de143088037415d08482e00b200002df91642ba14609684612020ea86902f214d88e839a17608e02ec0c400002df8bc52a193b89284401f40e286582de14808f83cc18109102e40bc00002df86022b194049304431f68e346722e2144888839217608c02fc0bc00002df803a2ae943c96e45d2028ee46ac2f214988d03a616d08982fc0d000002df7a702ba148099046c2048eac68e2ea14b08e43b416e08602d00b800002df74922c1947c9904672050ec06a02f914e89103cc18809583300b800002df6ebb2be94889b047a2138f306d030115109083cc18509002e40ac00002df68ea2bd14689864722020e906982e414708e03c417a08f03000ce00002df632e2b1940493a43d1ed8de46342be12d080034215107e82980a400002df5d5a2bb94689744602020e9469a2ee14a88dc3b4175091031c0d600002df57742c294989a24722070ebc6a42f0148890c3c818a09582ec0a800002df519f2ba94889864622038e9868e2e7143889039c17608c830c0ba00002df4bdd2b494249584591fd0e786702e514488a838e16c08903040bc00002df46262b1142494c4451f80e906842e5143087037c16f08882f40c200002df405b2bb146495a4521fe0e906a62f214808bc3ae18709303300be00002df3a9e2ae94389524531f88e5066c2e114688c439816507f02a009400002df34a02cb14f09ae4772088eb86a62f514f89003be19209603040c000002df2ec92bb948898e45c1fa0e706762da140089c39216d08a02dc0ae00002df28fb2b6143895a4572030e9c6922de13e08d43bc17709583280d800002df235e2a113b091c42c1e88dd06202c513b883435415f07f82b80b000002df1d872bf147c9904662020ea068c2e314388b83c217c08b82f80ae00002df17be2b7142496845f2018eac6bc2fb14c88ec3a416708402c00b600002df11d22c714bc9ae46c1fe0ebc6902dd13e087038a17508902d00ae00002df0c2c2a893f89464431f28e1c64a2cd13a887038c17508e83100c200002df065c2be947c97045d1f68e046582d113a085c37a16808a83000ba00002df00bb2a193a892443b1f40e486762ec14508a039817b08f02ec0ae00002defad72bd147098246720d0edc6ce30115209143c417508682d00b800002def52f2a513c89204421f28e4466a2d7140886436c15308382e00c400002deef3d2ca94d89b84702068ec46ae2ec14788e03c617809002fc0d000002dee9892ad13f49244391f50e5c66c2d313a889039416f08b02dc0ca00002dee3a82c694ac97446a2010e586742d5139088438015b08582cc0be00002deddc82be94a498e4672050eec6b02f814e88e83d019509683280c200002ded7dd2c294609804652028eac6882e0142089c3a017d08f02f80c800002ded2332a913cc91e43b1f50e206562e314a08d43be17809383080c600002decca02a293849204401ee8e186542cb134085436215407c028009600002dec6c62bc94789844702068eb869c2ea14888b039a17908e82f00b200002dec0f92b6943c95c44d1fd8e8468c2df13e885037616008b82bc09e00002debb342b7945497845b1fd8e886862e614088a03a417608c82e40c600002deb56e2b8144c94e45c1fb0e6c6722db14808b43a817408702e00aa00002deaf8e2bf948897845d2050ea06862ed14608b03a017608c02ec0be00002dea9c02bc144895e4591fa8e4866c2df13d887837c17008682b40aa00002dea3ee2bc144897045d1fa0ea06922e4142888c3a217a08f02d80b200002de9dfc2c814f89ae47a20e0f046cc30b15909143c618408e82e40b000002de98382b3940893844c1f78e4467a2dc13b085c38816c08a02d40b400002de92792b1941495c4521fd8e8c69e301150891c3cc18608f030c0d600002de8c972bd948899a4712080eac6942e514608a038216008602e80b600002de868e2da155c9f249a21a8f406dc31515589403dc18409003040ca00002de80a52c814c899046e20c0ef86c0301157092c3ce183091833c0be00002de7ac62c3148898c4692068eac6a82f414e08cc3b618a09102f00b000002de74ad2de958ca084a42208f506e831915f893c3da18c09403100d000002de6f082a793e09384471f50e2465c2d413c885838c16308782dc0ba00002de69242c2147899246f2060eb468e2e014308cc3b8187090832c0c200002de638029b93749084241e58dcc6362bb12c882c36215b07d029409800002de5d862c914d49a44732068e9469a2f714c08f03a817708e03100b4000 else 0x2e13fa62bd94689684591ff8e486682e014b08e83b416c08c02d40b400002e139dc2b394009584571f98e846882de13e088c39617a08f82e40b600002e134122b714309704601fd8e446742d514188b838c16f08a02ec0d200002e12e0f2ce950c9aa4752100f146cc30915409243cc19409503140c400002e128632ac14009404401f10e3c6662ce13f087039e17308d83100b400002e122aa2b013f09384451f48e2c64e2ce13a889439617108b02cc0b200002e11cf02ad141896e4561fc8e5c6682db13b887038416308602980a800002e117092ca94f89c04832148f406e030415289283b617e08f83140ba00002e111462b2143495e4591fe0e506822e513e085837816b08302800b400002e10b722b5143494a44f2008eb06c230014d08e83ae17908d03100dc00002e105892c794b098e46c2090eb46a22f714d891c3ba17e08e02fc0cc00002e0ffbd2b3944896444c1fb0e586782dd14008a039616b08882b80ae00002e0f9f72b314549824672080ea46982f714b08e43be18d09302fc0b600002e0f40e2c394b899c47120b0ed46b42f214508b83a017308e02fc0d600002e0ee132d095009e649921b8f746d831116009603f219309603180dc00002e0e84c2ba14389604521fb0e5066e2dd14308ac3aa17008a02f00c200002e0e2912aa93b091842f1e20dbc63e2c3138084438416508b02d80b400002e0dca02c4949c98e46b2068eb06ac2f814908c83b018109102e80b800002e0d6c02c0948499c47920c8ee86ac304155090c3d217e08702c00b200002e0d0da2c494bc9b04742058ec069e2f814a08c83a217508b03000b200002e0cad72d395289d649421c8f5c6e030614e08d83aa17608f03080c400002e0c50c2b313fc96245c1fd0e486522d313c886c38416908782d40b000002e0bf342c0149c9924702098ed46b02f614808f83ba18308d82f00b600002e0b9472c914b49844612000e746762df13a887839a17608e02e80b800002e0b37f2af141c9424491f40e6067a2d213f885039416508902d00a800002e0adaa2ba946c97a4602068e846902ea14408cc3b617608a83040c200002e0a7ed2b3142496845b1fd0e706802ef14408b839e17a09083200cc00002e0a25b296134c90842b1ec0df86442c3135081436015608002cc0ae00002e09c8f2b014289604532000e7c6862e9141889c3ac17508882cc0aa00002e096d22b294049504541f90e6466e2e4142087039417208782ec0be00002e091292a393989264251e18db06242b612e8818350153080029c09a00002e08b6c2b5143095045f2038e9468c2e514808cc3bc18309002ec0bc00002e0859a2be14789864592010e706842f214b88dc3c217f08d83000c000002e07fda2b3144096a4591fa8e6c6842e814988ec3ae17f08c02d40aa00002e07a0c2b2944496045e2000eac6a82fa14d08e43be17d08d82f80be00002e0743a2b814509644581ff8e846a42f014708e43b817a09083040b600002e06e552c994e89b848720f0f006ce30a154890c3c418509283200ce00002e068722c414b49904732098ed46b6300154090c3bc18408f03000ca00002e062a42b7945897a4652090ec469e2f315288d43a817808b82ec0ae00002e05cd02b8943895e44b1f28e586742e214188e03b417b09082fc0ca00002e0571a2ac13fc94e4401f78e746742e413e889039c17908682c80bc00002e051682a913e895c45d2008ea46842d6141888438216308b02d40c200002e04b892bc94809844652038e8c6962ef14808b43a017909003100c800002e045b22ba946497a4652020e7c68e2e714688f43ca18608e03180c000002e03fce2c194b89984742120f146bc2ff15389243c818209703480d000002e03a152b094209564511fc0e706822ee14988c43aa17508682f00ba00002e034232c594c499a46c2060ec46902ed14d08c83a817d08c82e80ba00002e02e3f2c2149c99e46a2008ebc6822de14208a43b417e08b02ec0c200002e0288e2b213f493e4441ef8e206602df14688b03ac17b08d82d40c400002e022c92b494189524481fb0e5866e2d113e08a83ba17708e03100b600002e01cdf2c694a899646c2060ebc6b22f614e09043e8195097032c0c400002e017112b9945096e4542008e986962e814408903a017208c02d80b800002e0113e2c3148c9884691fd0e6c6762dd13f08b838e16908682e80b200002e00b752b694509824712038eb869e2f114a08f03ca17d08a83100ba00002e0059b2b9946097444c1fa0e646722d513b887c38e16708302cc0bc00002dfffbc2bc14649784602020e906822e3143889439c17608f02e00b200002dffa0e2af94009584551ff8e4c66a2df142889c3a416d08802d80ae00002dff4452ba944897c4632008e9468c2ec14788bc3b217608b82e00c600002dfee4c2cf14e49aa47720c8f046d431315289043be17f09182f40c000002dfe89c2a893d09464391ef0e0866a2e013d886c37416b08282b80ba00002dfe2b52c394dc9b047920d8eec6a62fa15108e83bc18109603000ba00002dfdcdb2bd94809904692060ea467e2f114a08f03be18809403280d200002dfd72a2aa93dc94e44b1f50e546862e614508c039c17208b82d40b400002dfd15f2bc148098246d20a0ef06b82f6151092c3ce18c08f82e80c0000) else (if i < 483 then 0x2e2b3382cb94d499c4681ff0e886962eb143087038216708602d00b200002e2ad602c294a098846c20c0ee46a42f114909143ca18909683200d600002e2a79b2b2943094c4581f90e706782eb152091c3cc17e08f82f40c200002e2a1b82c894bc98046a2048e9c68a2f614c08ec3cc18209103100d600002e29bec2b194009504571f90e8467e2e114988a439a17309082e80b800002e2960d2c0147498646f2078ea069e2f514888d039e17d08c02d00b000002e2903b2ba948899a4692090e886862e614588bc3ae16b08682c00aa00002e28a832ad93f894a4451f38e2c6622d2140089039416a08702bc0b400002e284ac2be147c98e46d2088ea46982ed14a08cc3be18009082f80c000002e27ee02b393e493a44b1f30e2c66e2d813f88a839616d08802e40a200002e2792e2ac13f494443d1ea8de464a2d013a886438616708382cc0b400002e273532b9146896e4582018e9069a2e514408b439817408902e80c800002e26daf29e93c89284431f48e286662d313e889439c16508482b80a800002e267ef2b0140093e4481f50e186702d813f889039017108b03000bc00002e261f92c4148097a4642070ec468e2f014888b83a617708b82e80bc00002e25c372ad94149564501fa0e706822ee14908d03a216e08e02d80b800002e2565f2bd94709704561ff8ea068a2e714808b839c16c08902d40b000002e250782c414d09b04802138ed86a82f814d08f03aa17608782c80ae00002e24ad62a593e093c4521ff8e6068c2e714788d03a617408c831c0ce00002e244f72c814b899a47020b0ed46aa2fa14e09183ca18709102e80b400002e23f2e2b3143c98a46c2038ea06b230114d88e43c418209383080cc00002e2394c2c894c099446b2078ed86ca2f514d090c3bc17b08f02f00d200002e2338c2b8146097246e2048ec46a62f114d08e43c218708f02f00cc00002e22dd52ac140093643f1ee8e086562d513d889c38616808182cc0ac00002e228012b9147c9924642038eb06842e414588c43bc17608682dc0b200002e2220f2cf14c499247420b0ebc6aa2ed14808cc3a417208d02d00b600002e21c4c2b7142c94844b1fc8e906742dd141888036e16208902d40c200002e216712bc94789904642038ec86b62ff14c08d43ac17508d02f40d400002e2108a2bf949498e4602030e986862ea14108a03ac16e08982e80c200002e20add2ac941095c4511f88e4c6782d5138087037216708902e00b000002e205242b193fc93e4441f30e2c6602d613f08c43ca18b093030c0c200002e1ff5b2b4945497445c2018e8467a2d914708d43aa183090032c0c600002e1f9972b5144894e44b1f50e3865e2d514008b039017108702e80bc00002e1f3ce2b9944c9664672080ea867e2e814208b43b017008d03140b800002e1edfb2b9945096e4592008e8068a2f514c08e439e16508a82f40b800002e1e7f82cf94fc99647120c0eb86b42fa14b08d83ae17f08c82fc0ce00002e1e22f2b514289724632050e906962ee148889c3a017809202f00c400002e1dc6c2ad13f89444421f90e386642d313c889439617b08b82c80b200002e1d6ba2a913e09204441f50e5066a2e114488c43aa17b09002f40c200002e1d0f82ad13e893a43b1ec0e106582d3133085c37616708902b00b600002e1cb3c2aa93fc9504512020e946902ea14108b03a217508b82ec0b400002e1c52d2da955c9ea49b21c8f6c70230f15a89283cc17f08f02f80a800002e1bf6f2b014049424491f60e506782df142887838e16508782e80b400002e1b9c02a0938490443a1f20e0066a2d914108c03a417008b02cc0be00002e1b4012ad93dc92c4451f38e3066e2db14108a039216908802e40a600002e1ae462b8145c9724502000e7c6722e7142089c39c17208782c40ba00002e1a8732b7944c96445f1fe8e686742dd14208a039216808e02c40ae00002e1a2a52b7943095e4511f90e786802e2140887038616208302d00c200002e19cc42c514c49b246d2008e9c68c2e513f089c3a618009103280d800002e1970f2ab94009504501fd0e706682d8142089038816b08102ac0a800002e191442b3143897445f2010e9869c2f514e88f43b418008e03200b400002e18b742b6142496444e1f38e2c6522d313c088439a17608902cc0c600002e185862c894e49b84742098e8c69a2fe15088f03b617908c02ec0d000002e17fc62b2943895044e1fa0e486682df141887c38816008482cc0b400002e179e92c514ec9b047820f8ee06b430014c08fc3c818c09383400bc00002e1741c2b8945896a4521fc8e6c67a2d914308d83ae17e08d02ec0c400002e16e702ae141494a44f1f88e446762df13c089839c17508d02ec0be00002e168b02b2940c96845a1fc8e7c68a2f115189003b417608d02d80b600002e163072a113bc93e4391e88e0064e2c3133083c38816608902d80b800002e15d272c3147497c4621fd0e206682d913f089439416508502b40ac00002e1573c2c414b099445e1ff0e846842dd142088839417e09483200c600002e151542c814bc9b647f2120f246cc2fe15089083ac17308902f00b400002e14b5c2cb94d499c4762100f046e830b15809603f418108f83000c000002e145862bf947c98c46a2058ea46822ea14a08d43cc18e09a83640d4000 else 0x2e2fe9f000000000000000000000002ec14888b839416e09103180be00002e2f8b22c194a09ae4802100f086ae2fd14f08d03a617e09403200d200002e2f2e52ba148097846b2070ef06a42f514b08c03aa16f08d82f40ce00002e2ed1a2b694109604491f58e486682e514288dc39a16a08702b40a000002e2e7522b614309684571f90e2863c2cc13a088437816908982bc0a600002e2e1912b7143095844e1f80e606882df14108cc3aa17308c02e80cc00002e2dbbb2c294b099e4722068ecc6ac2f814d08f83ae17608e82fc0b200002e2d5f72b9144c9624501fa0e7c6862e314688c03ac16e08e02e40b600002e2d0512a713d492a4401ed0df86402ce135884435614a07d029809e00002e2ca932ae13e095c4551f58e506722d913f089c3ae17708d02d80a400002e2c4ca2b8146897a45d2020e9c68c2ef14688a439817208682c00a400002e2bee92c414d09b847e20b8ef06c430915088fc3b418108d83000c600002e2b9342ab940494e44a1f30e446742d613d086436c15908402c00aa000)))))))))

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



private theorem b481744 : covered 481744 481864 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b481864 : covered 481864 481985 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b481985 : covered 481985 482106 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b482106 : covered 482106 482227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b482227 : covered 482227 482347 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b482347 : covered 482347 482468 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b482468 : covered 482468 482589 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b482589 : covered 482589 482710 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b482710 : covered 482710 482831 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b482831 : covered 482831 482952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b482952 : covered 482952 483073 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b483073 : covered 483073 483194 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b483194 : covered 483194 483314 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b483314 : covered 483314 483435 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b483435 : covered 483435 483556 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b483556 : covered 483556 483677 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b483677 : covered 483677 483797 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b483797 : covered 483797 483918 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b483918 : covered 483918 484039 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b484039 : covered 484039 484160 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b484160 : covered 484160 484280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b484280 : covered 484280 484401 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b484401 : covered 484401 484522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b484522 : covered 484522 484643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b484643 : covered 484643 484764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b484764 : covered 484764 484885 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b484885 : covered 484885 485006 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485006 : covered 485006 485127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485127 : covered 485127 485247 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485247 : covered 485247 485368 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485368 : covered 485368 485489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485489 : covered 485489 485610 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485610 : covered 485610 485730 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485730 : covered 485730 485851 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485851 : covered 485851 485972 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b485972 : covered 485972 486093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b486093 : covered 486093 486213 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b486213 : covered 486213 486334 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b486334 : covered 486334 486455 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b486455 : covered 486455 486576 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b486576 : covered 486576 486697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b486697 : covered 486697 486818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b486818 : covered 486818 486939 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b486939 : covered 486939 487060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b487060 : covered 487060 487180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b487180 : covered 487180 487301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b487301 : covered 487301 487422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b487422 : covered 487422 487543 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b487543 : covered 487543 487663 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b487663 : covered 487663 487784 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b487784 : covered 487784 487905 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b487905 : covered 487905 488026 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488026 : covered 488026 488146 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488146 : covered 488146 488267 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488267 : covered 488267 488388 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488388 : covered 488388 488509 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488509 : covered 488509 488630 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488630 : covered 488630 488751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488751 : covered 488751 488872 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488872 : covered 488872 488993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b488993 : covered 488993 489113 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b489113 : covered 489113 489234 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b489234 : covered 489234 489355 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b489355 : covered 489355 489476 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b489476 : covered 489476 489596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b489596 : covered 489596 489717 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b489717 : covered 489717 489838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b489838 : covered 489838 489959 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b489959 : covered 489959 490079 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b490079 : covered 490079 490200 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b490200 : covered 490200 490321 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b490321 : covered 490321 490442 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b490442 : covered 490442 490563 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b490563 : covered 490563 490684 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b490684 : covered 490684 490805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b490805 : covered 490805 490926 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b490926 : covered 490926 491046 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b491046 : covered 491046 491167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b491167 : covered 491167 491288 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b491288 : covered 491288 491409 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b491409 : covered 491409 491529 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b491529 : covered 491529 491650 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b491650 : covered 491650 491771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b491771 : covered 491771 491892 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b491892 : covered 491892 492012 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492012 : covered 492012 492133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492133 : covered 492133 492254 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492254 : covered 492254 492375 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492375 : covered 492375 492496 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492496 : covered 492496 492617 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492617 : covered 492617 492738 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492738 : covered 492738 492859 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492859 : covered 492859 492979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b492979 : covered 492979 493100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b493100 : covered 493100 493221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b493221 : covered 493221 493342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b493342 : covered 493342 493462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b493462 : covered 493462 493583 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b493583 : covered 493583 493704 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b493704 : covered 493704 493825 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b493825 : covered 493825 493945 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b493945 : covered 493945 494066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494066 : covered 494066 494187 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494187 : covered 494187 494308 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494308 : covered 494308 494429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494429 : covered 494429 494550 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494550 : covered 494550 494671 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494671 : covered 494671 494792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 481744 494792 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b481744 (joinCoverage b481864 b481985)) (joinCoverage b482106 (joinCoverage b482227 b482347))) (joinCoverage (joinCoverage b482468 (joinCoverage b482589 b482710)) (joinCoverage (joinCoverage b482831 b482952) (joinCoverage b483073 b483194)))) (joinCoverage (joinCoverage (joinCoverage b483314 (joinCoverage b483435 b483556)) (joinCoverage (joinCoverage b483677 b483797) (joinCoverage b483918 b484039))) (joinCoverage (joinCoverage b484160 (joinCoverage b484280 b484401)) (joinCoverage (joinCoverage b484522 b484643) (joinCoverage b484764 b484885))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b485006 (joinCoverage b485127 b485247)) (joinCoverage b485368 (joinCoverage b485489 b485610))) (joinCoverage (joinCoverage b485730 (joinCoverage b485851 b485972)) (joinCoverage (joinCoverage b486093 b486213) (joinCoverage b486334 b486455)))) (joinCoverage (joinCoverage (joinCoverage b486576 (joinCoverage b486697 b486818)) (joinCoverage (joinCoverage b486939 b487060) (joinCoverage b487180 b487301))) (joinCoverage (joinCoverage b487422 (joinCoverage b487543 b487663)) (joinCoverage (joinCoverage b487784 b487905) (joinCoverage b488026 b488146)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b488267 (joinCoverage b488388 b488509)) (joinCoverage b488630 (joinCoverage b488751 b488872))) (joinCoverage (joinCoverage b488993 (joinCoverage b489113 b489234)) (joinCoverage (joinCoverage b489355 b489476) (joinCoverage b489596 b489717)))) (joinCoverage (joinCoverage (joinCoverage b489838 (joinCoverage b489959 b490079)) (joinCoverage (joinCoverage b490200 b490321) (joinCoverage b490442 b490563))) (joinCoverage (joinCoverage b490684 (joinCoverage b490805 b490926)) (joinCoverage (joinCoverage b491046 b491167) (joinCoverage b491288 b491409))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b491529 (joinCoverage b491650 b491771)) (joinCoverage b491892 (joinCoverage b492012 b492133))) (joinCoverage (joinCoverage b492254 (joinCoverage b492375 b492496)) (joinCoverage (joinCoverage b492617 b492738) (joinCoverage b492859 b492979)))) (joinCoverage (joinCoverage (joinCoverage b493100 (joinCoverage b493221 b493342)) (joinCoverage (joinCoverage b493462 b493583) (joinCoverage b493704 b493825))) (joinCoverage (joinCoverage b493945 (joinCoverage b494066 b494187)) (joinCoverage (joinCoverage b494308 b494429) (joinCoverage b494550 b494671)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 481744 ≤ index 925000000/512 := by decide +kernel
private theorem starting_value : fast 925000000=47221646 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 925000000=47221646) (n : ℕ) (low : 925000000≤n) (bound : n≤950000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=925000000
    · rw [first,anchor]
      exact starting_value
    · have past : 925000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤950000000 by omega)
        have within : index n / 512 < 494792 := by omega
        have lower : index 925000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤950000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ925000000To950000000
