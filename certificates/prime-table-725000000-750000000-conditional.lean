import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ725000000To750000000

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




private def radical : ℕ := 0x2c748a0ebe9d259f0a0d642f0e160ccdf3376fb855e81b3f050b0974b45e5c396d36bfa9afa52084eab21815ca61fa808d65ff759a6abed8fa1f75ec6db0ee0c0986481d97df2669e72b396d5847cb15b176978c539f550d78386011969ca6631f2d1206e273135aeae66e4e015e25e3493aa3e43217a250bd811a9ca9a173744b38d555dcb8e4254d065ea08252402791580dbf37d6706073c77af441f0fda2f07378e6d7652215d2c5fa1a763cd4d5ec2c5752c55af78135640d35aaae6321025d5b9cf0e482c9121756c79fc6d48850ba50e14f10e3b33454c73693d4fb945d9e6815d7cccf97f37655177a271948f8053a7be702a9742332512e100bb4c8b62d4b6b101f1152b169d413e256a2a238c6d67f678418489ab25b736a3f0aeb08403570b80257a554a4323830cdd2b44e19cb7e222acb1b064f82e81c468fe97ffb9be2f5d6b5cc9615859ab8db4d448e05b5b8dd7c447d671de45e41c76e95106bcf6a6d6654d1b0f3470919fd29e4e1fb497beba602038abdff5ef840fc50bc1a72ae0866164f3ebf627f9506b7f7eae5a0e0dbb2644cbfb3d9865b4d469e3763abcb3e8648eb0f2b582e9b94d3afc7617de203c2dd76f4ff973ed7011a62f7f7e7501bed0a778edffc912eccbf387c4503ae12672d7d811942a290d384ead4d968a6c200680461d9c13d78dea91af2f3b8983dbed2629368c40dfc0d6f3fcc409f92a38ba1b3af52935b8920c552ed26505b9ebc9c8c312f2969f4db36baac221d7505358a9acb2a213c43d8caefb84c72706c6252fe6be31f2e98edc167fa4912fc50190bd7af66cc940d6053c5f3328a687d1a433a9502e564bdfbae107640fb400d31bd7dd5a814e563751e7065daee356d9e080a391178f133b31b80458eb7e61921f9322c1c830f1d8847be68dc877a0871e24e6e816b91a73d01ad4ba8872e64994f49a2c50b2a35c56255fc0fcf9e390f15ca176f4057ddf40aae23b4525bdd56ecc30c3b0fc7e79e1dbad400f507cb37102fb4a0bbe4b7a0e3d11d6df1251296464ddf9b0d5f244c9e22007869ed9906d032f3a10b325de36e02c2e7a07f72f9296656e32327640e3a9a9abd6e7e5853599916fd29379d35388dbac45106634b153fe2ea9508e22e3aa5645073c61da1442536b533aafb05bfad947dda4373df5f3b3fc2d3a29f9da364197c290343fce1ac146a80c2ab5bb8d4ae3bcb43424445c3d5093a25ab8880fc990402faecc1ebb0aff74dc6e22be4880790e5d286bdae4ce6f0fe46076a52c353bc6b992937c1e6310f18c7c4ddbb239169c9c8dcdd488ab77eaf3c1b2efe017ab0eaef07ec0973963bb33c6b21fcc10b2741e47e6d38a1ea15dd75165a0ed58b8f3fb041e58ab0fc13724a1f47ad81158c587c51238bcde40200c3d2d1df169b9e94312955310bc19443b93a90108504a9ad185fb5114cca4c1c942aac70b4196ff7a0286ed98e599c30b53b574a06f6ead40babad23e7c1cdf223e168e7770dd4303610cc3c65181ccd0fa93678f5f767d2146b70143d4247485fb8ab750ae1b06c04493d0d5763b37984f15a2586a291c5812e95f15ae219b5323401de9b9bbf3ccd85d911459181aa2911e6a80694b57880dde18e9b39fb08bc0d7927238cdfe0280bde9a320ba93e65b46e269d3dae00b3282dbc86e0b9642fbaeff30bc202bc5f595cb03add62f285145f40cd30324bffcd56631c79c00027dcdf8c9d7080d5c74be5e261d1d775f0cff230cc7364eba04d0f9d10df22d55d53497cfec67ca7b26e8a605d238ad9897bd7ce8012774908e4a70d77c9260854227a8ead411b5cea9591feb8b0a47ce43e2f4272fea8893291a5a4ade93fe18df828336ee05a8f221df429d408235947b755cbeae240fdfbc4995a6fc662eff5f6cc9b541153496fd8a51ec2d893342c241ce5fdd21df9ade80971b1914fe66e7a95b0665a4de7a13cf162cc5eebf93d34bd2cd3bf4817ae02849ee43c2aeaf072f6b789c6db5fc118dbb687bc84f54c81c08a100c813489df6d48329b7fc9919cf993aafbd75db9bada4ffc5cab47a94a4258cd0f4cdf78a20d03c4fdaf4a6afabfabbd5f0e70ec847dd91e10a3f0a4ab19b567ebcc5f934036afc551c6225a0a154d99efdc332cc123c60f98f4a28c99c58747e2b9765238cf62c63fe593bfc5a77545a2445ca54c555e4daf1b234ed067b81bdbc9c74c0b752fa0b0cb21e42ed60085884bf7274b68a32576eb1e6c23ba04516d2a95d3be9a27779915eeb8fbdb85ede4354f9d057e092f69758c4453d6ec99d428c32bd0e4a046652101ac4380ab5e624e5a3436e484e5d7cbf342ad91159e161561688d5e1999321ba6e1cf83189fb2155552d9e763f06d0b5e96b4c5937742fcf6244d3457bf61c65dfa00e252f27eb7c82489905a4876376e49c021a69ddac432c9426731a197a65cb981145acbf04601bbb8d38bd4110e8f28312a0fc33218556f1ccbc99991f138e2472311529d7cd43d1d449013c7bdda3f97d2e43b7ec0b97b1da078a0de37789a36f2e3e9c2513a2ef6dd9d8f019cc7c7f63579c19a6c781b1cd5b09fafc9d06a87fab9b8ac53b8bf42ffd98d8c4f04d5dcf7d44e2b63fa20f660f59d2c254734edfd12fb214774fce48a1b0e969537b66d5cf696f332ee8cd07ebe06ffbcee528f509719d88279ef1cfca294ecf5099b5defaaa204bc6740310e17b55457893d115fe55ae48e9f688537eb769dc6e394d13ce4e4b55ff74f01a27224f6b3e312c01fdb3c7e5051adad022b1acb33a0a2f7f37691aef8a470cb8944b8bafcdea1f441c53b3ce82b8e5458461a8e08cb783c7c29b627d0c5328e3beddb7b8ba3bbe2f633d783f5ed80bd51f900aa96dd8c02c128c7e8e4296b05bc35619dbad08c8a23e6e85f7488c3727fd480fc2d69a2a22c133b1991a31e4361a153256d9fe25b35add5e7c670f669bc7b41fb428be2c86a91c314637a67f51c363fbf307ac0ca3473a717e52aa49670a005406be9d9456ab50895f82c1beb574b157925712107f27afd165a69ce99340d5b2a7cd539359de656ba58f1f905aef9ae82cd583527f4b8660cda64b316ef2f415199e52aa48021f236e428d1fe069166fcbeee459e9604bf13d59f531c2aabad983bb3667a78dc52a00be8e724d1a7f5a11bfbdb3f310cb2f6f565795501cfae2060d8535de6f953b54bfcc1f55b51b2fb454aa62e4efdc84983930fde2d02c8a4ccc075c4b06dc0b888d6c2bfb87028332ab8c3130cbaef394ed67d3257d24031d03aa51a7c9b23d15422e275f578a532d1742f54ff7c81fba20731d52d13eeea9ee60d8a8223ed6e0da9417a63c9508f1aa5edb8f33007cf5c8d8b9e3a83f2cc406ae18b5f35bfcb80b17cb952cc3566dd225ce576f562ecdcdca9e1882e333eecd3c96838d4fd62ea21a84781d4e203d7a497cd0daad9f7a00c162baca7bc219c86305e5117135f135bf088e8b08f8b3fff37e717c9f06e93f45787124811a84989992917ace1135afa1233121867aff38e7b61ac26e1a7bf30c4dc708b436eb7651ba99a9684b18d7722b247d7aed43166dfd3ba17867cf43ba9d8bd17037df65691041e1a32c4e401491f12db9c58a01cfcc44a7f9fd574248c132f441b2112116721538960038e0b0cafcabf5e75d72045317b1f506bf51be87224baaab75cb541daa5ac6ec2c019274a3570afa6f38ed4ba1e3b26f7308fd7e12c01504ddb2184050f72feb448ef4937f5e09ab623e4fbb06fec8fc667c0ad8b09e4569d86df9d1939f73bb61695be0d1f899878a3735d5493e397e48aee817923dfc91240e8f05978e020794857dc419b7230ac2ef9bfaa0eb86298fbde7c0455f9cc3b6529cdd2fade68ac9894d365ee9bf6bb3e9a322c432638cce99999c285df4dbda9db1894370f5c222f555e7470d85108e47aee2942b2ec3052e8458a333e9cafb387f1e54de842e116f1d93d52e5c07468ddd5eeefd2144ebd7731ec81cccc8d6d53b811d60a7050c9aec048e81ec895f661e51818f4e3221bc4d087fecbc4d5268f21b44d975b5a554fa6aebefee49221db5430f2b6af3262cb93e8a66e92648b6615e94176e2adda814540c9b0565d59f26cb5c0a11d67d3fbd29eeb05b5433e010d0ed001bb3821a6904025a4702d5359389cb99b07adec29729b6a928e34965a061439942efc0691f71288203e6f64d42efa0a0b97b75c3f3e6951484d27a3615149398a84155f55e7680aa4d31c4be55559e1941acf69e4581f2721946e9211958a5324a9f7a4f407cfc6a728cea3c4827efbc1f0e9618dc3651813821a43f65795195ee49328f58ef13a33a6339a2678396a98d96e3d64f81fe8b15e561a69796980c6762b93f8fd99392b89e83ee8d0fad2b189d55f3cf5dc051f3a4a67fa372d93e62834758cf4c346108c7889f927eccb275c1aa719c220fbb69c24512e00a67f7f330d80c318b6de3e77cfaff3a3d481b188ce680e0d5e97d8ee358ff07b1f21e132ad760ed8efa29055cf8aeaaef88bfd2c3c3e4a778b7dffd0c26b7615bab9db04c2f8a30c6eab7ae8787b02669b411075dc4ff7652e017cdf6594e5652e17dc9995b9402f1e5947bbfa7e792e8909a6816516a94cc20d47feb9bf42c0ecb540e5cb4bec8ec0ee600c7de79cebb2045c032441fcf1141a0039e75fce7e64f2fb0d54bf8f3e0a98b00e8d08d51a4093f8fe8431ad557f586de3cd23ed1ee6ffb9f68bac4040f0aa0f77cebe92e7ed10554f8a293aa3d3aa23285b09de2c095d1c7bbaae6a71d2344bdfec859b1085b476aa0dbbe36054fbbcc5ea30c7c5385b4083d0095d113e857ed219bbc4baeea07f02d4c2b1c643cbfcce2058151cf26764b1fa6b1f33bd6f9473ec2be43782661bfa6d5390f1456c468999e8a977fce245beaff651cc86bc7c61549b550ac5e6ab558c778865f4bddf4ce694436a7de184ef408b0808428b9429db1c3843f08bae1a1a4303acd76984352cb6f2ec5c7e6880b418dce914efd6af526cde9d3dd79fac7d44a3e94641922a610c0f495bf00eb6d0fc17d8180aadac2a3e26379b966e88af3c703d10d4d0cf44424675937f737d1c869a4224deebf61fb7895d5944987ca93c8b3ce04eb9ff6f81a23823a62b14b8f1482ff77b60cc1711dcf5a5814748ef80e909eef1a13bec0b5c0f28550ab72ae1db904c1403c2b1e6ee8c20ea66c91a38ac43580609c9403e0882aab4ba60797653f35e719fcf6eaf7d44c147f1144b724f21b13ad08ace44f099a91a8d16ff12527cd40ae56ffc85e8636e34adb8c39fa89dff89f86f01aa37e72f97882ecf64c64479c85de56460d5b7416ea007aa71a1144a7c8d401f0002c39cd642b6c4a79682a2a42d7fdd314b5ed8aadaf98acb6c21f7d8170309cfa6fa500da869b3d1e777614723c532c9f67e960c6a3cfa07cfc4ab0fad3762f7f9e3acd9e2f65082529f469211dc01aa2c1e330d499ae2b3e2409d5aa7274620e4f57b9a75d79cf7e5aebf30c1fab72bd5011e7993a01566450ad346e962b39969f8de82f560fa3fed4b8abe5ad1a3738c5702ada7702cf03e95d0311dd6200f59f35d986a4f33760c914c3315e8dff2ef32181a215bb648b5f22582e3f7bd7cfd4e51c18946b4b551686a92776c2b16e63525d8f44b929bff9f92be207c36ec31a5ea000eebd27bd1dab2b3199f3847d9f1a3e629603cbbafd925a4cc8bc0c8178a30380df0f898bd6c713f9f45e16983bf6e549cd2de6bb07af92fa13972efb05f612240cefef1e672f191d37168b9805f295a1d5fa03dcb16d53f2510bb37cb92a9aa62248008661d326b1c9138fe939431d60a5b648424621479f3e114dfd3ebb2c8c8dfcd63dcb6cabd247f20c774297d68c5263294b5e9790da502280edea4c0eeebf1703e75b3131b981f424f9ba2b514190e3dbfc863252fe99ae50f16be2e9a73fefe7d46bbc3a660f4b15015d4a837bdd408dd68b09a5decec816cffee8298099047a415abd31db34754504c62453bc8438bd5997f06226b7badd277c28c7336e2926c707fcfaf9eae4e2ac5ec62c49cf1ef357e52e3a9580b229556d92f9038007130da5e7e1161e7ab47903196663ba3cce3a76644eb293bdfef56d973f412fc2566e36ca5c79a41714595455121f7e26730293e5ad7379cba99854f920107dd08a86e600cde0cd1e2cdec68caff73e4828b2427af8df0dffb546c1628419dcb347e2b84ed3aae4d7aa446d173ff7079c6b6edbfc8b1a795c664609de406ec007ae9bf94048527cb2499b1a83ce4ab3fb50121e6ad39d91530502f399a06ae7250f54b1ddb88daa957332a0a6b0be49b163b0869855a13d9fef052ef2515945f4caeb69bb2881d7301daca2af10f68715ef9588b760a603e322dcf36452d6406de194149f9171494088b86923615847049e25dd040c624cb1734c4475c570748311c75d1ddc288e6749384a07913c848cc215ee342235773fb24ecc8dd29b17628d37924235d79cef26669cf8a3a14c1943dcb4a8d59b5e6cc1363ff9d69034d0f8e107f48756fbeca99f6dc1feba936e9b8b67d81a6504f08fa7b65d0d8c1c323afad550de720c71fbc4a5fbcfa4bdb615dcdb37b394e338ee92f8629cf2467e4a79610943c31b4cebe707344a30c38e947ac93c83aa85e882f375d256e30b5bcac6eef5b7fde3d9f352cbdbbbd7ad2ccd2e493281ee00eeced1179358b63db2218dc8feb486b0ca1f6ad55f682030bfbaae9fedbe5a034e1441453855b017ff069adca0b217d84794166f02fecbe07eb8dfecd0bb2cb2669b14fdd4ac98adbdb6225d13b0df0ece867382ba15fb9d25b3e74747215cf0b5ae51c8afbb1b2e7a61024374a7f46a1cd8596e10e7ef54a50ab1c41139c4dc9df8962e5c67380703f0e7a

private def light (n : ℕ) : Bool :=
  if n≤165 then decide n.Prime else n.gcd 54239106661315887749844950142128418438215720379413698342567269131165730172604765680403290849565015553604650354393935095487058155225915554489271207416431263907819225703574088519286376487014046409943976621391856730220500349076942933314077895545443758280540160000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤27386) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 165 = 54239106661315887749844950142128418438215720379413698342567269131165730172604765680403290849565015553604650354393935095487058155225915554489271207416431263907819225703574088519286376487014046409943976621391856730220500349076942933314077895545443758280540160000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 165 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤27386 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 53 := by unfold smallValid; decide +kernel

private theorem sp53 : smallValid 53 53 := by unfold smallValid; decide +kernel

private theorem sp106 : smallValid 106 53 := by unfold smallValid; decide +kernel

private theorem sp159 : smallValid 159 54 := by unfold smallValid; decide +kernel

private theorem sp213 : smallValid 213 53 := by unfold smallValid; decide +kernel

private theorem sp266 : smallValid 266 54 := by unfold smallValid; decide +kernel

private theorem sp320 : smallValid 320 53 := by unfold smallValid; decide +kernel

private theorem sp373 : smallValid 373 54 := by unfold smallValid; decide +kernel

private theorem sp427 : smallValid 427 53 := by unfold smallValid; decide +kernel

private theorem sp480 : smallValid 480 54 := by unfold smallValid; decide +kernel

private theorem sp534 : smallValid 534 53 := by unfold smallValid; decide +kernel

private theorem sp587 : smallValid 587 54 := by unfold smallValid; decide +kernel

private theorem sp641 : smallValid 641 53 := by unfold smallValid; decide +kernel

private theorem sp694 : smallValid 694 54 := by unfold smallValid; decide +kernel

private theorem sp748 : smallValid 748 53 := by unfold smallValid; decide +kernel

private theorem sp801 : smallValid 801 54 := by unfold smallValid; decide +kernel

private theorem sp855 : smallValid 855 53 := by unfold smallValid; decide +kernel

private theorem sp908 : smallValid 908 54 := by unfold smallValid; decide +kernel

private theorem sp962 : smallValid 962 53 := by unfold smallValid; decide +kernel

private theorem sp1015 : smallValid 1015 54 := by unfold smallValid; decide +kernel

private theorem sp1069 : smallValid 1069 53 := by unfold smallValid; decide +kernel

private theorem sp1122 : smallValid 1122 54 := by unfold smallValid; decide +kernel

private theorem sp1176 : smallValid 1176 53 := by unfold smallValid; decide +kernel

private theorem sp1229 : smallValid 1229 54 := by unfold smallValid; decide +kernel

private theorem sp1283 : smallValid 1283 53 := by unfold smallValid; decide +kernel

private theorem sp1336 : smallValid 1336 54 := by unfold smallValid; decide +kernel

private theorem sp1390 : smallValid 1390 53 := by unfold smallValid; decide +kernel

private theorem sp1443 : smallValid 1443 54 := by unfold smallValid; decide +kernel

private theorem sp1497 : smallValid 1497 53 := by unfold smallValid; decide +kernel

private theorem sp1550 : smallValid 1550 54 := by unfold smallValid; decide +kernel

private theorem sp1604 : smallValid 1604 53 := by unfold smallValid; decide +kernel

private theorem sp1657 : smallValid 1657 54 := by unfold smallValid; decide +kernel

private theorem sp1711 : smallValid 1711 53 := by unfold smallValid; decide +kernel

private theorem sp1764 : smallValid 1764 54 := by unfold smallValid; decide +kernel

private theorem sp1818 : smallValid 1818 53 := by unfold smallValid; decide +kernel

private theorem sp1871 : smallValid 1871 54 := by unfold smallValid; decide +kernel

private theorem sp1925 : smallValid 1925 53 := by unfold smallValid; decide +kernel

private theorem sp1978 : smallValid 1978 54 := by unfold smallValid; decide +kernel

private theorem sp2032 : smallValid 2032 53 := by unfold smallValid; decide +kernel

private theorem sp2085 : smallValid 2085 54 := by unfold smallValid; decide +kernel

private theorem sp2139 : smallValid 2139 53 := by unfold smallValid; decide +kernel

private theorem sp2192 : smallValid 2192 54 := by unfold smallValid; decide +kernel

private theorem sp2246 : smallValid 2246 53 := by unfold smallValid; decide +kernel

private theorem sp2299 : smallValid 2299 54 := by unfold smallValid; decide +kernel

private theorem sp2353 : smallValid 2353 53 := by unfold smallValid; decide +kernel

private theorem sp2406 : smallValid 2406 54 := by unfold smallValid; decide +kernel

private theorem sp2460 : smallValid 2460 53 := by unfold smallValid; decide +kernel

private theorem sp2513 : smallValid 2513 54 := by unfold smallValid; decide +kernel

private theorem sp2567 : smallValid 2567 53 := by unfold smallValid; decide +kernel

private theorem sp2620 : smallValid 2620 54 := by unfold smallValid; decide +kernel

private theorem sp2674 : smallValid 2674 53 := by unfold smallValid; decide +kernel

private theorem sp2727 : smallValid 2727 54 := by unfold smallValid; decide +kernel

private theorem sp2781 : smallValid 2781 53 := by unfold smallValid; decide +kernel

private theorem sp2834 : smallValid 2834 54 := by unfold smallValid; decide +kernel

private theorem sp2888 : smallValid 2888 53 := by unfold smallValid; decide +kernel

private theorem sp2941 : smallValid 2941 54 := by unfold smallValid; decide +kernel

private theorem sp2995 : smallValid 2995 53 := by unfold smallValid; decide +kernel

private theorem sp3048 : smallValid 3048 54 := by unfold smallValid; decide +kernel

private theorem sp3102 : smallValid 3102 53 := by unfold smallValid; decide +kernel

private theorem sp3155 : smallValid 3155 54 := by unfold smallValid; decide +kernel

private theorem sp3209 : smallValid 3209 53 := by unfold smallValid; decide +kernel

private theorem sp3262 : smallValid 3262 54 := by unfold smallValid; decide +kernel

private theorem sp3316 : smallValid 3316 53 := by unfold smallValid; decide +kernel

private theorem sp3369 : smallValid 3369 54 := by unfold smallValid; decide +kernel

private theorem sp3423 : smallValid 3423 53 := by unfold smallValid; decide +kernel

private theorem sp3476 : smallValid 3476 53 := by unfold smallValid; decide +kernel

private theorem sp3529 : smallValid 3529 53 := by unfold smallValid; decide +kernel

private theorem sp3582 : smallValid 3582 54 := by unfold smallValid; decide +kernel

private theorem sp3636 : smallValid 3636 53 := by unfold smallValid; decide +kernel

private theorem sp3689 : smallValid 3689 54 := by unfold smallValid; decide +kernel

private theorem sp3743 : smallValid 3743 53 := by unfold smallValid; decide +kernel

private theorem sp3796 : smallValid 3796 54 := by unfold smallValid; decide +kernel

private theorem sp3850 : smallValid 3850 53 := by unfold smallValid; decide +kernel

private theorem sp3903 : smallValid 3903 54 := by unfold smallValid; decide +kernel

private theorem sp3957 : smallValid 3957 53 := by unfold smallValid; decide +kernel

private theorem sp4010 : smallValid 4010 54 := by unfold smallValid; decide +kernel

private theorem sp4064 : smallValid 4064 53 := by unfold smallValid; decide +kernel

private theorem sp4117 : smallValid 4117 54 := by unfold smallValid; decide +kernel

private theorem sp4171 : smallValid 4171 53 := by unfold smallValid; decide +kernel

private theorem sp4224 : smallValid 4224 54 := by unfold smallValid; decide +kernel

private theorem sp4278 : smallValid 4278 53 := by unfold smallValid; decide +kernel

private theorem sp4331 : smallValid 4331 54 := by unfold smallValid; decide +kernel

private theorem sp4385 : smallValid 4385 53 := by unfold smallValid; decide +kernel

private theorem sp4438 : smallValid 4438 54 := by unfold smallValid; decide +kernel

private theorem sp4492 : smallValid 4492 53 := by unfold smallValid; decide +kernel

private theorem sp4545 : smallValid 4545 54 := by unfold smallValid; decide +kernel

private theorem sp4599 : smallValid 4599 53 := by unfold smallValid; decide +kernel

private theorem sp4652 : smallValid 4652 54 := by unfold smallValid; decide +kernel

private theorem sp4706 : smallValid 4706 53 := by unfold smallValid; decide +kernel

private theorem sp4759 : smallValid 4759 54 := by unfold smallValid; decide +kernel

private theorem sp4813 : smallValid 4813 53 := by unfold smallValid; decide +kernel

private theorem sp4866 : smallValid 4866 54 := by unfold smallValid; decide +kernel

private theorem sp4920 : smallValid 4920 53 := by unfold smallValid; decide +kernel

private theorem sp4973 : smallValid 4973 54 := by unfold smallValid; decide +kernel

private theorem sp5027 : smallValid 5027 53 := by unfold smallValid; decide +kernel

private theorem sp5080 : smallValid 5080 54 := by unfold smallValid; decide +kernel

private theorem sp5134 : smallValid 5134 53 := by unfold smallValid; decide +kernel

private theorem sp5187 : smallValid 5187 54 := by unfold smallValid; decide +kernel

private theorem sp5241 : smallValid 5241 53 := by unfold smallValid; decide +kernel

private theorem sp5294 : smallValid 5294 54 := by unfold smallValid; decide +kernel

private theorem sp5348 : smallValid 5348 53 := by unfold smallValid; decide +kernel

private theorem sp5401 : smallValid 5401 54 := by unfold smallValid; decide +kernel

private theorem sp5455 : smallValid 5455 53 := by unfold smallValid; decide +kernel

private theorem sp5508 : smallValid 5508 54 := by unfold smallValid; decide +kernel

private theorem sp5562 : smallValid 5562 53 := by unfold smallValid; decide +kernel

private theorem sp5615 : smallValid 5615 54 := by unfold smallValid; decide +kernel

private theorem sp5669 : smallValid 5669 53 := by unfold smallValid; decide +kernel

private theorem sp5722 : smallValid 5722 54 := by unfold smallValid; decide +kernel

private theorem sp5776 : smallValid 5776 53 := by unfold smallValid; decide +kernel

private theorem sp5829 : smallValid 5829 54 := by unfold smallValid; decide +kernel

private theorem sp5883 : smallValid 5883 53 := by unfold smallValid; decide +kernel

private theorem sp5936 : smallValid 5936 54 := by unfold smallValid; decide +kernel

private theorem sp5990 : smallValid 5990 53 := by unfold smallValid; decide +kernel

private theorem sp6043 : smallValid 6043 54 := by unfold smallValid; decide +kernel

private theorem sp6097 : smallValid 6097 53 := by unfold smallValid; decide +kernel

private theorem sp6150 : smallValid 6150 54 := by unfold smallValid; decide +kernel

private theorem sp6204 : smallValid 6204 53 := by unfold smallValid; decide +kernel

private theorem sp6257 : smallValid 6257 54 := by unfold smallValid; decide +kernel

private theorem sp6311 : smallValid 6311 53 := by unfold smallValid; decide +kernel

private theorem sp6364 : smallValid 6364 54 := by unfold smallValid; decide +kernel

private theorem sp6418 : smallValid 6418 53 := by unfold smallValid; decide +kernel

private theorem sp6471 : smallValid 6471 54 := by unfold smallValid; decide +kernel

private theorem sp6525 : smallValid 6525 53 := by unfold smallValid; decide +kernel

private theorem sp6578 : smallValid 6578 54 := by unfold smallValid; decide +kernel

private theorem sp6632 : smallValid 6632 53 := by unfold smallValid; decide +kernel

private theorem sp6685 : smallValid 6685 54 := by unfold smallValid; decide +kernel

private theorem sp6739 : smallValid 6739 53 := by unfold smallValid; decide +kernel

private theorem sp6792 : smallValid 6792 54 := by unfold smallValid; decide +kernel

private theorem sp6846 : smallValid 6846 53 := by unfold smallValid; decide +kernel

private theorem sp6899 : smallValid 6899 53 := by unfold smallValid; decide +kernel

private theorem sp6952 : smallValid 6952 53 := by unfold smallValid; decide +kernel

private theorem sp7005 : smallValid 7005 54 := by unfold smallValid; decide +kernel

private theorem sp7059 : smallValid 7059 53 := by unfold smallValid; decide +kernel

private theorem sp7112 : smallValid 7112 54 := by unfold smallValid; decide +kernel

private theorem sp7166 : smallValid 7166 53 := by unfold smallValid; decide +kernel

private theorem sp7219 : smallValid 7219 54 := by unfold smallValid; decide +kernel

private theorem sp7273 : smallValid 7273 53 := by unfold smallValid; decide +kernel

private theorem sp7326 : smallValid 7326 54 := by unfold smallValid; decide +kernel

private theorem sp7380 : smallValid 7380 53 := by unfold smallValid; decide +kernel

private theorem sp7433 : smallValid 7433 54 := by unfold smallValid; decide +kernel

private theorem sp7487 : smallValid 7487 53 := by unfold smallValid; decide +kernel

private theorem sp7540 : smallValid 7540 54 := by unfold smallValid; decide +kernel

private theorem sp7594 : smallValid 7594 53 := by unfold smallValid; decide +kernel

private theorem sp7647 : smallValid 7647 54 := by unfold smallValid; decide +kernel

private theorem sp7701 : smallValid 7701 53 := by unfold smallValid; decide +kernel

private theorem sp7754 : smallValid 7754 54 := by unfold smallValid; decide +kernel

private theorem sp7808 : smallValid 7808 53 := by unfold smallValid; decide +kernel

private theorem sp7861 : smallValid 7861 54 := by unfold smallValid; decide +kernel

private theorem sp7915 : smallValid 7915 53 := by unfold smallValid; decide +kernel

private theorem sp7968 : smallValid 7968 54 := by unfold smallValid; decide +kernel

private theorem sp8022 : smallValid 8022 53 := by unfold smallValid; decide +kernel

private theorem sp8075 : smallValid 8075 54 := by unfold smallValid; decide +kernel

private theorem sp8129 : smallValid 8129 53 := by unfold smallValid; decide +kernel

private theorem sp8182 : smallValid 8182 54 := by unfold smallValid; decide +kernel

private theorem sp8236 : smallValid 8236 53 := by unfold smallValid; decide +kernel

private theorem sp8289 : smallValid 8289 54 := by unfold smallValid; decide +kernel

private theorem sp8343 : smallValid 8343 53 := by unfold smallValid; decide +kernel

private theorem sp8396 : smallValid 8396 54 := by unfold smallValid; decide +kernel

private theorem sp8450 : smallValid 8450 53 := by unfold smallValid; decide +kernel

private theorem sp8503 : smallValid 8503 54 := by unfold smallValid; decide +kernel

private theorem sp8557 : smallValid 8557 53 := by unfold smallValid; decide +kernel

private theorem sp8610 : smallValid 8610 54 := by unfold smallValid; decide +kernel

private theorem sp8664 : smallValid 8664 53 := by unfold smallValid; decide +kernel

private theorem sp8717 : smallValid 8717 54 := by unfold smallValid; decide +kernel

private theorem sp8771 : smallValid 8771 53 := by unfold smallValid; decide +kernel

private theorem sp8824 : smallValid 8824 54 := by unfold smallValid; decide +kernel

private theorem sp8878 : smallValid 8878 53 := by unfold smallValid; decide +kernel

private theorem sp8931 : smallValid 8931 54 := by unfold smallValid; decide +kernel

private theorem sp8985 : smallValid 8985 53 := by unfold smallValid; decide +kernel

private theorem sp9038 : smallValid 9038 54 := by unfold smallValid; decide +kernel

private theorem sp9092 : smallValid 9092 53 := by unfold smallValid; decide +kernel

private theorem sp9145 : smallValid 9145 54 := by unfold smallValid; decide +kernel

private theorem sp9199 : smallValid 9199 53 := by unfold smallValid; decide +kernel

private theorem sp9252 : smallValid 9252 54 := by unfold smallValid; decide +kernel

private theorem sp9306 : smallValid 9306 53 := by unfold smallValid; decide +kernel

private theorem sp9359 : smallValid 9359 54 := by unfold smallValid; decide +kernel

private theorem sp9413 : smallValid 9413 53 := by unfold smallValid; decide +kernel

private theorem sp9466 : smallValid 9466 54 := by unfold smallValid; decide +kernel

private theorem sp9520 : smallValid 9520 53 := by unfold smallValid; decide +kernel

private theorem sp9573 : smallValid 9573 54 := by unfold smallValid; decide +kernel

private theorem sp9627 : smallValid 9627 53 := by unfold smallValid; decide +kernel

private theorem sp9680 : smallValid 9680 54 := by unfold smallValid; decide +kernel

private theorem sp9734 : smallValid 9734 53 := by unfold smallValid; decide +kernel

private theorem sp9787 : smallValid 9787 54 := by unfold smallValid; decide +kernel

private theorem sp9841 : smallValid 9841 53 := by unfold smallValid; decide +kernel

private theorem sp9894 : smallValid 9894 54 := by unfold smallValid; decide +kernel

private theorem sp9948 : smallValid 9948 53 := by unfold smallValid; decide +kernel

private theorem sp10001 : smallValid 10001 54 := by unfold smallValid; decide +kernel

private theorem sp10055 : smallValid 10055 53 := by unfold smallValid; decide +kernel

private theorem sp10108 : smallValid 10108 54 := by unfold smallValid; decide +kernel

private theorem sp10162 : smallValid 10162 53 := by unfold smallValid; decide +kernel

private theorem sp10215 : smallValid 10215 54 := by unfold smallValid; decide +kernel

private theorem sp10269 : smallValid 10269 53 := by unfold smallValid; decide +kernel

private theorem sp10322 : smallValid 10322 54 := by unfold smallValid; decide +kernel

private theorem sp10376 : smallValid 10376 53 := by unfold smallValid; decide +kernel

private theorem sp10429 : smallValid 10429 54 := by unfold smallValid; decide +kernel

private theorem sp10483 : smallValid 10483 53 := by unfold smallValid; decide +kernel

private theorem sp10536 : smallValid 10536 54 := by unfold smallValid; decide +kernel

private theorem sp10590 : smallValid 10590 53 := by unfold smallValid; decide +kernel

private theorem sp10643 : smallValid 10643 54 := by unfold smallValid; decide +kernel

private theorem sp10697 : smallValid 10697 53 := by unfold smallValid; decide +kernel

private theorem sp10750 : smallValid 10750 54 := by unfold smallValid; decide +kernel

private theorem sp10804 : smallValid 10804 53 := by unfold smallValid; decide +kernel

private theorem sp10857 : smallValid 10857 54 := by unfold smallValid; decide +kernel

private theorem sp10911 : smallValid 10911 53 := by unfold smallValid; decide +kernel

private theorem sp10964 : smallValid 10964 54 := by unfold smallValid; decide +kernel

private theorem sp11018 : smallValid 11018 53 := by unfold smallValid; decide +kernel

private theorem sp11071 : smallValid 11071 54 := by unfold smallValid; decide +kernel

private theorem sp11125 : smallValid 11125 53 := by unfold smallValid; decide +kernel

private theorem sp11178 : smallValid 11178 54 := by unfold smallValid; decide +kernel

private theorem sp11232 : smallValid 11232 53 := by unfold smallValid; decide +kernel

private theorem sp11285 : smallValid 11285 54 := by unfold smallValid; decide +kernel

private theorem sp11339 : smallValid 11339 53 := by unfold smallValid; decide +kernel

private theorem sp11392 : smallValid 11392 54 := by unfold smallValid; decide +kernel

private theorem sp11446 : smallValid 11446 53 := by unfold smallValid; decide +kernel

private theorem sp11499 : smallValid 11499 54 := by unfold smallValid; decide +kernel

private theorem sp11553 : smallValid 11553 53 := by unfold smallValid; decide +kernel

private theorem sp11606 : smallValid 11606 54 := by unfold smallValid; decide +kernel

private theorem sp11660 : smallValid 11660 53 := by unfold smallValid; decide +kernel

private theorem sp11713 : smallValid 11713 54 := by unfold smallValid; decide +kernel

private theorem sp11767 : smallValid 11767 53 := by unfold smallValid; decide +kernel

private theorem sp11820 : smallValid 11820 54 := by unfold smallValid; decide +kernel

private theorem sp11874 : smallValid 11874 53 := by unfold smallValid; decide +kernel

private theorem sp11927 : smallValid 11927 54 := by unfold smallValid; decide +kernel

private theorem sp11981 : smallValid 11981 53 := by unfold smallValid; decide +kernel

private theorem sp12034 : smallValid 12034 54 := by unfold smallValid; decide +kernel

private theorem sp12088 : smallValid 12088 53 := by unfold smallValid; decide +kernel

private theorem sp12141 : smallValid 12141 54 := by unfold smallValid; decide +kernel

private theorem sp12195 : smallValid 12195 53 := by unfold smallValid; decide +kernel

private theorem sp12248 : smallValid 12248 54 := by unfold smallValid; decide +kernel

private theorem sp12302 : smallValid 12302 53 := by unfold smallValid; decide +kernel

private theorem sp12355 : smallValid 12355 54 := by unfold smallValid; decide +kernel

private theorem sp12409 : smallValid 12409 53 := by unfold smallValid; decide +kernel

private theorem sp12462 : smallValid 12462 54 := by unfold smallValid; decide +kernel

private theorem sp12516 : smallValid 12516 53 := by unfold smallValid; decide +kernel

private theorem sp12569 : smallValid 12569 54 := by unfold smallValid; decide +kernel

private theorem sp12623 : smallValid 12623 53 := by unfold smallValid; decide +kernel

private theorem sp12676 : smallValid 12676 54 := by unfold smallValid; decide +kernel

private theorem sp12730 : smallValid 12730 53 := by unfold smallValid; decide +kernel

private theorem sp12783 : smallValid 12783 54 := by unfold smallValid; decide +kernel

private theorem sp12837 : smallValid 12837 53 := by unfold smallValid; decide +kernel

private theorem sp12890 : smallValid 12890 54 := by unfold smallValid; decide +kernel

private theorem sp12944 : smallValid 12944 53 := by unfold smallValid; decide +kernel

private theorem sp12997 : smallValid 12997 54 := by unfold smallValid; decide +kernel

private theorem sp13051 : smallValid 13051 53 := by unfold smallValid; decide +kernel

private theorem sp13104 : smallValid 13104 54 := by unfold smallValid; decide +kernel

private theorem sp13158 : smallValid 13158 53 := by unfold smallValid; decide +kernel

private theorem sp13211 : smallValid 13211 54 := by unfold smallValid; decide +kernel

private theorem sp13265 : smallValid 13265 53 := by unfold smallValid; decide +kernel

private theorem sp13318 : smallValid 13318 54 := by unfold smallValid; decide +kernel

private theorem sp13372 : smallValid 13372 53 := by unfold smallValid; decide +kernel

private theorem sp13425 : smallValid 13425 54 := by unfold smallValid; decide +kernel

private theorem sp13479 : smallValid 13479 53 := by unfold smallValid; decide +kernel

private theorem sp13532 : smallValid 13532 54 := by unfold smallValid; decide +kernel

private theorem sp13586 : smallValid 13586 53 := by unfold smallValid; decide +kernel

private theorem sp13639 : smallValid 13639 54 := by unfold smallValid; decide +kernel

private theorem sp13693 : smallValid 13693 53 := by unfold smallValid; decide +kernel

private theorem sp13746 : smallValid 13746 53 := by unfold smallValid; decide +kernel

private theorem sp13799 : smallValid 13799 53 := by unfold smallValid; decide +kernel

private theorem sp13852 : smallValid 13852 54 := by unfold smallValid; decide +kernel

private theorem sp13906 : smallValid 13906 53 := by unfold smallValid; decide +kernel

private theorem sp13959 : smallValid 13959 54 := by unfold smallValid; decide +kernel

private theorem sp14013 : smallValid 14013 53 := by unfold smallValid; decide +kernel

private theorem sp14066 : smallValid 14066 54 := by unfold smallValid; decide +kernel

private theorem sp14120 : smallValid 14120 53 := by unfold smallValid; decide +kernel

private theorem sp14173 : smallValid 14173 54 := by unfold smallValid; decide +kernel

private theorem sp14227 : smallValid 14227 53 := by unfold smallValid; decide +kernel

private theorem sp14280 : smallValid 14280 54 := by unfold smallValid; decide +kernel

private theorem sp14334 : smallValid 14334 53 := by unfold smallValid; decide +kernel

private theorem sp14387 : smallValid 14387 54 := by unfold smallValid; decide +kernel

private theorem sp14441 : smallValid 14441 53 := by unfold smallValid; decide +kernel

private theorem sp14494 : smallValid 14494 54 := by unfold smallValid; decide +kernel

private theorem sp14548 : smallValid 14548 53 := by unfold smallValid; decide +kernel

private theorem sp14601 : smallValid 14601 54 := by unfold smallValid; decide +kernel

private theorem sp14655 : smallValid 14655 53 := by unfold smallValid; decide +kernel

private theorem sp14708 : smallValid 14708 54 := by unfold smallValid; decide +kernel

private theorem sp14762 : smallValid 14762 53 := by unfold smallValid; decide +kernel

private theorem sp14815 : smallValid 14815 54 := by unfold smallValid; decide +kernel

private theorem sp14869 : smallValid 14869 53 := by unfold smallValid; decide +kernel

private theorem sp14922 : smallValid 14922 54 := by unfold smallValid; decide +kernel

private theorem sp14976 : smallValid 14976 53 := by unfold smallValid; decide +kernel

private theorem sp15029 : smallValid 15029 54 := by unfold smallValid; decide +kernel

private theorem sp15083 : smallValid 15083 53 := by unfold smallValid; decide +kernel

private theorem sp15136 : smallValid 15136 54 := by unfold smallValid; decide +kernel

private theorem sp15190 : smallValid 15190 53 := by unfold smallValid; decide +kernel

private theorem sp15243 : smallValid 15243 54 := by unfold smallValid; decide +kernel

private theorem sp15297 : smallValid 15297 53 := by unfold smallValid; decide +kernel

private theorem sp15350 : smallValid 15350 54 := by unfold smallValid; decide +kernel

private theorem sp15404 : smallValid 15404 53 := by unfold smallValid; decide +kernel

private theorem sp15457 : smallValid 15457 54 := by unfold smallValid; decide +kernel

private theorem sp15511 : smallValid 15511 53 := by unfold smallValid; decide +kernel

private theorem sp15564 : smallValid 15564 54 := by unfold smallValid; decide +kernel

private theorem sp15618 : smallValid 15618 53 := by unfold smallValid; decide +kernel

private theorem sp15671 : smallValid 15671 54 := by unfold smallValid; decide +kernel

private theorem sp15725 : smallValid 15725 53 := by unfold smallValid; decide +kernel

private theorem sp15778 : smallValid 15778 54 := by unfold smallValid; decide +kernel

private theorem sp15832 : smallValid 15832 53 := by unfold smallValid; decide +kernel

private theorem sp15885 : smallValid 15885 54 := by unfold smallValid; decide +kernel

private theorem sp15939 : smallValid 15939 53 := by unfold smallValid; decide +kernel

private theorem sp15992 : smallValid 15992 54 := by unfold smallValid; decide +kernel

private theorem sp16046 : smallValid 16046 53 := by unfold smallValid; decide +kernel

private theorem sp16099 : smallValid 16099 54 := by unfold smallValid; decide +kernel

private theorem sp16153 : smallValid 16153 53 := by unfold smallValid; decide +kernel

private theorem sp16206 : smallValid 16206 54 := by unfold smallValid; decide +kernel

private theorem sp16260 : smallValid 16260 53 := by unfold smallValid; decide +kernel

private theorem sp16313 : smallValid 16313 54 := by unfold smallValid; decide +kernel

private theorem sp16367 : smallValid 16367 53 := by unfold smallValid; decide +kernel

private theorem sp16420 : smallValid 16420 54 := by unfold smallValid; decide +kernel

private theorem sp16474 : smallValid 16474 53 := by unfold smallValid; decide +kernel

private theorem sp16527 : smallValid 16527 54 := by unfold smallValid; decide +kernel

private theorem sp16581 : smallValid 16581 53 := by unfold smallValid; decide +kernel

private theorem sp16634 : smallValid 16634 54 := by unfold smallValid; decide +kernel

private theorem sp16688 : smallValid 16688 53 := by unfold smallValid; decide +kernel

private theorem sp16741 : smallValid 16741 54 := by unfold smallValid; decide +kernel

private theorem sp16795 : smallValid 16795 53 := by unfold smallValid; decide +kernel

private theorem sp16848 : smallValid 16848 54 := by unfold smallValid; decide +kernel

private theorem sp16902 : smallValid 16902 53 := by unfold smallValid; decide +kernel

private theorem sp16955 : smallValid 16955 54 := by unfold smallValid; decide +kernel

private theorem sp17009 : smallValid 17009 53 := by unfold smallValid; decide +kernel

private theorem sp17062 : smallValid 17062 54 := by unfold smallValid; decide +kernel

private theorem sp17116 : smallValid 17116 53 := by unfold smallValid; decide +kernel

private theorem sp17169 : smallValid 17169 54 := by unfold smallValid; decide +kernel

private theorem sp17223 : smallValid 17223 53 := by unfold smallValid; decide +kernel

private theorem sp17276 : smallValid 17276 54 := by unfold smallValid; decide +kernel

private theorem sp17330 : smallValid 17330 53 := by unfold smallValid; decide +kernel

private theorem sp17383 : smallValid 17383 54 := by unfold smallValid; decide +kernel

private theorem sp17437 : smallValid 17437 53 := by unfold smallValid; decide +kernel

private theorem sp17490 : smallValid 17490 54 := by unfold smallValid; decide +kernel

private theorem sp17544 : smallValid 17544 53 := by unfold smallValid; decide +kernel

private theorem sp17597 : smallValid 17597 54 := by unfold smallValid; decide +kernel

private theorem sp17651 : smallValid 17651 53 := by unfold smallValid; decide +kernel

private theorem sp17704 : smallValid 17704 54 := by unfold smallValid; decide +kernel

private theorem sp17758 : smallValid 17758 53 := by unfold smallValid; decide +kernel

private theorem sp17811 : smallValid 17811 54 := by unfold smallValid; decide +kernel

private theorem sp17865 : smallValid 17865 53 := by unfold smallValid; decide +kernel

private theorem sp17918 : smallValid 17918 54 := by unfold smallValid; decide +kernel

private theorem sp17972 : smallValid 17972 53 := by unfold smallValid; decide +kernel

private theorem sp18025 : smallValid 18025 54 := by unfold smallValid; decide +kernel

private theorem sp18079 : smallValid 18079 53 := by unfold smallValid; decide +kernel

private theorem sp18132 : smallValid 18132 54 := by unfold smallValid; decide +kernel

private theorem sp18186 : smallValid 18186 53 := by unfold smallValid; decide +kernel

private theorem sp18239 : smallValid 18239 54 := by unfold smallValid; decide +kernel

private theorem sp18293 : smallValid 18293 53 := by unfold smallValid; decide +kernel

private theorem sp18346 : smallValid 18346 54 := by unfold smallValid; decide +kernel

private theorem sp18400 : smallValid 18400 53 := by unfold smallValid; decide +kernel

private theorem sp18453 : smallValid 18453 54 := by unfold smallValid; decide +kernel

private theorem sp18507 : smallValid 18507 53 := by unfold smallValid; decide +kernel

private theorem sp18560 : smallValid 18560 54 := by unfold smallValid; decide +kernel

private theorem sp18614 : smallValid 18614 53 := by unfold smallValid; decide +kernel

private theorem sp18667 : smallValid 18667 54 := by unfold smallValid; decide +kernel

private theorem sp18721 : smallValid 18721 53 := by unfold smallValid; decide +kernel

private theorem sp18774 : smallValid 18774 54 := by unfold smallValid; decide +kernel

private theorem sp18828 : smallValid 18828 53 := by unfold smallValid; decide +kernel

private theorem sp18881 : smallValid 18881 54 := by unfold smallValid; decide +kernel

private theorem sp18935 : smallValid 18935 53 := by unfold smallValid; decide +kernel

private theorem sp18988 : smallValid 18988 54 := by unfold smallValid; decide +kernel

private theorem sp19042 : smallValid 19042 53 := by unfold smallValid; decide +kernel

private theorem sp19095 : smallValid 19095 54 := by unfold smallValid; decide +kernel

private theorem sp19149 : smallValid 19149 53 := by unfold smallValid; decide +kernel

private theorem sp19202 : smallValid 19202 54 := by unfold smallValid; decide +kernel

private theorem sp19256 : smallValid 19256 53 := by unfold smallValid; decide +kernel

private theorem sp19309 : smallValid 19309 54 := by unfold smallValid; decide +kernel

private theorem sp19363 : smallValid 19363 53 := by unfold smallValid; decide +kernel

private theorem sp19416 : smallValid 19416 54 := by unfold smallValid; decide +kernel

private theorem sp19470 : smallValid 19470 53 := by unfold smallValid; decide +kernel

private theorem sp19523 : smallValid 19523 54 := by unfold smallValid; decide +kernel

private theorem sp19577 : smallValid 19577 53 := by unfold smallValid; decide +kernel

private theorem sp19630 : smallValid 19630 54 := by unfold smallValid; decide +kernel

private theorem sp19684 : smallValid 19684 53 := by unfold smallValid; decide +kernel

private theorem sp19737 : smallValid 19737 54 := by unfold smallValid; decide +kernel

private theorem sp19791 : smallValid 19791 53 := by unfold smallValid; decide +kernel

private theorem sp19844 : smallValid 19844 54 := by unfold smallValid; decide +kernel

private theorem sp19898 : smallValid 19898 53 := by unfold smallValid; decide +kernel

private theorem sp19951 : smallValid 19951 54 := by unfold smallValid; decide +kernel

private theorem sp20005 : smallValid 20005 53 := by unfold smallValid; decide +kernel

private theorem sp20058 : smallValid 20058 54 := by unfold smallValid; decide +kernel

private theorem sp20112 : smallValid 20112 53 := by unfold smallValid; decide +kernel

private theorem sp20165 : smallValid 20165 54 := by unfold smallValid; decide +kernel

private theorem sp20219 : smallValid 20219 53 := by unfold smallValid; decide +kernel

private theorem sp20272 : smallValid 20272 54 := by unfold smallValid; decide +kernel

private theorem sp20326 : smallValid 20326 53 := by unfold smallValid; decide +kernel

private theorem sp20379 : smallValid 20379 54 := by unfold smallValid; decide +kernel

private theorem sp20433 : smallValid 20433 53 := by unfold smallValid; decide +kernel

private theorem sp20486 : smallValid 20486 54 := by unfold smallValid; decide +kernel

private theorem sp20540 : smallValid 20540 53 := by unfold smallValid; decide +kernel

private theorem sp20593 : smallValid 20593 53 := by unfold smallValid; decide +kernel

private theorem sp20646 : smallValid 20646 53 := by unfold smallValid; decide +kernel

private theorem sp20699 : smallValid 20699 54 := by unfold smallValid; decide +kernel

private theorem sp20753 : smallValid 20753 53 := by unfold smallValid; decide +kernel

private theorem sp20806 : smallValid 20806 54 := by unfold smallValid; decide +kernel

private theorem sp20860 : smallValid 20860 53 := by unfold smallValid; decide +kernel

private theorem sp20913 : smallValid 20913 54 := by unfold smallValid; decide +kernel

private theorem sp20967 : smallValid 20967 53 := by unfold smallValid; decide +kernel

private theorem sp21020 : smallValid 21020 54 := by unfold smallValid; decide +kernel

private theorem sp21074 : smallValid 21074 53 := by unfold smallValid; decide +kernel

private theorem sp21127 : smallValid 21127 54 := by unfold smallValid; decide +kernel

private theorem sp21181 : smallValid 21181 53 := by unfold smallValid; decide +kernel

private theorem sp21234 : smallValid 21234 54 := by unfold smallValid; decide +kernel

private theorem sp21288 : smallValid 21288 53 := by unfold smallValid; decide +kernel

private theorem sp21341 : smallValid 21341 54 := by unfold smallValid; decide +kernel

private theorem sp21395 : smallValid 21395 53 := by unfold smallValid; decide +kernel

private theorem sp21448 : smallValid 21448 54 := by unfold smallValid; decide +kernel

private theorem sp21502 : smallValid 21502 53 := by unfold smallValid; decide +kernel

private theorem sp21555 : smallValid 21555 54 := by unfold smallValid; decide +kernel

private theorem sp21609 : smallValid 21609 53 := by unfold smallValid; decide +kernel

private theorem sp21662 : smallValid 21662 54 := by unfold smallValid; decide +kernel

private theorem sp21716 : smallValid 21716 53 := by unfold smallValid; decide +kernel

private theorem sp21769 : smallValid 21769 54 := by unfold smallValid; decide +kernel

private theorem sp21823 : smallValid 21823 53 := by unfold smallValid; decide +kernel

private theorem sp21876 : smallValid 21876 54 := by unfold smallValid; decide +kernel

private theorem sp21930 : smallValid 21930 53 := by unfold smallValid; decide +kernel

private theorem sp21983 : smallValid 21983 54 := by unfold smallValid; decide +kernel

private theorem sp22037 : smallValid 22037 53 := by unfold smallValid; decide +kernel

private theorem sp22090 : smallValid 22090 54 := by unfold smallValid; decide +kernel

private theorem sp22144 : smallValid 22144 53 := by unfold smallValid; decide +kernel

private theorem sp22197 : smallValid 22197 54 := by unfold smallValid; decide +kernel

private theorem sp22251 : smallValid 22251 53 := by unfold smallValid; decide +kernel

private theorem sp22304 : smallValid 22304 54 := by unfold smallValid; decide +kernel

private theorem sp22358 : smallValid 22358 53 := by unfold smallValid; decide +kernel

private theorem sp22411 : smallValid 22411 54 := by unfold smallValid; decide +kernel

private theorem sp22465 : smallValid 22465 53 := by unfold smallValid; decide +kernel

private theorem sp22518 : smallValid 22518 54 := by unfold smallValid; decide +kernel

private theorem sp22572 : smallValid 22572 53 := by unfold smallValid; decide +kernel

private theorem sp22625 : smallValid 22625 54 := by unfold smallValid; decide +kernel

private theorem sp22679 : smallValid 22679 53 := by unfold smallValid; decide +kernel

private theorem sp22732 : smallValid 22732 54 := by unfold smallValid; decide +kernel

private theorem sp22786 : smallValid 22786 53 := by unfold smallValid; decide +kernel

private theorem sp22839 : smallValid 22839 54 := by unfold smallValid; decide +kernel

private theorem sp22893 : smallValid 22893 53 := by unfold smallValid; decide +kernel

private theorem sp22946 : smallValid 22946 54 := by unfold smallValid; decide +kernel

private theorem sp23000 : smallValid 23000 53 := by unfold smallValid; decide +kernel

private theorem sp23053 : smallValid 23053 54 := by unfold smallValid; decide +kernel

private theorem sp23107 : smallValid 23107 53 := by unfold smallValid; decide +kernel

private theorem sp23160 : smallValid 23160 54 := by unfold smallValid; decide +kernel

private theorem sp23214 : smallValid 23214 53 := by unfold smallValid; decide +kernel

private theorem sp23267 : smallValid 23267 54 := by unfold smallValid; decide +kernel

private theorem sp23321 : smallValid 23321 53 := by unfold smallValid; decide +kernel

private theorem sp23374 : smallValid 23374 54 := by unfold smallValid; decide +kernel

private theorem sp23428 : smallValid 23428 53 := by unfold smallValid; decide +kernel

private theorem sp23481 : smallValid 23481 54 := by unfold smallValid; decide +kernel

private theorem sp23535 : smallValid 23535 53 := by unfold smallValid; decide +kernel

private theorem sp23588 : smallValid 23588 54 := by unfold smallValid; decide +kernel

private theorem sp23642 : smallValid 23642 53 := by unfold smallValid; decide +kernel

private theorem sp23695 : smallValid 23695 54 := by unfold smallValid; decide +kernel

private theorem sp23749 : smallValid 23749 53 := by unfold smallValid; decide +kernel

private theorem sp23802 : smallValid 23802 54 := by unfold smallValid; decide +kernel

private theorem sp23856 : smallValid 23856 53 := by unfold smallValid; decide +kernel

private theorem sp23909 : smallValid 23909 54 := by unfold smallValid; decide +kernel

private theorem sp23963 : smallValid 23963 53 := by unfold smallValid; decide +kernel

private theorem sp24016 : smallValid 24016 54 := by unfold smallValid; decide +kernel

private theorem sp24070 : smallValid 24070 53 := by unfold smallValid; decide +kernel

private theorem sp24123 : smallValid 24123 54 := by unfold smallValid; decide +kernel

private theorem sp24177 : smallValid 24177 53 := by unfold smallValid; decide +kernel

private theorem sp24230 : smallValid 24230 54 := by unfold smallValid; decide +kernel

private theorem sp24284 : smallValid 24284 53 := by unfold smallValid; decide +kernel

private theorem sp24337 : smallValid 24337 54 := by unfold smallValid; decide +kernel

private theorem sp24391 : smallValid 24391 53 := by unfold smallValid; decide +kernel

private theorem sp24444 : smallValid 24444 54 := by unfold smallValid; decide +kernel

private theorem sp24498 : smallValid 24498 53 := by unfold smallValid; decide +kernel

private theorem sp24551 : smallValid 24551 54 := by unfold smallValid; decide +kernel

private theorem sp24605 : smallValid 24605 53 := by unfold smallValid; decide +kernel

private theorem sp24658 : smallValid 24658 54 := by unfold smallValid; decide +kernel

private theorem sp24712 : smallValid 24712 53 := by unfold smallValid; decide +kernel

private theorem sp24765 : smallValid 24765 54 := by unfold smallValid; decide +kernel

private theorem sp24819 : smallValid 24819 53 := by unfold smallValid; decide +kernel

private theorem sp24872 : smallValid 24872 54 := by unfold smallValid; decide +kernel

private theorem sp24926 : smallValid 24926 53 := by unfold smallValid; decide +kernel

private theorem sp24979 : smallValid 24979 54 := by unfold smallValid; decide +kernel

private theorem sp25033 : smallValid 25033 53 := by unfold smallValid; decide +kernel

private theorem sp25086 : smallValid 25086 54 := by unfold smallValid; decide +kernel

private theorem sp25140 : smallValid 25140 53 := by unfold smallValid; decide +kernel

private theorem sp25193 : smallValid 25193 54 := by unfold smallValid; decide +kernel

private theorem sp25247 : smallValid 25247 53 := by unfold smallValid; decide +kernel

private theorem sp25300 : smallValid 25300 54 := by unfold smallValid; decide +kernel

private theorem sp25354 : smallValid 25354 53 := by unfold smallValid; decide +kernel

private theorem sp25407 : smallValid 25407 54 := by unfold smallValid; decide +kernel

private theorem sp25461 : smallValid 25461 53 := by unfold smallValid; decide +kernel

private theorem sp25514 : smallValid 25514 54 := by unfold smallValid; decide +kernel

private theorem sp25568 : smallValid 25568 53 := by unfold smallValid; decide +kernel

private theorem sp25621 : smallValid 25621 54 := by unfold smallValid; decide +kernel

private theorem sp25675 : smallValid 25675 53 := by unfold smallValid; decide +kernel

private theorem sp25728 : smallValid 25728 54 := by unfold smallValid; decide +kernel

private theorem sp25782 : smallValid 25782 53 := by unfold smallValid; decide +kernel

private theorem sp25835 : smallValid 25835 54 := by unfold smallValid; decide +kernel

private theorem sp25889 : smallValid 25889 53 := by unfold smallValid; decide +kernel

private theorem sp25942 : smallValid 25942 54 := by unfold smallValid; decide +kernel

private theorem sp25996 : smallValid 25996 53 := by unfold smallValid; decide +kernel

private theorem sp26049 : smallValid 26049 54 := by unfold smallValid; decide +kernel

private theorem sp26103 : smallValid 26103 53 := by unfold smallValid; decide +kernel

private theorem sp26156 : smallValid 26156 54 := by unfold smallValid; decide +kernel

private theorem sp26210 : smallValid 26210 53 := by unfold smallValid; decide +kernel

private theorem sp26263 : smallValid 26263 54 := by unfold smallValid; decide +kernel

private theorem sp26317 : smallValid 26317 53 := by unfold smallValid; decide +kernel

private theorem sp26370 : smallValid 26370 54 := by unfold smallValid; decide +kernel

private theorem sp26424 : smallValid 26424 53 := by unfold smallValid; decide +kernel

private theorem sp26477 : smallValid 26477 54 := by unfold smallValid; decide +kernel

private theorem sp26531 : smallValid 26531 53 := by unfold smallValid; decide +kernel

private theorem sp26584 : smallValid 26584 54 := by unfold smallValid; decide +kernel

private theorem sp26638 : smallValid 26638 53 := by unfold smallValid; decide +kernel

private theorem sp26691 : smallValid 26691 54 := by unfold smallValid; decide +kernel

private theorem sp26745 : smallValid 26745 53 := by unfold smallValid; decide +kernel

private theorem sp26798 : smallValid 26798 54 := by unfold smallValid; decide +kernel

private theorem sp26852 : smallValid 26852 53 := by unfold smallValid; decide +kernel

private theorem sp26905 : smallValid 26905 54 := by unfold smallValid; decide +kernel

private theorem sp26959 : smallValid 26959 53 := by unfold smallValid; decide +kernel

private theorem sp27012 : smallValid 27012 54 := by unfold smallValid; decide +kernel

private theorem sp27066 : smallValid 27066 53 := by unfold smallValid; decide +kernel

private theorem sp27119 : smallValid 27119 54 := by unfold smallValid; decide +kernel

private theorem sp27173 : smallValid 27173 53 := by unfold smallValid; decide +kernel

private theorem sp27226 : smallValid 27226 54 := by unfold smallValid; decide +kernel

private theorem sp27280 : smallValid 27280 53 := by unfold smallValid; decide +kernel

private theorem sp27333 : smallValid 27333 54 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤27386) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 27387 := (joinSmall (lo:=0) (a:=13693) (b:=13694) (joinSmall (lo:=0) (a:=6846) (b:=6847) (joinSmall (lo:=0) (a:=3423) (b:=3423) (joinSmall (lo:=0) (a:=1711) (b:=1712) (joinSmall (lo:=0) (a:=855) (b:=856) (joinSmall (lo:=0) (a:=427) (b:=428) (joinSmall (lo:=0) (a:=213) (b:=214) (joinSmall (lo:=0) (a:=106) (b:=107) (joinSmall (lo:=0) (a:=53) (b:=53) sp0 sp53) (joinSmall (lo:=106) (a:=53) (b:=54) sp106 sp159)) (joinSmall (lo:=213) (a:=107) (b:=107) (joinSmall (lo:=213) (a:=53) (b:=54) sp213 sp266) (joinSmall (lo:=320) (a:=53) (b:=54) sp320 sp373))) (joinSmall (lo:=427) (a:=214) (b:=214) (joinSmall (lo:=427) (a:=107) (b:=107) (joinSmall (lo:=427) (a:=53) (b:=54) sp427 sp480) (joinSmall (lo:=534) (a:=53) (b:=54) sp534 sp587)) (joinSmall (lo:=641) (a:=107) (b:=107) (joinSmall (lo:=641) (a:=53) (b:=54) sp641 sp694) (joinSmall (lo:=748) (a:=53) (b:=54) sp748 sp801)))) (joinSmall (lo:=855) (a:=428) (b:=428) (joinSmall (lo:=855) (a:=214) (b:=214) (joinSmall (lo:=855) (a:=107) (b:=107) (joinSmall (lo:=855) (a:=53) (b:=54) sp855 sp908) (joinSmall (lo:=962) (a:=53) (b:=54) sp962 sp1015)) (joinSmall (lo:=1069) (a:=107) (b:=107) (joinSmall (lo:=1069) (a:=53) (b:=54) sp1069 sp1122) (joinSmall (lo:=1176) (a:=53) (b:=54) sp1176 sp1229))) (joinSmall (lo:=1283) (a:=214) (b:=214) (joinSmall (lo:=1283) (a:=107) (b:=107) (joinSmall (lo:=1283) (a:=53) (b:=54) sp1283 sp1336) (joinSmall (lo:=1390) (a:=53) (b:=54) sp1390 sp1443)) (joinSmall (lo:=1497) (a:=107) (b:=107) (joinSmall (lo:=1497) (a:=53) (b:=54) sp1497 sp1550) (joinSmall (lo:=1604) (a:=53) (b:=54) sp1604 sp1657))))) (joinSmall (lo:=1711) (a:=856) (b:=856) (joinSmall (lo:=1711) (a:=428) (b:=428) (joinSmall (lo:=1711) (a:=214) (b:=214) (joinSmall (lo:=1711) (a:=107) (b:=107) (joinSmall (lo:=1711) (a:=53) (b:=54) sp1711 sp1764) (joinSmall (lo:=1818) (a:=53) (b:=54) sp1818 sp1871)) (joinSmall (lo:=1925) (a:=107) (b:=107) (joinSmall (lo:=1925) (a:=53) (b:=54) sp1925 sp1978) (joinSmall (lo:=2032) (a:=53) (b:=54) sp2032 sp2085))) (joinSmall (lo:=2139) (a:=214) (b:=214) (joinSmall (lo:=2139) (a:=107) (b:=107) (joinSmall (lo:=2139) (a:=53) (b:=54) sp2139 sp2192) (joinSmall (lo:=2246) (a:=53) (b:=54) sp2246 sp2299)) (joinSmall (lo:=2353) (a:=107) (b:=107) (joinSmall (lo:=2353) (a:=53) (b:=54) sp2353 sp2406) (joinSmall (lo:=2460) (a:=53) (b:=54) sp2460 sp2513)))) (joinSmall (lo:=2567) (a:=428) (b:=428) (joinSmall (lo:=2567) (a:=214) (b:=214) (joinSmall (lo:=2567) (a:=107) (b:=107) (joinSmall (lo:=2567) (a:=53) (b:=54) sp2567 sp2620) (joinSmall (lo:=2674) (a:=53) (b:=54) sp2674 sp2727)) (joinSmall (lo:=2781) (a:=107) (b:=107) (joinSmall (lo:=2781) (a:=53) (b:=54) sp2781 sp2834) (joinSmall (lo:=2888) (a:=53) (b:=54) sp2888 sp2941))) (joinSmall (lo:=2995) (a:=214) (b:=214) (joinSmall (lo:=2995) (a:=107) (b:=107) (joinSmall (lo:=2995) (a:=53) (b:=54) sp2995 sp3048) (joinSmall (lo:=3102) (a:=53) (b:=54) sp3102 sp3155)) (joinSmall (lo:=3209) (a:=107) (b:=107) (joinSmall (lo:=3209) (a:=53) (b:=54) sp3209 sp3262) (joinSmall (lo:=3316) (a:=53) (b:=54) sp3316 sp3369)))))) (joinSmall (lo:=3423) (a:=1711) (b:=1712) (joinSmall (lo:=3423) (a:=855) (b:=856) (joinSmall (lo:=3423) (a:=427) (b:=428) (joinSmall (lo:=3423) (a:=213) (b:=214) (joinSmall (lo:=3423) (a:=106) (b:=107) (joinSmall (lo:=3423) (a:=53) (b:=53) sp3423 sp3476) (joinSmall (lo:=3529) (a:=53) (b:=54) sp3529 sp3582)) (joinSmall (lo:=3636) (a:=107) (b:=107) (joinSmall (lo:=3636) (a:=53) (b:=54) sp3636 sp3689) (joinSmall (lo:=3743) (a:=53) (b:=54) sp3743 sp3796))) (joinSmall (lo:=3850) (a:=214) (b:=214) (joinSmall (lo:=3850) (a:=107) (b:=107) (joinSmall (lo:=3850) (a:=53) (b:=54) sp3850 sp3903) (joinSmall (lo:=3957) (a:=53) (b:=54) sp3957 sp4010)) (joinSmall (lo:=4064) (a:=107) (b:=107) (joinSmall (lo:=4064) (a:=53) (b:=54) sp4064 sp4117) (joinSmall (lo:=4171) (a:=53) (b:=54) sp4171 sp4224)))) (joinSmall (lo:=4278) (a:=428) (b:=428) (joinSmall (lo:=4278) (a:=214) (b:=214) (joinSmall (lo:=4278) (a:=107) (b:=107) (joinSmall (lo:=4278) (a:=53) (b:=54) sp4278 sp4331) (joinSmall (lo:=4385) (a:=53) (b:=54) sp4385 sp4438)) (joinSmall (lo:=4492) (a:=107) (b:=107) (joinSmall (lo:=4492) (a:=53) (b:=54) sp4492 sp4545) (joinSmall (lo:=4599) (a:=53) (b:=54) sp4599 sp4652))) (joinSmall (lo:=4706) (a:=214) (b:=214) (joinSmall (lo:=4706) (a:=107) (b:=107) (joinSmall (lo:=4706) (a:=53) (b:=54) sp4706 sp4759) (joinSmall (lo:=4813) (a:=53) (b:=54) sp4813 sp4866)) (joinSmall (lo:=4920) (a:=107) (b:=107) (joinSmall (lo:=4920) (a:=53) (b:=54) sp4920 sp4973) (joinSmall (lo:=5027) (a:=53) (b:=54) sp5027 sp5080))))) (joinSmall (lo:=5134) (a:=856) (b:=856) (joinSmall (lo:=5134) (a:=428) (b:=428) (joinSmall (lo:=5134) (a:=214) (b:=214) (joinSmall (lo:=5134) (a:=107) (b:=107) (joinSmall (lo:=5134) (a:=53) (b:=54) sp5134 sp5187) (joinSmall (lo:=5241) (a:=53) (b:=54) sp5241 sp5294)) (joinSmall (lo:=5348) (a:=107) (b:=107) (joinSmall (lo:=5348) (a:=53) (b:=54) sp5348 sp5401) (joinSmall (lo:=5455) (a:=53) (b:=54) sp5455 sp5508))) (joinSmall (lo:=5562) (a:=214) (b:=214) (joinSmall (lo:=5562) (a:=107) (b:=107) (joinSmall (lo:=5562) (a:=53) (b:=54) sp5562 sp5615) (joinSmall (lo:=5669) (a:=53) (b:=54) sp5669 sp5722)) (joinSmall (lo:=5776) (a:=107) (b:=107) (joinSmall (lo:=5776) (a:=53) (b:=54) sp5776 sp5829) (joinSmall (lo:=5883) (a:=53) (b:=54) sp5883 sp5936)))) (joinSmall (lo:=5990) (a:=428) (b:=428) (joinSmall (lo:=5990) (a:=214) (b:=214) (joinSmall (lo:=5990) (a:=107) (b:=107) (joinSmall (lo:=5990) (a:=53) (b:=54) sp5990 sp6043) (joinSmall (lo:=6097) (a:=53) (b:=54) sp6097 sp6150)) (joinSmall (lo:=6204) (a:=107) (b:=107) (joinSmall (lo:=6204) (a:=53) (b:=54) sp6204 sp6257) (joinSmall (lo:=6311) (a:=53) (b:=54) sp6311 sp6364))) (joinSmall (lo:=6418) (a:=214) (b:=214) (joinSmall (lo:=6418) (a:=107) (b:=107) (joinSmall (lo:=6418) (a:=53) (b:=54) sp6418 sp6471) (joinSmall (lo:=6525) (a:=53) (b:=54) sp6525 sp6578)) (joinSmall (lo:=6632) (a:=107) (b:=107) (joinSmall (lo:=6632) (a:=53) (b:=54) sp6632 sp6685) (joinSmall (lo:=6739) (a:=53) (b:=54) sp6739 sp6792))))))) (joinSmall (lo:=6846) (a:=3423) (b:=3424) (joinSmall (lo:=6846) (a:=1711) (b:=1712) (joinSmall (lo:=6846) (a:=855) (b:=856) (joinSmall (lo:=6846) (a:=427) (b:=428) (joinSmall (lo:=6846) (a:=213) (b:=214) (joinSmall (lo:=6846) (a:=106) (b:=107) (joinSmall (lo:=6846) (a:=53) (b:=53) sp6846 sp6899) (joinSmall (lo:=6952) (a:=53) (b:=54) sp6952 sp7005)) (joinSmall (lo:=7059) (a:=107) (b:=107) (joinSmall (lo:=7059) (a:=53) (b:=54) sp7059 sp7112) (joinSmall (lo:=7166) (a:=53) (b:=54) sp7166 sp7219))) (joinSmall (lo:=7273) (a:=214) (b:=214) (joinSmall (lo:=7273) (a:=107) (b:=107) (joinSmall (lo:=7273) (a:=53) (b:=54) sp7273 sp7326) (joinSmall (lo:=7380) (a:=53) (b:=54) sp7380 sp7433)) (joinSmall (lo:=7487) (a:=107) (b:=107) (joinSmall (lo:=7487) (a:=53) (b:=54) sp7487 sp7540) (joinSmall (lo:=7594) (a:=53) (b:=54) sp7594 sp7647)))) (joinSmall (lo:=7701) (a:=428) (b:=428) (joinSmall (lo:=7701) (a:=214) (b:=214) (joinSmall (lo:=7701) (a:=107) (b:=107) (joinSmall (lo:=7701) (a:=53) (b:=54) sp7701 sp7754) (joinSmall (lo:=7808) (a:=53) (b:=54) sp7808 sp7861)) (joinSmall (lo:=7915) (a:=107) (b:=107) (joinSmall (lo:=7915) (a:=53) (b:=54) sp7915 sp7968) (joinSmall (lo:=8022) (a:=53) (b:=54) sp8022 sp8075))) (joinSmall (lo:=8129) (a:=214) (b:=214) (joinSmall (lo:=8129) (a:=107) (b:=107) (joinSmall (lo:=8129) (a:=53) (b:=54) sp8129 sp8182) (joinSmall (lo:=8236) (a:=53) (b:=54) sp8236 sp8289)) (joinSmall (lo:=8343) (a:=107) (b:=107) (joinSmall (lo:=8343) (a:=53) (b:=54) sp8343 sp8396) (joinSmall (lo:=8450) (a:=53) (b:=54) sp8450 sp8503))))) (joinSmall (lo:=8557) (a:=856) (b:=856) (joinSmall (lo:=8557) (a:=428) (b:=428) (joinSmall (lo:=8557) (a:=214) (b:=214) (joinSmall (lo:=8557) (a:=107) (b:=107) (joinSmall (lo:=8557) (a:=53) (b:=54) sp8557 sp8610) (joinSmall (lo:=8664) (a:=53) (b:=54) sp8664 sp8717)) (joinSmall (lo:=8771) (a:=107) (b:=107) (joinSmall (lo:=8771) (a:=53) (b:=54) sp8771 sp8824) (joinSmall (lo:=8878) (a:=53) (b:=54) sp8878 sp8931))) (joinSmall (lo:=8985) (a:=214) (b:=214) (joinSmall (lo:=8985) (a:=107) (b:=107) (joinSmall (lo:=8985) (a:=53) (b:=54) sp8985 sp9038) (joinSmall (lo:=9092) (a:=53) (b:=54) sp9092 sp9145)) (joinSmall (lo:=9199) (a:=107) (b:=107) (joinSmall (lo:=9199) (a:=53) (b:=54) sp9199 sp9252) (joinSmall (lo:=9306) (a:=53) (b:=54) sp9306 sp9359)))) (joinSmall (lo:=9413) (a:=428) (b:=428) (joinSmall (lo:=9413) (a:=214) (b:=214) (joinSmall (lo:=9413) (a:=107) (b:=107) (joinSmall (lo:=9413) (a:=53) (b:=54) sp9413 sp9466) (joinSmall (lo:=9520) (a:=53) (b:=54) sp9520 sp9573)) (joinSmall (lo:=9627) (a:=107) (b:=107) (joinSmall (lo:=9627) (a:=53) (b:=54) sp9627 sp9680) (joinSmall (lo:=9734) (a:=53) (b:=54) sp9734 sp9787))) (joinSmall (lo:=9841) (a:=214) (b:=214) (joinSmall (lo:=9841) (a:=107) (b:=107) (joinSmall (lo:=9841) (a:=53) (b:=54) sp9841 sp9894) (joinSmall (lo:=9948) (a:=53) (b:=54) sp9948 sp10001)) (joinSmall (lo:=10055) (a:=107) (b:=107) (joinSmall (lo:=10055) (a:=53) (b:=54) sp10055 sp10108) (joinSmall (lo:=10162) (a:=53) (b:=54) sp10162 sp10215)))))) (joinSmall (lo:=10269) (a:=1712) (b:=1712) (joinSmall (lo:=10269) (a:=856) (b:=856) (joinSmall (lo:=10269) (a:=428) (b:=428) (joinSmall (lo:=10269) (a:=214) (b:=214) (joinSmall (lo:=10269) (a:=107) (b:=107) (joinSmall (lo:=10269) (a:=53) (b:=54) sp10269 sp10322) (joinSmall (lo:=10376) (a:=53) (b:=54) sp10376 sp10429)) (joinSmall (lo:=10483) (a:=107) (b:=107) (joinSmall (lo:=10483) (a:=53) (b:=54) sp10483 sp10536) (joinSmall (lo:=10590) (a:=53) (b:=54) sp10590 sp10643))) (joinSmall (lo:=10697) (a:=214) (b:=214) (joinSmall (lo:=10697) (a:=107) (b:=107) (joinSmall (lo:=10697) (a:=53) (b:=54) sp10697 sp10750) (joinSmall (lo:=10804) (a:=53) (b:=54) sp10804 sp10857)) (joinSmall (lo:=10911) (a:=107) (b:=107) (joinSmall (lo:=10911) (a:=53) (b:=54) sp10911 sp10964) (joinSmall (lo:=11018) (a:=53) (b:=54) sp11018 sp11071)))) (joinSmall (lo:=11125) (a:=428) (b:=428) (joinSmall (lo:=11125) (a:=214) (b:=214) (joinSmall (lo:=11125) (a:=107) (b:=107) (joinSmall (lo:=11125) (a:=53) (b:=54) sp11125 sp11178) (joinSmall (lo:=11232) (a:=53) (b:=54) sp11232 sp11285)) (joinSmall (lo:=11339) (a:=107) (b:=107) (joinSmall (lo:=11339) (a:=53) (b:=54) sp11339 sp11392) (joinSmall (lo:=11446) (a:=53) (b:=54) sp11446 sp11499))) (joinSmall (lo:=11553) (a:=214) (b:=214) (joinSmall (lo:=11553) (a:=107) (b:=107) (joinSmall (lo:=11553) (a:=53) (b:=54) sp11553 sp11606) (joinSmall (lo:=11660) (a:=53) (b:=54) sp11660 sp11713)) (joinSmall (lo:=11767) (a:=107) (b:=107) (joinSmall (lo:=11767) (a:=53) (b:=54) sp11767 sp11820) (joinSmall (lo:=11874) (a:=53) (b:=54) sp11874 sp11927))))) (joinSmall (lo:=11981) (a:=856) (b:=856) (joinSmall (lo:=11981) (a:=428) (b:=428) (joinSmall (lo:=11981) (a:=214) (b:=214) (joinSmall (lo:=11981) (a:=107) (b:=107) (joinSmall (lo:=11981) (a:=53) (b:=54) sp11981 sp12034) (joinSmall (lo:=12088) (a:=53) (b:=54) sp12088 sp12141)) (joinSmall (lo:=12195) (a:=107) (b:=107) (joinSmall (lo:=12195) (a:=53) (b:=54) sp12195 sp12248) (joinSmall (lo:=12302) (a:=53) (b:=54) sp12302 sp12355))) (joinSmall (lo:=12409) (a:=214) (b:=214) (joinSmall (lo:=12409) (a:=107) (b:=107) (joinSmall (lo:=12409) (a:=53) (b:=54) sp12409 sp12462) (joinSmall (lo:=12516) (a:=53) (b:=54) sp12516 sp12569)) (joinSmall (lo:=12623) (a:=107) (b:=107) (joinSmall (lo:=12623) (a:=53) (b:=54) sp12623 sp12676) (joinSmall (lo:=12730) (a:=53) (b:=54) sp12730 sp12783)))) (joinSmall (lo:=12837) (a:=428) (b:=428) (joinSmall (lo:=12837) (a:=214) (b:=214) (joinSmall (lo:=12837) (a:=107) (b:=107) (joinSmall (lo:=12837) (a:=53) (b:=54) sp12837 sp12890) (joinSmall (lo:=12944) (a:=53) (b:=54) sp12944 sp12997)) (joinSmall (lo:=13051) (a:=107) (b:=107) (joinSmall (lo:=13051) (a:=53) (b:=54) sp13051 sp13104) (joinSmall (lo:=13158) (a:=53) (b:=54) sp13158 sp13211))) (joinSmall (lo:=13265) (a:=214) (b:=214) (joinSmall (lo:=13265) (a:=107) (b:=107) (joinSmall (lo:=13265) (a:=53) (b:=54) sp13265 sp13318) (joinSmall (lo:=13372) (a:=53) (b:=54) sp13372 sp13425)) (joinSmall (lo:=13479) (a:=107) (b:=107) (joinSmall (lo:=13479) (a:=53) (b:=54) sp13479 sp13532) (joinSmall (lo:=13586) (a:=53) (b:=54) sp13586 sp13639)))))))) (joinSmall (lo:=13693) (a:=6847) (b:=6847) (joinSmall (lo:=13693) (a:=3423) (b:=3424) (joinSmall (lo:=13693) (a:=1711) (b:=1712) (joinSmall (lo:=13693) (a:=855) (b:=856) (joinSmall (lo:=13693) (a:=427) (b:=428) (joinSmall (lo:=13693) (a:=213) (b:=214) (joinSmall (lo:=13693) (a:=106) (b:=107) (joinSmall (lo:=13693) (a:=53) (b:=53) sp13693 sp13746) (joinSmall (lo:=13799) (a:=53) (b:=54) sp13799 sp13852)) (joinSmall (lo:=13906) (a:=107) (b:=107) (joinSmall (lo:=13906) (a:=53) (b:=54) sp13906 sp13959) (joinSmall (lo:=14013) (a:=53) (b:=54) sp14013 sp14066))) (joinSmall (lo:=14120) (a:=214) (b:=214) (joinSmall (lo:=14120) (a:=107) (b:=107) (joinSmall (lo:=14120) (a:=53) (b:=54) sp14120 sp14173) (joinSmall (lo:=14227) (a:=53) (b:=54) sp14227 sp14280)) (joinSmall (lo:=14334) (a:=107) (b:=107) (joinSmall (lo:=14334) (a:=53) (b:=54) sp14334 sp14387) (joinSmall (lo:=14441) (a:=53) (b:=54) sp14441 sp14494)))) (joinSmall (lo:=14548) (a:=428) (b:=428) (joinSmall (lo:=14548) (a:=214) (b:=214) (joinSmall (lo:=14548) (a:=107) (b:=107) (joinSmall (lo:=14548) (a:=53) (b:=54) sp14548 sp14601) (joinSmall (lo:=14655) (a:=53) (b:=54) sp14655 sp14708)) (joinSmall (lo:=14762) (a:=107) (b:=107) (joinSmall (lo:=14762) (a:=53) (b:=54) sp14762 sp14815) (joinSmall (lo:=14869) (a:=53) (b:=54) sp14869 sp14922))) (joinSmall (lo:=14976) (a:=214) (b:=214) (joinSmall (lo:=14976) (a:=107) (b:=107) (joinSmall (lo:=14976) (a:=53) (b:=54) sp14976 sp15029) (joinSmall (lo:=15083) (a:=53) (b:=54) sp15083 sp15136)) (joinSmall (lo:=15190) (a:=107) (b:=107) (joinSmall (lo:=15190) (a:=53) (b:=54) sp15190 sp15243) (joinSmall (lo:=15297) (a:=53) (b:=54) sp15297 sp15350))))) (joinSmall (lo:=15404) (a:=856) (b:=856) (joinSmall (lo:=15404) (a:=428) (b:=428) (joinSmall (lo:=15404) (a:=214) (b:=214) (joinSmall (lo:=15404) (a:=107) (b:=107) (joinSmall (lo:=15404) (a:=53) (b:=54) sp15404 sp15457) (joinSmall (lo:=15511) (a:=53) (b:=54) sp15511 sp15564)) (joinSmall (lo:=15618) (a:=107) (b:=107) (joinSmall (lo:=15618) (a:=53) (b:=54) sp15618 sp15671) (joinSmall (lo:=15725) (a:=53) (b:=54) sp15725 sp15778))) (joinSmall (lo:=15832) (a:=214) (b:=214) (joinSmall (lo:=15832) (a:=107) (b:=107) (joinSmall (lo:=15832) (a:=53) (b:=54) sp15832 sp15885) (joinSmall (lo:=15939) (a:=53) (b:=54) sp15939 sp15992)) (joinSmall (lo:=16046) (a:=107) (b:=107) (joinSmall (lo:=16046) (a:=53) (b:=54) sp16046 sp16099) (joinSmall (lo:=16153) (a:=53) (b:=54) sp16153 sp16206)))) (joinSmall (lo:=16260) (a:=428) (b:=428) (joinSmall (lo:=16260) (a:=214) (b:=214) (joinSmall (lo:=16260) (a:=107) (b:=107) (joinSmall (lo:=16260) (a:=53) (b:=54) sp16260 sp16313) (joinSmall (lo:=16367) (a:=53) (b:=54) sp16367 sp16420)) (joinSmall (lo:=16474) (a:=107) (b:=107) (joinSmall (lo:=16474) (a:=53) (b:=54) sp16474 sp16527) (joinSmall (lo:=16581) (a:=53) (b:=54) sp16581 sp16634))) (joinSmall (lo:=16688) (a:=214) (b:=214) (joinSmall (lo:=16688) (a:=107) (b:=107) (joinSmall (lo:=16688) (a:=53) (b:=54) sp16688 sp16741) (joinSmall (lo:=16795) (a:=53) (b:=54) sp16795 sp16848)) (joinSmall (lo:=16902) (a:=107) (b:=107) (joinSmall (lo:=16902) (a:=53) (b:=54) sp16902 sp16955) (joinSmall (lo:=17009) (a:=53) (b:=54) sp17009 sp17062)))))) (joinSmall (lo:=17116) (a:=1712) (b:=1712) (joinSmall (lo:=17116) (a:=856) (b:=856) (joinSmall (lo:=17116) (a:=428) (b:=428) (joinSmall (lo:=17116) (a:=214) (b:=214) (joinSmall (lo:=17116) (a:=107) (b:=107) (joinSmall (lo:=17116) (a:=53) (b:=54) sp17116 sp17169) (joinSmall (lo:=17223) (a:=53) (b:=54) sp17223 sp17276)) (joinSmall (lo:=17330) (a:=107) (b:=107) (joinSmall (lo:=17330) (a:=53) (b:=54) sp17330 sp17383) (joinSmall (lo:=17437) (a:=53) (b:=54) sp17437 sp17490))) (joinSmall (lo:=17544) (a:=214) (b:=214) (joinSmall (lo:=17544) (a:=107) (b:=107) (joinSmall (lo:=17544) (a:=53) (b:=54) sp17544 sp17597) (joinSmall (lo:=17651) (a:=53) (b:=54) sp17651 sp17704)) (joinSmall (lo:=17758) (a:=107) (b:=107) (joinSmall (lo:=17758) (a:=53) (b:=54) sp17758 sp17811) (joinSmall (lo:=17865) (a:=53) (b:=54) sp17865 sp17918)))) (joinSmall (lo:=17972) (a:=428) (b:=428) (joinSmall (lo:=17972) (a:=214) (b:=214) (joinSmall (lo:=17972) (a:=107) (b:=107) (joinSmall (lo:=17972) (a:=53) (b:=54) sp17972 sp18025) (joinSmall (lo:=18079) (a:=53) (b:=54) sp18079 sp18132)) (joinSmall (lo:=18186) (a:=107) (b:=107) (joinSmall (lo:=18186) (a:=53) (b:=54) sp18186 sp18239) (joinSmall (lo:=18293) (a:=53) (b:=54) sp18293 sp18346))) (joinSmall (lo:=18400) (a:=214) (b:=214) (joinSmall (lo:=18400) (a:=107) (b:=107) (joinSmall (lo:=18400) (a:=53) (b:=54) sp18400 sp18453) (joinSmall (lo:=18507) (a:=53) (b:=54) sp18507 sp18560)) (joinSmall (lo:=18614) (a:=107) (b:=107) (joinSmall (lo:=18614) (a:=53) (b:=54) sp18614 sp18667) (joinSmall (lo:=18721) (a:=53) (b:=54) sp18721 sp18774))))) (joinSmall (lo:=18828) (a:=856) (b:=856) (joinSmall (lo:=18828) (a:=428) (b:=428) (joinSmall (lo:=18828) (a:=214) (b:=214) (joinSmall (lo:=18828) (a:=107) (b:=107) (joinSmall (lo:=18828) (a:=53) (b:=54) sp18828 sp18881) (joinSmall (lo:=18935) (a:=53) (b:=54) sp18935 sp18988)) (joinSmall (lo:=19042) (a:=107) (b:=107) (joinSmall (lo:=19042) (a:=53) (b:=54) sp19042 sp19095) (joinSmall (lo:=19149) (a:=53) (b:=54) sp19149 sp19202))) (joinSmall (lo:=19256) (a:=214) (b:=214) (joinSmall (lo:=19256) (a:=107) (b:=107) (joinSmall (lo:=19256) (a:=53) (b:=54) sp19256 sp19309) (joinSmall (lo:=19363) (a:=53) (b:=54) sp19363 sp19416)) (joinSmall (lo:=19470) (a:=107) (b:=107) (joinSmall (lo:=19470) (a:=53) (b:=54) sp19470 sp19523) (joinSmall (lo:=19577) (a:=53) (b:=54) sp19577 sp19630)))) (joinSmall (lo:=19684) (a:=428) (b:=428) (joinSmall (lo:=19684) (a:=214) (b:=214) (joinSmall (lo:=19684) (a:=107) (b:=107) (joinSmall (lo:=19684) (a:=53) (b:=54) sp19684 sp19737) (joinSmall (lo:=19791) (a:=53) (b:=54) sp19791 sp19844)) (joinSmall (lo:=19898) (a:=107) (b:=107) (joinSmall (lo:=19898) (a:=53) (b:=54) sp19898 sp19951) (joinSmall (lo:=20005) (a:=53) (b:=54) sp20005 sp20058))) (joinSmall (lo:=20112) (a:=214) (b:=214) (joinSmall (lo:=20112) (a:=107) (b:=107) (joinSmall (lo:=20112) (a:=53) (b:=54) sp20112 sp20165) (joinSmall (lo:=20219) (a:=53) (b:=54) sp20219 sp20272)) (joinSmall (lo:=20326) (a:=107) (b:=107) (joinSmall (lo:=20326) (a:=53) (b:=54) sp20326 sp20379) (joinSmall (lo:=20433) (a:=53) (b:=54) sp20433 sp20486))))))) (joinSmall (lo:=20540) (a:=3423) (b:=3424) (joinSmall (lo:=20540) (a:=1711) (b:=1712) (joinSmall (lo:=20540) (a:=855) (b:=856) (joinSmall (lo:=20540) (a:=427) (b:=428) (joinSmall (lo:=20540) (a:=213) (b:=214) (joinSmall (lo:=20540) (a:=106) (b:=107) (joinSmall (lo:=20540) (a:=53) (b:=53) sp20540 sp20593) (joinSmall (lo:=20646) (a:=53) (b:=54) sp20646 sp20699)) (joinSmall (lo:=20753) (a:=107) (b:=107) (joinSmall (lo:=20753) (a:=53) (b:=54) sp20753 sp20806) (joinSmall (lo:=20860) (a:=53) (b:=54) sp20860 sp20913))) (joinSmall (lo:=20967) (a:=214) (b:=214) (joinSmall (lo:=20967) (a:=107) (b:=107) (joinSmall (lo:=20967) (a:=53) (b:=54) sp20967 sp21020) (joinSmall (lo:=21074) (a:=53) (b:=54) sp21074 sp21127)) (joinSmall (lo:=21181) (a:=107) (b:=107) (joinSmall (lo:=21181) (a:=53) (b:=54) sp21181 sp21234) (joinSmall (lo:=21288) (a:=53) (b:=54) sp21288 sp21341)))) (joinSmall (lo:=21395) (a:=428) (b:=428) (joinSmall (lo:=21395) (a:=214) (b:=214) (joinSmall (lo:=21395) (a:=107) (b:=107) (joinSmall (lo:=21395) (a:=53) (b:=54) sp21395 sp21448) (joinSmall (lo:=21502) (a:=53) (b:=54) sp21502 sp21555)) (joinSmall (lo:=21609) (a:=107) (b:=107) (joinSmall (lo:=21609) (a:=53) (b:=54) sp21609 sp21662) (joinSmall (lo:=21716) (a:=53) (b:=54) sp21716 sp21769))) (joinSmall (lo:=21823) (a:=214) (b:=214) (joinSmall (lo:=21823) (a:=107) (b:=107) (joinSmall (lo:=21823) (a:=53) (b:=54) sp21823 sp21876) (joinSmall (lo:=21930) (a:=53) (b:=54) sp21930 sp21983)) (joinSmall (lo:=22037) (a:=107) (b:=107) (joinSmall (lo:=22037) (a:=53) (b:=54) sp22037 sp22090) (joinSmall (lo:=22144) (a:=53) (b:=54) sp22144 sp22197))))) (joinSmall (lo:=22251) (a:=856) (b:=856) (joinSmall (lo:=22251) (a:=428) (b:=428) (joinSmall (lo:=22251) (a:=214) (b:=214) (joinSmall (lo:=22251) (a:=107) (b:=107) (joinSmall (lo:=22251) (a:=53) (b:=54) sp22251 sp22304) (joinSmall (lo:=22358) (a:=53) (b:=54) sp22358 sp22411)) (joinSmall (lo:=22465) (a:=107) (b:=107) (joinSmall (lo:=22465) (a:=53) (b:=54) sp22465 sp22518) (joinSmall (lo:=22572) (a:=53) (b:=54) sp22572 sp22625))) (joinSmall (lo:=22679) (a:=214) (b:=214) (joinSmall (lo:=22679) (a:=107) (b:=107) (joinSmall (lo:=22679) (a:=53) (b:=54) sp22679 sp22732) (joinSmall (lo:=22786) (a:=53) (b:=54) sp22786 sp22839)) (joinSmall (lo:=22893) (a:=107) (b:=107) (joinSmall (lo:=22893) (a:=53) (b:=54) sp22893 sp22946) (joinSmall (lo:=23000) (a:=53) (b:=54) sp23000 sp23053)))) (joinSmall (lo:=23107) (a:=428) (b:=428) (joinSmall (lo:=23107) (a:=214) (b:=214) (joinSmall (lo:=23107) (a:=107) (b:=107) (joinSmall (lo:=23107) (a:=53) (b:=54) sp23107 sp23160) (joinSmall (lo:=23214) (a:=53) (b:=54) sp23214 sp23267)) (joinSmall (lo:=23321) (a:=107) (b:=107) (joinSmall (lo:=23321) (a:=53) (b:=54) sp23321 sp23374) (joinSmall (lo:=23428) (a:=53) (b:=54) sp23428 sp23481))) (joinSmall (lo:=23535) (a:=214) (b:=214) (joinSmall (lo:=23535) (a:=107) (b:=107) (joinSmall (lo:=23535) (a:=53) (b:=54) sp23535 sp23588) (joinSmall (lo:=23642) (a:=53) (b:=54) sp23642 sp23695)) (joinSmall (lo:=23749) (a:=107) (b:=107) (joinSmall (lo:=23749) (a:=53) (b:=54) sp23749 sp23802) (joinSmall (lo:=23856) (a:=53) (b:=54) sp23856 sp23909)))))) (joinSmall (lo:=23963) (a:=1712) (b:=1712) (joinSmall (lo:=23963) (a:=856) (b:=856) (joinSmall (lo:=23963) (a:=428) (b:=428) (joinSmall (lo:=23963) (a:=214) (b:=214) (joinSmall (lo:=23963) (a:=107) (b:=107) (joinSmall (lo:=23963) (a:=53) (b:=54) sp23963 sp24016) (joinSmall (lo:=24070) (a:=53) (b:=54) sp24070 sp24123)) (joinSmall (lo:=24177) (a:=107) (b:=107) (joinSmall (lo:=24177) (a:=53) (b:=54) sp24177 sp24230) (joinSmall (lo:=24284) (a:=53) (b:=54) sp24284 sp24337))) (joinSmall (lo:=24391) (a:=214) (b:=214) (joinSmall (lo:=24391) (a:=107) (b:=107) (joinSmall (lo:=24391) (a:=53) (b:=54) sp24391 sp24444) (joinSmall (lo:=24498) (a:=53) (b:=54) sp24498 sp24551)) (joinSmall (lo:=24605) (a:=107) (b:=107) (joinSmall (lo:=24605) (a:=53) (b:=54) sp24605 sp24658) (joinSmall (lo:=24712) (a:=53) (b:=54) sp24712 sp24765)))) (joinSmall (lo:=24819) (a:=428) (b:=428) (joinSmall (lo:=24819) (a:=214) (b:=214) (joinSmall (lo:=24819) (a:=107) (b:=107) (joinSmall (lo:=24819) (a:=53) (b:=54) sp24819 sp24872) (joinSmall (lo:=24926) (a:=53) (b:=54) sp24926 sp24979)) (joinSmall (lo:=25033) (a:=107) (b:=107) (joinSmall (lo:=25033) (a:=53) (b:=54) sp25033 sp25086) (joinSmall (lo:=25140) (a:=53) (b:=54) sp25140 sp25193))) (joinSmall (lo:=25247) (a:=214) (b:=214) (joinSmall (lo:=25247) (a:=107) (b:=107) (joinSmall (lo:=25247) (a:=53) (b:=54) sp25247 sp25300) (joinSmall (lo:=25354) (a:=53) (b:=54) sp25354 sp25407)) (joinSmall (lo:=25461) (a:=107) (b:=107) (joinSmall (lo:=25461) (a:=53) (b:=54) sp25461 sp25514) (joinSmall (lo:=25568) (a:=53) (b:=54) sp25568 sp25621))))) (joinSmall (lo:=25675) (a:=856) (b:=856) (joinSmall (lo:=25675) (a:=428) (b:=428) (joinSmall (lo:=25675) (a:=214) (b:=214) (joinSmall (lo:=25675) (a:=107) (b:=107) (joinSmall (lo:=25675) (a:=53) (b:=54) sp25675 sp25728) (joinSmall (lo:=25782) (a:=53) (b:=54) sp25782 sp25835)) (joinSmall (lo:=25889) (a:=107) (b:=107) (joinSmall (lo:=25889) (a:=53) (b:=54) sp25889 sp25942) (joinSmall (lo:=25996) (a:=53) (b:=54) sp25996 sp26049))) (joinSmall (lo:=26103) (a:=214) (b:=214) (joinSmall (lo:=26103) (a:=107) (b:=107) (joinSmall (lo:=26103) (a:=53) (b:=54) sp26103 sp26156) (joinSmall (lo:=26210) (a:=53) (b:=54) sp26210 sp26263)) (joinSmall (lo:=26317) (a:=107) (b:=107) (joinSmall (lo:=26317) (a:=53) (b:=54) sp26317 sp26370) (joinSmall (lo:=26424) (a:=53) (b:=54) sp26424 sp26477)))) (joinSmall (lo:=26531) (a:=428) (b:=428) (joinSmall (lo:=26531) (a:=214) (b:=214) (joinSmall (lo:=26531) (a:=107) (b:=107) (joinSmall (lo:=26531) (a:=53) (b:=54) sp26531 sp26584) (joinSmall (lo:=26638) (a:=53) (b:=54) sp26638 sp26691)) (joinSmall (lo:=26745) (a:=107) (b:=107) (joinSmall (lo:=26745) (a:=53) (b:=54) sp26745 sp26798) (joinSmall (lo:=26852) (a:=53) (b:=54) sp26852 sp26905))) (joinSmall (lo:=26959) (a:=214) (b:=214) (joinSmall (lo:=26959) (a:=107) (b:=107) (joinSmall (lo:=26959) (a:=53) (b:=54) sp26959 sp27012) (joinSmall (lo:=27066) (a:=53) (b:=54) sp27066 sp27119)) (joinSmall (lo:=27173) (a:=107) (b:=107) (joinSmall (lo:=27173) (a:=53) (b:=54) sp27173 sp27226) (joinSmall (lo:=27280) (a:=53) (b:=54) sp27280 sp27333)))))))))
  have good : (List.range 27387).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 750000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 27386 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 27386 := by
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


private def packet (i : ℕ) : ℕ := (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 8 then (if i < 6 then 0 else (if i < 7 then 0 else 0)) else (if i < 9 then 0 else (if i < 10 then 0 else 0)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0 else (if i < 13 then 0 else 0)) else (if i < 15 then 0 else (if i < 16 then 0 else 0))) else (if i < 20 then (if i < 18 then 0 else (if i < 19 then 0 else 0)) else (if i < 21 then 0 else (if i < 22 then 0 else 0))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then 0 else (if i < 25 then 0 else 0)) else (if i < 27 then 0 else (if i < 28 then 0 else 0))) else (if i < 32 then (if i < 30 then 0 else (if i < 31 then 0 else 0)) else (if i < 33 then 0 else (if i < 34 then 0 else 0)))) else (if i < 41 then (if i < 38 then (if i < 36 then 0 else (if i < 37 then 0 else 0)) else (if i < 39 then 0 else (if i < 40 then 0 else 0))) else (if i < 44 then (if i < 42 then 0 else (if i < 43 then 0 else 0)) else (if i < 45 then 0 else (if i < 46 then 0 else 0)))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then 0 else (if i < 49 then 0 else 0)) else (if i < 51 then 0 else (if i < 52 then 0 else 0))) else (if i < 56 then (if i < 54 then 0 else (if i < 55 then 0 else 0)) else (if i < 57 then 0 else (if i < 58 then 0 else 0)))) else (if i < 65 then (if i < 62 then (if i < 60 then 0 else (if i < 61 then 0 else 0)) else (if i < 63 then 0 else (if i < 64 then 0 else 0))) else (if i < 68 then (if i < 66 then 0 else (if i < 67 then 0 else 0)) else (if i < 69 then 0 else (if i < 70 then 0 else 0))))) else (if i < 83 then (if i < 77 then (if i < 74 then (if i < 72 then 0 else (if i < 73 then 0 else 0)) else (if i < 75 then 0 else (if i < 76 then 0 else 0))) else (if i < 80 then (if i < 78 then 0 else (if i < 79 then 0 else 0)) else (if i < 81 then 0 else (if i < 82 then 0 else 0)))) else (if i < 89 then (if i < 86 then (if i < 84 then 0 else (if i < 85 then 0 else 0)) else (if i < 87 then 0 else (if i < 88 then 0 else 0))) else (if i < 92 then (if i < 90 then 0 else (if i < 91 then 0 else 0)) else (if i < 93 then 0 else (if i < 94 then 0 else 0))))))) else (if i < 143 then (if i < 119 then (if i < 107 then (if i < 101 then (if i < 98 then (if i < 96 then 0 else (if i < 97 then 0 else 0)) else (if i < 99 then 0 else (if i < 100 then 0 else 0))) else (if i < 104 then (if i < 102 then 0 else (if i < 103 then 0 else 0)) else (if i < 105 then 0 else (if i < 106 then 0 else 0)))) else (if i < 113 then (if i < 110 then (if i < 108 then 0 else (if i < 109 then 0 else 0)) else (if i < 111 then 0 else (if i < 112 then 0 else 0))) else (if i < 116 then (if i < 114 then 0 else (if i < 115 then 0 else 0)) else (if i < 117 then 0 else (if i < 118 then 0 else 0))))) else (if i < 131 then (if i < 125 then (if i < 122 then (if i < 120 then 0 else (if i < 121 then 0 else 0)) else (if i < 123 then 0 else (if i < 124 then 0 else 0))) else (if i < 128 then (if i < 126 then 0 else (if i < 127 then 0 else 0)) else (if i < 129 then 0 else (if i < 130 then 0 else 0)))) else (if i < 137 then (if i < 134 then (if i < 132 then 0 else (if i < 133 then 0 else 0)) else (if i < 135 then 0 else (if i < 136 then 0 else 0))) else (if i < 140 then (if i < 138 then 0 else (if i < 139 then 0 else 0)) else (if i < 141 then 0 else (if i < 142 then 0 else 0)))))) else (if i < 167 then (if i < 155 then (if i < 149 then (if i < 146 then (if i < 144 then 0 else (if i < 145 then 0 else 0)) else (if i < 147 then 0 else (if i < 148 then 0 else 0))) else (if i < 152 then (if i < 150 then 0 else (if i < 151 then 0 else 0)) else (if i < 153 then 0 else (if i < 154 then 0 else 0)))) else (if i < 161 then (if i < 158 then (if i < 156 then 0 else (if i < 157 then 0 else 0)) else (if i < 159 then 0 else (if i < 160 then 0 else 0))) else (if i < 164 then (if i < 162 then 0 else (if i < 163 then 0 else 0)) else (if i < 165 then 0 else (if i < 166 then 0 else 0))))) else (if i < 179 then (if i < 173 then (if i < 170 then (if i < 168 then 0 else (if i < 169 then 0 else 0)) else (if i < 171 then 0 else (if i < 172 then 0 else 0))) else (if i < 176 then (if i < 174 then 0 else (if i < 175 then 0 else 0)) else (if i < 177 then 0 else (if i < 178 then 0 else 0)))) else (if i < 185 then (if i < 182 then (if i < 180 then 0 else (if i < 181 then 0 else 0)) else (if i < 183 then 0 else (if i < 184 then 0 else 0))) else (if i < 188 then (if i < 186 then 0 else (if i < 187 then 0 else 0)) else (if i < 189 then 0 else (if i < 190 then 0 else 0)))))))) else (if i < 286 then (if i < 238 then (if i < 214 then (if i < 202 then (if i < 196 then (if i < 193 then (if i < 192 then 0 else 0) else (if i < 194 then 0 else (if i < 195 then 0 else 0))) else (if i < 199 then (if i < 197 then 0 else (if i < 198 then 0 else 0)) else (if i < 200 then 0 else (if i < 201 then 0 else 0)))) else (if i < 208 then (if i < 205 then (if i < 203 then 0 else (if i < 204 then 0 else 0)) else (if i < 206 then 0 else (if i < 207 then 0 else 0))) else (if i < 211 then (if i < 209 then 0 else (if i < 210 then 0 else 0)) else (if i < 212 then 0 else (if i < 213 then 0 else 0))))) else (if i < 226 then (if i < 220 then (if i < 217 then (if i < 215 then 0 else (if i < 216 then 0 else 0)) else (if i < 218 then 0 else (if i < 219 then 0 else 0))) else (if i < 223 then (if i < 221 then 0 else (if i < 222 then 0 else 0)) else (if i < 224 then 0 else (if i < 225 then 0 else 0)))) else (if i < 232 then (if i < 229 then (if i < 227 then 0 else (if i < 228 then 0 else 0)) else (if i < 230 then 0 else (if i < 231 then 0 else 0))) else (if i < 235 then (if i < 233 then 0 else (if i < 234 then 0 else 0)) else (if i < 236 then 0 else (if i < 237 then 0 else 0)))))) else (if i < 262 then (if i < 250 then (if i < 244 then (if i < 241 then (if i < 239 then 0 else (if i < 240 then 0 else 0)) else (if i < 242 then 0 else (if i < 243 then 0 else 0))) else (if i < 247 then (if i < 245 then 0 else (if i < 246 then 0 else 0)) else (if i < 248 then 0 else (if i < 249 then 0 else 0)))) else (if i < 256 then (if i < 253 then (if i < 251 then 0 else (if i < 252 then 0 else 0)) else (if i < 254 then 0 else (if i < 255 then 0 else 0))) else (if i < 259 then (if i < 257 then 0 else (if i < 258 then 0 else 0)) else (if i < 260 then 0 else (if i < 261 then 0 else 0))))) else (if i < 274 then (if i < 268 then (if i < 265 then (if i < 263 then 0 else (if i < 264 then 0 else 0)) else (if i < 266 then 0 else (if i < 267 then 0 else 0))) else (if i < 271 then (if i < 269 then 0 else (if i < 270 then 0 else 0)) else (if i < 272 then 0 else (if i < 273 then 0 else 0)))) else (if i < 280 then (if i < 277 then (if i < 275 then 0 else (if i < 276 then 0 else 0)) else (if i < 278 then 0 else (if i < 279 then 0 else 0))) else (if i < 283 then (if i < 281 then 0 else (if i < 282 then 0 else 0)) else (if i < 284 then 0 else (if i < 285 then 0 else 0))))))) else (if i < 334 then (if i < 310 then (if i < 298 then (if i < 292 then (if i < 289 then (if i < 287 then 0 else (if i < 288 then 0 else 0)) else (if i < 290 then 0 else (if i < 291 then 0 else 0))) else (if i < 295 then (if i < 293 then 0 else (if i < 294 then 0 else 0)) else (if i < 296 then 0 else (if i < 297 then 0 else 0)))) else (if i < 304 then (if i < 301 then (if i < 299 then 0 else (if i < 300 then 0 else 0)) else (if i < 302 then 0 else (if i < 303 then 0 else 0))) else (if i < 307 then (if i < 305 then 0 else (if i < 306 then 0 else 0)) else (if i < 308 then 0 else (if i < 309 then 0 else 0))))) else (if i < 322 then (if i < 316 then (if i < 313 then (if i < 311 then 0 else (if i < 312 then 0 else 0)) else (if i < 314 then 0 else (if i < 315 then 0 else 0))) else (if i < 319 then (if i < 317 then 0 else (if i < 318 then 0 else 0)) else (if i < 320 then 0 else (if i < 321 then 0 else 0)))) else (if i < 328 then (if i < 325 then (if i < 323 then 0 else (if i < 324 then 0 else 0)) else (if i < 326 then 0 else (if i < 327 then 0 else 0))) else (if i < 331 then (if i < 329 then 0 else (if i < 330 then 0 else 0)) else (if i < 332 then 0 else (if i < 333 then 0 else 0)))))) else (if i < 358 then (if i < 346 then (if i < 340 then (if i < 337 then (if i < 335 then 0 else (if i < 336 then 0 else 0)) else (if i < 338 then 0 else (if i < 339 then 0 else 0))) else (if i < 343 then (if i < 341 then 0 else (if i < 342 then 0 else 0)) else (if i < 344 then 0 else (if i < 345 then 0 else 0)))) else (if i < 352 then (if i < 349 then (if i < 347 then 0 else (if i < 348 then 0 else 0)) else (if i < 350 then 0 else (if i < 351 then 0 else 0))) else (if i < 355 then (if i < 353 then 0 else (if i < 354 then 0 else 0)) else (if i < 356 then 0 else (if i < 357 then 0 else 0))))) else (if i < 370 then (if i < 364 then (if i < 361 then (if i < 359 then 0 else (if i < 360 then 0 else 0)) else (if i < 362 then 0 else (if i < 363 then 0 else 0))) else (if i < 367 then (if i < 365 then 0 else (if i < 366 then 0 else 0)) else (if i < 368 then 0 else (if i < 369 then 0x23c3a772c294949784531fa8e646682dc14308c03a617a08f02d40c4000023c34b02b494289544501f68e4c6662e714188ac39c17008e82e00ac000023c2ec52c714d099e4682040ea469a2ee144089439817108a82d40ac000023c28e52bd147c9904712078e9068a2f1146089c38c16808582bc0ac000023c230f2ba14549684501fe0e8469c2fd15008fc3c417508a82d80b6000023c1d192ce14e49aa47420a0eb46942f214b08fc3d019009483180bc000023c17322c514c89b648c2100f1c6d030c15909003d218409683300d0000023c118e2a413bc91a43b1f50e286682dd13d88983ae17a08d82d80c6000023c0b902cb94e49b24732010ebc6902ea14688d03a416d08d82cc0ae000023c05922cc14d499a4651fd8e8066e2d214208a439e17608d82d40aa000023bffd12b914849744602010e646902f714c08bc39a17308e830c0ca000023bfa162aa93f893e4531f78e646822e413c885837616708902b00b2000023bf41b2cb14f49ce4892108ef06b22f814b88f039a17408a83300ca000023bee392c414949884632048ec46a42ef14408b439216c08682a809c000023be8992a793e49544551fb8e906822f2142888839617508a02a80ac000023be2ca2b6944c96c44b1f70e406742dd14188a03a617b08d82e40ba000023bdd142ab14089564481fa0e846942f715009143c417a09383140ce000023bd7352c394a89a248120e8ee86b630314b88bc3ba17d08c82f40bc000023bd1722b2940c94e44f1fe8e7467a2df13d88a039c16808a02e00b8000023bcb812cc14ac99e4762060eb06a22f814d08d43b6185094832c0ae000023bc57d2d415449de49621d8f7c6f031415b897c3f019609203100c0000023bbfa22bf949c98a45f2020e9c6a02f714a88e83b817c09783500de000023bb9862e01574a084a821f0f586e031015609243c617b08f82fc0cc000023bb3a52c1148c99446d2030ec46a82ef14a88ec3c418709002f80ba000023bade12ae942494a4541fc0e8066a2df13d086837c15b08082a4098000023ba7d62d195349da4872128ef86b62f415389303ce18809403280c2000023ba1f92be94609704591fa8e4466a2de14508b839417008c031c0c4000023b9c112c494b49a046520a0eb46982e914108a03a017008882c00ac000023b961e2ca94e89a847720b8ec06c62fd15089083c819009102f00be000023b904c2bf149c98646b2070ec469e2ee143088c39217309083240c4000023b8a3f2d395189c04832120f046c0302153892c3d618f09783340d6000023b84862a9140c9624521f80e686642dd13d08a039a16808282b80b4000023b7eb62ba946c97a4571fc8e6c6782e614008b83a216f08a82e00c4000023b78b22d315449e44852178f506ee31615a09603ea19b09c03300c4000023b72c22c794b89a44782078ea46a62f614508d83aa17908f02e80b4000023b6cd32c514ac99846c2058ea86962ef14608a039e16d08a82d00b6000023b67062b894389644521f78e486682d513b08943a017208c83040be000023b61342b4145097c4562008e7c6822e414388ac3aa17808802a80a6000023b5b542c014ac9a647420f0f086c630815a09543d618b09203040d0000023b55852b7943c96244f1f10e086522c8132083435e15707b82840ac000023b4f722dd95609e848a21a8f646fe31515d89783fa1a009883280cc000023b49782ca94d09b047820a0ed86a430414c08e03b016f08a02e00ba000023b43982c394b098c46b2000e706882ea14588b03ac179085029c0a2000023b3db22ca94d89ae46c2060eb869c2e114208a83ac17308882e40b8000023b37ef2b4142c9784692040eb46a230015189303cc18008f02d80b2000023b32122c514a498445c2048e986942f414a08bc38e16f08782c80b6000023b2c312c1146896c45e2028eac6a42f314a08c43aa17e08c02e00b2000023b265d2bb944497645d1fc0e846802db142888438c15d08102b80b4000023b20872b814609784621fe0e686722d713e888439616d08f02d40ac000023b1a8f2c794bc99e4802130f106b82fd15289003ca18e095830c0b0000023b14c32b3145097c45e1ff0e9c69e2fc14e89103d6186093033c0d4000023b0ec12d115049b24812108ef46ae2f314b88f83c218109302fc0ba000023b08d22cc94e89b84792138f146d830015409303da18908e82f80c0000023b030f2b0940495245a2000ec86982e513d08b439e17308682d00b6000023afd1e2c094ac98c47020c0edc69e2f814e88d43ac17c09302f80ca000023af7252c814a899646d2078ea06942f514d090c3ea18b09a83240c0000023af13a2c614d09a847920b8ec46b02f014c88e439c17908f02d40c4000023aeb5e2bc145c9704561fe0e7c6922e614288bc39617008482b40b0000023ae5892be948099446b2040ee46c030415009043ba17509102f80ce000023adfa12ca14c49b047a20a8ef86ac2f815489043ce188094831c0d4000023ad9bd2c494a09a846b2068edc6a82fd14c08dc3c618609a83240c8000023ad3e62bd94689664612000e7c6822f314708cc3b418109283180cc000023acdfa2c694cc9a646e20b0f006c230615209283ea192097031c0d0000023ac8082cb94e09cc4972168f346e431315a895c3d618808f82e00b4000 else 0x23db3352bd147c98a45a2080ec46b230015008f43be18108f82f80b4000023dad412c794e89ba48020e0ee86ac2f514a88d03ae17c08b02ec0bc000023da72f2d594fc9bc4852148f1c6b22ff14d09103c818508c02dc0b6000023da1302cf95089d24932188f4c6de316157091c3c618709383340d8000023d9b652b8143c94443e1f10e4c66e2db13b088038817408d82bc0c2000023d95832c1149c98246c2018e786702dd14408b439c17208702cc0ac000023d8fa02c014949864682068e8c6902eb14708b83b217509203140c8000023d89a12da15489cc4852138f346dc30c15509403fa19c09a035c0d2000023d83b42c614c49984662080ec06a22f414888a039a17209083000ba000023d7ddb2c314849944611fd8e486822e214408a83a217208e02fc0b6000023d77bf2de95589f249e2178f386de312154891c3c0183094830c0d8000023d71e02c2148499e47720b8eac68a2ec14788e03b4173090830c0c2000023d6c012c194909824662010e806962f014d08e43a617108782e00bc000023d66122be947497a46d20b8ed46ba2f614f08e43c617d09102fc0c2000023d60162ca14e09b64842130f286e031815809243c617c09503100c4000023d5a292cb15009ca4882140f246d030914d09203ca18709783100cc000023d54692b5144c9884632060eac68a2e413f088439217208882e80b0000023d4e742d015009c447f20f8ef46ce30b15189303d418b09583140d0000023d48792cc950c9d44802138f506ea31c15809483ec19409b83540dc000023d42a22c214949a247120a8eb06882ed14608c039616608502d00b4000023d3cf12ab93e493443f1f28e7068c2ec14888cc3b017908502bc0ba000023d37132c014809824622008ea86a62f514988fc3be18709303140b6000023d311c2cb94f89b04792110efc6a62f714708b039c17108702e40b2000023d2b3c2bd147c97845c2010e886a22ed14a890c3c217a08f030c0bc000023d25572c594c09b848020d0f286d230715309583d219409483180b8000023d1fc229d13a093e43a1f08e1065a2d113e887838616308882d00bc000023d1a052b014109364441fa0e486662cb13a884c37015c08302cc0b6000023d14342bb945c95c4572008e946982fc15008d03a417a08a02e40b2000023d0e672bb146897445d1fd8e746842dd13b885437016c08702cc0b4000023d086f2c994c09a647c2098eb86ac2f614d08fc3be181092831c0c0000023d02912b9947498646f20c0ed869a2f914588b03ac17308c82d40aa000023cfca42c5147c9764632030e906aa2f114c88cc3c817c09503140b8000023cf6ca2c494ac9ae47020e0f0c6d2311158891c3b618409383280c6000023cf0f82b7143496e4591ff8e7469e2ee14788d43c617a09003240d4000023ceb2f2b6144c96c45c2018e786782e114808d03be18808e83140bc000023ce5672af140895044b1f50e5c67a2e614508b039e17b08802c80ba000023cdf572d3151c9b647420a0ecc6a62e814588a03a017d08702ac0b4000023cd9432dc95389e448f2148ef86d430814f89103b017508b03000c0000023cd36a2bb145c97a46b2018e646742d513c88b03a617309003140b4000023ccd8a2c494b09ac47e2098ee06b62fc14e08d43d2182095031c0dc000023cc7af2bc94789784561fc0e4466a2dd13d885837416108402b40c0000023cc1d72be14809824592028e9468e2ed14a08d83a617708f03000b8000023cbbdd2cc94e89b047c2088ecc6942ef14408b43aa18509282f80bc000023cb5f72bb144496c45c1fe0e886942eb13e08843a817508a02d40be000023cb01e2bb94809924672088e9c6942e914608b439e17709002e40be000023caa452c2948c98445c2020e646862e1140888c38e17308982f80bc000023ca45f2c594d49ac47b2110ef46be2fd14988f83c017f08c02e40be000023c9e7e2c394a098a46c2070edc6aa30014d08e03b018009082e00b8000023c98a92ba94649784541ff0e846802e1141889838a16f08502c80ba000023c92ae2c914c89a64702060eb06a02e914588d83a617a08802f40c2000023c8cf52af93f095444d1f58e2c6522d213c887037815e082829c0aa000023c87082cc14e898645d2018e786982ec14a08ac39e16b08a030c0c2000023c81422bc945097645b1fe8e986982e214208b83a817408c02d80b4000023c7b652c714c49aa4802078ecc69a2eb14a88ac39816d08982bc0a8000023c759a2b6144097c45d1fe8e6867c2e4140889c3a016a08882e00b2000023c6f932d4152c9e84902170f3c6d030015409083c818a09582bc0b6000023c69ba2c1147497c4531f90e706862f214608e03c817a08f03180ae000023c63e22c0146098846a2058ec06b62f514988dc3b817e09002e80c0000023c5df52c714c899e47c20f0f006c830a15709203d819009c83600d4000023c581c2b8944096845f2040ecc6c230214f89103ce18c08b83000ce000023c52282c914b099846c2060ec46902f514988e43b618308e82ec0ba000023c4c3f2c694ac98e4672080ebc68c2e214a89003b217708f02f80a2000023c464e2c994e49a44732070ed06aa2f914f88ec3b017908b82d00b6000023c40612cb14c49a44722050e8468a2e914408903a216e08702f40d2000)))) else (if i < 376 then (if i < 373 then (if i < 371 then 0x23f2aaf2bc148097c4591fc0e986a02f715008ec3aa17a08f02e80c8000023f24bf2ca95009c848620f8f4c6da30715a89403f219809583040c2000023f1f172a613d494044b2018e9067e2f514888e83a817008902d40b4000023f191e2d0950099846f2028e946982f114e09303ce18b09683040c4000023f13212d194e099e46b2070ec469c2f514b08fc3bc180094833c0d8000023f0d332cb14c49b24762098ee06c230114c88c03b018408f02e80ca000023f07532c094b49c04762078eac6982ef14808e03aa17c08e02ec0ba000023f01642c714bc9b047b2088efc6d030b15a09743ea18f099031c0ca000023efbad2ac93cc94e4491f28e246562d013a886839a17008682f00d4000023ef5e02ba945c96844c1fc0e2c6522bb12f07dc34215107f02b00a8000023eeff32c694a498a46c2038eb86a02ee141088839616f08a83080c0000023eea412a993e494a4591fd8ea06942e814988e83bc17c08d82dc0bc000023ee4762b9145897c46e20d0eec6b42fe14e890c3d618b09783300bc000023ede9c2bc944896444d1fa0e886862eb14708c83a017a08c830c0a2000023ed8c82ba14709904672088ed06a02f114888b43a617008b02e00c0000023ed30e2ae14089564582008eac68c2e814788c039c17108f02e00b8000023ecd2c2c614b499c46c2080eec6c430e14e08f03c418508d02d80be000023ec76d2b4140c9624431f38e1465e2ce13d887437415c08182a80a6000023ec1772c814d499a46d2098ebc6962eb14888c83a617908f83080be000023ebbb32b494409764561ff8e706862eb14408c439017008802dc0b2000023eb5b92cf94dc9be47920d8f286d831715c09183c418109082e40be000023eb0122a1939892042f1e38dec64a2c412f881836415f08882d80bc000023eaa242c614a89884692008e786a02f814c88e83c818609403180c4000023ea4282cf94ec9b04772140f506f031615809403b218109083040ca000023e9e3a2c814b49844592050e8867c2dc141888838816908e830c0ba000023e984b2c694989a447320c0eb06a02f714888dc3ae18008b03080b8000023e92822b414389564501fe0ea069a2f014908c83b017e09003080c2000023e8cb12b9948499646d20c0edc6882f114f89043ce17608902fc0b6000023e86fd2ae140094c44e1f90e646902ee14a08b439a16908802c00ae000023e80dc2e795909f649c2160f446ec31015309203d218509783600e0000023e7afb2bf94b89a847a20c0f046c431015109243d018408b02f40ac000023e75102c594d899a47420c0f206ba30015209343e219509883180c6000023e6f592a713e493e4481f40e3465c2e013f886836215b08702b00a6000023e697a2c414a498c4581fd0e606742df14508a839a17908f83180cc000023e63a62b8941c96845c1ff8e586582d913c088c38417508a02fc0c2000023e5dba2c294c89b64842158f2c6f030715289403d219109102e80ae000023e57e92b9144896a4441ef0e0065e2cf139082c36615d08602a40a4000023e52052c814d09be4832110f306e030e14e89083c017608e02cc0b8000023e4c2f2be14bc9964672078ebc6aa2f814c08e03a817708d82fc0d0000023e464d2c594a89864622048eac68c2e814308b039016208902d00ae000023e405a2c994ec9b047b20e8ed86c830114e08d03a617408e02dc09e000023e3a632cb14e49c047620c0f086cc30014e88c839e16e08702c80bc000023e349f2b3941494a4401ee0de86442b6130084838416508682fc0ca000023e2eb82c694e09b847b2100ee86b230114d88e439a17508882e80be000023e28d62c414c89ba4782060e9068c2ea14588a038816408602c40b0000023e22f92b914349664621fe0e746882f1144089c39016e08b82c80c0000023e1d392ab13c493e4401f50e186442cd13b086039e17008b02e00c6000023e17422ca94cc9aa47a2108ee86b82f815089143c817a08b02c00ac000023e117a2b7141c96a4562048ec068a2e9140088439217308982e00ba000023e0b8d2ca14b89a04712088ea86a22f714e88e83c6184095835c0d4000023e05892cc95009b247f20d0f006ac2fa14c08ec3be172091031c0c2000023dff9d2ca94b49964682040e906ae2f714d88f03c418008f83180b8000023df9a32d114dc9cc48120e8f106c82fd15108d83ac17308e83080c0000023df3ca2bd945096a4591fd8e786842ec14708f03b418209003180c0000023dedf32be947898a46d2070ed46b02ea14708e43ce18809303240c2000023de82f2b014149664612038e946a02fb14b08f03a816c08882d80b2000023de2682bb148098a46a1ff0e986902e614408d83a817408983180ce000023ddc762ce150c9ca47f2138f306c430314e88cc3a616c08d02d00ae000023dd6902c294a49a04792060e9869e2f514b88d03c017e09003000d8000023dd0be2bf947c97845b2010ea86962ff14b88dc3b017208902d40bc000023dcaae2d095189c848720f0ec86a02f314a08d43a617b09183180c4000023dc4e42b9143096a4511f48e4c6802ea14788d43a217808c02e40c6000023dbef92c614949884702058e986922ea14988d03b417108b831c0c0000023db90a2cf94e89d44952178f2c6c030014d88f83b418908f03100c4000 else (if i < 372 then 0x240a2f82bd14609844692010e946982ef15088e03b217708d82ec0b400002409d082cb14dc9aa47c20b0ed869a2ef14608c83b418409182f00ca0000240972e2bd94949a447e20f8ef06ca30215088fc3c217a08d83140bc0000240914c2bf149099446b20a8ef46d630a15789303d418808e82ec0b600002408b4a2ce14f89bc4782050ea86882f114688b839017308782d40b20000240855a2c0947c9904742098ec86a62eb146889839017208c82f40b000002407f662cd15009c847520c0ed46962df14388b03a816d08782dc0be000024079802c314b099c46f2068ed86b430315208f83bc17908c83140b80000240738e2ca14b09ae4752098ee86ac2fc14c08d03b417008d82dc0c200002406d9d2c614d89a447220c0ec06aa2ef14c08fc3ce18508e830c0b6000024067b72c194b49a84732060ee06b030014908b43b017208a02f80b6000024061db2bc14609764682020e886762d4140089c3aa17108a02b80be00002405bf92c4147c9784622008eac69e2f014a08bc3a217108982b80ae000024055e62dc15709e04972218f6c6ec31b15c09783f218909483000c40000240500f2bd947899046c20a0ec86a82f615108f83bc18108f031c0d400002404a452b9146497a45c1ff0ea86882f014a88b03a6180091031c0c80000240445c2bf94c49ac47c2120f0c6c8306152890c3b017e08c82e80c200002403e662d1150c9b448020e8f146c42fc14f08f03a216308602e00ca000024038972b5942c94643d1f20e446842eb14508ac38816e08c02cc0aa000024032712e315549f049b21a8f386d0312159893c3ce189090031c0c400002402c7e2c794a498045e2060ea06a22e714b88e83b017808882dc0b0000024026aa2b8944096244f1f60e3066c2db14408ac39a17e08902bc0b6000024020c62c2149c9a24722120f306e2314157893c3ca17c08d82dc0b800002401acc2cc14e49aa47320a0ee86aa2f214a88d83b817508d82fc0aa000024015152aa13c093a4351ed8e2c6742d313c087838016508682e40c800002400ee82e695dca244a52218f5c6d631615b896c3fc19109783400c4000024008ed2ca14e09ba47b20d8ee46a22f214f09083c017f09183180ce0000240034c2a693b49164281e48dcc63a2c5135085037e16107f82c40aa000023ffd5f2c914e89b447e20a0edc6c830715108f83c018108c02f40ba000023ff7bd2a813cc92e4381ed8e106602d513b887c37416908582c40a2000023ff1d32c814d09a24662028ea468c2e013f087c38e16208302c00b4000023febf82bd946c98046a2068ec86b02f714c08e83b417708d02fc0d8000023fe6132c294989864702068ec46b42f714e89143d218809583280d0000023fe0312c2148897e4682088e8c6a42ee14288bc3ae17b08e03080c6000023fda6d2b7944c98a45a2038ebc6ac2fd14b09103c017408e02e80ba000023fd4b62ac13e092c43d1fa0e8069e2fd15389103d018409002fc0c0000023fcee62bb947498446a2070ee46b430d153891c3c4181092830c0ca000023fc9272b2141c96c4511f70e3865c2d314608ec3c217708a02bc0b4000023fc3462b9944895644f1f38e3c6682d913a084035c15a07f82c40be000023fbd4c2cb15009d44862170f006b42fa14e88bc3b017608c82fc0be000023fb77b2b2144897445a1f98e5c6782db143089c39817609082d80aa000023fb16d2d795409dc4892140ee86cc307155091c3d417e090830c0d0000023fabaa2b4944c9484431f68e1c65c2d513c887438216008683000bc000023fa5b92c814cc9a44792188f4c6e630b15108e03b217809403300c8000023f9fe82c194ac98e4632010ea46a22ef14308c03ae18909883180c8000023f99f82cc94ac9944692040ec06902e914688cc3ae17708582b80bc000023f94112c914e49a44852170f4c6f031915a09603dc18d093831c0ce000023f8e652ab14049424491f38e506782e814488c43b618409103140ba000023f88852c794dc9cc48a2148f346d231015b09543e219109883240c4000023f82a82bf946c9764601fc0e706922f014608c03b617f08c82f80aa000023f7cb82d195289c247a20b8ec46a02fa14b88d83be18008f82d40c2000023f76c62cf95209d64882150f346dc30c15309103cc17708882ec0a8000023f70d52c594a898e4622070ea06b62f814b88dc3b217a08d82e40b4000023f6b142b093f49404441f40e1066c2d714088a039a17108b02e40bc000023f65492b714409804642008ea86882e8143889c38c16408b82ac0a8000023f5f532c894b898c46e2070e9c67e2e013e089c3a017508902e40c0000023f596e2c794d49a847b20f0f246ce2fc14a08d43bc17808c82c40ac000023f53952bc947c9884682048ea86a430314e890c3ba17a08e02f80b2000023f4dd62a813c893444c1f60e746642d3140089c38c17308f830c0c0000023f48012bc146498a4682030ebc6902e214088903a816908182a80ac000023f42262ba945896044d1f88e7866c2d3140088039a16008002b00a8000023f3c642b193f49424411ef0e106602d713a084037016108882e40ae000023f366e2c994a099a45e2010e8c6a42f114f891c3b417d09183180ba000023f307c2c494ac99e4712090eac6962e314488ac39016a08b02d80b0000 else 0x2421ae02c594c49ba47a20d0eec6b42f514708c43ae17608c02c40ba000024215032c894c89ac4702088ed86b830114f08dc3ba16608982ec0b800002420f102c694bc9a84782090ee46a82f714c88fc3b817c09083200c6000024209372bc94889884692040ed06ae2f814a08e03b418b09083140b6000024203442cd94ec9b847c20b0ec06a22f1142887839c17008a82e80be0000241fd712c014789864672008eb46962f514889003c618c09683040c40000241f76f2d194f09ac4762078e7867c2da13c885037016b08b02dc0b00000241f17a2c494d09ac46c2080ebc6b62f214b88d83c0184096031c0d00000241eba12bd148099446b2068eb06902ef14d08c43aa16e08982f00bc0000241e5b52c4147497a4692098ea46842df13e886c38016a08682b80aa0000241dfcd2c214b89a447120a8eec6ae2f114808ac39616808402b40b20000241d9df2c3947898e4682058ec46b02fe14988a037c17108c02e40a80000241d4192b694309504501f80e446622ce138886c37816508b02a40aa0000241ce112d515249c047b2108ef86b22f714908fc3ba18009083080c40000241c82f2c494a498446c2080e9067a2de140888039817308882f40c20000241c2302cb14b497e4672008e9468e2f415009083de18508e02f00b60000241bc682b594289604521f90e2866e2e014008a038216f08d82e40bc0000241b67f2c394c099e4792070eb06a22fb14a89043b418308f830c0be0000241b08f2cb14e499847220b8eec6b630114f88f43cc18609003080c20000241aab22c214a898845e2008e7c6802d9137888439816b08882940a60000241a4ee2b6142c96a4561ff0e5466a2d613f087c39016708582f80b600002419f152b8945898645f1fe0eac6982e714408b839817108a02e00be000024199372c614a09804702088ee06a02ef14588a83a617b08b02ec0b60000241939a2a213a091a4391f28e446682e414188c438c17008982ac0ae00002418db72c214a09944772098ee46a630315288d839216d08802c40ba000024187b92cd15049b247b2090ec46b02f915089043ca18809603640ce000024181fa2ba946c9764691fd8e446762d913a888439617609203080c200002417c2a2b9142c95a4541f58e2064a2ca138082c37015d08402c00a40000241763e2c614a49b046d2078e9c6a02f014a08d43ac17d08882b00a80000241704f2c795009b447c2138f086c42f214808c83a617309303380ce00002416a992b2942095c4541fe0e5467a2e514688dc3a617408a82fc0c2000024164b02c814c09ac46c2068ea06882ee14208c43aa17008902c80aa00002415ec42c714a09804652040eac6902df13c883c37616608182c40b0000024158bb2d695209ce48020d8ee46c430115509283ba17b08d82f40a8000024152f32b293f093c4461f98e506702da14588ac39017208b02c40b400002414d282b7146896a45e1fe0e8c6902f715289043c418109203080cc000024147222d215289d248c2120f046ba2fc14f891c3d018108b02bc0a6000024141492c194949864692060eb86a22e914b88e43b416d08f82e40b400002413b702b7945495e4531fe0e846ae2f614a08e03b017608e83080be000024135692d515249e649221d8f286c830815189303e218d09b83240e000002412f5e2d114fc9ba4712048ecc69e2e7147888c39816f08582c00b0000024129962b9147499645d1fd8e6466c2d313f085c37016808b02d00b2000024123b32ba148897e4582020e9c6802df143088038416e08802c80c200002411dfa2b4943493a43e1ef8e246622d813f889038616908482d40ac000024118302b814509724551fd8e906862e514788bc39617108802d80bc000024112782a813cc9284331ee8e0c6482c513b088439416e08902f00b400002410c692d795209d448720f0ee86a82f414d890c3c0184092030c0c4000024106912c0949c99a47b20e0ef06d830815389203b818408e82cc0a6000024100a62c114b49864662038eb06ac2f714888e83ce18a09102ec0be0000240faba2c914c099646f2008e9468c2e413f88c039816f08b02e80ce0000240f4d42c2947c99645b2030eb06a430715809143be17c09183240c20000240eed62d395049aa4792090ea86902f113f08c439817308a02fc0ba0000240e8d52cc95009d24922130f206e831115489283b817708c83000c20000240e3022bd947c98c46b2060ec06ae2f314b88c439817308803040ba0000240dd362b7942496445a2018e6c66a2df14408ac3a016e08182b80a60000240d75b2ba945898246a2008e8c67c2df13d084c35e15f08202e00b60000240d1832bb145c97e4621f88e4065e2cf138888439a17308902dc0be0000240cbb42ba147c9784662018eac69c2ef15008e43a617908d02fc0b60000240c6022a793e093a4431f28e3c6462c7139088837216e08602b00aa0000240c04e2ae13e092a4441f28e4065e2d4140088438c17009083340d20000240ba6a2c614b89ac46c20b8ee06ba30015308d03c018509182f80cc0000240b4852bf148c99446a2000e946742d613e088038617108c82e40bc0000240ae9e2c514c09ae46e1ff8ea068a2e114408b03b017f09002fc0c40000240a8ce2b794509764521fa0e5c6782eb14188c03aa17109502fc0ba000)) else (if i < 374 then 0x24392b02c594b09884612010e7867c2e6140886836c15708402ac0b600002438cb72c914d49ae48020f8ee86bc2ff15409183c617c08e83080c2000024386f82ae13e09564571fc8e8067a2cf13b088438e16b08802e00b0000024380e52d915489da48c2170f146d030315289183b417f09102f80b200002437afe2ca14bc99e47d20e0f3c6fc31515809203a617308b02e80be000024375362b2942c95c4491f68e1c6542ca13d087838016e08f02f80cc00002436f6d2b5943896244c1f58e6c6782eb14908c039e17708f83100c80000243697c2bf948c9984602038ec469c2f614888c438816c08b02ec0bc000024363a22c1949499a4752098ecc69a2ea14c88f43cc18609603200d600002435d8d2dd95549d84922178f586de31615c095c3ee18a09282f40b4000024357b42bc948c9724562038e8867c2d113a087c38416d08602e00be000024351f32b5943897245d2038e9868e2e313f889c38c16808582c40aa00002434bf62ce14fc9c047720e0ef46c430714e890c3c217b09002d80ae0000243463c2ab93a892243e1f00e406762dc143887038a17108382c80ae0000243402c2d795289ce48620b8eec6b830115589243ca18308c831c0cc00002433a402c994ec9b247720b0f006aa30215188e83be17c09383340b80000243347c2b9143896845c1fe8eac6962e114688b839417508d82f00be00002432ea82b5944896e45d1fb8e706542ca136882436c162084829809c000024328cd2be148098e45e2008e9c6742e214488d83c218609703240ca000024322cc2cf95109da48d2170f2c6d230214d88d43bc18009083180ba00002431cfe2bc14389704521ff0e7c6922f114688c8398175090030c0c4000024317232c294849824682020e9869c2e514a08f03bc18309783200c4000024311242ce14d899646e20d0ee06ac2ff14e89143c618109503300da00002430b792a593dc92a4391ea8dc06282c4134883436a15a07b0284092000024305712d195209ba47320e8f146ca30e15689503e2187094832c0c60000242ffa62b7945896c4441f48e4c66e2df142089439a17808902e40b20000242f9ed2b5944c98245a1fc8e5c67e2d614108903a216908782cc0be0000242f3ea2d714e09b24772110ef46aa2ff14d88e43ac17608a82d00b80000242ee182bf948c99c46f2080f0c6cc30214a88d43c018609703340da0000242e8282c714c098c45e1ff0e906942ef14588b439617b090830c0d00000242e2472c014b89a246c2000e8468a2e714a08d839e17008402b80b40000242dc602c2949c9864612040e946a22ee149090c3b817c08c83040bc0000242d6962b4142c9524521fc0e7c6822ea14908d83bc18608f02e80d00000242d0d72b6943c96445a1f90e7c6882f8152890c3d618f09883340cc0000242cace2d115109c84832138f286d831415a09403dc18e09282e40bc0000242c4f92b7946096a4541fc0e846822dc14288a039017108a82dc0a80000242bef52cf95209d24962148f0c6ce30e15309343d018b08f02ec0c80000242b9272bd144c97045d2070ec46a42f514b88bc3a017608882bc0a80000242b3282cb14f89c647c20c0ec06a42fa14f88e03ba17c09103100d20000242ad6c2b0140c9464461f80e506722e014708d03b418609382fc0c20000242a7992b5144097645e1fe0e6868e2f414d08ec39a16608802d40b20000242a1d02b9142895a44f1f98e706762da140888038a16508782bc0a000002429c092b6942494c4461f48e4867a2e014508983a216e08982d00c20000242960a2ce94c49b247720b8eb46b830214f08fc3d218209283340c8000024290082ca14c49a647420e0edc6a82f014788cc3b217d09283280d0000024289f62df15549d64892178f146be2f815089003b817708d02fc0b6000024284172bd94489784622038e946962f1141886039016508702c80c400002427e4a2b814609764612040e9068a2f214a08d03b017709503040ca000024278672c414b89904732038e9c69c2ef14a08c83ca17808e83240d6000024272a62b094009304531f80e486662db13e887836615208482a40c000002426cc42c6149099e47020c8ea06a42ee14a08e839a17909082f00b0000024266c72cf95009c04852130f146ca30614908f03b417a08c03000a6000024260e02ca94e899c4732050e906b22fe14e08d43ce18409282f00b600002425b232ac94009424441f28e146602d413a888039817008e030c0ca0000242559629c93a491442d1e68dd06462c2131084c36816408382bc0ac00002424fc92b6944497a4682020ea469a2f114e88d039e18509403180c6000024249cb2d6153c9e84912178f1c6d630b15289243d018209083040bc000024244022b2941495a4471fa8e7466e2db13f087038816808182a00a600002423e282be14649684581fc8e8067e2df143887438a16d08882f80be0000242384f2be14b09884671fe0e6467c2d813f886437e1600828298092000024232732c0945c9704592020e946822eb14c08ec3be18209182dc0b600002422c6d2d2151c9c848220e8f0c6ba30b15389283cc18d09983080c00000242268f2be94389584551fc8e846922e8141089439a17508a02e40be000024220be2b9945c9784632028ea467c2e4143087839617508a82d00bc000 else (if i < 375 then 0x2450aad2e19580a1a4a72250f8c6f631b15c09503ce18908f03040ba000024504d92bf14a099e4732088eac6942e7142889c38616e08b02c00b60000244fef32c0947097a45b1fc8e2c6602d213b088039217108702bc0b60000244f9162c1948898046a2050ed86ac2fb14a08c839217308883040dc0000244f31f2d014dc99e4672020e8867e2de13f889438816307f02b80ac0000244ed2c2c614bc99646920a8ed46902ee14788c839817c08b82ec0c00000244e7412c614ac99447920b8efc6d230715589543e819309a83280c60000244e1542c114bc9ae4852148f106be30315189283ce185094831c0b00000244db802c414dc9bc47c20c0f2c6e031115c89503ea19409103400ce0000244d5a22be947897e45f2018ed06a630015509043b217709102e80b40000244cfbd2c414d49a046b2080ea06922dc14408d03aa17809202f00ba0000244c9db2c694cc9b047420f0f386e830815409103bc18008e02d80c20000244c4112b6146499246d2070eb86942f414888e83a817108e02e80c20000244be622b293ec94c44c1f50e4067e2f214208b838e17508c82f00bc0000244b87d2ca14a897c46c2060ebc6a42f1148889c3a217108b03040c40000244b27b2d515209cc48120c0ee06ae2fd14c08f43d419209703440e40000244acb72b2942c95c4471f70e3c6882e514608ac39e16a08982b80ae0000244a6e02b9947897645a2010e746882e513d888838c16208582ec0b80000244a0e42cc94c89944792088edc6b62ff14b09103b817608702c80b400002449b072bf145895e45c2008ea46ae2fc14b08ec3d418908c82c00b6000024495152ca14b89a847320c8edc6b02f914888a83a817008a82f00c400002448f2d2c514b49984762128f186cc30015089203bc18209203080bc000024489172df95809fa4a621f0f506f032015a89483f41a409c032c0cc0000244835d2b0144095e4481f48e4066e2e314288a03a216b08582c00a400002447d722c914d09b447b2148f206c42ff14b88b839a17608c02e00b80000244779b2bb946897845d1fb0e746802e114288c43ac17408a82f40ae000024471b32c114d49a446f2048ea06962ea14288b03aa17108f82d00aa00002446bf72aa13dc9384411f40e346722d3139886037815808502cc0a2000024466182c394889964652038eac6b4302153891c3d418008f82e40c4000024460532ad944897c45d1fa0e486622d814688d43ba18709383280d400002445a702c5148097a4541f98e606862ed14708c03ba17a08d02fc0be0000244547a2d495209be4812088ec86962f414908e43b017808f02e40b000002444e9b2c414b899246c2058e9c6982ed14b88f43ba17508e02ec0b4000024448d02b4144c96c4582000ecc6942f714988c43ae17708982dc0ae000024442f32bd14609884632000ed06b230715709043d419509983440d000002443cff2c894ac9b247a20d8ef86ca2fc15189143e018b09603380c4000024437462af940493644f1f78e286662de14888bc3a217608c82fc0b6000024431822b7944896044f1f80e2c6702df14408a039417008882d80c200002442b862cd94f09a847a20e0f206c030515389003a016a08502a80b00000244259b2c394e09ca48d2130f2c6d030d15809503d418a09703400ce00002441fb82c294649924652058eb06a030015209383f418b093032c0c6000024419db2bd14649744511f68e4c6882f014388a037a16208802dc0b8000024413ca2d815349e64822110ecc6ae2f314b88fc3b417e09282f00c600002440de02c714d09b04832128ee469a2fa14a88c037816c08782ac0c2000024408092bb946496e4632018ea46862f014c08f439217108982ec0ba000024402312be949c98a4672028eb06ac2f714808dc3be18609603280ca0000243fc712b514289404401f20e146522cd13b087837415907d82a00ae0000243f68c2bd146898c46a2068ec86ae2f515088fc3ca18b08f02fc0ca0000243f0ad2be94a099847320b0f086b42f114b08e43b017408882cc0c60000243eac62ca94d09a64742078ebc6942e4145889438616e08902b80b00000243e4cf2cc94e09b44772128f006c42fd14a88e43ba181090830c0b60000243defb2b8142c9664592028e7c67a2d613a888c38816108182a40a80000243d93b2b8944496e45c1fd8e906882e2145888839215f08182cc0ba0000243d3442ca14d09bc4742098ec86ae2f614908c43b0171092030c0ca0000243cd2f2d815549ee4932168f246e230c15509103ce18a09383180ca0000243c7472c594909944642068e8c6902db143086439216a08b02d40b40000243c13d2d495309be4792128f246c430415289143de18809403280be0000243bb612bf14a099046a2050eb869a2f514d08bc3b217f09282f00bc0000243b5b12ae141c93c4381eb8df46582cb13a887438615f07f02a40b00000243afdf2b9145c97c4692020e9068c2e313f888838e17108902c80b80000243a9ef2c914d89b246720a0eb069e2f514b88f83ac183093032c0c40000243a4412ab13f094c4481f48e186582cc13b085038616208202d40bc00002439e412d315289c44872150f346e031615b89703d218109103100da000024398922ac140895844c1fa8e646722dd13e888037a16a08982d80bc000 else 0x24682b92c4949099247320d8edc6a42eb14708c83ac17b09283180c600002467cdc2bd946c97e4661fe8ea06a22f014988e439817608b03180c0000024676ed2c814b49ac4731ff0eb86ac2f714b09103b817409103100d00000246710b2c1946096e45d1fa8e6468a2de13c08a43ac17c08f02f00bc00002466b282c3149898e4682088ef86b02fa14d08fc3b017709003080ca000024665532bb94349624592000e786802e614788c43ac18309682f00c400002465fa82aa93ec9324401f18e046522d013d887038817108c02d40aa000024659bd2c314949624642078ec469e2e514108c03ae18109083000ca000024653d72c694d49a847720b0ebc6b42fc14a88b03a417808882d40b400002464df62c214bc9a646b20f0ebc6862ec14208a43b818109103100aa000024648162be14949744612060eb86a82f314f89103bc17a09102d40bc000024642312bf94b89ae48120c8edc6b22f614b88cc3ac17f08d82f40b600002463c712b0142094e4341e40dd06462cb136083037216408602a80ae000024636a42ba143496646a2078eb86922ed14908a839817208582d40a6000024630bb2c4949c97c4651ff8ea868c2ed14c09043b817a08b82f40cc00002462aa72d615049d248d2160f206cc30714e88e43b418308f03200ca000024624902df954c9f049a2198f446d430a15409203dc18f09283000c800002461eb52c494dc99a4752110f146b22f415089183cc18509182dc0b0000024618b62cd94f09b848020d0ef06ba30015089203c617d08b82f40ce000024612e42ba946897e45b2010ed46ba2fe152890c3d8185096833c0ce00002460d2e2b0141c9444401f48e546622e1141088c38a16108882b409e0000246072f2cf14e499a47620f0ef86ca30114d88c43b417c09002d80ba000024601562c0149c98c45c1ff8e9469a2f414f08cc3a417308d831c0c40000245fb862bd145896c45d1ff0e5c6722d613a886c38416b08382b40b40000245f5c32af94309524481f28e486762e214008a439a16a08482d00a80000245efee2c2947498045c2010e906882e214388b439e17208882b00aa0000245e9f52cf15209de48520e8ee06c230515289083a416a08302b40a80000245e4232b9146c97445c1fa8e9869e2f715509183cc18209183000c80000245de522bd14749844692090f046b22fa14c08e43b018209183040b20000245d85f2ce14e09a846e2070eb06ae2ff15189283d618908f02f00c60000245d2782c814d89ae4732098ed46b62f3153091c3e019409683440be0000245cc752cf94fc9b247920a0ebc6a62eb14a08dc3be17708602f00b80000245c6ae2b5944097446720a8ef06b42f614e08dc39416908b82e40c00000245c0dc2bd949099647220d0ef06b830115609143ca17d08e82fc0bc0000245bad62d315209da4892148f3c6c82ff15109043aa16708982f00cc0000245b5212ad941495a4541f88e406722e214588e83b217d08b02e00b00000245af2b2ca14e89a247820a8eb46862ef14c89083d418c09302e40bc0000245a91a2db956c9f04a221e8f7c70031c15c09603c818209483200c80000245a3552b4941096c45e2010e8068a2eb14788e43aa17308e02fc0c400002459d762c394949864592058ec46ae2fb14d89003cc18509102f00b8000024597712d515289da48f2188f386d630f15509043c818a09403380ca000024591712cd95009dc48c2120f246c42fe15408fc3be17c08982e80b000002458bb62b0940c95844e1f90e3c65c2cc14208a439a16908682b00b2000024585d42ca94c89a24682078eec6b22f014608c03b017608f82d00ba00002457ffe2c0949499a47220d8ef86c630515589383e418509003080b800002457a242bf947898445c2038e746802e414488ac38616808602e00b6000024574632b7943896c45b1fc0e6c6982db141087038616908802b40ac00002456e752c714a898846d2078ec86a42fa14c09043b817c08982e40be000024568b42b1940495044a1fb8e6867e2e214308c83b617b09183040c8000024562d82be94349584531f90e646722df14008a039e17909183240c800002455cc92d4151c9de4842110f0c6ca30115609203c618309102fc0c0000024556dc2c994e09c248d21a0f586ce2fe15089043c418308a82c40a80000245510d2bb949498a46c20a8ec06b62f614888ec3d018309202e00a600002454b572ad940895c44a1f30e1463c2c7138887c37c16a08482a40a0000024545562d194dc9ac48120f0ef86c4301154891c3e218d09803180c000002453f8f2b0940c94e4542000ec068a2e113e88a439e17708a82b80b6000024539d12af13d094644b1f38e1c64c2d414208ac3a817808b02dc0a0000024533ec2c3949c9924702080e886842e414108b03a417908802dc0b600002452e032cb14b49a447f20e8ef06c62fd14f08f03be17508b82ec0b0000024528182c1148c98c45f2010ea86942fd15009003ca18b09503480ca000024522482bc947898645c1ff8e906902de13d88a837a16508202980a400002451c7e2b594349724602050ebc69a2ea14a08e83a417208982fc0b8000024516a32bf94b097a4651ff8e646782e814888f03ae177091030c0de000024510cd2bf148497045b2060ecc6ae2f414f88e03b817c09182ec0c2000))) else (if i < 379 then (if i < 377 then 0x247fb932bd94b09a647a20a0eac6b630415108ec3b017c08802bc0c00000247f5bf2bb945897a45e2020e786782e314808bc3be18a09583440d00000247efab2de15409cc47620b0efc6c22fe14f89043c617408902f40c60000247e9ce2bc947c9944672048ec068c2ec14a08bc3a417a08982b80a40000247e4072ba146096645e1fe0e8068e2ea143889c3a617708902e00b40000247de342c0148c98c46e2020eb46b02fe15489383ca19009483100cc0000247d83b2ca94e49b647a2118ed46ba302156096c3ec18b09082e00b60000247d2662bd14809a447320e8efc6b82fc14f89243d018609483080cc0000247cc832c5948098c4651ff8e806802e213f889437e16307c82a80a00000247c6ae2ba945495c45e2048ed06a62f814d08e83b217708b02ec0b80000247c0f12ab13e49324471f58e4865e2c112f881c36c16b08f83240c00000247badf2d795249b247a2110f006be30115009203b218009282e00b40000247b50f2b8144c9684632070ed069a2f314808ac38616508182b40a20000247af252c814a09a24692068ec86ae2fb15488fc3d418a09603340ba0000247a9372c5948c99046c2010e846702d914308a438e16f08882c00a60000247a3502c1949c99c47820f0eec6ba2fb14e89083ca18a08d82ec0c200002479d542d414f099446220a8ebc6ac307156892c3c618808e83200d80000247976b2c3148098c46f2068ed86bc2f414708d83a816b08882b80a0000024791a12b5945499045f1f90e106522cf137886437a16508082a00bc00002478bae2c614a499047220c8f1c6dc30d15689243dc18708f82ec0b6000024785ee2af13f495044b1f70e7467e2e213c88a838e16007f82b00a800002477ff52cd14f099e47620c0ecc6a82ee14608d03a417708f832c0b000002477a1b2bf944c9724552010eb46922e414488c03c217b09283140ca000024774372bf948098247020b0ea06962f414b08d03cc17808b82f00b800002476e542cd94ec9b64852158f3c6e230e15609103d018a09603380dc0000247686a2cb14d099a47220e0ee06aa2f514d08f43c817c08f02f00cc0000247627b2c914c09a047620a8ed069a2f614a091c3ca17c08f82fc0b800002475c942c214c099c4752008e786802f314b08fc3bc18a09303140d8000024756b82c014749964692040e4866c2dc143889838216f08482b80c0000024750e42be947098a46c2030eb86ac2f114e89083ca18c09783380da00002474b1a2b9145497c45d1fd0e806842df13c888439617308802bc0be0000247452a2c614a898446e2028e846942ef14888c03a417008882e40b200002473f382ca95049b44722048e8c6962eb141089839c17609002dc0c6000024739622bb147098446c2098ec469c2f414e89103c617e09282f00d00000247336a2cc14b49924652068ec869e2e314408bc39817e09402ec0ba00002472d8c2b9946898a4612018eb46942ed14888c03b017a09283040b4000024727db2a913e494044b1f50e4866c2d4138886839216c08a82f00ba000024721f52c2947097c46c2078eb86942e5145889039c175087829c0a200002471c152bb147c98c4602000e9c69c2ee14588b039a17308d02f00ce000024716272c794d09a646d2078ea069c30015108f43d219209883200be000024710552bc946895a4471f40e4866e2d3137884036015407b02b40ae00002470a612d094d099647220c0ed06ac2f214e88fc3bc17708f831c0c0000024704702c894d09b847c20c0ee86ca30215389083ca18809503100b80000246fea22ba942096c4612000e806862ea14508a439417509083080cc0000246f8a82c714b899847220c8ed46ba2f614908ac39616708902ec0c60000246f2982d5951c9ce4822108f0c6d830115009303c218909983080c60000246ecda2b014389544471fa0e846782e613f88b438e17108f02ec0a40000246e6e72ca94c499646f20a8ecc6a02f514e88cc3a417c08c83080c40000246e1012c3149498846d2070ec069a2e8141088c38c17408c82e40b40000246db292bd148c9864692058ea06942f814e88fc3ba18009183000cc0000246d5502b8141c94c4441f08e4c6742dc13c889038816f08c03000c80000246cf512cf94fc9ac4762070eb869a2f714c88d43a416808882dc0b40000246c9712c2947c9a046e2088eb86a02f514988d43a817309002f40c60000246c38b2cd14f49c247e2120f286cc30e16009443dc184092032c0e40000246bdb12bf149899c4652048eb86ae2f714e08e83b418108b02f00b60000246b7d22bf147098e46b20e0eec6c82fd14b08e83b617708682f00b40000246b1fd2ba144096e45d2038ee06a62e914908cc3a216f08882f40b60000246ac272c114a899447120c8ed46b02f214888d03a617609303100cc0000246a6392cb15049bc48820f0ef06ba30814b08c43b417408f02e80bc0000246a01e2db15809f449621b0f5c6ea31515c89543ea18e094832c0ba00002469a352c894d89a64732050eec6a22f915109203ca17508c02ec0c0000024694612bc945495e45b1fb0e7c6882ed14788a839417308c02f00c000002468e962b594609824601fe0e746662df14488d83a417608a82f80ca000024688952d2950c9d44902170f446e631215809003c617f08d030c0be000 else (if i < 378 then 0x24973d92d095149ce4822118ef86be30615609543ca187094831c0ce00002496e362a593e49344481f58e1064e2da144089438015f086830c0b6000024968442cd15049b04752140efc6c02f414b88a43a217508782c80b6000024962792bb943894a4411f28dfc65a2d713e885c36015107a02a40ba00002495cb82b414209484431f10e3465c2d913e088039416908202a80b4000024956fe2b1141895044f1f50e206542db140889439016608982e80be000024950f62db95609e64902168f206de30f15909783f618d092032c0dc00002494b1e2ba145c99047620c0edc6bc2f914988ec3c618209283200c80000249452d2c294d49b84852110ee46b42f414d88f43c417b08f02e00b200002493f6a2b3141c94c43a1f68e4866a2cf13a087838c17308682cc0b60000249396c2d195309d247e2110ec86a02f0147889839817408a82d80be0000249339d2b7943098e47820e8ef46ba2fa14788e83ae17f09383200d800002492da32cd15109d249221a0f6c6e430715209243ec18909202f40d2000024927f32a993bc9324451fd8e646762d713b089039a17108c83000ce000024922222b494589844662048e906982ec14288843ae18008f02e80c200002491c4d2c2949898445c2040e9c6982e814688dc3b217908e83140bc000024916642c694a499445d1fc0e6c67a2db143088c38816f08b82d80b2000024910942bb943c94244a1f80e4c66c2d413e087c39816f08882cc0ae00002490a982cf14f49bc4812110f346c630d15909383de18c09283240c4000024904de2b114089644582000e846982ee14908f03b417509002e80c60000248ff162b694389704632048eb868e2e314a88d43b016f09103140c20000248f93c2b9146c96244f1fc8e886722de13d087c38616608502dc0be0000248f3602b9142896045a1f70e2c65c2cf139082835015207f82cc0c40000248ed6b2d295249e048f21a8f486c22fe14f090c3ca17e09282f40c60000248e7892c514c497c46b2088ec86902f114c08e83a817708a82fc0b60000248e1a72be948097a4602018ec06982d713f889839817208702b00ca0000248dbf32a513a49184341ee0e1c6482cd140888838a16708502e40ba0000248d5b52eb15fca2e4aa2240f9c6fc30d15b097c3f019c0a1035c0ca0000248cff42b3944496845d2038ec06ba2fb15189283d818b09703400ea0000248ca042c914c49b647920a8ee86b830014f88f83b417e09082f80c00000248c4212c2146098045d1fe8ea46a22f915209443d018109203080c00000248be392c614c499646b2040eac69e2ee14a08d03b617608802d80b60000248b8482c914cc9be4812128f046da306159893c3e018f09783300bc0000248b2662c114a898a4662080ee86c22ff15008f43b818108c82dc0be0000248ac8e2bc94489664581f80e746842e0142887037c167083827c0960000248a6c52b8140896a4551fa0e6067c2e214308a83a418609182f40c60000248a0d62ca94b49a047620e8f146dc30c15789203d0183093831c0be00002489af92bc948098a4612060eb869e2fc14f08c43b818309383480e4000024894ff2cd14f49ca48d2178f546de310158895c3d818908f83340dc00002488f4d2ad93e49244311e98dec62a2c713a085036c15b07f82ac0aa0000248897a2b994409704561ff0ea469c2f214a08bc39016d08b82f00ba0000248837a2cb94a899446c2040e806962ea14388c039616308582d00a800002487d942c214b499e46c2078ec06902eb14908e83b617709203000cc000024877b52bb948c9984672058eb86ac2f014908f03c218909383080c6000024871cb2c4149499e46f20a8edc6ac2f814708f83c218509503500c600002486bec2bf944496a45a2008e886842de14188a43a016b08c030c0b8000024866002c5948c97c46d2090ee46cc2fe15589543da19909383280d4000024860012cd95149de48e2178f246dc2fd14d08f03ba18a09603240d000002485a502aa140493643f1f48e6065a2d2139887839016308202b80ac000024854782ba14509724512008e786662d4139086437216d08682c80ae00002484ea12ba14789744652040eb068e2ea148089439e17708c82e80d4000024848a72cb94f49aa47e2128ef86b02fb15009083ce18709303180c4000024842cc2bc948c98446a2068eb86962ee14a08d83b417c08a82e00ba00002483ce32c714d49cc48e2188efc6c030615609483dc18109603080d40000248370b2bd145c9644551ff8e786802e814808e03b817b08782d40b20000248312b2c494ac9b047e20d8ec469c2ea14408dc3b018509503280c200002482b392cc94e09ba4782100f246d630d151891c3c218109183300bc000024825352d015089bc47d20b8ecc6a02f514589003c217308d02cc0b600002481f332d694f89ce4862198f386c62f715189243c818f09402f80b4000024819412c8149898c4662028ea86a22eb14388a838c15d08182bc0aa000024813432d194ec9ba48320d0f0c6da30915589243c818d08f83040ba00002480d702be148898245a2008ea869c2f514a88d43b018208e82e00b4000024807772cb14f89ca4932158f286c230415089103be17708c02fc0da0000248016c2d495349da48f20e8ed86ba2f514d88c83b618509003000b8000 else 0x24aeb952c2948896e44f1fc0e686622dc14208883a416d08702cc0aa000024ae5982d595189ee49721e8f6870031415289183d419209183040b8000024adfbf2c0148499646820a8eac6a22ec14988c43b017408f033c0d6000024ad9f12b514509824632010e9c6882de13b087437216308182a80b0000024ad3e12de9568a0649c21e0f8c72833316889a84021a0098832c0d8000024ace0a2bb147898a47420c8ed46c42fc14888d03a817a08f02e40c4000024ac82b2bf146096045a1fe8e8c6982fc14f08d43c818209403300d0000024ac2442bf14949904652018e7868c2eb14688a839616a08782c00bc000024abc742b5145896c4582008e886942e3140889839e16408702d40b8000024ab6a62b6140495444e1f00df46522d2138085038616508702d00a6000024ab0c02c0948c9824661fc0e6066a2e214488b03a816e08882b00b0000024aaaf02ba948095e4511fa0e706782df14588a839c16f08482ec0c8000024aa52b2b1942895244b1f68e4c67a2dc13f086836615f08582b00b4000024a9f492c094ac9904612038e986862ef14588bc3a817408c82b00a6000024a997d2b594509744642078ec46822e0141089c39c16f08782a40ae000024a93882d194fc9ba47a2080edc6aa30214d88fc3d4182092831c0ca000024a8d5e2e395609de4892148f446ec31515909383da18909703040b8000024a87872c394b499c4682088ef46a02f014588a83a217308682e80b4000024a81a22c1149c9924782070ec869c2e814c08f83a817608d02f00b8000024a7bd42b294289504531f80e546702d914588a039616008382c80b0000024a760d2b4945c98c4611fa0e7c67e2de14388c03b617a09002e80bc000024a70322c194a09904662050ec06b62fd14e88f43d418408e03080c8000024a6a542c0148896a4481f88e546722e714588f43ac18309383140be000024a64782bd14849864662068eb06982f714c08b439e17c08d02c40b0000024a5eae2b7944096845d1fc0e346602d013d08883a417508582e00b6000024a58c02cb14d899e47a20c8ea86942f114a08e43b817108883000d0000024a52db2c014949944642030eac6ae2fa14e08e43ae17308a02f00b2000024a4cfd2c414fc9b447f2110ef46aa2ff15609503e419009203280d4000024a472c2b4144897a4571fd0e8c67c2e814508dc3ae17308f03280d4000024a414a2bf94a899c4692058eec6b42fd14e89143e019309e836c0da000024a3b722bc946c98a4611ff0e746662cd138886c39216e08a02d80c0000024a35522e2953c9e849221d8f706fa30e15589583e418708f83180be000024a2f8d2b8941c9684561fa8e806842e514308c83a817d08b02e80a8000024a299d2cb14d89a245d2020e7c6862ef14788b43a817408902c40ae000024a23b82c294b09a246f2098ecc6a02f914d09003b617b08a82dc0a2000024a1de22ba146c9804632018e8468e2e614788dc3be17e08c82cc0bc000024a180f2b9147098445f2020e7c68a2e614708e43b417808b02d80ba000024a12232c694c89a447b20a8efc6c431015e097c3f219409483280b8000024a0c242d5152c9e648e2158f2c6d430a15389403d618b095833c0c6000024a06492be148498c46d20d8f186be30314e09003c817808d83100c6000024a00682bb145496e4582070ea06842ed14a08cc39c16808802a80be0000249fa9b2b9948498e4682088eb86982e314288c03a817808e83080bc0000249f4dd2b414389524511fa8e746902e7141887837e15b08202a40960000249ef002c1149099446f2038e686802e613e887437c17008782c80ba0000249e9292c594a09a246c2030e946862e3143089c3a017808c82e00b00000249e3712b114349684592018ea86922f414d88d83bc18109502f40c80000249dd942c0949899046a2070ed06b82fd15109183c4186093830c0c80000249d7c72bf947c9784641f98e346622de13d086c38017208e82bc0aa0000249d1dc2c914ac9a64742048ed86aa2fe14f88f03ae17708e03040c20000249cbeb2ce14dc9ae47720a0ef86b430c15c09703e019208f030c0b20000249c60b2c194a89a847520f8ed06c42fd14e89003b217408882d00b60000249c02b2be94449744612020eb06902df141889c38a16f08702bc0be0000249ba4d2c3148c99a4712098eac6a82f814b09003a417a08d82fc0b40000249b47a2bd147898845e2010eb468e2eb14788e03bc18308d82d00b20000249aeb12b6142c9544421f20e546742de142089837216608a02d00b20000249a8ba2cc94bc9ae4772068ee86b82f214988e03a616c08b02fc0ac0000249a2b02d095189d44932198f086ce30715089503e418c08d82fc0be00002499cb02ce95049d848a2150ef46b430b15a89383c818909603140c40000249971c29d13b89364441f40e8c69c2e2142089439a17b08882e80bc000024991392c394a099e47220d8ea86a82f214888ac39417d08b02f80ba00002498b3b2cd14ec9be47a2108f006ae2f614e89083a617608b02cc0bc0000249857d2a9941894843a1f18e146502ce13d086838a16708a83080c800002497faa2bd14609844612018e846742d513d888837a16c08802e00c4000024979d82b8946097245e2000e9867a2e3141888c38e17909203180c4000)) else (if i < 380 then 0x24c624d2bb14709864631ff0e886822ea14888b43a617608e03000d4000024c5c752b3943895a44f1fc0e646622d214108ac38016908c82e80cc000024c566d2d6950c9de4892188f506d230a15709343d419309e03680d8000024c50ae2b2143096445c2000e906762e213d085837015707f02a009c000024c4ad92b6943096c44c1f78e606622d814208a038a163081828c0be000024c44d32cf95149da4892190f1c6b62fd14f08f83ba17709102e40c0000024c3f1e2ab940c9464411ef8dfc64e2d113c08c43a017408f03180cc000024c39562b714449604542008e786662ce13a885436e15b08202d80bc000024c33922b614309744561f58dfc6622dd14088a038a16e08a82dc0aa000024c2dbe2b8143c97a4552010e9869c2f114708b83aa17d08f02e40ae000024c27a82dd95509e048a2128f246dc30e15c896c3fa194098831c0d6000024c21e52b314209504451f60e4466c2df140889c3b016f08682d00ac000024c1c342ac140893c4411f20e2065e2db141889c38e17308f831c0ae000024c165e2bc94849884612028e986942e313e886037a16208402b40ae000024c10792c294649804632078edc6b62fc14b88f03ac17d08d02f00ba000024c0a832d094e49a246b2028e946a02f014a08cc3be17b08a82f40be000024c04c22af943495e44e1f98e706942e7144889039a17008802dc0be000024bff0f2ad93e494c4531f38e3c6542d913f08bc3a817608982e00b6000024bf90f2d295049d448c2198f3c6e431915f897c3ec19309683180d0000024bf32f2bf94a497c46d20a8ee46cc31415a89303d217b089830c0ba000024bed352d015109aa4812130f206ce2ff14f88f43b218a095031c0d6000024be7742b6145c96245a2048e8c68a2de13a085c37c16407d025008c000024be1892c394ac9a047820d0ed868e2ef14a08c83b618109102e80d2000024bdbc02b694309744561fb8e8c6842ee144089039c18008b02dc0bc000024bd6002b5143095c4552000e9c6942f414c09083ce18609203140d2000024bd0452af93e092e4421f50e286602d313b8878378161084029c0a0000024bca542c914ec9aa47d20e8ed46a830115008f03c817b09083200c2000024bc4792c2949c9b44802170f386e631015709543e018a08c03040c4000024bbe7d2cf94c499a46a2000e8466c2e414208a03b418409202f80c6000024bb8a02c094b099247120a0ee46b22f714c88e03b217d08f82ec0ae000024bb2ba2bf94a49a646f2068ec06bc30415789443ea19809203200ca000024bace02bd949498e45c1f88e486722da14308bc39e17c08e02f40ba000024ba6f42c795049c247520b8edc6ba2fc14c88d43aa16508802cc0aa000024ba11f2bc147c99646f2090ec86b42f714908cc3b017208c82e80ca000024b9b0f2d415189e249621a8f3c6ea31715c09143ca18109282f00ce000024b957729f139091e4351ef0e2466a2e4140089439c176090830c0c2000024b8f8c2cb14e49c64842150f186ca301153891c3cc18609603180c0000024b89af2c014ac99a4682048ef06a82f514a08d83ba17808d03040d2000024b83ef2af94009404471f80e706762ec14308a839817208902fc0da000024b7e092be945097845b1fa0eac6a82f514f091c3c618c09283080ca000024b78292c314a89924672008e946922f514d890c3c418609503140d4000024b72542be14609604511fa8e3c6682d5138084839216508902c40b6000024b6c6d2c394b49a446c2078ef46c430514e08f03b018508f02ec0b6000024b66802c794bc9ae47520c0ef46be30414e88d43a817308c02b80a8000024b60a02c314e89a04752068e9c68a2df14288c439e17508a82f00b2000024b5ab22cc94cc9ba47b2120ef06c430214f88b439e17609182fc0d0000024b54d82c194a09a04662028ea46982f214c88b439a17508b82d40a4000024b4f122bc947898a46f2050ec46a22eb146889038016d08a82e40b0000024b49292c2149c98045d2028e6067c2d413b886838216e08782cc0b0000024b436a2ae13c493e44c1fb8e5066c2df14408c43ae16c08a03100b2000024b3d882c5146898645e2040e806922e014108ac39816f08b82fc0ae000024b37ad2c114949844652038e7c67e2df142089838a16f09283080b8000024b31db2bb147c98a4632040ec46b42f915189483f818809283140c0000024b2bed2c614c099647320a0ec86ae2f814b88a839217d08f03080b0000024b25e92d495689fe4a32290f886fe31715789243d819009403040c0000024b20042c794fc9b646e2080eb86b02f914d890c3be17708b02e40b8000024b1a2d2be14789764671fe0e686822df14288a038a16408282b80b2000024b14412c114849864581fb0e2c6562d514388c43bc17c09282f00ba000024b0e712bd94749804652008e746902e5140087837416408202980a8000024b08842c514b89ae47a2070ed06c42ff14a08f03ba17f08f030c0ca000024b029a2c314a89a047220a8eec6d6307156095c3d418b09803480de000024afcb62c294a098c46c20b0ec86b22f714888ec3ce18b08f83140ba000024af72129d939891e4301e58dbc63a2bd12f082836e15d08102b80ae000024af16c2a993f894644d1f90e6066a2de14408c439817008d82f00ce000 else (if i < 381 then 0x24dd97f2d715309dc4912188f6c6f831615789103d2182093033c0c2000024dd3a92be947497a46a2048e9467c2dd13e887839c16c08502c009a000024dcdab2d495549b847d20d8f006c42fc14a88e83be18109002dc0ca000024dc7de2ba94589684581fe8e906822df14608d43aa17f08b82e40b0000024dc1f12c614d49c647e20f8f046c630515008f83c818f09603440d0000024dbc582a193bc9184281eb0dec6442c9134887838616208702d40b0000024db6592cd95109c247f20f0ecc6a62fc15109183d218d09983340dc000024db0ab2a493b092843b1f20e3c6642db139887c3a017208882c40a0000024daac02cd14ec9c24932180f046c430515609704021a909a03100c6000024da4ec2bd145c9664551fe0e9c6862f214a09083be18109203300c8000024d9f1e2b6142895c44d1fc8e986a22ff15288e83b018409602f40ce000024d99562b094209604551f80e5c6722cd139084837a16307d82bc0a8000024d936f2c694d89c648d2130f086bc2fc14c88e83ac17c08c83280d6000024d8d9c2bd14609744581fb0e5c66e2d713e08ac39416808982f80c4000024d87d12b6943c93a44e1f60e606722e114a08d03ae17308a82e00b6000024d82122b014649764661ff0eac6842e414688a039417209102d00a8000024d7c482b614589724541fc0e746862e014608c03a817f09283000b4000024d768a2ac93f894044c1fb8e806862e114488b439016208302c80aa000024d70912c2949c99e46e2020ea869c2f114c88e43d218409403280c4000024d6ab72c014a498846b20a8ed06b42f114788cc39e17408b02c80aa000024d64f42b113f89444391f48e1065e2d5139886036815e08302ac0ac000024d5f142bf148c98847420e0ef06d030815089683d217d09002ec0c4000024d592a2c894a89ac4772030e946982eb14988d83ac17708802e80b0000024d535e2b514189404461f48e3866a2de14108a439417008c83000be000024d4da12b193f494644a1f28e4466c2d713d88a439c16b08783000d0000024d47cd2be147897a4601ff0eb46922e614308bc3aa17808e030c0d2000024d41cf2cb14c89a84782128f2c6d230d15709143d217c09183040bc000024d3be12c714b899c4732128f246e030b156093c3d418b09583180c6000024d35e62cf15009c848e2188f246d02f914c88e839c16b08e03240b8000024d30052bc148099847720a8ec86b030214a08b439617208b02fc0aa000024d29f72d795389e049a2150f2c6da31015909443e018008f02e40aa000024d242c2b9145c97a4682048ea06aa30314f89003cc187098030c0d4000024d1e5d2b8946495a4582008e686802ee14b08f439e17b09483200d8000024d18822bb147c9804672070eb86a62f814b08d839e16908a83100ca000024d12be2b5145c9684592010e806882ee14a089839016908682e40b6000024d0cd12ca150c9c24862110f1c6c830415009083c217c08f82e80ba000024d06ee2bf147898a46e2090e986a62f714d89103b618008e02e80b6000024d010d2bf148c9964722040e7c6822f014608c039817a08d03080cc000024cfb182c894bc9a647720a0ee06b230114b08d83ac17708a82c00a8000024cf52c2c4947898e4732070eac6962ef14888d83a617408d02fc0ba000024cef5b2b8144497c4662048e986762ec14a08fc3d217c08a031c0c8000024ce98f2b6145c96a4531fe8e6c6862d913c88a839816608582b40ae000024ce3af2bf149899646920e8f0c6ac2e714708d43b618809203000d0000024cdda72cd94f09bc48120e8eec6a62f314c08c83aa17708a82e40ca000024cd7b92c394c89aa4712030eb869a2f414b88ec3bc18109282ec0be000024cd1e62bd14849844602028e9469c2e814588c43a017508803000b6000024ccc0b2b894449524541fa0e6466a2dc14608b83a216a08882cc0a8000024cc62d2bd942c95e45c1fb8e646782d8139084c37a16108502b40b0000024cc04b2c5948097c45b1f90e3c66e2d5136885836615b08682b40b0000024cba4c2d695589c84882120f186e231215a09543f2192093830c0cc000024cb4892b0141c9684541ff8e8c69c2ea14588c839e17f09003080c4000024caeaa2bf949c98646a2080eec6be2fb14e09083bc18308c82d80c0000024ca8a92cd15009bc4722068ea86ae2f814c09083ca17e08b02e00bc000024ca2b82c514a897a4732070e9869c2f314608b83ac17d08e02fc0c4000024c9cd72bc148899e47520d0eec6ae2f815189203be18008f83040bc000024c96ed2c4948c99e4682080ed86ae2fe15008d83be17f08b82f40c8000024c912b2b614609784531fc8e906902e914688a839a17408902e40c0000024c8b5e2be948c99a4762108f186cc30714e89043aa17408902ec0b2000024c857d2c314949944672060ebc6bc30015089043b018109003040cc000024c7f862cd14e09ba47d2088edc6a62ed14788cc39016708502d80cc000024c79b72bc147497a4581fa8e7467e2dd141087839816e08a02e00a8000024c73c32ca15049b24802110ef06c02fd15009003bc18508e03240d8000024c6dea2c514ac9a447920f8f086b62f314b08b43aa17508e03100c8000024c68222b614589724571fd0eb86902f514988f83a417608b83000bc000 else 0x24e8ff200000000000000000000000000000000000000000002f80b0000024e8a132bb946898e46f2070ea86ac30114d08ec3b018209283100be000024e84442b9946896a4602008e6467e2df141889039a17108902d00b4000024e7e4e2c814b89984632008e9868c2e113f888038e16908482c009c000024e783a2dd9580a104a221f8f6470031815609283da18d09703180cc000024e72682b714549724531f90e9468e2f014a88c83a217109402fc0b0000024e6c812c814f89b447920e0ef46ce31115609183d218709783240ca000024e66ae2ba144096c45d2038e6c68a2e814488ac3a017508c82ec0b8000024e60e32b5943895e45c1f58e386482cb13a086837816308582b809c000024e5aef2c714cc9aa47520c0efc6b22f814d08f43e2191096035c0cc000024e54e32d595149ca48a2158f1c6d230a15489283d818a09683300c2000024e4f1f2b7943494c4441f38e306662cf13c088038c16b08702dc0ac000024e49242cb94c499c4772080e986882de14488b83b417308982b80b2000024e43402c214e09a847d20c0ee46a42f1148089c39617308582b40ae000024e3d6b2b8145c9604581f88e7069e2f614d08dc3c217e08b02f80c8000024e376e2d194fc9aa47820d8ecc69a2f1142889c38c16f088031c0b8000024e31b32b513fc94244e1f30e3066c2d613e08a839217108902ec0c6000024e2bba2c894e09ce48a20f8f106ac2f414d090c3ce18709782f40b0000024e25e52ba945495c44e1f80e4c6802de13b887437a16c08302c00b0000024e20292af940496245c1fa8e6c65e2cd140086c38216907e829c0ac000024e1a4b2c0948898246820d0f0c6d22fd14e09043d4186095833c0da000024e14722be946496c4571fd0e806822f014808c439616808782b80b0000024e0e8a2c894bc9be47b2108f186c430615088e03b217308a02dc0d0000024e089b2c894849964702070eac6a42f214b88cc3b018a09683500c0000024e02ca2b5144898045f2070edc6ca2f614888b839e16f08e02f80b4000024dfcc62d215289c247e2150f106c430015088ec3b017708e83040a6000024df6f12bf949097845e2028e986962e3140089039e16608382a80b0000024df11e2b9145897c4521fa8e5c65c2d113d087037a16108402b40a0000024deb362c914bc99646c2090edc6a02f214908fc3b818409582f40c2000024de57e2b014049564511fb8e3c66e2d814288ac39616f08402d809c000024ddf812c614dc9aa47f20e8ef46be308155890c3d218609302f80be000)))))))))

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



private theorem b377559 : covered 377559 377655 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377655 : covered 377655 377750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377750 : covered 377750 377845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377845 : covered 377845 377940 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377940 : covered 377940 378036 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378036 : covered 378036 378131 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378131 : covered 378131 378227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378227 : covered 378227 378322 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378322 : covered 378322 378418 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378418 : covered 378418 378513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378513 : covered 378513 378608 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378608 : covered 378608 378703 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378703 : covered 378703 378799 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378799 : covered 378799 378894 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378894 : covered 378894 378990 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b378990 : covered 378990 379085 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379085 : covered 379085 379181 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379181 : covered 379181 379276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379276 : covered 379276 379371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379371 : covered 379371 379466 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379466 : covered 379466 379562 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379562 : covered 379562 379657 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379657 : covered 379657 379753 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379753 : covered 379753 379848 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379848 : covered 379848 379944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b379944 : covered 379944 380039 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380039 : covered 380039 380134 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380134 : covered 380134 380229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380229 : covered 380229 380325 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380325 : covered 380325 380420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380420 : covered 380420 380516 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380516 : covered 380516 380611 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380611 : covered 380611 380707 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380707 : covered 380707 380802 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380802 : covered 380802 380897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380897 : covered 380897 380992 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b380992 : covered 380992 381088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381088 : covered 381088 381183 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381183 : covered 381183 381279 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381279 : covered 381279 381374 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381374 : covered 381374 381470 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381470 : covered 381470 381565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381565 : covered 381565 381660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381660 : covered 381660 381755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381755 : covered 381755 381851 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381851 : covered 381851 381946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b381946 : covered 381946 382042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382042 : covered 382042 382137 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382137 : covered 382137 382233 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382233 : covered 382233 382328 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382328 : covered 382328 382423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382423 : covered 382423 382518 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382518 : covered 382518 382614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382614 : covered 382614 382709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382709 : covered 382709 382805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382805 : covered 382805 382900 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382900 : covered 382900 382996 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b382996 : covered 382996 383091 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383091 : covered 383091 383186 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383186 : covered 383186 383281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383281 : covered 383281 383377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383377 : covered 383377 383472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383472 : covered 383472 383568 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383568 : covered 383568 383663 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383663 : covered 383663 383759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383759 : covered 383759 383854 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383854 : covered 383854 383949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b383949 : covered 383949 384044 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384044 : covered 384044 384140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384140 : covered 384140 384235 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384235 : covered 384235 384331 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384331 : covered 384331 384426 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384426 : covered 384426 384522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384522 : covered 384522 384617 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384617 : covered 384617 384712 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384712 : covered 384712 384807 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384807 : covered 384807 384903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384903 : covered 384903 384998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b384998 : covered 384998 385094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385094 : covered 385094 385189 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385189 : covered 385189 385285 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385285 : covered 385285 385380 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385380 : covered 385380 385475 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385475 : covered 385475 385570 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385570 : covered 385570 385666 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385666 : covered 385666 385761 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385761 : covered 385761 385857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385857 : covered 385857 385952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b385952 : covered 385952 386048 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386048 : covered 386048 386143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386143 : covered 386143 386238 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386238 : covered 386238 386333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386333 : covered 386333 386429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386429 : covered 386429 386524 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386524 : covered 386524 386620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386620 : covered 386620 386715 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386715 : covered 386715 386811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386811 : covered 386811 386906 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b386906 : covered 386906 387001 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387001 : covered 387001 387096 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387096 : covered 387096 387192 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387192 : covered 387192 387287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387287 : covered 387287 387383 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387383 : covered 387383 387478 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387478 : covered 387478 387574 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387574 : covered 387574 387669 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387669 : covered 387669 387764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387764 : covered 387764 387859 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387859 : covered 387859 387955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b387955 : covered 387955 388050 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388050 : covered 388050 388146 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388146 : covered 388146 388241 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388241 : covered 388241 388337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388337 : covered 388337 388432 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388432 : covered 388432 388527 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388527 : covered 388527 388622 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388622 : covered 388622 388718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388718 : covered 388718 388813 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388813 : covered 388813 388909 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b388909 : covered 388909 389004 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389004 : covered 389004 389100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389100 : covered 389100 389195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389195 : covered 389195 389290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389290 : covered 389290 389385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389385 : covered 389385 389481 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389481 : covered 389481 389576 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389576 : covered 389576 389672 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389672 : covered 389672 389767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389767 : covered 389767 389863 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389863 : covered 389863 389958 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b389958 : covered 389958 390053 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390053 : covered 390053 390148 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390148 : covered 390148 390244 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390244 : covered 390244 390339 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390339 : covered 390339 390435 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390435 : covered 390435 390530 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b390530 : covered 390530 390626 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 377559 390626 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b377559 b377655) (joinCoverage b377750 b377845)) (joinCoverage (joinCoverage b377940 b378036) (joinCoverage b378131 b378227))) (joinCoverage (joinCoverage (joinCoverage b378322 b378418) (joinCoverage b378513 b378608)) (joinCoverage (joinCoverage b378703 b378799) (joinCoverage b378894 (joinCoverage b378990 b379085))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b379181 b379276) (joinCoverage b379371 b379466)) (joinCoverage (joinCoverage b379562 b379657) (joinCoverage b379753 b379848))) (joinCoverage (joinCoverage (joinCoverage b379944 b380039) (joinCoverage b380134 b380229)) (joinCoverage (joinCoverage b380325 b380420) (joinCoverage b380516 (joinCoverage b380611 b380707)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b380802 b380897) (joinCoverage b380992 b381088)) (joinCoverage (joinCoverage b381183 b381279) (joinCoverage b381374 b381470))) (joinCoverage (joinCoverage (joinCoverage b381565 b381660) (joinCoverage b381755 b381851)) (joinCoverage (joinCoverage b381946 b382042) (joinCoverage b382137 (joinCoverage b382233 b382328))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b382423 b382518) (joinCoverage b382614 b382709)) (joinCoverage (joinCoverage b382805 b382900) (joinCoverage b382996 b383091))) (joinCoverage (joinCoverage (joinCoverage b383186 b383281) (joinCoverage b383377 b383472)) (joinCoverage (joinCoverage b383568 b383663) (joinCoverage b383759 (joinCoverage b383854 b383949))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b384044 b384140) (joinCoverage b384235 b384331)) (joinCoverage (joinCoverage b384426 b384522) (joinCoverage b384617 b384712))) (joinCoverage (joinCoverage (joinCoverage b384807 b384903) (joinCoverage b384998 b385094)) (joinCoverage (joinCoverage b385189 b385285) (joinCoverage b385380 (joinCoverage b385475 b385570))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b385666 b385761) (joinCoverage b385857 b385952)) (joinCoverage (joinCoverage b386048 b386143) (joinCoverage b386238 b386333))) (joinCoverage (joinCoverage (joinCoverage b386429 b386524) (joinCoverage b386620 b386715)) (joinCoverage (joinCoverage b386811 b386906) (joinCoverage b387001 (joinCoverage b387096 b387192)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b387287 b387383) (joinCoverage b387478 b387574)) (joinCoverage (joinCoverage b387669 b387764) (joinCoverage b387859 b387955))) (joinCoverage (joinCoverage (joinCoverage b388050 b388146) (joinCoverage b388241 b388337)) (joinCoverage (joinCoverage b388432 b388527) (joinCoverage b388622 (joinCoverage b388718 b388813))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b388909 b389004) (joinCoverage b389100 b389195)) (joinCoverage (joinCoverage b389290 b389385) (joinCoverage b389481 (joinCoverage b389576 b389672)))) (joinCoverage (joinCoverage (joinCoverage b389767 b389863) (joinCoverage b389958 b390053)) (joinCoverage (joinCoverage b390148 b390244) (joinCoverage b390339 (joinCoverage b390435 b390530))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 377559 ≤ index 725000000/512 := by decide +kernel
private theorem starting_value : fast 725000000=37479513 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 725000000=37479513) (n : ℕ) (low : 725000000≤n) (bound : n≤750000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=725000000
    · rw [first,anchor]
      exact starting_value
    · have past : 725000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤750000000 by omega)
        have within : index n / 512 < 390626 := by omega
        have lower : index 725000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤750000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ725000000To750000000
