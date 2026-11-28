import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ700000000To725000000

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




private def radical : ℕ := 0x148b6201ff2bf5a00721a23053d29289efc7bd523fe85b114eef0aa565c34ef1cfe8550d44c30bcd8226411d67818023fcaf75cdee935f288fa9785091a740b3636571a1aa45f3e2420695176f2bb4a0386d9dd3b6494bf1b3ca89986af5bed08ce6cf166e2dccaedefb2dc8c688d46d6b2575ca7ef340b11df54aa4bbfc650aa7f550c4c8323fda37a4ffb4041d64e9ee2ec23230cd0b6af198eeb063f10fe6e5f985ac62ccb092763a0a4dfdb7742c719b70d5257f181252f092d7988864048ee2ac0c112fba29f53106ef40ca19903b4207d68bcd7993bf8f4197dfea9fce22beb83e08b318269a476bea30daf3f7cee2ccf672d08a7c177f7fe06269ae4a03807244f5d7198b240e6a4aca600f8cf680f364a5b40708796269b70248e4822e35707cf0e809f62de3e01c67422da6823ce4c70386c4b58b4f5d4575ff1f53655e2c0dfa73635f1c05d92fcd6878d26aecf2325ddaa40048e94413c884e3d1caf4bc675c63e9c223e64c48bb9da03f7b0c734978621bb04a1c6eab093e3b661cfe432e1b231bb9e53a9451d8ae1b89847526e94072b9866975bbcf219dfa99650de6ad35f2d9b0177d0a5c439e40c6ee7c862c9bcafef0b631ee5f723822facb59746dd19e8d4f38f0f01cff2267695774ee413440cf10fd4123a9cac42e6e832c152643643cf95661035b96ee66af5a1da9b80cddf74214d00a5742b2b0f796e43a65d81b601f3feb438c3bd7f1613f403a9fd7e1d270fa024f2494258b5416d88ad8a58ee888ca859ce9b994d93488052a27e858ea782f183e5019f05574d07270a1d5c7e52e4986e46aefd0bf2283af63e9b5c6f12e70f299e604686124fd93c17bb566434ad00c6fe66dec23626a26d9d7759f104346da303a834d857c7e5f335be7cf56da22cd0f0d61e68e0d0898eecc4098f3f3432c4399c9cb85275f7dbd943d9ef411816c4a64584c6df13675845c19314d5b98ac860c9eb21a4579e2a0e1ececcc47b4b36cc410dae5a304fe96475bb8c73b32048c775f32e777d0845b548a9547913af33c77b55df5b837ecd22af3a0413515c2253c29958a972f6a0c7f27c82c97cd41c2c633004ba53c4a14cc9599642efbb181120805dd4edcb5891edfe785859fa8b4a7df4a6f939981acd81119540cdd49d089395bcd1cb2ea39c7d471b153e8d49e96ff86189e19bbb10cce88e63cf74ef560a1da57f6ac1dc5d5d14f7187306aa2b1496a032897ea526262ce5f3529b5db987fdf0d2966bed543caaa1f120d5061dc2e156f6ca6f5ce178c253f46aa5b9909bec9916992b7347a7dfc260b05b366d9197df4eecba59b13ee019a8fe3e3b996bcfe49fe982bd168905fc705730292da7decd03afd9434f550b2a2bbf0e925f9a1cdecfa222408703e9fe94859aa0fe2f840c6635a839ab1de6da0521e23b26985476800b645f411ff681e23ad94e875a991410e88ed2d3737d1aaba51184b55688eca9caa1f32ec30cc707af98377ac59a46f9c25b296449c5fdac985067220b494f73c34767544fa565bfd58f48b10f323f89ffc6dcacc66e39f36ec8b4cd0385eac501876685c95e618b928af9718e52bde7c433f1223b3b0d5bf312c6a1966e108e944b8a31c2a6dd2bd1fdbf50ff356e27ece04dfa41eeaf897064bed24ee808ecf0213a6d7ee497f53c554c08786f4fc27de679e316a52136d232393c33fd62fe55a52745766861c84386d8f0dc2dabbe6874df4c6242764ec099e8c1557b0c1921f4e90d468e990065ef26a8c8bb05c391aa7f830d1aeff37d4f12cde4014a7f26065b16af800d2908869725137506f3264a16c80c70818bff13d3016f23a8c885fed024e9b00cf309f632633a7f47fc343108f855682f43d49ebb6245f0b0e6be88998c2d7667aaca9edd79ae7c5fb37ded3bbd6d38fb94e6b6435e4dc4ddd7358d9e1f75f682524bbff24b4154d6963305016dc0281ebf7e8ee48a739d5cfe921f87e6a2bdfd12368ec73cd28ec974da5918bf47fa37dc20e5cc2ebb453bee00afddb3e1a8afdee3402d1d8ed57538bc482860741401b30c13f04de450d09cf32d217d6dc18488657606e36a57a4a45f3bdeb52ec15d04987e3453e8d63b7cc98d135b558060e46e5662f49b5b9e9463f991b9a9545dacab612a01b3723f489189cb0db4eaa96de2dc325939ae35d7add6cf94512562d4ec374e530ef61e345ce0444a7d0785cf1b4b37605bf735afabe3b09cf1068c6cebb4202b5ebce5d9e4bc60407c1384fb9c68055eef8339331496c8e430fb2a534a6f8efd477235a77749e89bc3fa4706351a39aec827c72d63a7289e14353baad22e349fa084e590c6abc4d13085bcb699bc0a40649f38ef8bd456a64ebf2b6498f8bd017e78a772b0979b7d45973628c07576313d000ed4e7d94073b36235621b3a342da2c0e496532f4e6f93ea08236ace331b737d95206f7ee7befdb1966d4ae4ab2352c302edc5156834e9ac22bbd196dc2416a3371cb84eec72ccc78c8b469ad8fbc7a60d43d977a3488b748d3662e461fbf83f6d485d1f65d00a67926b5ae92b09eeb3fb51291bb59cbfe08c8236906741953fd097ed87a022b77eb26b6c8c2e59f2afa912a2be699856c9102f133648e0b332980ef56dff8b4051601ed09ae3a0bd02ab19494ad89ff12f4893e1320255a367447dfb591af32eccd13427b1391555fe6fac998fbe132522881e33229bfaa54d164b59a68d95a292f5903c16ad76eb97d4f94382c97bee6a42cddccb1d5bab1dfc0bd8dd981ace51ff28225ce115d87f2463eb3842d454d5a534604b19218ddbafcedb6f96d6dac2f639d76ba7ff674baa053eb0927a654e0c7e0ef1fa7c81ef2bc15f4398d17bfe22d9621ece9bbc3d7af1d169fb6be760dc804b035464d17e92eef4356864a84a4807f9c43e36b810b665568d3672e3508a60302286aca8641c9225e9745841efc2046ceb6b654f29bc446f714856504f4d68679b2716ccdbca5a6595909a74e6a39054c6d4b76a4e7d17da42f8675eef9c3d70c2ad8c4e9214a4d170ad6dc646d3904c8429967cd8c39ec77c67f83f6dd2a7a3d144ad62f1db403e702c4c463789a2b0f0158497ad00840fc42c69ddac853a519f2a7e6ee5a2959686296e1256cba816523f664011939313052ee203652cb3c54715def15c191d1416d452b9c972815d3fcc134a398e68c1aff590dc0545cfe47fe7b21b6d4c2cf0173aa891a22fef214be391391bbd5c3189f34ce290643048629bd76bd2a33446908ff1230be074c369d81db59ef0c73950a6e45dbe98370862437f0050117b2e26c1abc17e05fd2a8da84033f76ef0c1773cc1cbb449c1fee8bdf24ec4d60990f5e5bdea639ea9268d2a850830ee55d105cc293c8578330587db8eb6fa60ccfbc261ea288e4aca7d60c3333a052a361112be9bd898098571e3a9713255060f987fdcb84f382426b2b179726b674577da2773f55d8d0c9736900420b6ec9e2cbf1a02b92ecc319e24362b105fadbcf0d16f391ae0353928ea15f6487820ed5f96197c2a1f2e9717865db6d8013127aba6d6fe6c206d37cfc7a11dc52c50eb50d6c9e10c01cd7eca3c46094193321a2f18078d57a839b75ebcb0199e61cef319497752459a1bed940e51ca8f4e111be1905da7250bf7ca2ef65419e4321cca0852bf109044cab9034f73b1b53e35bde4d79205b16518fdd502e0b66417411b6f7434c3e5d0b1ef913cd4d271cf93e83da8c035422fe9f36c73f9d34971486e452bcfe061d3c249cc9ce1df8b90b53554af6891900683f3af5bf4e1ba27bfd541f063fc9c844dacbdfd807df049b2d1c0dfc721f4604947126ea607d7c309f282270c06aca3e5a81fc8a1fe2245935b2440b96fc9af60e05094396b8c347f929567f3f888af5a44dbe7eb8c857f5234d16c961290250168b29dad89fabde956cd499c0e2e30590ac85b74873e67d7006449a8acd2de9d3b0dbf0858d07c4fac10c5c5f411a04db48c81aa8593882a70e6d86fd2225f0c5b3bd15ad725eb2583ae63635c463e7ecafd3cefeaccb58f8ec621b97c30a9b8fe1c92b4d5f168abf04ab9b44afb5bdd934418fe52c85ed007188fe8b93c4cbfa7de93b79b2e21e60a66f6b1d7c315217b50f09cc8a7d85b83219e3c38214ae190e526fdc590bc22ab139d91a0b070b589abda0d2961aa1c2de48a08b0c60ffa323625cbe7727b34b3c1123b7b3e9f6335481c34e1d9f19730861dc9efe5f031a450c751b6476d9519a813d083674d7a2e0b0e64f947daa7fda72cc10ae75abaf870f262f7d22b80f4a99571207187324ed694854b37d2f11c6fe0b7a32f182bc82d52552a2eadfc1a8a7ea45723feea9395c84ccc2037f943ab4a902718e025712f1f458cb20a391af92cbaa0e58cf05bf45c86abf91e938ceff89c037caad4f69c609b9dce0a94fba7cdc6fff6c0126d1dade31c33f96bf40a6008627e85dd377515b000b4ef4174e0375affd26735a4e618f6c2d2854e30879ef88f6e7a5f8fc6aef8250562ca6d659bc87d07b97a863ddf256d1cfcf14df95ba3ba3c09d2a6a93090271ed7580c5a4903a677296388c23d8b739ca1c657e0983f62d794785293083ef0f3f269ead205d2d1570c682b1018cb67a0a05500b36556ba9da0b6e19ffbc4f4eea123332ee0e43d31e91a87dd18a5c3f5bd4b1ef38fcb9fa804c5a94786b8ac88ca6be53d4e91cd131b72aa519a737d93e2f7e4cacc8028d2a0dd25bfbca79278c9b6affe7f392cb35399d955d3e02e340336c69ab8e0f73eedab70d9afc87e00268f450e9cc04ed878ad3c9e2612043b4c830d574c9ba27ef672e00a70acdca2dc78a623549ac53d36273ca01ed298af386aa39bd49dd06edb37cd12fbd66e2c1c449b9178ba28aafe86826e775e3fb00b0066c6f85d9fb80387292dbac61f67568b145db627ff1cb7eb204605b962b69e67544a76c55aef8cb504d3563804922232bca2d69f1c8c4a8b972e8661b1abcd84aaf317ccf7da13902a167eb59aeb2023b772191d1c6b6760efc50df1cc5971786a7151d1a1149a2272ae15ca4fc9d995cf1f9740a79c4a8ba028b3bc27d680a8303017a93e3b0471b9390ee0e75d346ea1994e70b53c626b5c466be520cf711efc4ea400d833ff37495a77bd4f01eda07f9fc8c07ee29c8ef689d50eded31637afc71bfa277ebc4e6e849de0a125655eaf58f130cbf8d3b7d177d3279e9d84824da6169ce4ba555ffe070ee3d38a52ea7b86d30ec63c42bf6acb3c681c4ac9a9b1731c542d84bb85143eaaa66d00ccd773f4cdf453ffb56947c4d594205107e88846d06006da85f4ddf9b54754061a2463b21f7b78eefe4f30a42d2cf15c82fc5d3dba618961be092e6598071ba78454eeba12126cdb47c53d16aee39702a3747383be41a171b72541a2cab0060384bec26afba4a3b9e1f88de5019493b51747a1818104734947d603c00b6f1194fcda970b24c3233a35174c775049078a3092160611cb1c0a18e730e14621d27039b0f7ec46c3d49b6eef1dae54a459f6f17c58c35c3174404618c2bfb5f89fc732b37650fc5c779c96acddc87a94753db770dfcd7b6f111b71ba73f05d5e2c6e04bcfd7769de67904c8535a08499921ba2f613965e2aeba0ff796daeaca19d42488401624c320cc5eb4c7ffa9762f9086898602d6029ef9b5a7dfb9f1b9f8e5141d2b384811c0aef6e54b28093b14644d0df90d432a2aa542254f07e167d51f7ef04df90e79346d4571d974544a74e326422cba8898c11a43fca2bfffc2ff65e800201602448347ca15ce2d85afa0a9a3c81b603b3c659c42a238bf392d5c0efdb451aa968cab567b1c3229fb456d925df548a750b6aa1130869de12edfbe4faa233ba07c0bf4394fa6d9e19f91969cfedaa116b296b61d26c25ff7b3ce0ddfffdf95d0c853726c9453e94fe2f90a7d437f092dc3024b519031fd6cf741bab433886a45b57dfafbc9b44392a90e4391cbc758395789e175f86a2186194210f5786719b9734f1f6648d1e93b42001ca78a748dc095b59832a142d7a80344c2ba6c1d44cf162ae4b6f7e6089a48d08172530d52c862de6d501afa8c3b8d5a9865e90c2ae3acfe89d36bf6014f3874d242436897c932182f19a76c1d203de649e92b58447ddba05a97a1b80bfe518bb6055281ac1003a41c0f406b6096c7c9c3fe4b645472a1c8445a64903ad3007401198c514328ad6b59284932e22e10b42d4dabf78a73f7ef86c85695dcf3d4200b2e9542e04a5eb1a6cf2d84f19632290af488f6291aa2e1d93d03b3f2ba9eba81d595db06495e5af196c58635edb60bceeeccac1a837ac9b5f3dc34ad562c002e71b01cee2f65060b30acccae336a3210081ce64838d6f37866ca3370a6a24dd7c3ced8f696e94dd9287c71d2a5965c8183c01f8a016c062f6b75f73ad402a2450486d7679285989ed00001147b48e6844aef85742922b581aba5a82b238027298e22f98ad67170ec16d989ed52597d0b73b31673e995b7a8acbce997711606707e59182d29bb9fa7da01b03d95dead2b256317fc30c7ecbfa5755b52ff478217d61439be91141f07d1c1ea2c9194b51019b784f28fc1f61e96e44b70541ca859e1b3f1a50692e7bbc1af19beb25bdf3ee0cd66ad160bf0db6008925c0b05190a02335913a0b25d24e45c8b7bb0d6787c641f215391cb1cc4e3d5b54b1ba496f55d375470d795d2b07f66024e971b5dc9800b381438b17400aee550bb248e5bd3f9d2ed77bf588cdfd065f01a5da10fcbef6cb680d232b310dd0ca958538de7a

private def light (n : ℕ) : Bool :=
  if n≤164 then decide n.Prime else n.gcd 328721858553429622726333031164414657201307396238870899045862237158580182864271307153959338482212215476391820329660212699921564577126760936298613378281401599441328640627721748601735615072812402484508949220556707455881820297436017777661078154820871262306304000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤26925) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 164 = 328721858553429622726333031164414657201307396238870899045862237158580182864271307153959338482212215476391820329660212699921564577126760936298613378281401599441328640627721748601735615072812402484508949220556707455881820297436017777661078154820871262306304000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 164 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤26925 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 52 := by unfold smallValid; decide +kernel

private theorem sp52 : smallValid 52 53 := by unfold smallValid; decide +kernel

private theorem sp105 : smallValid 105 52 := by unfold smallValid; decide +kernel

private theorem sp157 : smallValid 157 53 := by unfold smallValid; decide +kernel

private theorem sp210 : smallValid 210 52 := by unfold smallValid; decide +kernel

private theorem sp262 : smallValid 262 53 := by unfold smallValid; decide +kernel

private theorem sp315 : smallValid 315 52 := by unfold smallValid; decide +kernel

private theorem sp367 : smallValid 367 53 := by unfold smallValid; decide +kernel

private theorem sp420 : smallValid 420 52 := by unfold smallValid; decide +kernel

private theorem sp472 : smallValid 472 53 := by unfold smallValid; decide +kernel

private theorem sp525 : smallValid 525 52 := by unfold smallValid; decide +kernel

private theorem sp577 : smallValid 577 53 := by unfold smallValid; decide +kernel

private theorem sp630 : smallValid 630 52 := by unfold smallValid; decide +kernel

private theorem sp682 : smallValid 682 53 := by unfold smallValid; decide +kernel

private theorem sp735 : smallValid 735 53 := by unfold smallValid; decide +kernel

private theorem sp788 : smallValid 788 53 := by unfold smallValid; decide +kernel

private theorem sp841 : smallValid 841 52 := by unfold smallValid; decide +kernel

private theorem sp893 : smallValid 893 53 := by unfold smallValid; decide +kernel

private theorem sp946 : smallValid 946 52 := by unfold smallValid; decide +kernel

private theorem sp998 : smallValid 998 53 := by unfold smallValid; decide +kernel

private theorem sp1051 : smallValid 1051 52 := by unfold smallValid; decide +kernel

private theorem sp1103 : smallValid 1103 53 := by unfold smallValid; decide +kernel

private theorem sp1156 : smallValid 1156 52 := by unfold smallValid; decide +kernel

private theorem sp1208 : smallValid 1208 53 := by unfold smallValid; decide +kernel

private theorem sp1261 : smallValid 1261 52 := by unfold smallValid; decide +kernel

private theorem sp1313 : smallValid 1313 53 := by unfold smallValid; decide +kernel

private theorem sp1366 : smallValid 1366 52 := by unfold smallValid; decide +kernel

private theorem sp1418 : smallValid 1418 53 := by unfold smallValid; decide +kernel

private theorem sp1471 : smallValid 1471 52 := by unfold smallValid; decide +kernel

private theorem sp1523 : smallValid 1523 53 := by unfold smallValid; decide +kernel

private theorem sp1576 : smallValid 1576 53 := by unfold smallValid; decide +kernel

private theorem sp1629 : smallValid 1629 53 := by unfold smallValid; decide +kernel

private theorem sp1682 : smallValid 1682 52 := by unfold smallValid; decide +kernel

private theorem sp1734 : smallValid 1734 53 := by unfold smallValid; decide +kernel

private theorem sp1787 : smallValid 1787 52 := by unfold smallValid; decide +kernel

private theorem sp1839 : smallValid 1839 53 := by unfold smallValid; decide +kernel

private theorem sp1892 : smallValid 1892 52 := by unfold smallValid; decide +kernel

private theorem sp1944 : smallValid 1944 53 := by unfold smallValid; decide +kernel

private theorem sp1997 : smallValid 1997 52 := by unfold smallValid; decide +kernel

private theorem sp2049 : smallValid 2049 53 := by unfold smallValid; decide +kernel

private theorem sp2102 : smallValid 2102 52 := by unfold smallValid; decide +kernel

private theorem sp2154 : smallValid 2154 53 := by unfold smallValid; decide +kernel

private theorem sp2207 : smallValid 2207 52 := by unfold smallValid; decide +kernel

private theorem sp2259 : smallValid 2259 53 := by unfold smallValid; decide +kernel

private theorem sp2312 : smallValid 2312 52 := by unfold smallValid; decide +kernel

private theorem sp2364 : smallValid 2364 53 := by unfold smallValid; decide +kernel

private theorem sp2417 : smallValid 2417 53 := by unfold smallValid; decide +kernel

private theorem sp2470 : smallValid 2470 53 := by unfold smallValid; decide +kernel

private theorem sp2523 : smallValid 2523 52 := by unfold smallValid; decide +kernel

private theorem sp2575 : smallValid 2575 53 := by unfold smallValid; decide +kernel

private theorem sp2628 : smallValid 2628 52 := by unfold smallValid; decide +kernel

private theorem sp2680 : smallValid 2680 53 := by unfold smallValid; decide +kernel

private theorem sp2733 : smallValid 2733 52 := by unfold smallValid; decide +kernel

private theorem sp2785 : smallValid 2785 53 := by unfold smallValid; decide +kernel

private theorem sp2838 : smallValid 2838 53 := by unfold smallValid; decide +kernel

private theorem sp2891 : smallValid 2891 53 := by unfold smallValid; decide +kernel

private theorem sp2944 : smallValid 2944 52 := by unfold smallValid; decide +kernel

private theorem sp2996 : smallValid 2996 53 := by unfold smallValid; decide +kernel

private theorem sp3049 : smallValid 3049 52 := by unfold smallValid; decide +kernel

private theorem sp3101 : smallValid 3101 53 := by unfold smallValid; decide +kernel

private theorem sp3154 : smallValid 3154 52 := by unfold smallValid; decide +kernel

private theorem sp3206 : smallValid 3206 53 := by unfold smallValid; decide +kernel

private theorem sp3259 : smallValid 3259 53 := by unfold smallValid; decide +kernel

private theorem sp3312 : smallValid 3312 53 := by unfold smallValid; decide +kernel

private theorem sp3365 : smallValid 3365 52 := by unfold smallValid; decide +kernel

private theorem sp3417 : smallValid 3417 53 := by unfold smallValid; decide +kernel

private theorem sp3470 : smallValid 3470 52 := by unfold smallValid; decide +kernel

private theorem sp3522 : smallValid 3522 53 := by unfold smallValid; decide +kernel

private theorem sp3575 : smallValid 3575 52 := by unfold smallValid; decide +kernel

private theorem sp3627 : smallValid 3627 53 := by unfold smallValid; decide +kernel

private theorem sp3680 : smallValid 3680 52 := by unfold smallValid; decide +kernel

private theorem sp3732 : smallValid 3732 53 := by unfold smallValid; decide +kernel

private theorem sp3785 : smallValid 3785 52 := by unfold smallValid; decide +kernel

private theorem sp3837 : smallValid 3837 53 := by unfold smallValid; decide +kernel

private theorem sp3890 : smallValid 3890 52 := by unfold smallValid; decide +kernel

private theorem sp3942 : smallValid 3942 53 := by unfold smallValid; decide +kernel

private theorem sp3995 : smallValid 3995 52 := by unfold smallValid; decide +kernel

private theorem sp4047 : smallValid 4047 53 := by unfold smallValid; decide +kernel

private theorem sp4100 : smallValid 4100 53 := by unfold smallValid; decide +kernel

private theorem sp4153 : smallValid 4153 53 := by unfold smallValid; decide +kernel

private theorem sp4206 : smallValid 4206 52 := by unfold smallValid; decide +kernel

private theorem sp4258 : smallValid 4258 53 := by unfold smallValid; decide +kernel

private theorem sp4311 : smallValid 4311 52 := by unfold smallValid; decide +kernel

private theorem sp4363 : smallValid 4363 53 := by unfold smallValid; decide +kernel

private theorem sp4416 : smallValid 4416 52 := by unfold smallValid; decide +kernel

private theorem sp4468 : smallValid 4468 53 := by unfold smallValid; decide +kernel

private theorem sp4521 : smallValid 4521 53 := by unfold smallValid; decide +kernel

private theorem sp4574 : smallValid 4574 53 := by unfold smallValid; decide +kernel

private theorem sp4627 : smallValid 4627 52 := by unfold smallValid; decide +kernel

private theorem sp4679 : smallValid 4679 53 := by unfold smallValid; decide +kernel

private theorem sp4732 : smallValid 4732 52 := by unfold smallValid; decide +kernel

private theorem sp4784 : smallValid 4784 53 := by unfold smallValid; decide +kernel

private theorem sp4837 : smallValid 4837 52 := by unfold smallValid; decide +kernel

private theorem sp4889 : smallValid 4889 53 := by unfold smallValid; decide +kernel

private theorem sp4942 : smallValid 4942 53 := by unfold smallValid; decide +kernel

private theorem sp4995 : smallValid 4995 53 := by unfold smallValid; decide +kernel

private theorem sp5048 : smallValid 5048 52 := by unfold smallValid; decide +kernel

private theorem sp5100 : smallValid 5100 53 := by unfold smallValid; decide +kernel

private theorem sp5153 : smallValid 5153 52 := by unfold smallValid; decide +kernel

private theorem sp5205 : smallValid 5205 53 := by unfold smallValid; decide +kernel

private theorem sp5258 : smallValid 5258 52 := by unfold smallValid; decide +kernel

private theorem sp5310 : smallValid 5310 53 := by unfold smallValid; decide +kernel

private theorem sp5363 : smallValid 5363 52 := by unfold smallValid; decide +kernel

private theorem sp5415 : smallValid 5415 53 := by unfold smallValid; decide +kernel

private theorem sp5468 : smallValid 5468 52 := by unfold smallValid; decide +kernel

private theorem sp5520 : smallValid 5520 53 := by unfold smallValid; decide +kernel

private theorem sp5573 : smallValid 5573 52 := by unfold smallValid; decide +kernel

private theorem sp5625 : smallValid 5625 53 := by unfold smallValid; decide +kernel

private theorem sp5678 : smallValid 5678 52 := by unfold smallValid; decide +kernel

private theorem sp5730 : smallValid 5730 53 := by unfold smallValid; decide +kernel

private theorem sp5783 : smallValid 5783 53 := by unfold smallValid; decide +kernel

private theorem sp5836 : smallValid 5836 53 := by unfold smallValid; decide +kernel

private theorem sp5889 : smallValid 5889 52 := by unfold smallValid; decide +kernel

private theorem sp5941 : smallValid 5941 53 := by unfold smallValid; decide +kernel

private theorem sp5994 : smallValid 5994 52 := by unfold smallValid; decide +kernel

private theorem sp6046 : smallValid 6046 53 := by unfold smallValid; decide +kernel

private theorem sp6099 : smallValid 6099 52 := by unfold smallValid; decide +kernel

private theorem sp6151 : smallValid 6151 53 := by unfold smallValid; decide +kernel

private theorem sp6204 : smallValid 6204 53 := by unfold smallValid; decide +kernel

private theorem sp6257 : smallValid 6257 53 := by unfold smallValid; decide +kernel

private theorem sp6310 : smallValid 6310 52 := by unfold smallValid; decide +kernel

private theorem sp6362 : smallValid 6362 53 := by unfold smallValid; decide +kernel

private theorem sp6415 : smallValid 6415 52 := by unfold smallValid; decide +kernel

private theorem sp6467 : smallValid 6467 53 := by unfold smallValid; decide +kernel

private theorem sp6520 : smallValid 6520 52 := by unfold smallValid; decide +kernel

private theorem sp6572 : smallValid 6572 53 := by unfold smallValid; decide +kernel

private theorem sp6625 : smallValid 6625 53 := by unfold smallValid; decide +kernel

private theorem sp6678 : smallValid 6678 53 := by unfold smallValid; decide +kernel

private theorem sp6731 : smallValid 6731 52 := by unfold smallValid; decide +kernel

private theorem sp6783 : smallValid 6783 53 := by unfold smallValid; decide +kernel

private theorem sp6836 : smallValid 6836 52 := by unfold smallValid; decide +kernel

private theorem sp6888 : smallValid 6888 53 := by unfold smallValid; decide +kernel

private theorem sp6941 : smallValid 6941 52 := by unfold smallValid; decide +kernel

private theorem sp6993 : smallValid 6993 53 := by unfold smallValid; decide +kernel

private theorem sp7046 : smallValid 7046 52 := by unfold smallValid; decide +kernel

private theorem sp7098 : smallValid 7098 53 := by unfold smallValid; decide +kernel

private theorem sp7151 : smallValid 7151 52 := by unfold smallValid; decide +kernel

private theorem sp7203 : smallValid 7203 53 := by unfold smallValid; decide +kernel

private theorem sp7256 : smallValid 7256 52 := by unfold smallValid; decide +kernel

private theorem sp7308 : smallValid 7308 53 := by unfold smallValid; decide +kernel

private theorem sp7361 : smallValid 7361 52 := by unfold smallValid; decide +kernel

private theorem sp7413 : smallValid 7413 53 := by unfold smallValid; decide +kernel

private theorem sp7466 : smallValid 7466 53 := by unfold smallValid; decide +kernel

private theorem sp7519 : smallValid 7519 53 := by unfold smallValid; decide +kernel

private theorem sp7572 : smallValid 7572 52 := by unfold smallValid; decide +kernel

private theorem sp7624 : smallValid 7624 53 := by unfold smallValid; decide +kernel

private theorem sp7677 : smallValid 7677 52 := by unfold smallValid; decide +kernel

private theorem sp7729 : smallValid 7729 53 := by unfold smallValid; decide +kernel

private theorem sp7782 : smallValid 7782 52 := by unfold smallValid; decide +kernel

private theorem sp7834 : smallValid 7834 53 := by unfold smallValid; decide +kernel

private theorem sp7887 : smallValid 7887 53 := by unfold smallValid; decide +kernel

private theorem sp7940 : smallValid 7940 53 := by unfold smallValid; decide +kernel

private theorem sp7993 : smallValid 7993 52 := by unfold smallValid; decide +kernel

private theorem sp8045 : smallValid 8045 53 := by unfold smallValid; decide +kernel

private theorem sp8098 : smallValid 8098 52 := by unfold smallValid; decide +kernel

private theorem sp8150 : smallValid 8150 53 := by unfold smallValid; decide +kernel

private theorem sp8203 : smallValid 8203 52 := by unfold smallValid; decide +kernel

private theorem sp8255 : smallValid 8255 53 := by unfold smallValid; decide +kernel

private theorem sp8308 : smallValid 8308 53 := by unfold smallValid; decide +kernel

private theorem sp8361 : smallValid 8361 53 := by unfold smallValid; decide +kernel

private theorem sp8414 : smallValid 8414 52 := by unfold smallValid; decide +kernel

private theorem sp8466 : smallValid 8466 53 := by unfold smallValid; decide +kernel

private theorem sp8519 : smallValid 8519 52 := by unfold smallValid; decide +kernel

private theorem sp8571 : smallValid 8571 53 := by unfold smallValid; decide +kernel

private theorem sp8624 : smallValid 8624 52 := by unfold smallValid; decide +kernel

private theorem sp8676 : smallValid 8676 53 := by unfold smallValid; decide +kernel

private theorem sp8729 : smallValid 8729 52 := by unfold smallValid; decide +kernel

private theorem sp8781 : smallValid 8781 53 := by unfold smallValid; decide +kernel

private theorem sp8834 : smallValid 8834 52 := by unfold smallValid; decide +kernel

private theorem sp8886 : smallValid 8886 53 := by unfold smallValid; decide +kernel

private theorem sp8939 : smallValid 8939 52 := by unfold smallValid; decide +kernel

private theorem sp8991 : smallValid 8991 53 := by unfold smallValid; decide +kernel

private theorem sp9044 : smallValid 9044 52 := by unfold smallValid; decide +kernel

private theorem sp9096 : smallValid 9096 53 := by unfold smallValid; decide +kernel

private theorem sp9149 : smallValid 9149 53 := by unfold smallValid; decide +kernel

private theorem sp9202 : smallValid 9202 53 := by unfold smallValid; decide +kernel

private theorem sp9255 : smallValid 9255 52 := by unfold smallValid; decide +kernel

private theorem sp9307 : smallValid 9307 53 := by unfold smallValid; decide +kernel

private theorem sp9360 : smallValid 9360 52 := by unfold smallValid; decide +kernel

private theorem sp9412 : smallValid 9412 53 := by unfold smallValid; decide +kernel

private theorem sp9465 : smallValid 9465 52 := by unfold smallValid; decide +kernel

private theorem sp9517 : smallValid 9517 53 := by unfold smallValid; decide +kernel

private theorem sp9570 : smallValid 9570 53 := by unfold smallValid; decide +kernel

private theorem sp9623 : smallValid 9623 53 := by unfold smallValid; decide +kernel

private theorem sp9676 : smallValid 9676 52 := by unfold smallValid; decide +kernel

private theorem sp9728 : smallValid 9728 53 := by unfold smallValid; decide +kernel

private theorem sp9781 : smallValid 9781 52 := by unfold smallValid; decide +kernel

private theorem sp9833 : smallValid 9833 53 := by unfold smallValid; decide +kernel

private theorem sp9886 : smallValid 9886 52 := by unfold smallValid; decide +kernel

private theorem sp9938 : smallValid 9938 53 := by unfold smallValid; decide +kernel

private theorem sp9991 : smallValid 9991 53 := by unfold smallValid; decide +kernel

private theorem sp10044 : smallValid 10044 53 := by unfold smallValid; decide +kernel

private theorem sp10097 : smallValid 10097 52 := by unfold smallValid; decide +kernel

private theorem sp10149 : smallValid 10149 53 := by unfold smallValid; decide +kernel

private theorem sp10202 : smallValid 10202 52 := by unfold smallValid; decide +kernel

private theorem sp10254 : smallValid 10254 53 := by unfold smallValid; decide +kernel

private theorem sp10307 : smallValid 10307 52 := by unfold smallValid; decide +kernel

private theorem sp10359 : smallValid 10359 53 := by unfold smallValid; decide +kernel

private theorem sp10412 : smallValid 10412 52 := by unfold smallValid; decide +kernel

private theorem sp10464 : smallValid 10464 53 := by unfold smallValid; decide +kernel

private theorem sp10517 : smallValid 10517 52 := by unfold smallValid; decide +kernel

private theorem sp10569 : smallValid 10569 53 := by unfold smallValid; decide +kernel

private theorem sp10622 : smallValid 10622 52 := by unfold smallValid; decide +kernel

private theorem sp10674 : smallValid 10674 53 := by unfold smallValid; decide +kernel

private theorem sp10727 : smallValid 10727 52 := by unfold smallValid; decide +kernel

private theorem sp10779 : smallValid 10779 53 := by unfold smallValid; decide +kernel

private theorem sp10832 : smallValid 10832 53 := by unfold smallValid; decide +kernel

private theorem sp10885 : smallValid 10885 53 := by unfold smallValid; decide +kernel

private theorem sp10938 : smallValid 10938 52 := by unfold smallValid; decide +kernel

private theorem sp10990 : smallValid 10990 53 := by unfold smallValid; decide +kernel

private theorem sp11043 : smallValid 11043 52 := by unfold smallValid; decide +kernel

private theorem sp11095 : smallValid 11095 53 := by unfold smallValid; decide +kernel

private theorem sp11148 : smallValid 11148 52 := by unfold smallValid; decide +kernel

private theorem sp11200 : smallValid 11200 53 := by unfold smallValid; decide +kernel

private theorem sp11253 : smallValid 11253 53 := by unfold smallValid; decide +kernel

private theorem sp11306 : smallValid 11306 53 := by unfold smallValid; decide +kernel

private theorem sp11359 : smallValid 11359 52 := by unfold smallValid; decide +kernel

private theorem sp11411 : smallValid 11411 53 := by unfold smallValid; decide +kernel

private theorem sp11464 : smallValid 11464 52 := by unfold smallValid; decide +kernel

private theorem sp11516 : smallValid 11516 53 := by unfold smallValid; decide +kernel

private theorem sp11569 : smallValid 11569 52 := by unfold smallValid; decide +kernel

private theorem sp11621 : smallValid 11621 53 := by unfold smallValid; decide +kernel

private theorem sp11674 : smallValid 11674 53 := by unfold smallValid; decide +kernel

private theorem sp11727 : smallValid 11727 53 := by unfold smallValid; decide +kernel

private theorem sp11780 : smallValid 11780 52 := by unfold smallValid; decide +kernel

private theorem sp11832 : smallValid 11832 53 := by unfold smallValid; decide +kernel

private theorem sp11885 : smallValid 11885 52 := by unfold smallValid; decide +kernel

private theorem sp11937 : smallValid 11937 53 := by unfold smallValid; decide +kernel

private theorem sp11990 : smallValid 11990 52 := by unfold smallValid; decide +kernel

private theorem sp12042 : smallValid 12042 53 := by unfold smallValid; decide +kernel

private theorem sp12095 : smallValid 12095 52 := by unfold smallValid; decide +kernel

private theorem sp12147 : smallValid 12147 53 := by unfold smallValid; decide +kernel

private theorem sp12200 : smallValid 12200 52 := by unfold smallValid; decide +kernel

private theorem sp12252 : smallValid 12252 53 := by unfold smallValid; decide +kernel

private theorem sp12305 : smallValid 12305 52 := by unfold smallValid; decide +kernel

private theorem sp12357 : smallValid 12357 53 := by unfold smallValid; decide +kernel

private theorem sp12410 : smallValid 12410 52 := by unfold smallValid; decide +kernel

private theorem sp12462 : smallValid 12462 53 := by unfold smallValid; decide +kernel

private theorem sp12515 : smallValid 12515 53 := by unfold smallValid; decide +kernel

private theorem sp12568 : smallValid 12568 53 := by unfold smallValid; decide +kernel

private theorem sp12621 : smallValid 12621 52 := by unfold smallValid; decide +kernel

private theorem sp12673 : smallValid 12673 53 := by unfold smallValid; decide +kernel

private theorem sp12726 : smallValid 12726 52 := by unfold smallValid; decide +kernel

private theorem sp12778 : smallValid 12778 53 := by unfold smallValid; decide +kernel

private theorem sp12831 : smallValid 12831 52 := by unfold smallValid; decide +kernel

private theorem sp12883 : smallValid 12883 53 := by unfold smallValid; decide +kernel

private theorem sp12936 : smallValid 12936 53 := by unfold smallValid; decide +kernel

private theorem sp12989 : smallValid 12989 53 := by unfold smallValid; decide +kernel

private theorem sp13042 : smallValid 13042 52 := by unfold smallValid; decide +kernel

private theorem sp13094 : smallValid 13094 53 := by unfold smallValid; decide +kernel

private theorem sp13147 : smallValid 13147 52 := by unfold smallValid; decide +kernel

private theorem sp13199 : smallValid 13199 53 := by unfold smallValid; decide +kernel

private theorem sp13252 : smallValid 13252 52 := by unfold smallValid; decide +kernel

private theorem sp13304 : smallValid 13304 53 := by unfold smallValid; decide +kernel

private theorem sp13357 : smallValid 13357 53 := by unfold smallValid; decide +kernel

private theorem sp13410 : smallValid 13410 53 := by unfold smallValid; decide +kernel

private theorem sp13463 : smallValid 13463 52 := by unfold smallValid; decide +kernel

private theorem sp13515 : smallValid 13515 53 := by unfold smallValid; decide +kernel

private theorem sp13568 : smallValid 13568 52 := by unfold smallValid; decide +kernel

private theorem sp13620 : smallValid 13620 53 := by unfold smallValid; decide +kernel

private theorem sp13673 : smallValid 13673 52 := by unfold smallValid; decide +kernel

private theorem sp13725 : smallValid 13725 53 := by unfold smallValid; decide +kernel

private theorem sp13778 : smallValid 13778 52 := by unfold smallValid; decide +kernel

private theorem sp13830 : smallValid 13830 53 := by unfold smallValid; decide +kernel

private theorem sp13883 : smallValid 13883 52 := by unfold smallValid; decide +kernel

private theorem sp13935 : smallValid 13935 53 := by unfold smallValid; decide +kernel

private theorem sp13988 : smallValid 13988 52 := by unfold smallValid; decide +kernel

private theorem sp14040 : smallValid 14040 53 := by unfold smallValid; decide +kernel

private theorem sp14093 : smallValid 14093 52 := by unfold smallValid; decide +kernel

private theorem sp14145 : smallValid 14145 53 := by unfold smallValid; decide +kernel

private theorem sp14198 : smallValid 14198 53 := by unfold smallValid; decide +kernel

private theorem sp14251 : smallValid 14251 53 := by unfold smallValid; decide +kernel

private theorem sp14304 : smallValid 14304 52 := by unfold smallValid; decide +kernel

private theorem sp14356 : smallValid 14356 53 := by unfold smallValid; decide +kernel

private theorem sp14409 : smallValid 14409 52 := by unfold smallValid; decide +kernel

private theorem sp14461 : smallValid 14461 53 := by unfold smallValid; decide +kernel

private theorem sp14514 : smallValid 14514 52 := by unfold smallValid; decide +kernel

private theorem sp14566 : smallValid 14566 53 := by unfold smallValid; decide +kernel

private theorem sp14619 : smallValid 14619 52 := by unfold smallValid; decide +kernel

private theorem sp14671 : smallValid 14671 53 := by unfold smallValid; decide +kernel

private theorem sp14724 : smallValid 14724 52 := by unfold smallValid; decide +kernel

private theorem sp14776 : smallValid 14776 53 := by unfold smallValid; decide +kernel

private theorem sp14829 : smallValid 14829 52 := by unfold smallValid; decide +kernel

private theorem sp14881 : smallValid 14881 53 := by unfold smallValid; decide +kernel

private theorem sp14934 : smallValid 14934 52 := by unfold smallValid; decide +kernel

private theorem sp14986 : smallValid 14986 53 := by unfold smallValid; decide +kernel

private theorem sp15039 : smallValid 15039 53 := by unfold smallValid; decide +kernel

private theorem sp15092 : smallValid 15092 53 := by unfold smallValid; decide +kernel

private theorem sp15145 : smallValid 15145 52 := by unfold smallValid; decide +kernel

private theorem sp15197 : smallValid 15197 53 := by unfold smallValid; decide +kernel

private theorem sp15250 : smallValid 15250 52 := by unfold smallValid; decide +kernel

private theorem sp15302 : smallValid 15302 53 := by unfold smallValid; decide +kernel

private theorem sp15355 : smallValid 15355 52 := by unfold smallValid; decide +kernel

private theorem sp15407 : smallValid 15407 53 := by unfold smallValid; decide +kernel

private theorem sp15460 : smallValid 15460 52 := by unfold smallValid; decide +kernel

private theorem sp15512 : smallValid 15512 53 := by unfold smallValid; decide +kernel

private theorem sp15565 : smallValid 15565 52 := by unfold smallValid; decide +kernel

private theorem sp15617 : smallValid 15617 53 := by unfold smallValid; decide +kernel

private theorem sp15670 : smallValid 15670 52 := by unfold smallValid; decide +kernel

private theorem sp15722 : smallValid 15722 53 := by unfold smallValid; decide +kernel

private theorem sp15775 : smallValid 15775 52 := by unfold smallValid; decide +kernel

private theorem sp15827 : smallValid 15827 53 := by unfold smallValid; decide +kernel

private theorem sp15880 : smallValid 15880 53 := by unfold smallValid; decide +kernel

private theorem sp15933 : smallValid 15933 53 := by unfold smallValid; decide +kernel

private theorem sp15986 : smallValid 15986 52 := by unfold smallValid; decide +kernel

private theorem sp16038 : smallValid 16038 53 := by unfold smallValid; decide +kernel

private theorem sp16091 : smallValid 16091 52 := by unfold smallValid; decide +kernel

private theorem sp16143 : smallValid 16143 53 := by unfold smallValid; decide +kernel

private theorem sp16196 : smallValid 16196 52 := by unfold smallValid; decide +kernel

private theorem sp16248 : smallValid 16248 53 := by unfold smallValid; decide +kernel

private theorem sp16301 : smallValid 16301 53 := by unfold smallValid; decide +kernel

private theorem sp16354 : smallValid 16354 53 := by unfold smallValid; decide +kernel

private theorem sp16407 : smallValid 16407 52 := by unfold smallValid; decide +kernel

private theorem sp16459 : smallValid 16459 53 := by unfold smallValid; decide +kernel

private theorem sp16512 : smallValid 16512 52 := by unfold smallValid; decide +kernel

private theorem sp16564 : smallValid 16564 53 := by unfold smallValid; decide +kernel

private theorem sp16617 : smallValid 16617 52 := by unfold smallValid; decide +kernel

private theorem sp16669 : smallValid 16669 53 := by unfold smallValid; decide +kernel

private theorem sp16722 : smallValid 16722 53 := by unfold smallValid; decide +kernel

private theorem sp16775 : smallValid 16775 53 := by unfold smallValid; decide +kernel

private theorem sp16828 : smallValid 16828 52 := by unfold smallValid; decide +kernel

private theorem sp16880 : smallValid 16880 53 := by unfold smallValid; decide +kernel

private theorem sp16933 : smallValid 16933 52 := by unfold smallValid; decide +kernel

private theorem sp16985 : smallValid 16985 53 := by unfold smallValid; decide +kernel

private theorem sp17038 : smallValid 17038 52 := by unfold smallValid; decide +kernel

private theorem sp17090 : smallValid 17090 53 := by unfold smallValid; decide +kernel

private theorem sp17143 : smallValid 17143 52 := by unfold smallValid; decide +kernel

private theorem sp17195 : smallValid 17195 53 := by unfold smallValid; decide +kernel

private theorem sp17248 : smallValid 17248 52 := by unfold smallValid; decide +kernel

private theorem sp17300 : smallValid 17300 53 := by unfold smallValid; decide +kernel

private theorem sp17353 : smallValid 17353 52 := by unfold smallValid; decide +kernel

private theorem sp17405 : smallValid 17405 53 := by unfold smallValid; decide +kernel

private theorem sp17458 : smallValid 17458 52 := by unfold smallValid; decide +kernel

private theorem sp17510 : smallValid 17510 53 := by unfold smallValid; decide +kernel

private theorem sp17563 : smallValid 17563 53 := by unfold smallValid; decide +kernel

private theorem sp17616 : smallValid 17616 53 := by unfold smallValid; decide +kernel

private theorem sp17669 : smallValid 17669 52 := by unfold smallValid; decide +kernel

private theorem sp17721 : smallValid 17721 53 := by unfold smallValid; decide +kernel

private theorem sp17774 : smallValid 17774 52 := by unfold smallValid; decide +kernel

private theorem sp17826 : smallValid 17826 53 := by unfold smallValid; decide +kernel

private theorem sp17879 : smallValid 17879 52 := by unfold smallValid; decide +kernel

private theorem sp17931 : smallValid 17931 53 := by unfold smallValid; decide +kernel

private theorem sp17984 : smallValid 17984 53 := by unfold smallValid; decide +kernel

private theorem sp18037 : smallValid 18037 53 := by unfold smallValid; decide +kernel

private theorem sp18090 : smallValid 18090 52 := by unfold smallValid; decide +kernel

private theorem sp18142 : smallValid 18142 53 := by unfold smallValid; decide +kernel

private theorem sp18195 : smallValid 18195 52 := by unfold smallValid; decide +kernel

private theorem sp18247 : smallValid 18247 53 := by unfold smallValid; decide +kernel

private theorem sp18300 : smallValid 18300 52 := by unfold smallValid; decide +kernel

private theorem sp18352 : smallValid 18352 53 := by unfold smallValid; decide +kernel

private theorem sp18405 : smallValid 18405 53 := by unfold smallValid; decide +kernel

private theorem sp18458 : smallValid 18458 53 := by unfold smallValid; decide +kernel

private theorem sp18511 : smallValid 18511 52 := by unfold smallValid; decide +kernel

private theorem sp18563 : smallValid 18563 53 := by unfold smallValid; decide +kernel

private theorem sp18616 : smallValid 18616 52 := by unfold smallValid; decide +kernel

private theorem sp18668 : smallValid 18668 53 := by unfold smallValid; decide +kernel

private theorem sp18721 : smallValid 18721 52 := by unfold smallValid; decide +kernel

private theorem sp18773 : smallValid 18773 53 := by unfold smallValid; decide +kernel

private theorem sp18826 : smallValid 18826 52 := by unfold smallValid; decide +kernel

private theorem sp18878 : smallValid 18878 53 := by unfold smallValid; decide +kernel

private theorem sp18931 : smallValid 18931 52 := by unfold smallValid; decide +kernel

private theorem sp18983 : smallValid 18983 53 := by unfold smallValid; decide +kernel

private theorem sp19036 : smallValid 19036 52 := by unfold smallValid; decide +kernel

private theorem sp19088 : smallValid 19088 53 := by unfold smallValid; decide +kernel

private theorem sp19141 : smallValid 19141 52 := by unfold smallValid; decide +kernel

private theorem sp19193 : smallValid 19193 53 := by unfold smallValid; decide +kernel

private theorem sp19246 : smallValid 19246 53 := by unfold smallValid; decide +kernel

private theorem sp19299 : smallValid 19299 53 := by unfold smallValid; decide +kernel

private theorem sp19352 : smallValid 19352 52 := by unfold smallValid; decide +kernel

private theorem sp19404 : smallValid 19404 53 := by unfold smallValid; decide +kernel

private theorem sp19457 : smallValid 19457 52 := by unfold smallValid; decide +kernel

private theorem sp19509 : smallValid 19509 53 := by unfold smallValid; decide +kernel

private theorem sp19562 : smallValid 19562 52 := by unfold smallValid; decide +kernel

private theorem sp19614 : smallValid 19614 53 := by unfold smallValid; decide +kernel

private theorem sp19667 : smallValid 19667 53 := by unfold smallValid; decide +kernel

private theorem sp19720 : smallValid 19720 53 := by unfold smallValid; decide +kernel

private theorem sp19773 : smallValid 19773 52 := by unfold smallValid; decide +kernel

private theorem sp19825 : smallValid 19825 53 := by unfold smallValid; decide +kernel

private theorem sp19878 : smallValid 19878 52 := by unfold smallValid; decide +kernel

private theorem sp19930 : smallValid 19930 53 := by unfold smallValid; decide +kernel

private theorem sp19983 : smallValid 19983 52 := by unfold smallValid; decide +kernel

private theorem sp20035 : smallValid 20035 53 := by unfold smallValid; decide +kernel

private theorem sp20088 : smallValid 20088 53 := by unfold smallValid; decide +kernel

private theorem sp20141 : smallValid 20141 53 := by unfold smallValid; decide +kernel

private theorem sp20194 : smallValid 20194 52 := by unfold smallValid; decide +kernel

private theorem sp20246 : smallValid 20246 53 := by unfold smallValid; decide +kernel

private theorem sp20299 : smallValid 20299 52 := by unfold smallValid; decide +kernel

private theorem sp20351 : smallValid 20351 53 := by unfold smallValid; decide +kernel

private theorem sp20404 : smallValid 20404 52 := by unfold smallValid; decide +kernel

private theorem sp20456 : smallValid 20456 53 := by unfold smallValid; decide +kernel

private theorem sp20509 : smallValid 20509 52 := by unfold smallValid; decide +kernel

private theorem sp20561 : smallValid 20561 53 := by unfold smallValid; decide +kernel

private theorem sp20614 : smallValid 20614 52 := by unfold smallValid; decide +kernel

private theorem sp20666 : smallValid 20666 53 := by unfold smallValid; decide +kernel

private theorem sp20719 : smallValid 20719 52 := by unfold smallValid; decide +kernel

private theorem sp20771 : smallValid 20771 53 := by unfold smallValid; decide +kernel

private theorem sp20824 : smallValid 20824 52 := by unfold smallValid; decide +kernel

private theorem sp20876 : smallValid 20876 53 := by unfold smallValid; decide +kernel

private theorem sp20929 : smallValid 20929 53 := by unfold smallValid; decide +kernel

private theorem sp20982 : smallValid 20982 53 := by unfold smallValid; decide +kernel

private theorem sp21035 : smallValid 21035 52 := by unfold smallValid; decide +kernel

private theorem sp21087 : smallValid 21087 53 := by unfold smallValid; decide +kernel

private theorem sp21140 : smallValid 21140 52 := by unfold smallValid; decide +kernel

private theorem sp21192 : smallValid 21192 53 := by unfold smallValid; decide +kernel

private theorem sp21245 : smallValid 21245 52 := by unfold smallValid; decide +kernel

private theorem sp21297 : smallValid 21297 53 := by unfold smallValid; decide +kernel

private theorem sp21350 : smallValid 21350 53 := by unfold smallValid; decide +kernel

private theorem sp21403 : smallValid 21403 53 := by unfold smallValid; decide +kernel

private theorem sp21456 : smallValid 21456 52 := by unfold smallValid; decide +kernel

private theorem sp21508 : smallValid 21508 53 := by unfold smallValid; decide +kernel

private theorem sp21561 : smallValid 21561 52 := by unfold smallValid; decide +kernel

private theorem sp21613 : smallValid 21613 53 := by unfold smallValid; decide +kernel

private theorem sp21666 : smallValid 21666 52 := by unfold smallValid; decide +kernel

private theorem sp21718 : smallValid 21718 53 := by unfold smallValid; decide +kernel

private theorem sp21771 : smallValid 21771 53 := by unfold smallValid; decide +kernel

private theorem sp21824 : smallValid 21824 53 := by unfold smallValid; decide +kernel

private theorem sp21877 : smallValid 21877 52 := by unfold smallValid; decide +kernel

private theorem sp21929 : smallValid 21929 53 := by unfold smallValid; decide +kernel

private theorem sp21982 : smallValid 21982 52 := by unfold smallValid; decide +kernel

private theorem sp22034 : smallValid 22034 53 := by unfold smallValid; decide +kernel

private theorem sp22087 : smallValid 22087 52 := by unfold smallValid; decide +kernel

private theorem sp22139 : smallValid 22139 53 := by unfold smallValid; decide +kernel

private theorem sp22192 : smallValid 22192 52 := by unfold smallValid; decide +kernel

private theorem sp22244 : smallValid 22244 53 := by unfold smallValid; decide +kernel

private theorem sp22297 : smallValid 22297 52 := by unfold smallValid; decide +kernel

private theorem sp22349 : smallValid 22349 53 := by unfold smallValid; decide +kernel

private theorem sp22402 : smallValid 22402 52 := by unfold smallValid; decide +kernel

private theorem sp22454 : smallValid 22454 53 := by unfold smallValid; decide +kernel

private theorem sp22507 : smallValid 22507 52 := by unfold smallValid; decide +kernel

private theorem sp22559 : smallValid 22559 53 := by unfold smallValid; decide +kernel

private theorem sp22612 : smallValid 22612 53 := by unfold smallValid; decide +kernel

private theorem sp22665 : smallValid 22665 53 := by unfold smallValid; decide +kernel

private theorem sp22718 : smallValid 22718 52 := by unfold smallValid; decide +kernel

private theorem sp22770 : smallValid 22770 53 := by unfold smallValid; decide +kernel

private theorem sp22823 : smallValid 22823 52 := by unfold smallValid; decide +kernel

private theorem sp22875 : smallValid 22875 53 := by unfold smallValid; decide +kernel

private theorem sp22928 : smallValid 22928 52 := by unfold smallValid; decide +kernel

private theorem sp22980 : smallValid 22980 53 := by unfold smallValid; decide +kernel

private theorem sp23033 : smallValid 23033 53 := by unfold smallValid; decide +kernel

private theorem sp23086 : smallValid 23086 53 := by unfold smallValid; decide +kernel

private theorem sp23139 : smallValid 23139 52 := by unfold smallValid; decide +kernel

private theorem sp23191 : smallValid 23191 53 := by unfold smallValid; decide +kernel

private theorem sp23244 : smallValid 23244 52 := by unfold smallValid; decide +kernel

private theorem sp23296 : smallValid 23296 53 := by unfold smallValid; decide +kernel

private theorem sp23349 : smallValid 23349 52 := by unfold smallValid; decide +kernel

private theorem sp23401 : smallValid 23401 53 := by unfold smallValid; decide +kernel

private theorem sp23454 : smallValid 23454 53 := by unfold smallValid; decide +kernel

private theorem sp23507 : smallValid 23507 53 := by unfold smallValid; decide +kernel

private theorem sp23560 : smallValid 23560 52 := by unfold smallValid; decide +kernel

private theorem sp23612 : smallValid 23612 53 := by unfold smallValid; decide +kernel

private theorem sp23665 : smallValid 23665 52 := by unfold smallValid; decide +kernel

private theorem sp23717 : smallValid 23717 53 := by unfold smallValid; decide +kernel

private theorem sp23770 : smallValid 23770 52 := by unfold smallValid; decide +kernel

private theorem sp23822 : smallValid 23822 53 := by unfold smallValid; decide +kernel

private theorem sp23875 : smallValid 23875 52 := by unfold smallValid; decide +kernel

private theorem sp23927 : smallValid 23927 53 := by unfold smallValid; decide +kernel

private theorem sp23980 : smallValid 23980 52 := by unfold smallValid; decide +kernel

private theorem sp24032 : smallValid 24032 53 := by unfold smallValid; decide +kernel

private theorem sp24085 : smallValid 24085 52 := by unfold smallValid; decide +kernel

private theorem sp24137 : smallValid 24137 53 := by unfold smallValid; decide +kernel

private theorem sp24190 : smallValid 24190 52 := by unfold smallValid; decide +kernel

private theorem sp24242 : smallValid 24242 53 := by unfold smallValid; decide +kernel

private theorem sp24295 : smallValid 24295 53 := by unfold smallValid; decide +kernel

private theorem sp24348 : smallValid 24348 53 := by unfold smallValid; decide +kernel

private theorem sp24401 : smallValid 24401 52 := by unfold smallValid; decide +kernel

private theorem sp24453 : smallValid 24453 53 := by unfold smallValid; decide +kernel

private theorem sp24506 : smallValid 24506 52 := by unfold smallValid; decide +kernel

private theorem sp24558 : smallValid 24558 53 := by unfold smallValid; decide +kernel

private theorem sp24611 : smallValid 24611 52 := by unfold smallValid; decide +kernel

private theorem sp24663 : smallValid 24663 53 := by unfold smallValid; decide +kernel

private theorem sp24716 : smallValid 24716 53 := by unfold smallValid; decide +kernel

private theorem sp24769 : smallValid 24769 53 := by unfold smallValid; decide +kernel

private theorem sp24822 : smallValid 24822 52 := by unfold smallValid; decide +kernel

private theorem sp24874 : smallValid 24874 53 := by unfold smallValid; decide +kernel

private theorem sp24927 : smallValid 24927 52 := by unfold smallValid; decide +kernel

private theorem sp24979 : smallValid 24979 53 := by unfold smallValid; decide +kernel

private theorem sp25032 : smallValid 25032 52 := by unfold smallValid; decide +kernel

private theorem sp25084 : smallValid 25084 53 := by unfold smallValid; decide +kernel

private theorem sp25137 : smallValid 25137 53 := by unfold smallValid; decide +kernel

private theorem sp25190 : smallValid 25190 53 := by unfold smallValid; decide +kernel

private theorem sp25243 : smallValid 25243 52 := by unfold smallValid; decide +kernel

private theorem sp25295 : smallValid 25295 53 := by unfold smallValid; decide +kernel

private theorem sp25348 : smallValid 25348 52 := by unfold smallValid; decide +kernel

private theorem sp25400 : smallValid 25400 53 := by unfold smallValid; decide +kernel

private theorem sp25453 : smallValid 25453 52 := by unfold smallValid; decide +kernel

private theorem sp25505 : smallValid 25505 53 := by unfold smallValid; decide +kernel

private theorem sp25558 : smallValid 25558 52 := by unfold smallValid; decide +kernel

private theorem sp25610 : smallValid 25610 53 := by unfold smallValid; decide +kernel

private theorem sp25663 : smallValid 25663 52 := by unfold smallValid; decide +kernel

private theorem sp25715 : smallValid 25715 53 := by unfold smallValid; decide +kernel

private theorem sp25768 : smallValid 25768 52 := by unfold smallValid; decide +kernel

private theorem sp25820 : smallValid 25820 53 := by unfold smallValid; decide +kernel

private theorem sp25873 : smallValid 25873 52 := by unfold smallValid; decide +kernel

private theorem sp25925 : smallValid 25925 53 := by unfold smallValid; decide +kernel

private theorem sp25978 : smallValid 25978 53 := by unfold smallValid; decide +kernel

private theorem sp26031 : smallValid 26031 53 := by unfold smallValid; decide +kernel

private theorem sp26084 : smallValid 26084 52 := by unfold smallValid; decide +kernel

private theorem sp26136 : smallValid 26136 53 := by unfold smallValid; decide +kernel

private theorem sp26189 : smallValid 26189 52 := by unfold smallValid; decide +kernel

private theorem sp26241 : smallValid 26241 53 := by unfold smallValid; decide +kernel

private theorem sp26294 : smallValid 26294 52 := by unfold smallValid; decide +kernel

private theorem sp26346 : smallValid 26346 53 := by unfold smallValid; decide +kernel

private theorem sp26399 : smallValid 26399 53 := by unfold smallValid; decide +kernel

private theorem sp26452 : smallValid 26452 53 := by unfold smallValid; decide +kernel

private theorem sp26505 : smallValid 26505 52 := by unfold smallValid; decide +kernel

private theorem sp26557 : smallValid 26557 53 := by unfold smallValid; decide +kernel

private theorem sp26610 : smallValid 26610 52 := by unfold smallValid; decide +kernel

private theorem sp26662 : smallValid 26662 53 := by unfold smallValid; decide +kernel

private theorem sp26715 : smallValid 26715 52 := by unfold smallValid; decide +kernel

private theorem sp26767 : smallValid 26767 53 := by unfold smallValid; decide +kernel

private theorem sp26820 : smallValid 26820 53 := by unfold smallValid; decide +kernel

private theorem sp26873 : smallValid 26873 53 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤26925) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 26926 := (joinSmall (lo:=0) (a:=13463) (b:=13463) (joinSmall (lo:=0) (a:=6731) (b:=6732) (joinSmall (lo:=0) (a:=3365) (b:=3366) (joinSmall (lo:=0) (a:=1682) (b:=1683) (joinSmall (lo:=0) (a:=841) (b:=841) (joinSmall (lo:=0) (a:=420) (b:=421) (joinSmall (lo:=0) (a:=210) (b:=210) (joinSmall (lo:=0) (a:=105) (b:=105) (joinSmall (lo:=0) (a:=52) (b:=53) sp0 sp52) (joinSmall (lo:=105) (a:=52) (b:=53) sp105 sp157)) (joinSmall (lo:=210) (a:=105) (b:=105) (joinSmall (lo:=210) (a:=52) (b:=53) sp210 sp262) (joinSmall (lo:=315) (a:=52) (b:=53) sp315 sp367))) (joinSmall (lo:=420) (a:=210) (b:=211) (joinSmall (lo:=420) (a:=105) (b:=105) (joinSmall (lo:=420) (a:=52) (b:=53) sp420 sp472) (joinSmall (lo:=525) (a:=52) (b:=53) sp525 sp577)) (joinSmall (lo:=630) (a:=105) (b:=106) (joinSmall (lo:=630) (a:=52) (b:=53) sp630 sp682) (joinSmall (lo:=735) (a:=53) (b:=53) sp735 sp788)))) (joinSmall (lo:=841) (a:=420) (b:=421) (joinSmall (lo:=841) (a:=210) (b:=210) (joinSmall (lo:=841) (a:=105) (b:=105) (joinSmall (lo:=841) (a:=52) (b:=53) sp841 sp893) (joinSmall (lo:=946) (a:=52) (b:=53) sp946 sp998)) (joinSmall (lo:=1051) (a:=105) (b:=105) (joinSmall (lo:=1051) (a:=52) (b:=53) sp1051 sp1103) (joinSmall (lo:=1156) (a:=52) (b:=53) sp1156 sp1208))) (joinSmall (lo:=1261) (a:=210) (b:=211) (joinSmall (lo:=1261) (a:=105) (b:=105) (joinSmall (lo:=1261) (a:=52) (b:=53) sp1261 sp1313) (joinSmall (lo:=1366) (a:=52) (b:=53) sp1366 sp1418)) (joinSmall (lo:=1471) (a:=105) (b:=106) (joinSmall (lo:=1471) (a:=52) (b:=53) sp1471 sp1523) (joinSmall (lo:=1576) (a:=53) (b:=53) sp1576 sp1629))))) (joinSmall (lo:=1682) (a:=841) (b:=842) (joinSmall (lo:=1682) (a:=420) (b:=421) (joinSmall (lo:=1682) (a:=210) (b:=210) (joinSmall (lo:=1682) (a:=105) (b:=105) (joinSmall (lo:=1682) (a:=52) (b:=53) sp1682 sp1734) (joinSmall (lo:=1787) (a:=52) (b:=53) sp1787 sp1839)) (joinSmall (lo:=1892) (a:=105) (b:=105) (joinSmall (lo:=1892) (a:=52) (b:=53) sp1892 sp1944) (joinSmall (lo:=1997) (a:=52) (b:=53) sp1997 sp2049))) (joinSmall (lo:=2102) (a:=210) (b:=211) (joinSmall (lo:=2102) (a:=105) (b:=105) (joinSmall (lo:=2102) (a:=52) (b:=53) sp2102 sp2154) (joinSmall (lo:=2207) (a:=52) (b:=53) sp2207 sp2259)) (joinSmall (lo:=2312) (a:=105) (b:=106) (joinSmall (lo:=2312) (a:=52) (b:=53) sp2312 sp2364) (joinSmall (lo:=2417) (a:=53) (b:=53) sp2417 sp2470)))) (joinSmall (lo:=2523) (a:=421) (b:=421) (joinSmall (lo:=2523) (a:=210) (b:=211) (joinSmall (lo:=2523) (a:=105) (b:=105) (joinSmall (lo:=2523) (a:=52) (b:=53) sp2523 sp2575) (joinSmall (lo:=2628) (a:=52) (b:=53) sp2628 sp2680)) (joinSmall (lo:=2733) (a:=105) (b:=106) (joinSmall (lo:=2733) (a:=52) (b:=53) sp2733 sp2785) (joinSmall (lo:=2838) (a:=53) (b:=53) sp2838 sp2891))) (joinSmall (lo:=2944) (a:=210) (b:=211) (joinSmall (lo:=2944) (a:=105) (b:=105) (joinSmall (lo:=2944) (a:=52) (b:=53) sp2944 sp2996) (joinSmall (lo:=3049) (a:=52) (b:=53) sp3049 sp3101)) (joinSmall (lo:=3154) (a:=105) (b:=106) (joinSmall (lo:=3154) (a:=52) (b:=53) sp3154 sp3206) (joinSmall (lo:=3259) (a:=53) (b:=53) sp3259 sp3312)))))) (joinSmall (lo:=3365) (a:=1683) (b:=1683) (joinSmall (lo:=3365) (a:=841) (b:=842) (joinSmall (lo:=3365) (a:=420) (b:=421) (joinSmall (lo:=3365) (a:=210) (b:=210) (joinSmall (lo:=3365) (a:=105) (b:=105) (joinSmall (lo:=3365) (a:=52) (b:=53) sp3365 sp3417) (joinSmall (lo:=3470) (a:=52) (b:=53) sp3470 sp3522)) (joinSmall (lo:=3575) (a:=105) (b:=105) (joinSmall (lo:=3575) (a:=52) (b:=53) sp3575 sp3627) (joinSmall (lo:=3680) (a:=52) (b:=53) sp3680 sp3732))) (joinSmall (lo:=3785) (a:=210) (b:=211) (joinSmall (lo:=3785) (a:=105) (b:=105) (joinSmall (lo:=3785) (a:=52) (b:=53) sp3785 sp3837) (joinSmall (lo:=3890) (a:=52) (b:=53) sp3890 sp3942)) (joinSmall (lo:=3995) (a:=105) (b:=106) (joinSmall (lo:=3995) (a:=52) (b:=53) sp3995 sp4047) (joinSmall (lo:=4100) (a:=53) (b:=53) sp4100 sp4153)))) (joinSmall (lo:=4206) (a:=421) (b:=421) (joinSmall (lo:=4206) (a:=210) (b:=211) (joinSmall (lo:=4206) (a:=105) (b:=105) (joinSmall (lo:=4206) (a:=52) (b:=53) sp4206 sp4258) (joinSmall (lo:=4311) (a:=52) (b:=53) sp4311 sp4363)) (joinSmall (lo:=4416) (a:=105) (b:=106) (joinSmall (lo:=4416) (a:=52) (b:=53) sp4416 sp4468) (joinSmall (lo:=4521) (a:=53) (b:=53) sp4521 sp4574))) (joinSmall (lo:=4627) (a:=210) (b:=211) (joinSmall (lo:=4627) (a:=105) (b:=105) (joinSmall (lo:=4627) (a:=52) (b:=53) sp4627 sp4679) (joinSmall (lo:=4732) (a:=52) (b:=53) sp4732 sp4784)) (joinSmall (lo:=4837) (a:=105) (b:=106) (joinSmall (lo:=4837) (a:=52) (b:=53) sp4837 sp4889) (joinSmall (lo:=4942) (a:=53) (b:=53) sp4942 sp4995))))) (joinSmall (lo:=5048) (a:=841) (b:=842) (joinSmall (lo:=5048) (a:=420) (b:=421) (joinSmall (lo:=5048) (a:=210) (b:=210) (joinSmall (lo:=5048) (a:=105) (b:=105) (joinSmall (lo:=5048) (a:=52) (b:=53) sp5048 sp5100) (joinSmall (lo:=5153) (a:=52) (b:=53) sp5153 sp5205)) (joinSmall (lo:=5258) (a:=105) (b:=105) (joinSmall (lo:=5258) (a:=52) (b:=53) sp5258 sp5310) (joinSmall (lo:=5363) (a:=52) (b:=53) sp5363 sp5415))) (joinSmall (lo:=5468) (a:=210) (b:=211) (joinSmall (lo:=5468) (a:=105) (b:=105) (joinSmall (lo:=5468) (a:=52) (b:=53) sp5468 sp5520) (joinSmall (lo:=5573) (a:=52) (b:=53) sp5573 sp5625)) (joinSmall (lo:=5678) (a:=105) (b:=106) (joinSmall (lo:=5678) (a:=52) (b:=53) sp5678 sp5730) (joinSmall (lo:=5783) (a:=53) (b:=53) sp5783 sp5836)))) (joinSmall (lo:=5889) (a:=421) (b:=421) (joinSmall (lo:=5889) (a:=210) (b:=211) (joinSmall (lo:=5889) (a:=105) (b:=105) (joinSmall (lo:=5889) (a:=52) (b:=53) sp5889 sp5941) (joinSmall (lo:=5994) (a:=52) (b:=53) sp5994 sp6046)) (joinSmall (lo:=6099) (a:=105) (b:=106) (joinSmall (lo:=6099) (a:=52) (b:=53) sp6099 sp6151) (joinSmall (lo:=6204) (a:=53) (b:=53) sp6204 sp6257))) (joinSmall (lo:=6310) (a:=210) (b:=211) (joinSmall (lo:=6310) (a:=105) (b:=105) (joinSmall (lo:=6310) (a:=52) (b:=53) sp6310 sp6362) (joinSmall (lo:=6415) (a:=52) (b:=53) sp6415 sp6467)) (joinSmall (lo:=6520) (a:=105) (b:=106) (joinSmall (lo:=6520) (a:=52) (b:=53) sp6520 sp6572) (joinSmall (lo:=6625) (a:=53) (b:=53) sp6625 sp6678))))))) (joinSmall (lo:=6731) (a:=3366) (b:=3366) (joinSmall (lo:=6731) (a:=1683) (b:=1683) (joinSmall (lo:=6731) (a:=841) (b:=842) (joinSmall (lo:=6731) (a:=420) (b:=421) (joinSmall (lo:=6731) (a:=210) (b:=210) (joinSmall (lo:=6731) (a:=105) (b:=105) (joinSmall (lo:=6731) (a:=52) (b:=53) sp6731 sp6783) (joinSmall (lo:=6836) (a:=52) (b:=53) sp6836 sp6888)) (joinSmall (lo:=6941) (a:=105) (b:=105) (joinSmall (lo:=6941) (a:=52) (b:=53) sp6941 sp6993) (joinSmall (lo:=7046) (a:=52) (b:=53) sp7046 sp7098))) (joinSmall (lo:=7151) (a:=210) (b:=211) (joinSmall (lo:=7151) (a:=105) (b:=105) (joinSmall (lo:=7151) (a:=52) (b:=53) sp7151 sp7203) (joinSmall (lo:=7256) (a:=52) (b:=53) sp7256 sp7308)) (joinSmall (lo:=7361) (a:=105) (b:=106) (joinSmall (lo:=7361) (a:=52) (b:=53) sp7361 sp7413) (joinSmall (lo:=7466) (a:=53) (b:=53) sp7466 sp7519)))) (joinSmall (lo:=7572) (a:=421) (b:=421) (joinSmall (lo:=7572) (a:=210) (b:=211) (joinSmall (lo:=7572) (a:=105) (b:=105) (joinSmall (lo:=7572) (a:=52) (b:=53) sp7572 sp7624) (joinSmall (lo:=7677) (a:=52) (b:=53) sp7677 sp7729)) (joinSmall (lo:=7782) (a:=105) (b:=106) (joinSmall (lo:=7782) (a:=52) (b:=53) sp7782 sp7834) (joinSmall (lo:=7887) (a:=53) (b:=53) sp7887 sp7940))) (joinSmall (lo:=7993) (a:=210) (b:=211) (joinSmall (lo:=7993) (a:=105) (b:=105) (joinSmall (lo:=7993) (a:=52) (b:=53) sp7993 sp8045) (joinSmall (lo:=8098) (a:=52) (b:=53) sp8098 sp8150)) (joinSmall (lo:=8203) (a:=105) (b:=106) (joinSmall (lo:=8203) (a:=52) (b:=53) sp8203 sp8255) (joinSmall (lo:=8308) (a:=53) (b:=53) sp8308 sp8361))))) (joinSmall (lo:=8414) (a:=841) (b:=842) (joinSmall (lo:=8414) (a:=420) (b:=421) (joinSmall (lo:=8414) (a:=210) (b:=210) (joinSmall (lo:=8414) (a:=105) (b:=105) (joinSmall (lo:=8414) (a:=52) (b:=53) sp8414 sp8466) (joinSmall (lo:=8519) (a:=52) (b:=53) sp8519 sp8571)) (joinSmall (lo:=8624) (a:=105) (b:=105) (joinSmall (lo:=8624) (a:=52) (b:=53) sp8624 sp8676) (joinSmall (lo:=8729) (a:=52) (b:=53) sp8729 sp8781))) (joinSmall (lo:=8834) (a:=210) (b:=211) (joinSmall (lo:=8834) (a:=105) (b:=105) (joinSmall (lo:=8834) (a:=52) (b:=53) sp8834 sp8886) (joinSmall (lo:=8939) (a:=52) (b:=53) sp8939 sp8991)) (joinSmall (lo:=9044) (a:=105) (b:=106) (joinSmall (lo:=9044) (a:=52) (b:=53) sp9044 sp9096) (joinSmall (lo:=9149) (a:=53) (b:=53) sp9149 sp9202)))) (joinSmall (lo:=9255) (a:=421) (b:=421) (joinSmall (lo:=9255) (a:=210) (b:=211) (joinSmall (lo:=9255) (a:=105) (b:=105) (joinSmall (lo:=9255) (a:=52) (b:=53) sp9255 sp9307) (joinSmall (lo:=9360) (a:=52) (b:=53) sp9360 sp9412)) (joinSmall (lo:=9465) (a:=105) (b:=106) (joinSmall (lo:=9465) (a:=52) (b:=53) sp9465 sp9517) (joinSmall (lo:=9570) (a:=53) (b:=53) sp9570 sp9623))) (joinSmall (lo:=9676) (a:=210) (b:=211) (joinSmall (lo:=9676) (a:=105) (b:=105) (joinSmall (lo:=9676) (a:=52) (b:=53) sp9676 sp9728) (joinSmall (lo:=9781) (a:=52) (b:=53) sp9781 sp9833)) (joinSmall (lo:=9886) (a:=105) (b:=106) (joinSmall (lo:=9886) (a:=52) (b:=53) sp9886 sp9938) (joinSmall (lo:=9991) (a:=53) (b:=53) sp9991 sp10044)))))) (joinSmall (lo:=10097) (a:=1683) (b:=1683) (joinSmall (lo:=10097) (a:=841) (b:=842) (joinSmall (lo:=10097) (a:=420) (b:=421) (joinSmall (lo:=10097) (a:=210) (b:=210) (joinSmall (lo:=10097) (a:=105) (b:=105) (joinSmall (lo:=10097) (a:=52) (b:=53) sp10097 sp10149) (joinSmall (lo:=10202) (a:=52) (b:=53) sp10202 sp10254)) (joinSmall (lo:=10307) (a:=105) (b:=105) (joinSmall (lo:=10307) (a:=52) (b:=53) sp10307 sp10359) (joinSmall (lo:=10412) (a:=52) (b:=53) sp10412 sp10464))) (joinSmall (lo:=10517) (a:=210) (b:=211) (joinSmall (lo:=10517) (a:=105) (b:=105) (joinSmall (lo:=10517) (a:=52) (b:=53) sp10517 sp10569) (joinSmall (lo:=10622) (a:=52) (b:=53) sp10622 sp10674)) (joinSmall (lo:=10727) (a:=105) (b:=106) (joinSmall (lo:=10727) (a:=52) (b:=53) sp10727 sp10779) (joinSmall (lo:=10832) (a:=53) (b:=53) sp10832 sp10885)))) (joinSmall (lo:=10938) (a:=421) (b:=421) (joinSmall (lo:=10938) (a:=210) (b:=211) (joinSmall (lo:=10938) (a:=105) (b:=105) (joinSmall (lo:=10938) (a:=52) (b:=53) sp10938 sp10990) (joinSmall (lo:=11043) (a:=52) (b:=53) sp11043 sp11095)) (joinSmall (lo:=11148) (a:=105) (b:=106) (joinSmall (lo:=11148) (a:=52) (b:=53) sp11148 sp11200) (joinSmall (lo:=11253) (a:=53) (b:=53) sp11253 sp11306))) (joinSmall (lo:=11359) (a:=210) (b:=211) (joinSmall (lo:=11359) (a:=105) (b:=105) (joinSmall (lo:=11359) (a:=52) (b:=53) sp11359 sp11411) (joinSmall (lo:=11464) (a:=52) (b:=53) sp11464 sp11516)) (joinSmall (lo:=11569) (a:=105) (b:=106) (joinSmall (lo:=11569) (a:=52) (b:=53) sp11569 sp11621) (joinSmall (lo:=11674) (a:=53) (b:=53) sp11674 sp11727))))) (joinSmall (lo:=11780) (a:=841) (b:=842) (joinSmall (lo:=11780) (a:=420) (b:=421) (joinSmall (lo:=11780) (a:=210) (b:=210) (joinSmall (lo:=11780) (a:=105) (b:=105) (joinSmall (lo:=11780) (a:=52) (b:=53) sp11780 sp11832) (joinSmall (lo:=11885) (a:=52) (b:=53) sp11885 sp11937)) (joinSmall (lo:=11990) (a:=105) (b:=105) (joinSmall (lo:=11990) (a:=52) (b:=53) sp11990 sp12042) (joinSmall (lo:=12095) (a:=52) (b:=53) sp12095 sp12147))) (joinSmall (lo:=12200) (a:=210) (b:=211) (joinSmall (lo:=12200) (a:=105) (b:=105) (joinSmall (lo:=12200) (a:=52) (b:=53) sp12200 sp12252) (joinSmall (lo:=12305) (a:=52) (b:=53) sp12305 sp12357)) (joinSmall (lo:=12410) (a:=105) (b:=106) (joinSmall (lo:=12410) (a:=52) (b:=53) sp12410 sp12462) (joinSmall (lo:=12515) (a:=53) (b:=53) sp12515 sp12568)))) (joinSmall (lo:=12621) (a:=421) (b:=421) (joinSmall (lo:=12621) (a:=210) (b:=211) (joinSmall (lo:=12621) (a:=105) (b:=105) (joinSmall (lo:=12621) (a:=52) (b:=53) sp12621 sp12673) (joinSmall (lo:=12726) (a:=52) (b:=53) sp12726 sp12778)) (joinSmall (lo:=12831) (a:=105) (b:=106) (joinSmall (lo:=12831) (a:=52) (b:=53) sp12831 sp12883) (joinSmall (lo:=12936) (a:=53) (b:=53) sp12936 sp12989))) (joinSmall (lo:=13042) (a:=210) (b:=211) (joinSmall (lo:=13042) (a:=105) (b:=105) (joinSmall (lo:=13042) (a:=52) (b:=53) sp13042 sp13094) (joinSmall (lo:=13147) (a:=52) (b:=53) sp13147 sp13199)) (joinSmall (lo:=13252) (a:=105) (b:=106) (joinSmall (lo:=13252) (a:=52) (b:=53) sp13252 sp13304) (joinSmall (lo:=13357) (a:=53) (b:=53) sp13357 sp13410)))))))) (joinSmall (lo:=13463) (a:=6731) (b:=6732) (joinSmall (lo:=13463) (a:=3365) (b:=3366) (joinSmall (lo:=13463) (a:=1682) (b:=1683) (joinSmall (lo:=13463) (a:=841) (b:=841) (joinSmall (lo:=13463) (a:=420) (b:=421) (joinSmall (lo:=13463) (a:=210) (b:=210) (joinSmall (lo:=13463) (a:=105) (b:=105) (joinSmall (lo:=13463) (a:=52) (b:=53) sp13463 sp13515) (joinSmall (lo:=13568) (a:=52) (b:=53) sp13568 sp13620)) (joinSmall (lo:=13673) (a:=105) (b:=105) (joinSmall (lo:=13673) (a:=52) (b:=53) sp13673 sp13725) (joinSmall (lo:=13778) (a:=52) (b:=53) sp13778 sp13830))) (joinSmall (lo:=13883) (a:=210) (b:=211) (joinSmall (lo:=13883) (a:=105) (b:=105) (joinSmall (lo:=13883) (a:=52) (b:=53) sp13883 sp13935) (joinSmall (lo:=13988) (a:=52) (b:=53) sp13988 sp14040)) (joinSmall (lo:=14093) (a:=105) (b:=106) (joinSmall (lo:=14093) (a:=52) (b:=53) sp14093 sp14145) (joinSmall (lo:=14198) (a:=53) (b:=53) sp14198 sp14251)))) (joinSmall (lo:=14304) (a:=420) (b:=421) (joinSmall (lo:=14304) (a:=210) (b:=210) (joinSmall (lo:=14304) (a:=105) (b:=105) (joinSmall (lo:=14304) (a:=52) (b:=53) sp14304 sp14356) (joinSmall (lo:=14409) (a:=52) (b:=53) sp14409 sp14461)) (joinSmall (lo:=14514) (a:=105) (b:=105) (joinSmall (lo:=14514) (a:=52) (b:=53) sp14514 sp14566) (joinSmall (lo:=14619) (a:=52) (b:=53) sp14619 sp14671))) (joinSmall (lo:=14724) (a:=210) (b:=211) (joinSmall (lo:=14724) (a:=105) (b:=105) (joinSmall (lo:=14724) (a:=52) (b:=53) sp14724 sp14776) (joinSmall (lo:=14829) (a:=52) (b:=53) sp14829 sp14881)) (joinSmall (lo:=14934) (a:=105) (b:=106) (joinSmall (lo:=14934) (a:=52) (b:=53) sp14934 sp14986) (joinSmall (lo:=15039) (a:=53) (b:=53) sp15039 sp15092))))) (joinSmall (lo:=15145) (a:=841) (b:=842) (joinSmall (lo:=15145) (a:=420) (b:=421) (joinSmall (lo:=15145) (a:=210) (b:=210) (joinSmall (lo:=15145) (a:=105) (b:=105) (joinSmall (lo:=15145) (a:=52) (b:=53) sp15145 sp15197) (joinSmall (lo:=15250) (a:=52) (b:=53) sp15250 sp15302)) (joinSmall (lo:=15355) (a:=105) (b:=105) (joinSmall (lo:=15355) (a:=52) (b:=53) sp15355 sp15407) (joinSmall (lo:=15460) (a:=52) (b:=53) sp15460 sp15512))) (joinSmall (lo:=15565) (a:=210) (b:=211) (joinSmall (lo:=15565) (a:=105) (b:=105) (joinSmall (lo:=15565) (a:=52) (b:=53) sp15565 sp15617) (joinSmall (lo:=15670) (a:=52) (b:=53) sp15670 sp15722)) (joinSmall (lo:=15775) (a:=105) (b:=106) (joinSmall (lo:=15775) (a:=52) (b:=53) sp15775 sp15827) (joinSmall (lo:=15880) (a:=53) (b:=53) sp15880 sp15933)))) (joinSmall (lo:=15986) (a:=421) (b:=421) (joinSmall (lo:=15986) (a:=210) (b:=211) (joinSmall (lo:=15986) (a:=105) (b:=105) (joinSmall (lo:=15986) (a:=52) (b:=53) sp15986 sp16038) (joinSmall (lo:=16091) (a:=52) (b:=53) sp16091 sp16143)) (joinSmall (lo:=16196) (a:=105) (b:=106) (joinSmall (lo:=16196) (a:=52) (b:=53) sp16196 sp16248) (joinSmall (lo:=16301) (a:=53) (b:=53) sp16301 sp16354))) (joinSmall (lo:=16407) (a:=210) (b:=211) (joinSmall (lo:=16407) (a:=105) (b:=105) (joinSmall (lo:=16407) (a:=52) (b:=53) sp16407 sp16459) (joinSmall (lo:=16512) (a:=52) (b:=53) sp16512 sp16564)) (joinSmall (lo:=16617) (a:=105) (b:=106) (joinSmall (lo:=16617) (a:=52) (b:=53) sp16617 sp16669) (joinSmall (lo:=16722) (a:=53) (b:=53) sp16722 sp16775)))))) (joinSmall (lo:=16828) (a:=1683) (b:=1683) (joinSmall (lo:=16828) (a:=841) (b:=842) (joinSmall (lo:=16828) (a:=420) (b:=421) (joinSmall (lo:=16828) (a:=210) (b:=210) (joinSmall (lo:=16828) (a:=105) (b:=105) (joinSmall (lo:=16828) (a:=52) (b:=53) sp16828 sp16880) (joinSmall (lo:=16933) (a:=52) (b:=53) sp16933 sp16985)) (joinSmall (lo:=17038) (a:=105) (b:=105) (joinSmall (lo:=17038) (a:=52) (b:=53) sp17038 sp17090) (joinSmall (lo:=17143) (a:=52) (b:=53) sp17143 sp17195))) (joinSmall (lo:=17248) (a:=210) (b:=211) (joinSmall (lo:=17248) (a:=105) (b:=105) (joinSmall (lo:=17248) (a:=52) (b:=53) sp17248 sp17300) (joinSmall (lo:=17353) (a:=52) (b:=53) sp17353 sp17405)) (joinSmall (lo:=17458) (a:=105) (b:=106) (joinSmall (lo:=17458) (a:=52) (b:=53) sp17458 sp17510) (joinSmall (lo:=17563) (a:=53) (b:=53) sp17563 sp17616)))) (joinSmall (lo:=17669) (a:=421) (b:=421) (joinSmall (lo:=17669) (a:=210) (b:=211) (joinSmall (lo:=17669) (a:=105) (b:=105) (joinSmall (lo:=17669) (a:=52) (b:=53) sp17669 sp17721) (joinSmall (lo:=17774) (a:=52) (b:=53) sp17774 sp17826)) (joinSmall (lo:=17879) (a:=105) (b:=106) (joinSmall (lo:=17879) (a:=52) (b:=53) sp17879 sp17931) (joinSmall (lo:=17984) (a:=53) (b:=53) sp17984 sp18037))) (joinSmall (lo:=18090) (a:=210) (b:=211) (joinSmall (lo:=18090) (a:=105) (b:=105) (joinSmall (lo:=18090) (a:=52) (b:=53) sp18090 sp18142) (joinSmall (lo:=18195) (a:=52) (b:=53) sp18195 sp18247)) (joinSmall (lo:=18300) (a:=105) (b:=106) (joinSmall (lo:=18300) (a:=52) (b:=53) sp18300 sp18352) (joinSmall (lo:=18405) (a:=53) (b:=53) sp18405 sp18458))))) (joinSmall (lo:=18511) (a:=841) (b:=842) (joinSmall (lo:=18511) (a:=420) (b:=421) (joinSmall (lo:=18511) (a:=210) (b:=210) (joinSmall (lo:=18511) (a:=105) (b:=105) (joinSmall (lo:=18511) (a:=52) (b:=53) sp18511 sp18563) (joinSmall (lo:=18616) (a:=52) (b:=53) sp18616 sp18668)) (joinSmall (lo:=18721) (a:=105) (b:=105) (joinSmall (lo:=18721) (a:=52) (b:=53) sp18721 sp18773) (joinSmall (lo:=18826) (a:=52) (b:=53) sp18826 sp18878))) (joinSmall (lo:=18931) (a:=210) (b:=211) (joinSmall (lo:=18931) (a:=105) (b:=105) (joinSmall (lo:=18931) (a:=52) (b:=53) sp18931 sp18983) (joinSmall (lo:=19036) (a:=52) (b:=53) sp19036 sp19088)) (joinSmall (lo:=19141) (a:=105) (b:=106) (joinSmall (lo:=19141) (a:=52) (b:=53) sp19141 sp19193) (joinSmall (lo:=19246) (a:=53) (b:=53) sp19246 sp19299)))) (joinSmall (lo:=19352) (a:=421) (b:=421) (joinSmall (lo:=19352) (a:=210) (b:=211) (joinSmall (lo:=19352) (a:=105) (b:=105) (joinSmall (lo:=19352) (a:=52) (b:=53) sp19352 sp19404) (joinSmall (lo:=19457) (a:=52) (b:=53) sp19457 sp19509)) (joinSmall (lo:=19562) (a:=105) (b:=106) (joinSmall (lo:=19562) (a:=52) (b:=53) sp19562 sp19614) (joinSmall (lo:=19667) (a:=53) (b:=53) sp19667 sp19720))) (joinSmall (lo:=19773) (a:=210) (b:=211) (joinSmall (lo:=19773) (a:=105) (b:=105) (joinSmall (lo:=19773) (a:=52) (b:=53) sp19773 sp19825) (joinSmall (lo:=19878) (a:=52) (b:=53) sp19878 sp19930)) (joinSmall (lo:=19983) (a:=105) (b:=106) (joinSmall (lo:=19983) (a:=52) (b:=53) sp19983 sp20035) (joinSmall (lo:=20088) (a:=53) (b:=53) sp20088 sp20141))))))) (joinSmall (lo:=20194) (a:=3366) (b:=3366) (joinSmall (lo:=20194) (a:=1683) (b:=1683) (joinSmall (lo:=20194) (a:=841) (b:=842) (joinSmall (lo:=20194) (a:=420) (b:=421) (joinSmall (lo:=20194) (a:=210) (b:=210) (joinSmall (lo:=20194) (a:=105) (b:=105) (joinSmall (lo:=20194) (a:=52) (b:=53) sp20194 sp20246) (joinSmall (lo:=20299) (a:=52) (b:=53) sp20299 sp20351)) (joinSmall (lo:=20404) (a:=105) (b:=105) (joinSmall (lo:=20404) (a:=52) (b:=53) sp20404 sp20456) (joinSmall (lo:=20509) (a:=52) (b:=53) sp20509 sp20561))) (joinSmall (lo:=20614) (a:=210) (b:=211) (joinSmall (lo:=20614) (a:=105) (b:=105) (joinSmall (lo:=20614) (a:=52) (b:=53) sp20614 sp20666) (joinSmall (lo:=20719) (a:=52) (b:=53) sp20719 sp20771)) (joinSmall (lo:=20824) (a:=105) (b:=106) (joinSmall (lo:=20824) (a:=52) (b:=53) sp20824 sp20876) (joinSmall (lo:=20929) (a:=53) (b:=53) sp20929 sp20982)))) (joinSmall (lo:=21035) (a:=421) (b:=421) (joinSmall (lo:=21035) (a:=210) (b:=211) (joinSmall (lo:=21035) (a:=105) (b:=105) (joinSmall (lo:=21035) (a:=52) (b:=53) sp21035 sp21087) (joinSmall (lo:=21140) (a:=52) (b:=53) sp21140 sp21192)) (joinSmall (lo:=21245) (a:=105) (b:=106) (joinSmall (lo:=21245) (a:=52) (b:=53) sp21245 sp21297) (joinSmall (lo:=21350) (a:=53) (b:=53) sp21350 sp21403))) (joinSmall (lo:=21456) (a:=210) (b:=211) (joinSmall (lo:=21456) (a:=105) (b:=105) (joinSmall (lo:=21456) (a:=52) (b:=53) sp21456 sp21508) (joinSmall (lo:=21561) (a:=52) (b:=53) sp21561 sp21613)) (joinSmall (lo:=21666) (a:=105) (b:=106) (joinSmall (lo:=21666) (a:=52) (b:=53) sp21666 sp21718) (joinSmall (lo:=21771) (a:=53) (b:=53) sp21771 sp21824))))) (joinSmall (lo:=21877) (a:=841) (b:=842) (joinSmall (lo:=21877) (a:=420) (b:=421) (joinSmall (lo:=21877) (a:=210) (b:=210) (joinSmall (lo:=21877) (a:=105) (b:=105) (joinSmall (lo:=21877) (a:=52) (b:=53) sp21877 sp21929) (joinSmall (lo:=21982) (a:=52) (b:=53) sp21982 sp22034)) (joinSmall (lo:=22087) (a:=105) (b:=105) (joinSmall (lo:=22087) (a:=52) (b:=53) sp22087 sp22139) (joinSmall (lo:=22192) (a:=52) (b:=53) sp22192 sp22244))) (joinSmall (lo:=22297) (a:=210) (b:=211) (joinSmall (lo:=22297) (a:=105) (b:=105) (joinSmall (lo:=22297) (a:=52) (b:=53) sp22297 sp22349) (joinSmall (lo:=22402) (a:=52) (b:=53) sp22402 sp22454)) (joinSmall (lo:=22507) (a:=105) (b:=106) (joinSmall (lo:=22507) (a:=52) (b:=53) sp22507 sp22559) (joinSmall (lo:=22612) (a:=53) (b:=53) sp22612 sp22665)))) (joinSmall (lo:=22718) (a:=421) (b:=421) (joinSmall (lo:=22718) (a:=210) (b:=211) (joinSmall (lo:=22718) (a:=105) (b:=105) (joinSmall (lo:=22718) (a:=52) (b:=53) sp22718 sp22770) (joinSmall (lo:=22823) (a:=52) (b:=53) sp22823 sp22875)) (joinSmall (lo:=22928) (a:=105) (b:=106) (joinSmall (lo:=22928) (a:=52) (b:=53) sp22928 sp22980) (joinSmall (lo:=23033) (a:=53) (b:=53) sp23033 sp23086))) (joinSmall (lo:=23139) (a:=210) (b:=211) (joinSmall (lo:=23139) (a:=105) (b:=105) (joinSmall (lo:=23139) (a:=52) (b:=53) sp23139 sp23191) (joinSmall (lo:=23244) (a:=52) (b:=53) sp23244 sp23296)) (joinSmall (lo:=23349) (a:=105) (b:=106) (joinSmall (lo:=23349) (a:=52) (b:=53) sp23349 sp23401) (joinSmall (lo:=23454) (a:=53) (b:=53) sp23454 sp23507)))))) (joinSmall (lo:=23560) (a:=1683) (b:=1683) (joinSmall (lo:=23560) (a:=841) (b:=842) (joinSmall (lo:=23560) (a:=420) (b:=421) (joinSmall (lo:=23560) (a:=210) (b:=210) (joinSmall (lo:=23560) (a:=105) (b:=105) (joinSmall (lo:=23560) (a:=52) (b:=53) sp23560 sp23612) (joinSmall (lo:=23665) (a:=52) (b:=53) sp23665 sp23717)) (joinSmall (lo:=23770) (a:=105) (b:=105) (joinSmall (lo:=23770) (a:=52) (b:=53) sp23770 sp23822) (joinSmall (lo:=23875) (a:=52) (b:=53) sp23875 sp23927))) (joinSmall (lo:=23980) (a:=210) (b:=211) (joinSmall (lo:=23980) (a:=105) (b:=105) (joinSmall (lo:=23980) (a:=52) (b:=53) sp23980 sp24032) (joinSmall (lo:=24085) (a:=52) (b:=53) sp24085 sp24137)) (joinSmall (lo:=24190) (a:=105) (b:=106) (joinSmall (lo:=24190) (a:=52) (b:=53) sp24190 sp24242) (joinSmall (lo:=24295) (a:=53) (b:=53) sp24295 sp24348)))) (joinSmall (lo:=24401) (a:=421) (b:=421) (joinSmall (lo:=24401) (a:=210) (b:=211) (joinSmall (lo:=24401) (a:=105) (b:=105) (joinSmall (lo:=24401) (a:=52) (b:=53) sp24401 sp24453) (joinSmall (lo:=24506) (a:=52) (b:=53) sp24506 sp24558)) (joinSmall (lo:=24611) (a:=105) (b:=106) (joinSmall (lo:=24611) (a:=52) (b:=53) sp24611 sp24663) (joinSmall (lo:=24716) (a:=53) (b:=53) sp24716 sp24769))) (joinSmall (lo:=24822) (a:=210) (b:=211) (joinSmall (lo:=24822) (a:=105) (b:=105) (joinSmall (lo:=24822) (a:=52) (b:=53) sp24822 sp24874) (joinSmall (lo:=24927) (a:=52) (b:=53) sp24927 sp24979)) (joinSmall (lo:=25032) (a:=105) (b:=106) (joinSmall (lo:=25032) (a:=52) (b:=53) sp25032 sp25084) (joinSmall (lo:=25137) (a:=53) (b:=53) sp25137 sp25190))))) (joinSmall (lo:=25243) (a:=841) (b:=842) (joinSmall (lo:=25243) (a:=420) (b:=421) (joinSmall (lo:=25243) (a:=210) (b:=210) (joinSmall (lo:=25243) (a:=105) (b:=105) (joinSmall (lo:=25243) (a:=52) (b:=53) sp25243 sp25295) (joinSmall (lo:=25348) (a:=52) (b:=53) sp25348 sp25400)) (joinSmall (lo:=25453) (a:=105) (b:=105) (joinSmall (lo:=25453) (a:=52) (b:=53) sp25453 sp25505) (joinSmall (lo:=25558) (a:=52) (b:=53) sp25558 sp25610))) (joinSmall (lo:=25663) (a:=210) (b:=211) (joinSmall (lo:=25663) (a:=105) (b:=105) (joinSmall (lo:=25663) (a:=52) (b:=53) sp25663 sp25715) (joinSmall (lo:=25768) (a:=52) (b:=53) sp25768 sp25820)) (joinSmall (lo:=25873) (a:=105) (b:=106) (joinSmall (lo:=25873) (a:=52) (b:=53) sp25873 sp25925) (joinSmall (lo:=25978) (a:=53) (b:=53) sp25978 sp26031)))) (joinSmall (lo:=26084) (a:=421) (b:=421) (joinSmall (lo:=26084) (a:=210) (b:=211) (joinSmall (lo:=26084) (a:=105) (b:=105) (joinSmall (lo:=26084) (a:=52) (b:=53) sp26084 sp26136) (joinSmall (lo:=26189) (a:=52) (b:=53) sp26189 sp26241)) (joinSmall (lo:=26294) (a:=105) (b:=106) (joinSmall (lo:=26294) (a:=52) (b:=53) sp26294 sp26346) (joinSmall (lo:=26399) (a:=53) (b:=53) sp26399 sp26452))) (joinSmall (lo:=26505) (a:=210) (b:=211) (joinSmall (lo:=26505) (a:=105) (b:=105) (joinSmall (lo:=26505) (a:=52) (b:=53) sp26505 sp26557) (joinSmall (lo:=26610) (a:=52) (b:=53) sp26610 sp26662)) (joinSmall (lo:=26715) (a:=105) (b:=106) (joinSmall (lo:=26715) (a:=52) (b:=53) sp26715 sp26767) (joinSmall (lo:=26820) (a:=53) (b:=53) sp26820 sp26873)))))))))
  have good : (List.range 26926).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 725000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 26925 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 26925 := by
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


private def packet (i : ℕ) : ℕ := (if i < 184 then (if i < 92 then (if i < 46 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 8 then (if i < 6 then 0 else (if i < 7 then 0 else 0)) else (if i < 9 then 0 else (if i < 10 then 0 else 0)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0 else (if i < 13 then 0 else 0)) else (if i < 15 then 0 else (if i < 16 then 0 else 0))) else (if i < 20 then (if i < 18 then 0 else (if i < 19 then 0 else 0)) else (if i < 21 then 0 else (if i < 22 then 0 else 0))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else (if i < 27 then 0 else 0))) else (if i < 31 then (if i < 29 then 0 else (if i < 30 then 0 else 0)) else (if i < 32 then 0 else (if i < 33 then 0 else 0)))) else (if i < 40 then (if i < 37 then (if i < 35 then 0 else (if i < 36 then 0 else 0)) else (if i < 38 then 0 else (if i < 39 then 0 else 0))) else (if i < 43 then (if i < 41 then 0 else (if i < 42 then 0 else 0)) else (if i < 44 then 0 else (if i < 45 then 0 else 0)))))) else (if i < 69 then (if i < 57 then (if i < 51 then (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else (if i < 50 then 0 else 0))) else (if i < 54 then (if i < 52 then 0 else (if i < 53 then 0 else 0)) else (if i < 55 then 0 else (if i < 56 then 0 else 0)))) else (if i < 63 then (if i < 60 then (if i < 58 then 0 else (if i < 59 then 0 else 0)) else (if i < 61 then 0 else (if i < 62 then 0 else 0))) else (if i < 66 then (if i < 64 then 0 else (if i < 65 then 0 else 0)) else (if i < 67 then 0 else (if i < 68 then 0 else 0))))) else (if i < 80 then (if i < 74 then (if i < 71 then (if i < 70 then 0 else 0) else (if i < 72 then 0 else (if i < 73 then 0 else 0))) else (if i < 77 then (if i < 75 then 0 else (if i < 76 then 0 else 0)) else (if i < 78 then 0 else (if i < 79 then 0 else 0)))) else (if i < 86 then (if i < 83 then (if i < 81 then 0 else (if i < 82 then 0 else 0)) else (if i < 84 then 0 else (if i < 85 then 0 else 0))) else (if i < 89 then (if i < 87 then 0 else (if i < 88 then 0 else 0)) else (if i < 90 then 0 else (if i < 91 then 0 else 0))))))) else (if i < 138 then (if i < 115 then (if i < 103 then (if i < 97 then (if i < 94 then (if i < 93 then 0 else 0) else (if i < 95 then 0 else (if i < 96 then 0 else 0))) else (if i < 100 then (if i < 98 then 0 else (if i < 99 then 0 else 0)) else (if i < 101 then 0 else (if i < 102 then 0 else 0)))) else (if i < 109 then (if i < 106 then (if i < 104 then 0 else (if i < 105 then 0 else 0)) else (if i < 107 then 0 else (if i < 108 then 0 else 0))) else (if i < 112 then (if i < 110 then 0 else (if i < 111 then 0 else 0)) else (if i < 113 then 0 else (if i < 114 then 0 else 0))))) else (if i < 126 then (if i < 120 then (if i < 117 then (if i < 116 then 0 else 0) else (if i < 118 then 0 else (if i < 119 then 0 else 0))) else (if i < 123 then (if i < 121 then 0 else (if i < 122 then 0 else 0)) else (if i < 124 then 0 else (if i < 125 then 0 else 0)))) else (if i < 132 then (if i < 129 then (if i < 127 then 0 else (if i < 128 then 0 else 0)) else (if i < 130 then 0 else (if i < 131 then 0 else 0))) else (if i < 135 then (if i < 133 then 0 else (if i < 134 then 0 else 0)) else (if i < 136 then 0 else (if i < 137 then 0 else 0)))))) else (if i < 161 then (if i < 149 then (if i < 143 then (if i < 140 then (if i < 139 then 0 else 0) else (if i < 141 then 0 else (if i < 142 then 0 else 0))) else (if i < 146 then (if i < 144 then 0 else (if i < 145 then 0 else 0)) else (if i < 147 then 0 else (if i < 148 then 0 else 0)))) else (if i < 155 then (if i < 152 then (if i < 150 then 0 else (if i < 151 then 0 else 0)) else (if i < 153 then 0 else (if i < 154 then 0 else 0))) else (if i < 158 then (if i < 156 then 0 else (if i < 157 then 0 else 0)) else (if i < 159 then 0 else (if i < 160 then 0 else 0))))) else (if i < 172 then (if i < 166 then (if i < 163 then (if i < 162 then 0 else 0) else (if i < 164 then 0 else (if i < 165 then 0 else 0))) else (if i < 169 then (if i < 167 then 0 else (if i < 168 then 0 else 0)) else (if i < 170 then 0 else (if i < 171 then 0 else 0)))) else (if i < 178 then (if i < 175 then (if i < 173 then 0 else (if i < 174 then 0 else 0)) else (if i < 176 then 0 else (if i < 177 then 0 else 0))) else (if i < 181 then (if i < 179 then 0 else (if i < 180 then 0 else 0)) else (if i < 182 then 0 else (if i < 183 then 0 else 0)))))))) else (if i < 276 then (if i < 230 then (if i < 207 then (if i < 195 then (if i < 189 then (if i < 186 then (if i < 185 then 0 else 0) else (if i < 187 then 0 else (if i < 188 then 0 else 0))) else (if i < 192 then (if i < 190 then 0 else (if i < 191 then 0 else 0)) else (if i < 193 then 0 else (if i < 194 then 0 else 0)))) else (if i < 201 then (if i < 198 then (if i < 196 then 0 else (if i < 197 then 0 else 0)) else (if i < 199 then 0 else (if i < 200 then 0 else 0))) else (if i < 204 then (if i < 202 then 0 else (if i < 203 then 0 else 0)) else (if i < 205 then 0 else (if i < 206 then 0 else 0))))) else (if i < 218 then (if i < 212 then (if i < 209 then (if i < 208 then 0 else 0) else (if i < 210 then 0 else (if i < 211 then 0 else 0))) else (if i < 215 then (if i < 213 then 0 else (if i < 214 then 0 else 0)) else (if i < 216 then 0 else (if i < 217 then 0 else 0)))) else (if i < 224 then (if i < 221 then (if i < 219 then 0 else (if i < 220 then 0 else 0)) else (if i < 222 then 0 else (if i < 223 then 0 else 0))) else (if i < 227 then (if i < 225 then 0 else (if i < 226 then 0 else 0)) else (if i < 228 then 0 else (if i < 229 then 0 else 0)))))) else (if i < 253 then (if i < 241 then (if i < 235 then (if i < 232 then (if i < 231 then 0 else 0) else (if i < 233 then 0 else (if i < 234 then 0 else 0))) else (if i < 238 then (if i < 236 then 0 else (if i < 237 then 0 else 0)) else (if i < 239 then 0 else (if i < 240 then 0 else 0)))) else (if i < 247 then (if i < 244 then (if i < 242 then 0 else (if i < 243 then 0 else 0)) else (if i < 245 then 0 else (if i < 246 then 0 else 0))) else (if i < 250 then (if i < 248 then 0 else (if i < 249 then 0 else 0)) else (if i < 251 then 0 else (if i < 252 then 0 else 0))))) else (if i < 264 then (if i < 258 then (if i < 255 then (if i < 254 then 0 else 0) else (if i < 256 then 0 else (if i < 257 then 0 else 0))) else (if i < 261 then (if i < 259 then 0 else (if i < 260 then 0 else 0)) else (if i < 262 then 0 else (if i < 263 then 0 else 0)))) else (if i < 270 then (if i < 267 then (if i < 265 then 0 else (if i < 266 then 0 else 0)) else (if i < 268 then 0 else (if i < 269 then 0 else 0))) else (if i < 273 then (if i < 271 then 0 else (if i < 272 then 0 else 0)) else (if i < 274 then 0 else (if i < 275 then 0 else 0))))))) else (if i < 322 then (if i < 299 then (if i < 287 then (if i < 281 then (if i < 278 then (if i < 277 then 0 else 0) else (if i < 279 then 0 else (if i < 280 then 0 else 0))) else (if i < 284 then (if i < 282 then 0 else (if i < 283 then 0 else 0)) else (if i < 285 then 0 else (if i < 286 then 0 else 0)))) else (if i < 293 then (if i < 290 then (if i < 288 then 0 else (if i < 289 then 0 else 0)) else (if i < 291 then 0 else (if i < 292 then 0 else 0))) else (if i < 296 then (if i < 294 then 0 else (if i < 295 then 0 else 0)) else (if i < 297 then 0 else (if i < 298 then 0 else 0))))) else (if i < 310 then (if i < 304 then (if i < 301 then (if i < 300 then 0 else 0) else (if i < 302 then 0 else (if i < 303 then 0 else 0))) else (if i < 307 then (if i < 305 then 0 else (if i < 306 then 0 else 0)) else (if i < 308 then 0 else (if i < 309 then 0 else 0)))) else (if i < 316 then (if i < 313 then (if i < 311 then 0 else (if i < 312 then 0 else 0)) else (if i < 314 then 0 else (if i < 315 then 0 else 0))) else (if i < 319 then (if i < 317 then 0 else (if i < 318 then 0 else 0)) else (if i < 320 then 0 else (if i < 321 then 0 else 0)))))) else (if i < 345 then (if i < 333 then (if i < 327 then (if i < 324 then (if i < 323 then 0 else 0) else (if i < 325 then 0 else (if i < 326 then 0 else 0))) else (if i < 330 then (if i < 328 then 0 else (if i < 329 then 0 else 0)) else (if i < 331 then 0 else (if i < 332 then 0 else 0)))) else (if i < 339 then (if i < 336 then (if i < 334 then 0 else (if i < 335 then 0 else 0)) else (if i < 337 then 0 else (if i < 338 then 0 else 0))) else (if i < 342 then (if i < 340 then 0 else (if i < 341 then 0 else 0)) else (if i < 343 then 0 else (if i < 344 then 0 else 0))))) else (if i < 357 then (if i < 351 then (if i < 348 then (if i < 346 then 0 else (if i < 347 then 0 else 0)) else (if i < 349 then 0 else (if i < 350 then 0 else 0))) else (if i < 354 then (if i < 352 then 0 else (if i < 353 then 0 else 0)) else (if i < 355 then 0 else (if i < 356 then 0x22918992c0147498a4601fd0e6466a2df14308b038816a08583000b8000022912c92b514589624531fb0e686862d313e88a83ae17808902c40bc00002290cde2c294709784652048ed46b22fc14e09083c418508d83040c6000022907132bb94449764501fb8e6067c2de13d885037416408482e00b8000022900f62dc1558a0649c21c0f5c6f231115489003be18209283100be0000228faf32d415249bc4802128eec6b02f214c08f039c17408a02e40ac0000228f5452a813e09384401f50e0c6522c8133083035814a07d82a40b00000228ef562cd94bc99c4631ff0e806942e314408ac39a16e08902ec0b80000228e9682ca14ec99046a2068eac67a2e113d089c3a017408f02e80ba0000228e3702d214fc9b847920d0eec6b630015388f03ac17a092030c0b40000228dd902c514c09804621fd8e6867e2de13f887c37a15808902d00aa0000228d7c52b914749704621ff8e9068c2ea14388983aa17708e02dc0c20000228d1942e995b0a044a221b0f546e030b151091c3aa17909083000d00000228cbe22ad14109464421fb0e6467a2df13b886439016908482d80920000228c61e2b8943c95a4581ff0e7c6802d7140888439e16c08202d00b80000228c0692ab93ec9204381ef8dfc6522c213e887839417508c83240ba0000228ba7b2c594d89964652088ee86b62f814d89103d018109102e00b20000228b4962c0948c99c4702088ee46a42f214788e03b818008d03000ca0000228aea42c994c09b247b20c0edc6ae2fc14d89143ce18209302f00b80000228a8c22c114c499846d2040ebc6aa2f715208f03aa17208c02e00c20000228a2e72bf949c9864692030e8c69c2f114488c43a617808e03100cc00002289cf62cb14ac98a4722060e806962f114b88e83ba18408d83040ba0000228971a2c394b898846b2088ed86c02f114888b83a417608a02d80a40000228912d2c014b89ac4732088eb86942fa14788c438c16708a82dc0be00002288b552ba943096a45a2018e9c6a22ea14a08ec3b417d08a82e80b60000228856c2c514a09a647d20c0ec06b82ff14f88f43b617a08e03180ce00002287f772ce14ec9bc47720a8efc6b430815609103da18f09503100c8000022879872c294949a647420a0ee06bc2f614b88e03c218b094030c0be000022873ad2c0947c98a46b1fe8e886902ed14908a43a217c09203080ca00002286d9d2d715149cc4812110f106ca302154092c3ca18409103080b8000022867a42c794d49c44812120f146d230515609603ec19109583440d8000022861b42c894d899e4622088eb069c2ef14608dc39a17708b82d40b400002285bf42ac13fc93444f1ff8ea06a22fb15009303d418809603200b8000022856122bd949c99046c20c0f006b82f514b08c43b617308c02c00c0000022850592ad941c94044a1f80e446742dc14088bc3b017e08e02dc0aa00002284a9c2b0140895244b1fd8e5c66c2d5139086035e16308782e00a2000022844c22be14789844612000e606922e3146889c39017708482dc0c000002283ecd2cd14e89b64742120f446ea31515989483d818609403140b0000022838df2c694e89b647a20d0ed46962f314d08cc3ba17f09202f40ca000022833102b8946495a44f1f48e306562c713a889038e16a084829c0b600002282d032d615349ce4862148f546d830015609103ca18b09483180b8000022826ef2db95349d849121b0f486de30315389143c017d08b02e00b00000228210a2c594c89a64742088ecc6a82fa15708fc3cc18308e83140d000002281afe2d495309ec48f2198f3c6e631c15b09583e818f09103200d0000022815272be946896a4531fb8e5c67c2e913f087c38216408182a00b800002280f422be948899a4692050ed06a62f8152891c3bc17e08a82c40b2000022809682b8143897a4571fc8e3c6622d913c884837216c08482c80b0000022803822c294889844662088eec6b62f915008fc3a816d09083040b80000227fd992cc14cc9ac47c20d0ed86b22f014a089c38216a08482c00ba0000227f7b42c594b899c46b2080ee06b830215089143b417f08882d80bc0000227f1d92c3949c98045e1f80e4c68c2ea14808c03b017f08f82f40c20000227ec012bb94889964631fe0e8c67a2e714688a839217809382e80b40000227e6372b6142095a45b2018e5c6822e714608a439a17108a82e00a20000227e06e2b894709724592050ea069a2ef14588ac3a617808e02e00ac0000227da862ca94f09c04842158f3c6dc31315a899440c19e09d835c0d40000227d4b32c014709804682010e9c6942ef150890c3c017308b82c00a20000227ceb52ce94d09a246f2088eb06a62ee14788c03a217308e03080be0000227c91a29a93749084281e88dd863c2ce136886438215c08082b40b00000227c31c2ce150c9c84892170f286e230c157093c3d618208f83100ba0000227bd422c814f09ac46f2098ed068c2f614d88f03b218409283640d80000227b7732b9146c9724561f90e386602d2135883037015d08182c00b00000227b1912b9943c97645c1fe0eb46922f114788c038616c08202a00bc0000227ab982cc95049e04902138f306ca30014b89003c019409803380e00000227a5b72c2948c97c46b2098ebc6902f114888d43b818708d82f80ce000 else 0x22a92172c394c898e46620b0f086e030e153092c3d819109582fc0cc000022a8c102d915089c647d20c8ee86b42fc15008fc3ba18309303200c8000022a862d2c214c89aa47e2120eec6c030014e88e03aa17708b02e40b2000022a804f2be947497c4602008ea06902e314608e43b818408c02f40b0000022a7a8a2b3142095e44e1f58e3065a2d613a88a439617308c03040be000022a748f2cc14e89b44862130f286e030c15689343ba17908e82f40c4000022a6e972cb14e89a647220c8f006ae30115189103c018508d834c0ce000022a68bd2c1147c99a4732050ec46a22ee14808a438a17208e82f00a6000022a62dd2c3948898a4682040e946982e914408bc39817109303080b6000022a5ce52d015149d648f2140ee46b42f614908f03b217c08e03000c0000022a57042c5149498845d2008e6c6762d613c888038016b082829c0a6000022a51042c814ec9c247b20b0ee46be30615209003be18309583380ce000022a4b1c2c314b099446a2030eb469c2ec14408b43b017608f831c0be000022a455e2ad94109584501fa0e846702d6140088437816e08e82dc0b6000022a3f922b9143c96e45c2028ecc6902e914a88a83b017108682dc0b2000022a398b2d415049c248a2128f546f631715f09403f219109303240da000022a33a82c794d09924792108f086c030314f89443ca18609683680ca000022a2dc12c894d89a84702098ee86a02f314908bc3c417c08f82dc0ba000022a27e02c3949499e4672050e986882ed14d08d83be18508b82e40b8000022a21db2cd950c9c84872180f306e430d15509183d418608e82a80aa000022a1be42cb94f49d64872130f0c6d830315309303dc18909583180d2000022a15e42d6951c9c048020f0f006a22f014b88e83ae17f09003100ce000022a10122bc14949904612000e846842e7141886439416b08d03080c6000022a0a462b393e89384431f18e406602d813a887836e15d07e027c094000022a04352d495209c04702090ee06ae2f614b08dc3a017208902e40c60000229fe632b9941c95e4481f30e246542d513e087438815e08803040c40000229f8822c594c09b847420d8efc6d231115389283d218e09a033c0d40000229f2732d415389da48a2160f446ee31415509183d818c09103100c00000229ec902c914d89aa47a2080ed06ac2fe15189183d619509a83700da0000229e6a32c894c09a647620a0ee869e2ed14808b03a617708b02dc0ac0000229e0ba2c694f09bc4752058eb46942ef14588c03a417408902e00d20000229dad92ba146097445f2010e686902ef143089838e16a08582ec0c00000229d4f42c194809804682020ec06942ed14a88b439416b08602b80bc0000229ceed2d295389da48c21d0f306da31315389303dc18a09503100be0000229c9162bc94709904582008e8c6862ef14988e03aa171086829c0b40000229c31d2c514bc9a647420b0eb06942ea14708c839a17e08d02ec0bc0000229bd552b1942c95e4531fe0e906842f214b88f83b817e08e82e40c00000229b77a2bf148c98c4631fb8e786962fb14a88d43c418409283080c40000229b18d2c814c09a046d20a0f186cc30214f89003c018109803540ea0000229abe52a593c493243b1f50e1c65a2d113c085436a15e08082b00a20000229a5e82d295109d647f2140edc6c830214c88d43ac17708902c80d20000229a0252ba943094a4451f38e6c6842da14388bc3a017809183080d000002299a552b9947c97245d2030eb06ae2fc153892c3d218008b82c40a2000022994802b9946c9724642060eb46a02ec14308c03a616907e82980aa00002298e692d1150c9d84912138f086b42f714b89043c0185090830c0d2000022988862bf14a098e4652050ec069a2f014708cc39617008582d40b20000229829a2c514b899847420d8eec6aa2fa14e09083cc18509303100d200002297cda2b014349564542000e746762e013b08983aa17808c82e40ce000022976f62c094949844561fc8e6467a2e914508c83a417508b02f00cc000022971082c594c89a647b2100edc6aa2f214888c43ae17408d82e40b800002296b1e2c794d89b447d20d0f0c6ba2f114e09043b217308a02e00b4000022965592b094309404351f00df864e2d914288d03a416f08e02d40b400002295f462e1957c9f649f21f0f706f031115709583ea19409283200bc000022959492cf94ec9be47920f0f186da315157893c3b817608582980aa0000229538f2ac13f895a44d1f08e206542d314088ac3ae16908582c80b800002294d9a2cc14e89c247020e0ef86a42f414e88d83b818609202fc0ba000022947ab2c494b89ac48120d8ef86ba30815209203d018509103140c2000022941db2b7944496245b1fe8e306522dd142889839817408e02e80c000002293bcf2d295489e048f2170f446d030915109043c418309303300c6000022935dc2cf95049c24812130f006c02f814f09243d218e09502f40c4000022930282ae13e494c4511fa8e6866e2d813f085438816708902e00a600002292a312ca15109ca4822108f286da30f15689583dc18a08e82d00b6000022924662bb94549584511f50e346662d613c087c38c16c08702f40c200002291e712c914d09aa4782130f106cc2fe14c88dc3ba18309182ec0d0000)))) else (if i < 363 then (if i < 360 then (if i < 358 then 0x22c0a892f21608a304b62298fb471632415b091c3dc18609383000ce000022c04c22b5944096a4652028ea86922e6141888437e15e08802c80bc000022bfeea2bf143896a4542038eac69a2e914788d439c17609303180c0000022bf9372ab94149364401f78e3c6742e4146088037e16008182cc0bc000022bf3762b093f093a43f1ee8ddc63c2c7135886438a16808e82b00be000022bed682ca94d09ac47820f8ee46a82fd15709083d218609602f80a2000022be7992b7146895c4561f98e6065c2cf13708603a417108802c40a8000022be1c42be946897e4632010e5866c2da139885c36e15d07c02940a8000022bdbf32ba141895c4512038ec06882e313e889039816a08c02f00ac000022bd6272b3942096a4632028ebc6a82fe14888ac38c16308702dc09c000022bd0292d014d89ae47320d0ed86ac30315008dc3aa18309502e40ae000022bca192d515249c04892118f1c6dc30515a89443d218909483040b8000022bc4302c514d89ae4762100f046ca30615008f43be17008c02f00c4000022bbe562bc94789904772088ed46a02fe14908c039417108982b80ac000022bb8602cf14f89c64822148f146c42fb14788f03a617a08f02d80b8000022bb2842c2149c9904702078e8468e2e9141887439217608a82f80b2000022bacb02bb14489544561fd0e7868e2ec14688a838c16d08502e40ac000022ba6c92c594889824672078e946842f214d08bc39a16808882dc0a8000022ba0f32bf148899046c20d0f046be2fd14f88f03c219309983280ca000022b9b2f2b4142c94c4491fc8e4c6802e714488a839e17408b82e00c4000022b95622b9945897a4551fb0e806902e914208b039617208b02cc0be000022b8f782ca14d09b84752060ec469c2e614708f83ac17408a02e80c0000022b89712d015149c047f20d8ef46b42f414508e03c218309382e80ce000022b83842c114cc99e4732058ea069c2ea14488a439017308b02e40b8000022b7da32c0948099646d2080ec46b02ea14588ac39816b08682dc0b6000022b77c22c114889804632020e906762eb142089c3a017108d02dc0bc000022b71d22c8148498a46b2020ea46962e814708e43b217c09183040c6000022b6c082ba145496c4561fd8e8068e2e314208bc39617208b830c0ca000022b66072c994dc9ac4661ff8e886782e714b08c83c218609403040ae000022b60532ac93e495044d1fa8e646742d614208903a417508c02f40b8000022b5a5c2d114f89c648b2130eec6d030614e08d83b817f08c02e80c4000022b54732c814c499a46e2050eb46922ed144888438615f08582cc0b6000022b4eb02b494509724642080eac6ac2ea14608d83aa17308a82f00c2000022b48ab2cc14e49ba47c2100eec6a42f714b08e039a17908c02f00ae000022b42d32c1148899647620b8edc6ae30115209083d618a09082e80c0000022b3cf72c114a89984682040eac6a62f914a88ec3bc17508982c80a4000022b37312b514249744622038e986b8303151091c3dc18a09403080bc000022b31312c714c099646a2048ea86902e914408e03b618209083180c2000022b2b792ac13e09424471fa8e606622da13e088c38615c08382b80ae000022b258e2c5149099045b1fe8e946942ea14508d43a816a08d82e80ca000022b1fcf2b493f49464521f98e606782e714388d03aa17a094031c0ca000022b19c12d215049de48b2170f506ec30f157093c3da18309903300da000022b13d82c714b89904732070ec06a22fa14a88b83a217608a02cc0b6000022b0df42c0948899646b2070eec6c22f714c08e83b018008d02ec0b8000022b07fb2ca14c49a04712070ea068c2eb14508a839c16d08a02e00b0000022b01e42db15649fe49b21c0f706f031c15509203cc18e096831c0cc000022afc392ad940093a4421f38e6066a2c8138885c39016a08582c00a4000022af6632bc94909844612058ea469c2f914a08c83b417809003300bc000022af0782c1946497045c1ff0e806942ed14808f03ae17208a82d00ac000022aea772d014d49a648220a0ef06bc2f514b88cc3b818508e82f00ba000022ae4902c494cc9aa4712070ef06b02eb14b88ec3c417a09182f40b2000022adea22c614c099a47620e8ef46cc2fb14b88fc3b817508d02e00ca000022ad8ad2c894b499046f2088eac6a02f514a08b43b017308d03000c2000022ad2d32c0946895a4562000ea067c2ea145089c38c17709103200dc000022accf52c014a497c4602000e8c68e2ed14908bc3ae18209182f80be000022ac6fd2ce95109c44822160f106c630115209043bc17708f83040be000022ac12e2b8946498045d1f88e506862e7142889039c17508802bc096000022abb4d2c3146897a46a2060ea46aa2f414988b83a017608982f40be000022ab5732c0148897245c2040e9869a2e814208a438e17708e02f80ca000022aaf512e39580a064a42258f9071632f16389803e618508d02d80c8000022aa9682c394a89824631fe0e7467e2dd13f88bc39c17b08b02d40a0000022aa38e2bd14649684561fd0e9c6962ea14988f83b417508b02dc0c6000022a9daf2c214a89984702018e5c67e2e614b88c83a817408c02e00ba000022a97f82b014189624532058ea869a2ea14508a838616708a02c80b8000 else (if i < 359 then 0x22d83fa2ca94e09ba4812148f3c6d230415288f83b417e08902d00b4000022d7e412ad93e89364481f38e4867c2d913e088037617008502d80c4000022d78862b593f493c4441f60e406482d214208883a217308802f00be000022d72902c714c099c4792100f146c631115789483cc18608e83000c4000022d6ca52c314a098e46b2040eb86a42f514f89043aa17a08c82f00ce000022d66a82ca95089b247920d8f306c22ff14d08f83d017f08b03100b0000022d60bb2cb14c899c4732078ec86aa30014d08cc3a416e08c02d40b8000022d5ad12c894cc9ae47520c8ef06a62f614b89003ba18008e83140ba000022d54c02da15709f249f21b0f806ec30f15689203e218d098831c0c2000022d4ed02c494bc99646b2008ea469e2f914b88e43be17808b82e40b6000022d48ed2be948c9a046e2018ec46b22fc14c88d03ce18409203240c8000022d42d42dc15649d84942188f106bc30015589283c418809583180bc000022d3ce72cd14e89b847920e0f386e631415a09683dc17f08f83100b8000022d370a2c0949c99e4782090e906862dd13e889c3a017308e03080b8000022d31062d4953c9ec49b21a0f5c6ec31f15c89483e219209582f40c4000022d2b522ad93ec9444421f80e6c6882e514a08b039e17508a82d80bc000022d25872b2142895244d1fb0e406602e013c887037c16808602f40d2000022d1fd62ad94189444431f80e646762de14988e83c417e08c02f00b6000022d19f62c314709824692010e7868a2de14088b039817408902f00c4000022d14262b7942096e4581fe8ea068e2ed14a08c03ae17c09182e80aa000022d0e2d2ce95049c44872130ef86c030815489143c217f08e02f40b6000022d084f2c3947497e4551fe8e846882e714788cc3b217808c02f40c6000022d02632c694bc9b447a2140f1c6ae2f914c88ec3b017309082d40b6000022cfc852c2147497c4632018e8c6902ed14988cc3be17e08e82e80c8000022cf6a82b9143495a4441fd8e746702da13e089039c17808a82b80b0000022cf0b12c814ac9964631fe0eac6be30015389303dc18409203240b8000022ceab72cb94dc9ac4762098ebc6be30414d08c839616a08882d409e000022ce4d82bf944c9604581fb0e786822da143888c39c17508e83080be000022cdeac2eb15bca244a82220f506e231315c896c3fc19409703380ce000022cd8bf2c0147496e4592000e946922f114708b43aa16608f03100b2000022cd30e2ad140895044a1fe8e946822e914708d03a417208c830c0c4000022ccd662a613cc9344401f20e1c65a2ce13f888437a15f08302a40ae000022cc7952bb147496e4561ff8e8c6842f014a08e03a616d08602c80c0000022cc1dc2b1141096445b1f90e6467a2e814708d83a017108682e40c2000022cbc0b2bf94549784682078eec6b22f714f08f83b818408e82e00bc000022cb6202c514a89a24732078ea869c2ea14788f03c017608e83080c6000022cb05d2b5141094a4522048ea069c2f514888b03a217208b03180b6000022caa7b2c1148096a4591fd8e746822d6142889438c16f08b82d40bc000022ca4c52ab93fc9584551fc8e846882e3147889c39617308b82d40ac000022c9ede2c594a89864612078eb86a42f814f09083ce18909203240c6000022c98d92d3150c9d648f2110f006ce2fc14f89383ca191097833c0ba000022c93022b914709804632020ea869e2f815509103c018309183080c0000022c8d032cf94e09a647a20d8f106b230014988d839616a08a83000ce000022c87082d5954c9d04932188f306c230215489083b218809203200c6000022c80e12e3159ca184a421d8f5c6e630d156894c3e618c094030c0ca000022c7ac22df15809f04992198f686ee31e15f89583de19509b03140be000022c75002b4941c9424582010e9867a2e514788b03a216c08f02ec0bc000022c6f352b414389724581f78e7065a2d913e087039a17708882e40bc000022c692d2d515409d84832108f046dc31515c09283d218b09603240da000022c63722aa93d89424461f30e5c6742dd13d887439e17a08f82ec0bc000022c5d952ba945897645f2060e806862f114688e03be18409402fc0d4000022c579f2c694e89a647c20f0f046b02ee14a08f03b017708982c00b2000022c51b02c894d09c048220f0f006ca30615089183d018209103040c6000022c4bbf2c814ac9864661fe8e606782e914908cc3ac18109283100e0000022c45ce2c794c09a446f20b0ecc6982e814688a83bc17a09483480da000022c3fc62d615109b247e2128ef86b82ff15109103b818309083000c0000022c39ec2be947898e46b2098ea86a430214c08f03bc17808d82d00c2000022c34292af13fc9584481fb0e4466e2d31380838368168081829c09a000022c2e4e2b914609844652050ed86ba30014f08f03bc184090031c0d4000022c28772be946c9704602020eb469a2fb15109003c417a09002fc0bc000022c22a32ba945897e4612068eb46b2309153892c3d6186093830c0ca000022c1c922dd95709f449f21a8f486e031c15f09403e018b09783240cc000022c16962cf14ec9ba4792100ef86aa2e714788b039c16508682d80b0000022c10c62ba944097a4631fe8e9c67c2ed14088ac39a16108482a40a8000 else 0x22efcd92b6147098245b2030ed86ae2f115409203ce17a08b02c80c2000022ef6f32bf949c9804672098ed46a02ee14a88f83b6182090030c0b4000022ef1412ab93dc9384471f58e6067c2e514588c83c418008f82e40c6000022eeb562c894dc9aa47620b8edc6ac2fb14c09043a615f08102c40ae000022ee5642cd14f09904702088ec06b2301154892c3da18308e02ec0cc000022edf662cf94f49be47620a8ee069a2e2141089038e16908502bc0aa000022ed9862bc144c9704572000ea46842dd140085437216d08802ec0b4000022ed38c2d094c89d04832120f1c6ce30a153090c3c018c09382f00c6000022ecdb12bc145497e4662010ed46b22fb14c88fc3e018d09503000c0000022ec7dd2be14c09ba4802130f046bc2fe14908b438816d08b02e00b0000022ec1db2cd94e49b047520a8ec46b02f614a08fc3c216f08b02bc0b0000022ebc0c2bb146096e45e2038e806682d3137085c37e17008c03200c4000022eb6302b8944c9564551fb0e5068e2e414788d83bc17c09003140c8000022eb03f2c894d89ba48520b8eb46982ed14788c83a617808e83080c2000022eaa662bf94a097c4521fb0e5c66e2da140886437215e07f82a00b0000022ea4762c614c49a446b2050ec86a02f615208dc3c218108b82fc0c2000022e9ea72bd947c97c4672088ebc6a82e6141088838817309102e80ca000022e98e52b0943495c4511fc0e8069c2eb14788c43b018609583240d2000022e92d92d715189b24702080ed46bc30214f08f83b017c08c030c0be000022e8ce12cf15149b848220f0f0c6be30915809203da18509283240bc000022e873d2a793b49304471f08e2065a2d113a088039616b08703080d0000022e81332d215249ce48020f8f146d030815309203de18709803600e8000022e7b2a2db9568a044a02150f306cc30c14e08dc3a016908502c40b2000022e752a2d195249ec4982170f206dc30e15389083b817d08f03100c6000022e6f5e2b5942896c4592028ea06a82fa15089243d017d087829c09e000022e69592d295349f648f2178f446d830514d88e43bc17809082d40ae000022e63872b8144096444e1f68e6866a2db136884437415b08a82d80be000022e5d992c794c899a47620c8f0c6c630a15189503ea19009383200cc000022e57d72b4945c97246a2008e786a42ec14e88d03aa17308982b00b0000022e51f52c2949c98245c1f98e3c6782de14308b439817308c02f80b8000022e4c1a2bf947c96e4611fc0e8c6a62f014a88b038816708882e80c6000022e46482bc945896645b1fc0e9c6922f514888d43b818009003140ca000022e40702c294c49aa4742108f146c02fd15408d83b217708902c40ae000022e3a802c914c098e46f2030e986a02ee14a890c3d418e098833c0d4000022e34882d014c49aa4692080ed86b42f314b88cc39616c08b02d00bc000022e2e9a2c694a899247020a0ee86ae2fa14d08d43bc17508a82bc0cc000022e28ca2b5941897045a2000e7c6962e814808a439616e08d031c0bc000022e23292a093b092a43d1ea8db46182af12f883038016808782b40a6000022e1d142d395309cc48121b0f686fa31b15e89543e618e09103280da000022e173d2bc14709864612038e906742d913b088037414f07a82d40b0000022e11202d9953c9ca48d2168f406f430a158093c40019d09783380d6000022e0b3e2c0949899a47120a0ebc69c2e714488b039416908e03000d0000022e05382d215289da4822120f046ba2fc14608c03b817909203240cc000022dff722b5946496c44f1fc0e3465c2c8137085837616408682e00c2000022df9a82b014289464471f68e6067a2e0142088839816b08702dc0ba000022df3a42d014e49b24742068ea06a22f014408ac39a17608b02f80c0000022dedd62bb147898445e2000ea06942e114408ac3b217c08b02dc0b6000022de7d92cc94d499e4702068ea86862f214708a038e17409002f40b4000022de1d22d895509e64a32178f506ea31315d09583e418d098837c0e0000022ddc092b714409624541fb0ea06982e514408d03b417a09103080b4000022dd60d2c194989844682060e9c68a2ee14788e43a417c08e03040bc000022dd02b2c414709784582070edc6be30915208fc3ae18009283000b4000022dca522bc14509744622098ec86aa2fd15509283c417f09283080c0000022dc4682c314b89ac47a20f0f1c6b62fb15089003b417d09103140b8000022dbe7b2c594d49b247120c0f046b82f814f891c3cc18709603400ce000022db8db2a713d092843d1ee8e0065e2d914108c43ae17408b82d40b2000022db2e32cb14ac9aa46d2060ec869c2f014b09083ce18609003140c8000022dad0a2b5145c9684541f28e2465a2dd14508d43aa17a08682c40be000022da7232c514d89ae47620d0ee86ba2f814b08cc3a617c09183000c2000022da1392c794b49ae47b2090ea868e2e7141088838e16a08b02bc0b2000022d9b422cc94909a04662078eb86b62f214788b03ac17708a02fc0c0000022d95912ad141c9404451f70e5c6722d713d086436e16908a82c80bc000022d8fa02c194b09aa47220d8ed869e2f314c89003cc17c08e03100be000022d89e92b0142495c4552008e846962e114488d43a417608a82dc0ae000)) else (if i < 361 then 0x23076142a893d092a4381ec0dd86302c5131082436815c07d02a409c0000230705c2af13fc93443f1f38e406722d813e088038c15a08082b80b000002306a832bd94889844672070eac6a22e8144889039e16e08782c00a4000023064972c794e09a046c2038e9c6882db14188a838416f08d02f00ac00002305eb12c3148c99647320d8ecc6c230615989103d018209202f40b0000023058cb2c714d49a447b20c8ee06a22f814b08c83a817609002fc0c2000023052d42ce14f49be47b2148f246d030815209083b617e08b02fc0c000002304ced2cb94e09aa4682080ec469e2fa15088f03bc18009283180bc000023046e42d895289cc48a2118ee06b42f414f88c039c17b08b02f80ae000023041122b8944c97845f2008e846862e514188a838a16c08702ac0a000002303b2b2c294c099647720e8f006ac2fc14f09003cc17e09002f80b2000023035672b3143c95e4551f90e8867a2e014288b03a017f09203180c600002302f932c3949899c47920d0f046ba2f514688b83a617608b02cc0ba000023029aa2ce95089c847d20d8ef06b62f715108dc3b818508b82d80b2000023023972d615409ce48c2178f746ec31d15589483d218309403180ca00002301de02ad14189424451fd0e9c66a2e313f88c03a017008a82f80ca000023017bf2de9588a044a72268fa871432315e89a03e419409483100c8000023011cf2c914c49a447120b0ef06aa2fb15008dc3b617a09102fc0bc00002300be62c714b899a46b2050ebc6ae2f314788d03b017d093031c0c8000023005f52cc14d89a246e2080ea46a22e614808d038e17a08b82dc0c4000023000402aa940095044b1f88e486742dd14208803a217008b82f00b2000022ffa352d815549ec4922140f146d830d15789543c418908f83080c2000022ff4662bc944c96a4622028ea86982ea14708b83aa17808c03080dc000022fee742c894a09944671ff8e946a42fb15009083b617508982b80b8000022fe8752d194ec9a846a2038ed069e2f314a09043ba18609082fc0c0000022fe2842c694949784561fa0e2c6642d213c887037616308782cc0ae000022fdc932c694a899e46c20b8ef86ba30115409183c817f09082f40be000022fd6ba2ba947c98647220d0edc6c02f914a88c43aa17209003240ce000022fd0e22be948098e4662020e8468a2ee14908c839016d08802d80b6000022fcb292ab13c893a43c1ef8e2466a2dc13f88a039c17108c02e00c4000022fc5592c014b098c46a2048ed06a02f414b88a83b4176087029c0a0000022fbf282e295909ec49121a8f506de30815389003cc18709683400d6000022fb96f2b2140494e4431fa8e7868e2ec147089c39e17709883280c4000022fb3cd2a593f093a4401ee8e2466a2df13f887837815d08402e80b0000022fadcb2cd14f09cc4872128f1c6b82f914b88e83ae17d08d82e40ca000022fa7c62d195349c248a21d8f446c42fd14c88c83b017d09203340bc000022fa1fb2bd948c99a45e2060ebc69e2fe14a08b83a218308f03040c4000022f9c252c014489764592028eb46a82fb14c88d43ae18609402e4092000022f96622b4942894844e1f90e606882db13d087839016e08983040b0000022f90622cc14f49b24822108f286c030915509143c218909583100c8000022f8a9a2b3141c9724581ff8e746862ef14a08c438a16708382d40ae000022f84bf2c414cc9c047e2118ec86b02f414988b03ae17608d03040d6000022f7eba2d415089c848c21a8f286d830e15288f43d017f09603200c6000022f78c02cf94f49ca48b2130f1c6c830d14d88ec3b817709183200c0000022f72d22c894e89a44722088ee06cc2fd14b88cc3aa17208982e80c2000022f6cff2ba146897a4602058ec468e2ec14388a83a217508c82c40ac000022f670f2c714dc9ac4802108eec6a82f714708b039417a08c02e80bc000022f611c2cd14a498c46c20a0ebc69a2fb14688b03a816c08802b40aa000022f5b3a2ba94889844672038e7067a2e2144889c38c16708d02fc0be000022f555e2c514a498e45f2018ea86982f014808e03a017808b82dc0ba000022f4f7e2c294b09a646e2068ea468a2f514808c039416e08b02c80a4000022f497c2cd14e09bc4762100ee06b62ff14d88e83b618508d82f80c0000022f439b2c314a098c4692060eac6a42ed14508a839817508782f40c0000022f3d9d2cd14f49b247820e0f006c830414b88e43c218d09883340ce000022f37972d4952c9da48c2168f346dc30915909483ca18a09303040ac000022f31da2b013f49464411f40e4867c2e414708cc39816708482e00b4000022f2bf42c7948499247320b0ed06a82f614988dc3a017008b02f80b4000022f261d2b7945497a46b2058eb06962f014688a83a418309082e80b4000022f202d2c694b89ae47620b8f0c6be30314908f83c618009082e40d2000022f1a432c514b09aa46c2040ec06a02e714a88e43c018909503200ca000022f14762b7944496044c1fb0e6c6962e6143888038216e08582e80b2000022f0e812cf95049ca4872130f1c6c430515188ec3b418308902ac0aa000022f088c2cf15209b247c2120f006be303156091c3dc17e08b82f00be000022f02a62c714d09a24722090eb86962f614708e83a617508d83200c6000 else (if i < 362 then 0x231eea42b014389544501f80e246522cf13d887c37816e08b02dc0c00000231e8b82c794f09ba47e20d0ee46ae2f414808b439c17008f82ec0ba0000231e2c12c914dc9b64872120f186f030815089043bc17a08582e00a40000231dcd32c714a498a4682090e886882ed14508bc3ae18108f02f80c60000231d6e12c994c89aa47720e8f086d230815009243de18708e830c0c20000231d1082c1147c9804612020ec469c2ef14d08f03ba17d09083180d00000231cb432af941094044d1f58e2064e2c8138086838616108a02e00bc0000231c51d2eb15dca1e4b222b8fb470c322159896c40019f09f03580e00000231bf422bf94c49aa4742098eec6c630c15088ec39c17508d82e00b80000231b97a2b513ec9504401f90e5468a2e113d88903a017708e83000b40000231b3b62b4141893843e1f20e246562d8140887037616708882c409e0000231adc22cd14dc9a646d2070ec86b62fd15188fc3bc18008b82f40ba0000231a7fc2bb948099647120f0ee86a82fc14a08e83b217b09403180ca0000231a1d72e2158c9e849521c8f306e030715388fc3ba17a08c02dc0be00002319be12d015009bc4812110f186b830014808b039c17408b02e40a8000023196112bb947c97e4632000e886702e213e889838e16d0848294098000023190512b094109464441f80e386742de14708c83b017408d03440da00002318a2f2df95589f24902188f3c6e630915689183ce19109783100d0000023184622be14789704551fe8eb06a02ea14588d43c618009402fc0cc00002317e7d2c014749a647820e0ee46a82f714a08c83b017308903000c4000023178cb2aa13d494e4481f88e686702d61388850386163083029c0aa000023172cc2cc94e89a647120c0edc6a82fb14788a83a216f08c02b00a800002316cd42c8149c98e46f2070e9c6942ed143087038016608482c40b2000023166c62d295349c24862108ef86d230514889003b618509483240be000023160e32c2949898046e2028eb86a42f014c08e83ca18e09483400d000002315afb2c594a09a24752098eb86a62ee14888e83b417b09202f80ce000023155232be944c9724601ff8e8c6962ed14c09083d018509703100cc00002314f402c114789844601fa8ea06982e414308b83ae17108502b40a6000023149732b0942495e4441f08e1c64c2c813a887c37e16808182a40aa0000231437e2cb14cc9b446d2078ec86ac2f714888a03aa17009102ec0c600002313da22c1949c99e4682070ed46b22f4145089439216308202b00ba000023137b72c414889a247920b0ec868c2f214c89043c019209b030c0be000023131e82ba143896c45b1fe0e6c67e2d914408c03aa17a08802d80ba00002312c192bd94689724612018e706882e214408b03a817808e82fc0b6000023126522b794449544421f40e2c6562c913e086c37a16708382a40ac0000231203c2da15409f049921c0f606ec316158894c3e619709803440e400002311a532cb14f89b447320c0ec46a42f314c08e83b818509503180c2000023114782c294a098e46a2080ea069c2f114c08b038a16908802d80ba00002310eb42b4143096244d1fd0e9c6682d31398850376161082028c0aa000023108f32b014109704672078eb869e2f314d08d03cc18709703280cc000023103282b6140094a4471f88e3c6602d113a084836c15e08482e00b40000230fd152d215349dc4922148f5c70c31a15b89103d818a09403580dc0000230f7202c794949904712090ed86ac2fc152093c3ca18109182f40b40000230f1412bc144897445b1f98e5467c2e714888d43ac18108f82ec0bc0000230eb6f2bd947098e4732080ec469a2ee14a08dc3c217408f82f80be0000230e5902c2949898e4662038e8c6922ed144889039817108802e80aa0000230dfb22c394a899246720b0ecc69e2ea14688b43a817f09383180c40000230d9c92c4948c9824581fe0e706942ee14a08f03c417908d82f00aa0000230d3d22ca14e09aa47020e8f086a62f714d08fc3d017d09083000ce0000230cdfd2ba147896e45d2050e8c68c2f414a89003b617b08c02f00d80000230c80e2c614b89b847a20c0edc6b430515089083b417d08b82dc0aa0000230c2372b7943c98e4702058eb46aa2f014688e03b417708b02e80ae0000230bc8d2ae141095c44b1f58e4066a2df140888838416208802e00be0000230b6982d115189c248620f8ef06c22f614f08d83b617809102e00c60000230b0bd2be946c94e4572020e906822df14588a439416c08a82d80ce0000230ab022ae940c9484441f18e286602cb137087837816208502b40b40000230a5422ab13b89324401f28e286582c4134082835415607f82b80a600002309f3f2d595209d44882168f406e230f15909483ea18d09502f00b40000230993e2d495609e648c21a8f3c6d02ff153091c3d818008c82dc0ae000023093432c994c89a647d20b8ec46a630115589183d419009183080c200002308d682c214989aa47a20b8eec6a02f714808d83a617508802d80b4000023087872c194489704551ff0e7c67c2df14488bc3a217508902ec0be000023081bf2b5941c96244e1f58e6c6562cd139085035815a07d02c00b600002307bc42ce14d09a646f20c0ee86b030615689403d018c08e82e40ba000 else 0x233676b2b214049404451ed8e086582d0139888c38417808b02bc0b80000233618d2be947096c45e1fc0e6067c2e4140889439817a08e02f80ce00002335bba2c1149c99846a2070edc6a42ff14a88bc3ae17708982ec0ba000023355d92be946498645d2040eb069c2f014708c03b817508b82c409e0000233500b2b4143c96245a1fc8e686762dd13e88a837c16408882b40aa00002334a272c494fc99446a2068ec469a2f414988c83ba176091830c0d4000023344262cf14dc99c45e2028e9869a2ed14908a439017808982c40ba00002333e582b3943496e45f1fb0e7c67a2dd14188b43ac17e08a82dc0a6000023338772c694b89a046c2068ef86be2fe14e88f83ca18209002f40b8000023332592dc955ca1249c2198f4c6e631515709243b017c093830c0c400002332c7c2ba94909ac47c20d8ee06b62f414a88d83b417108c03100b8000023326bd2b3143c94e4411f30e6c6702d413e885c36816407d02940a2000023320f22b7943896844e1fa8e8c6882e8144089839616e08502dc0b400002331b2f2b9144496844f1fa8e5c66c2dd14888ec3c418209582f40ba000023315522be94709664541f80e3466e2da13b085038c16d08682e40bc00002330f642ce14e499e4682020ec46ac2f514c89043bc17808c02f00cc0000233099c2b7140c9624512000eb86b62ee14808bc3aa17708e02fc0ae000023303952ce94f89b647d20b0edc6aa2fb14988d43a617308982e80cc0000232fdb22c0149498e4692048e846802e414508e03b017308802dc0ae0000232f7c52cd94d09a647b20d0ee06a62ed14c08e83c8185091830c0c00000232f1d72c1147c9604461f58e586722e614208cc39e17108782c40b40000232ebec2c4146c97c45b2030e8c6782da13b085c37c16408902c40b60000232e5f82ce94e89be4862108eec6c430415089243bc18409203000cc0000232e0092c3949099246d20b0ee86aa2eb14508c039e17908982c00b20000232da0e2cf14fc9a846d20f0f106cc30515688e839817008b02e00a00000232d4132d214f09b847320b0ec06a62f715389143d617d09183000b80000232ce422b5945096c45a2010e6c6862dc13c087437815f08302a009a0000232c86f2c194689764562028ea86942ea14608ac3a217b08c02e80bc0000232c2ac2b6940895c45d2008e7067c2e6143889438216708b03000ca0000232bcd02bc14609804672078ea868a2eb14188a03a016f08b02ec0b00000232b6e32c514a49aa47a2108f2c6bc30b15409343e818c09a83580de0000232b0fe2c794f49b047d2088e9c6842ec14908fc3aa17408c82e80b60000232ab4b2ad13e493c4421f58e0c6562c2131082c35a15c08282a00ae0000232a5802b414689664562038e8468a2e914a88cc39e17b08d02f00b600002329f932cd14d49ac47f20b0f006c030014b08b83a217708c82e40c8000023299a12c894c89b24722080ee86ae2ed14b89103b618608c83100ce000023293c72bf94bc9a047320f0ef86c230c15388e83ba18308c82f00ac00002328de02bd949899446a2050ea868e2e7144088c39a17408a02e40b6000023287fa2bd144c96644d1fb0e7c6882e414508c03a2183097832c0c8000023282222c514809884602028e906aa2ea15209003b817808c03080b800002327c312c894c09ae4602020ea46922e914688e43b417a08d83040bc0000232763c2d115049c447a2100ef86c2301156090c3d618309103280be000023270372d395149ca48d2180f506e430215409243b017d09302ec0ba00002326a622bf946097c45c1f88e6c67c2d813f888039216908982dc0c60000232645f2d8955c9f24992178f446f231e15d09343e219209903180be00002325e922b9143c9664572010e5c67c2f214908bc3b417508a82d80b4000023258c52bd144896e4531fb0e986742e314288ac3aa17608802bc0b4000023252d52c994f89b04892158f2c6b82ed14988e03a618309183000c200002324cca2d195149dc47e20c0eec6b430715589103d618909182f40c0000023246e02c394d49a44692030ec469a2ec14c08f03ae17d08c82d80c0000023240f52c2948098e4732028eb06962e114408b439a16e08582c40aa00002323aea2d795509da4932110f186c630d158893c3dc18409382ec0bc0000232350f2bf948c98e4611fe8e9c68a2e914288d439416208b03140c200002322f382bf147497845d1fd8e7c6902ea14688d43b618508e02f40b0000023229392cb94e09ae47620c0ef06c030215109043c818109403180be000023223412cd15289d44892138efc6ac2fe15288f03b217808f03240be00002321d442ce950c9a64722070ef86be2f614b08f43c218508f82d00ba000023217772ba94509584542018e946882e4140088c37e16d08e03080d8000023211852cc94ec9b847b2140f4c6da30e15609303d017e08f02f40b400002320bcd2b0141c95c4521fa0e4c66c2db13c087837816908702d00aa000023205d02cf15149c84892148f146de31915b899c3f41a209c834c0d8000023200092b7946096e45b1fd0ea869e2eb14408b439e16d08182b40b20000231fa3a2b8148897a4581fc0e706862ee14508a039a17708a82d00960000231f46b2b9147097a4692098ef069e2eb14188b83a617d09183100c8000))) else (if i < 366 then (if i < 364 then 0x234df3d2bf148498a4612018ea069e2ea14588bc3ae18008c02f00a60000234d96a2b5946496a4561fe8e886842f114688a839817f08f02e409c0000234d3902c694cc99847320b8ed86b22f814d88ec3be17f09283140cc0000234cdb62c0147c98845a1fd0e846922dc14388c43ba18108f82f40b00000234c7e82b7946898845d2000e8068c2f214808a438a16308602a80aa0000234c1e92cc94e49a846e2058eb469c2ed142087837415d08382c00bc0000234bbca2e195a4a004a32200f6c6f2315157094c3cc18809203000c00000234b5f72c014949804642060edc6b22f114988b03b0184097031c0cc0000234b0052cb14d09ba4742170f306b82f314e89043bc17908e02f80bc0000234aa262bd942495844e1f78e586822e213b086037c16a08b82c40b20000234a4562b914349684611fe0e7c6982f414988dc39a17108802dc0c400002349e802c214b099c46f2050e986942f014588ac3b6180093830c0ae0000234988d2c794cc99846b2028ea46a02e9143887c37615b07f828c09c000023492b12c1949098c4702060eac6a830114908cc3a017c08b83100ce00002348cce2c3949c9924632068ea86a22f414c08bc3ac17e09102f40c4000023486e52cc14f49c04862168f446ea30d15809483f019d09683000d80000234811e2b594249524571fa8e686782de13e887837c16a08082a009a00002347b502b4142495c4531f30e186462cf13e088039016e08a03040b6000023475922b414009424461fa0e406742ef14908c839817408882cc0ba00002346fb52c114949684521f90e506702dd13d888c39a16808802dc09e000023469d92c294a899a4612050ee86b830214c88f03bc17908202d00b2000023463e22d395549f649a21e8f846fc32715e09743fc18909303280da00002345e392a793c49384441f98e646822da13a888039217708c82e80c4000023458362cc95049cc4832160f546c830a15789083c618c09102e40be0000234524e2c5946497a44a1fc8e706802ed14008c83aa17709383080bc00002344c5d2c0147c9744632008e506722d313f887837216b08b030c0c40000234465b2d795489e04882170f246ca2f814888cc3a217a08e02f40b40000234407e2bf94749884571f98e6467a2e214588d039416908e02c00ac00002343a982cb14b89aa46e2088ee06a42f714888cc39e16b08782ec0ce000023434d92b293fc95244f1fb8e906882df141089439a16e08682ec0ba00002342ef72be14b499c4712068ea06982ef14b08d83a217e08c02c80a80000234292b2b614249544431f70e246702d814788bc3a016908682c80ac0000234236f2b1942095c4411f60e646682db13e888037e16508c83040b400002341d832ca950c99e46f2070ed46b22fe14a88e03b018308f030c0c4000023417a12bf148098c46c2010eb06962ee14408b439e17708e02ec0c8000023411cd2b7946c9624511fe0e986802e513b087c39016d08b02fc0ae00002340c222a9140094e4461fb8e6467e2e614308b43a817608e83140be000023406472c094a899646b2080ecc6922f114908d43aa16d08d82d40ac0000234005a2c694ac9ac47020a8ed06c030214f090c3d218e09603440c60000233fa782c614c49904722078ec46982f614b88d43a017b08c03040c20000233f4a82bc948c9904622058ec469a2ed14988e03b417b09203040bc0000233ee832e0155ca044982248fb870431a15709343de19309983200c40000233e8be2b613f89304431f98e7866c2d4139086c37a15e08782e00a40000233e3062b2142c9424521f50e4c65e2c7136084036415d08282e00c40000233dd1c2c514ac9a046a2010e9067a2d813b087038616808802bc0a40000233d73c2bc14809884782128f106d230615289143ca18a09102fc0ba0000233d1512c914e09bc4892130f346cc30c15488f03ba17308b03000b20000233cb5d2c514a49884702058ea46a02f414c08f43b217d09483240c80000233c58f2c0144895a4582030e8469e2e514408bc39417508482d00b80000233bf932d014d49b24712078ec06a42f815008f83b417608e03100ca0000233b9ad2bf14789924632058ee06b430115288e83b017a08d02f00ae0000233b3e42b794489744672068ecc69e2f614788e03ba18208f02f80b20000233add02d495489d04862118f106b62eb143089839a16f08a82f00bc0000233a7c92d595309be47e2100ee46c630815a09343c818009002f40b40000233a1fe2b3142495a4551f60e306602da13f886437416408282c00aa00002339c322b594649904632020eb46a42f814c09003c818509183100d60000233965b2c094bc9a447c2110f046b830014b08e83b217808b82e00be0000233906f2c794b09904551fa0e806922e714308903a617508d02e00b000002338acf298136c9124261e38d906222b8130882437616108502bc0ac000023384fe2bf94889884702098e986922e814588c83be188093831c0be00002337ef62cd14f89b447d20a8eb86b430215189143ba18b09503440ba0000233791f2b494149684632070ed06b02f414b08dc3a417209002fc0c00000233731d2cc14d89b04792090ed46a82f214d892c3c818508d02f80a400002336d332c294a89a046d2008e706682db141888c39a16708702d40bc000 else (if i < 365 then 0x23657952c594d09a647020a0eec6c630415188f03c618209102e00c2000023651cd2b5142c95a4521f70e7c6902e4143085439616b08883000be00002364be82c2149498c4662068eb06922f614908a43a817208e82e40c6000023645f62cd952c9d44872140f106c630114d08fc3a817508802f00b8000023640182bf149498e46c2088ef86c030815108f83c017c094831c0ca00002363a492b6943c9484501f70e406562d713d884c37c16808502e40b00000236345f2c694989864652018ea86922f814b090c3b217a08d02e80ae00002362e802c014b09a047620c0ebc6bc2fb14c08ec3b817008982d00c00000236288d2cb94d49a44722058edc6ac2fd15309303e0190096033c0e4000023622c52b7146896c4652040e9867e2df14988e03b217b09183000c600002361cd32ce14d49b046e2090ebc6aa2f214a08a438a16708982e80ca000023616dd2c914d89a846c2048ea869e2e5143886838017308b82e40a80000236110c2bd949c99247820b0ec46b82fd15109403d418108c82fc0ac00002360b372be146498a4662068e9067e2dd141089c39417408702f40c00000236054d2c794b49a647120a0e9c68c2e514488a83ac17308a82f40d00000235ff7a2bc147c96a4641fe0e8067a2d713d883837417008802b00a40000235f9722d415049b047e2100f0c6d22ff14b08bc3a817308982d00c00000235f3a32ba14649744531f80e4c65a2de13d88943ae17408702b80b40000235edd12b5945c96c4611fc0e886862e714488d03aa17008a83040d00000235e7f32bc148898045b1fd8e8068c2df13e888c39016508182880a00000235e1e12d915509ee4932110f246d230d15789403c818a09682fc0b80000235dbf42c994fc9b04782108f346e230e15989343d419308f030c0bc0000235d60e2bc145496a45b1ff8ea86aa2f514b88bc39417308f82e40a20000235d0422b994749724622080edc6b62f614c88d03b218008c02e80bc0000235ca442d194c899a46d2058e986962ef14b08f03ce18209002dc0c40000235c4592cc94d49a046d2040e946902ec14808dc3b618709482e80b60000235be632ce94e49a447320a0f0c6d630715389183c818309182fc0c20000235b8822c014609724612028e8868e2eb14888c03c218109002f40c80000235b2a42be947896a4652040eac6962ef14b08c038416408282c40ac0000235acaa2ca94a099447220a8f086d031015589203cc17e09183040ba0000235a6d22b8142496c4591fd0e6c67c2d6143889839e17308b82f00b60000235a1032ba944896e4652048e9067c2e2143089c39e17408c82f80b400002359b562aa13f09384351ed0df06322bd12e886038016408582e00c2000023595762bd14789724622018e5c67e2dd141086c38216708582c40a600002358f882c814ac9a247920a0efc6bc2f514e88f03c017908902f80a6000023589842cf94fc9c248a2168f386dc2ff153091c3e819f0a103680ee000023583a62c094ac99a4632040ecc6b42f414b88f43ae17508602d00be00002357dd02c294909804632058ed06ca30114808f03b217b08982fc0b0000023578012bf947c98847220a8ed86ae30715188f43d218909383240b6000023572022cd14e09ac47a20d0ecc6a62f014608a838216008102a40b400002356c142ca14f49d048220f0f046c42f914f88f83d018409883340ca000023566452be149498646c2078edc6b02f314d88fc3b617708f82f40c00000235604a2c994fc9b647b20b8ef86b02f7148889439616f08602f80b400002355a742be14b09a046c2050e846882f114988e83a417908d03100a8000023554922c114a099847020b0ebc6a82f714b08e43c818809603340c600002354ea22ce14ec9a647720b0ed06b02f714888bc3be17f08c82e80b6000023548bc2c394609844652040ea86a62f414888c439e17008602c40ac000023542ea2b7944c9704612038e7066a2e3142889c39217208882d40b800002353d142bb949898e46d2058eac69c2e714588ac3a816e08c02dc0b6000023537542b4145c96a4591ff0e846862e213f884c37616008782ec0b8000023531602c7949097a4601fe0e786762e813f089438a167085029409600002352b882c0947099a47020a8ed46ac2f614d08f83b417e09182f80ba000023525852d515049b647e20a0ea868a2dd13d888439217908a02d40be00002351fd12ad13ec9364401f90e6c6662e514608b037a16308902c00b0000023519fd2c1948c99c46e2030ec86822db13d087437615f08882e40c0000023513fe2cb14d49b648220d8efc6bc308156091c3c817608c82d80bc00002350e412af940094e44e1f48e306642d2140088839017408e02ec0b40000235085a2c4148899246a2098edc6a22f614908e03a617908b82e80c8000023502852c0147c99046a2038eb86ae2f814b88d43b017408d82e40b80000234fc902cd94cc9b04852168f2c6d630e15589283d218709403440e40000234f6b12c494b09984702030e9067e2e814508bc39c17708f02f40ba0000234f0b62d3152c9ba48a20f0ef46d630a15789203ce18609383180c20000234eaed2b3144c9664591fe8ea469c2ea14a88b83a817608c82f80cc0000234e5272af94049464491f60e4865c2c6134083036615307f02900ac000 else 0x237d0b92ae141c94c4521fe8e6c66e2e014308c039a16308602a80980000237cace2c0149c98a46e2028eac69e2ef145889839417308e02d80b00000237c4db2c314789a046f2048e6c68c2e014388ac38e17108a82e00c20000237bed12d415209ce47620d0ed86a82f414688b039216408502f80cc0000237b8f02c0148097c4682058eb869a2f314b88f43ba17c08a02fc0ac0000237b3242b1142894e4491f58e486682e2143086c38216408802bc0bc0000237ad5b2b7143c96c4531fb0e6c6842df14588cc3a417508d02c80b60000237a7602cc94e49c04832158f146c830c14e08f43bc18c09483380c00000237a1632d115089ea48f21b8f3c6e830c14c88e83b416f08a02b00b800002379b722c4149899246a2068ebc6a22fe14c88e43a817608e83040b80000237957f2c894d49ae4722048e9c6942df14988d43a617508b02e40b400002378fc02b0942c96845c2008e786902e014808d43be17e08a02e40cc000023789ca2cb94c49a047020d8f086d230415509643ec18c09202f40ac000023783d72c794bc98e4752120f0c6ba2f814d09083be17808b02ec0c600002377de92c994b098c4662040ea06922f314588b03a216f08702d40b2000023777ff2c514ac98a4662060ec46be2fd15809203bc17608602f00b0000023772082c894dc9a247020a0ee46ba2fd15109083c017608c02c00b600002376c2a2c3149c99046c2088ed46b4304153891c3b817c08a82fc0bc0000237662e2ce14d49aa47220c8ed06b22f715389043c017d08f02f00bc0000237605e2bc946897c4611fd8e7067e2d813d886837415d08402d40b200002375a572d7153c9d24892130ec06a62f614b08f43b617a08f03280b8000023754922b414209564531fd0e906a42f214908f03bc18308f82f80ba00002374eb92c1945098046a2040ea068a2e013e086c37a16108a82e80b0000023748b42d115009ba47f2070ea46822e114608a438c16308102c80a8000023743132a313b89264311e98dd46502d513c089438816a08902c40a600002373d662a413b491a43f1ef8e406642d713d889c38416d08903000bc000023737812c0147498e4672020e6c68e2e914708c03ac177091830c0bc0000237319b2c394b49aa46c2040e9868e2dc13d88883a016a08782bc0b400002372ba82cf95209aa47b2060ec86aa2f514808d83a616b08802c00bc000023725c72c614a49884652088ee46a82ea14988fc3be18a096831c0d000002371fc32d715449e648d2158f206da30e15388c439416f08a02f40cc000023719b72d895509d248c2150f286e230e15689103c818a09403240d4000023713f42ba14409744592010e8c67e2e413e88ac39c16408902b00ae00002370e0e2bf947898e4602088ecc68c2e614b08e83b217508c03080c0000023708292c914e09a247820e8f106c22fb14508ec3ca18d08f83000c2000023702692b6944c9744642030ec06b82fa14f88d83b016c08882c00a40000236fc9a2b694649924742078eb868c2eb14608cc3a617508c02f80c20000236f6e02ae140893c44a1f50e3065c2cc139087039816508802d00c20000236f0d72d395409d449221a0f586d830514e08ec3b418509183100c40000236eae42cd14f89ba46f2038ebc6882eb14488b83a416e089030c0dc0000236e5102c094849864592030eb86a42e914708bc3ac17d09303100c60000236df162cf94ec9ae47420b8ec46ac2fc14b08d039416a08702b80b20000236d9392bc145097045e1fb8e7067e2e9145889c39817208682e80c60000236d3972a313c891e4401f30e0c6502cc134084438015b08182b80b60000236cda12cd94e89b04802078ec069c2f214908b439417108c02e00c20000236c7b92c814b899446b2040e8467c2ed14588b83a817508a02e00bc0000236c1f72b1940c9424451f68e6067a2e113f888839016f08682e40b20000236bc1d2c294a098a4682090eac6b62f414c08e43bc18308b82c40bc0000236b62b2ca14d49aa4722040ea86942f014608e43b017d08b83100d00000236b02c2ce94c09b047d20f0ef469e2f514608e83a817108882c00be0000236aa362c894b09a846f20a8ecc6b42fe153092c3de18d09182d80b40000236a4662b914689784712040ed86be30315589083d618a09202cc0b800002369e5f2d0950c9c248120e0ed86b22fb151892c3cc18109402f40ce0000236989b2b7142c95044b1f70e546762e514708d43a016a08f03200e2000023692a32d195289c648d2108ee06c230314a08e83b817f09203380c800002368cb42c814cc9a647920d0ef86ee31615989783f8196099831c0d4000023686bb2ca14ec9b84752080ed86ae303158893c3d8192096032c0d4000023680e72bc14649824632008ea069a2ef14f08e83ac17808d82cc0b800002367b0a2c594e09bc4762078ee469c2eb14088bc3a017108702d80c60000236750c2ce95109c848b2160f146cc30b15489183ca18d09082f00c200002366eff2d8954c9dc48f2180f606f230d15689083c617b08d02d40b4000023669162c314a499046e2060ee06b6304150090c3b818109202f80ac000023663282c914a498c4661fe8e7868a2e714388c03a616f08a02dc0c000002365d7a2a513d893843d1f00e2465c2c6135083035615708382a80ae000)) else (if i < 367 then 0x23949162c894b09ac46e2028e9c68a2ef14a08cc39c17e090831c0be0000239431c2cf94e89a84702090f0c6b22f815208ec3b017f09202dc0b000002393d262cc14ac9a647c20f8f006ce30314b88f83b217b08f03200d0000023937472c0148097e4602018e846862eb14d08ec3aa17808902ec0b2000023931722bf948497c46b2050eb86a82f314e08b83a016608502ac0b200002392b8c2c614d899846a20a8f186bc30515489343d618e09502f40b0000023925d92ad13ec9444461f58e186582cd138885437e16b08c02d40cc00002391ffa2c094949a647320d8eec6a02f514d08c43b217308e02cc0a800002391a042cc15109d648a2178efc6b62ff15009243d818909883400d6000023914442b0944496c4541fc0e906822e714288ac3a016f08a82e40c000002390e5c2c5949499e46f20c8eb06aa2ee14988dc3a217708a82ec0b20000239086b2c914e89ba4832148f186d630715789083ca18409483080ba000023902a52b094089524531fe8e9c6a02e814608a039416c08482d00ac0000238fcc72b6942895c4501f40e4c66e2e214708d03ae18209083300c60000238f6f82b7943c9604561fb8e706722ce13b086037816708782d00b40000238f0e72d5152c9ce4842100f1c6cc30414e08ec3c417308a82c80b20000238eb032c2948499446c2050ec06b030015009143c018509283080c40000238e53f2ae13e893243d1f58e2465e2d014588d039a17509183180c80000238df622c614d499e47620b0ee869c2fb14988c03a616d08a02d80aa0000238d9762c514c099c46f20c8efc6ba30415208e43ac18108e03040da0000238d38c2c694c89ca4882080eb86b830415509103d818a09783280de0000238cdbb2b494349764592048ec86b82fa14608a039c17108983100c20000238c7c72ce14f89b247820c8f086c630014e08e43b217908a02ec0b60000238c1d12c714a89a44641fc0e946982eb14188a439416d08682d40bc0000238bbe72c7148899c47420d8ecc6b42f014a089c39a16708482c80bc0000238b6222b5943496445d2020ebc69c2f314a08ec3a016e08e82e80b00000238b0652b5942c97c44a1f90e6065a2d013a886438e16e08502c00b20000238aa782ca14f89ca48620d0f286e430c15489203dc18908f82f40c40000238a4bd2ad13f095244c1f90e6867c2eb14788cc38a17408e82dc0b600002389ebe2d194fc9c04872130ef86aa30115089043ca17e09383180c8000023898bc2cf94e09ba47520c0f286c6309155091c3c818209103000ca000023892ce2c394809864652008e606942e314388ac3bc17a08d03200c800002388ceb2c494ac9a446c2090ebc6b42ff14c09003ae17808f02e80be000023886fa2cc14e49a64722068ee86ac2f514a08d43ba18008902dc0b4000023880ee2d315189d247e20e0ed86ae2ff15288e83b617b08c02ec0ca00002387af82ce14a89a24692030eac69c2f314c09083ae17708e83180cc000023874cc2de155c9f049a21b0f4c6e630f15b09403c618709503040c600002386ecd2d215309d84852140ef46be2fb15089143bc17b091030c0d20000238690a2b594489824571fc8e7c6822db13e885837e16108202ac0b8000023862f52d915049d048620d0eac6ae30115189103ca18709002fc0c200002385d4c2a513b893c43e1ef8df864a2bf136086c38016408282a80ba0000238576c2c314609724571f88e586742e514608c43a817708b82e40ba000023851862c4948899e47420b8ef46bc300158892c3d618509582f80ca00002384b942c894d49bc47a2108edc69e2ec14308fc3c018909703180b6000023845b52bf14a098e47420b0ec86ac2f714b08bc3a817908a83140c200002383ff72b314089644662028ea869e2f314488b038e16d08e83000b6000023839e12d715409ec4902120f106c831015389103c817f09383280d80000238340b2b3141c94244a1f80e606882db13f887438216708302dc0c200002382e1d2c494909964662020e8c6982ea14a88c03ae17308703040d4000023828652b3941096a4602010e5466a2d713d888038816f08482f40be0000238228d2bf146c97e4662008ea86962f014908e83b017308d02e00c800002381cd22b2141095e4591fe8e786802e514308a837c163084029c0aa000023816d72ca94dc9a446f2080ee86be30715088d039e17808e82f40c20000238114b29e139c93a43c1e90dc86262bb131883c36215c07f82b40b800002380b612ca14e09c04872140f146c630215289143cc17d08e82fc0c00000238059c2b1143495045b1fd0e5c67c2ea14488c83b817709183140be0000237ff8c2d415009ce4812120ef06b42ff14c08bc39c17508d02f00bc0000237f9ab2c494d49a047e20d0ebc6ac2fa14c08c43a616b08982e40c60000237f3cb2c1147c9844602010e8c69a2e214088a83a217308a02e80b80000237edd92c894d89d047f2088e9869e2f714708b839a16708802d00be0000237e7fa2bb147497e45d2050ed06a82f814a88d03ae17a08e02ec0a80000237e2172c514c49a646b20b8eec6dc30c15509583f81900a003580de0000237dc272c594a89a44742088ee06b22fb15008bc3b217808702d00ba0000237d6712aa140493c4451f28e3063c2c413c886837c16a08703040c0000 else (if i < 368 then 0x23ac2492ae140c93e4431f10e306622d5135083835815a08402d40c0000023abc512cd14e89ba47920d0ed06a62f514608a839e17a08902dc0be000023ab6742b894449824662020e746782e914388ac3a617c08702d80a4000023ab09e2bc145096a45c1fd8e9c67e2df14788b039c17b08902f00c6000023aaac62bd946096e4591fe0e686882e114188a43a016e08b82d80be000023aa5072af142c97645c2000e7c6862e3140885c38c17208c02f80c4000023a9f1f2c494a89944782078eec6b22f314c09003d218d09583400d0000023a99502b3143095c4511fb8e6c66e2dc142888039416608982d00b2000023a93442ce150c9ce4892120f186c230915008fc3b618209282e40b0000023a8d5d2bb94609644622018e7c6a02f914d88bc3ae17c08f83040ba000023a87722c994b49a24692098ed06b22f014788a839e17008e03140b0000023a81602d595449ec48a2158f246d6301152091c3b417608f82f40c2000023a7b8e2b7942c9644501f70e586782d513c887037816608882c8092000023a757f2d7153c9de48c2128ed46b02f914f08e43b218508f02f40c2000023a6fa52bd946c9884682038ec868c2e814b88e03b017008a02ec0ac000023a69ce2c2148c9884621ff8e706802d413e88a439817508b02ec0be000023a63b82d695489f848a2148f106d030915709283cc18c09703400cc000023a5dd42be946c96e46d2040ea86962f714b08f43d619109c03700e2000023a57f62bf147c98e4642028e8c6862e2143889438a16908682c80b4000023a52502a113c491a42b1e70dc46442ca137884435c16008102bc0c2000023a4c702bd947899246e2038eb86b430215288d83ba17f09083200da000023a46aa2b8946097e4682098eb46902ee14608a83b417808c82dc0c2000023a40c12bf94909924712078ee46a42ef14a88f83bc17809082fc0b6000023a3abb2d415509da48920e8f1c6d030c159893c3d819109403280d4000023a34eb2b194389584512010ea46a42f814e09043cc17b08b02dc0aa000023a2f5329e138090c42b1e88e1464e2ca138086837216008582b0096000023a29682c5149099c4702040e8469e2f114488d83c018108c02f00ae000023a23732ce14e09b647e2128f146c62ff14e08ec3ba17f093033c0b2000023a1d672d215209da47b2160f206d02fb15088bc3ac17508c82f00b8000023a174f2df958ca1449f21b8f746e631d15b09383da18b09482f00b4000023a115a2c994d49b248220f0ef06b42f314508b839016308802dc0b2000023a0b7a2c2947898e4652040eb06902f914988e03c017c09203040c8000023a05932c614b49a446d20a0ee06a82ef14688c839617209082e80b20000239ffbe2b7942c96a45f2050eac6a22f214a88e039e16e08b02e80c80000239f9c22c614c09864601fc8e6868c2e513f88a439017008782d40c60000239f3cf2c994e89b64802110ed869a2f815109003b218409303240d20000239ee0f2b7947c9844642030ea068a2f114608bc38e16708602d80bc0000239e8312c1148097e4672068ee86ac302154091c3d218608d82fc0ba0000239e2392cf15189e24922198f506de31615609143c218309482f00ba0000239dc432c994c098a4692018e806782e414208a43b417b08e83040c40000239d66d2b9145c96644a1f70e5466c2d3140088839816908802e80a80000239d0a12bb946497a4612040e8c68a2ec14888cc3a617308882d40c20000239cac82bd14489704591ff8e6c6742df13e88983a817508b82d00b00000239c4e32c0948c98045d2038ea46a02eb14488c03a416e08a82b80bc0000239bee22d315289d448320e8ecc6b02ef14388983a017208882d00c60000239b8fe2be147897e4632010ea46ae2f414d88d83a416f08a82ec0be0000239b32a2bd145496a45f2040ebc6a82ec14408a43b817e08b82f00c00000239ad3e2c714e09a24782090ed86a22fb14e08e03ac16f09002f00ca0000239a7502c814d09a24692078f006bc2f714608d03c617f095033c0c40000239a1742c794ec9a44712070ed46902f5142086037a16608682c80bc00002399b862c6149098a46b2080eb069a2f114b88dc3ae17808c83140b8000023995a72c714b89a64782060eb468e2ed14608d43a217508902e00bc00002398fdf2b594249544531ff0e806902ef14888e83ac16e08b82ec0c4000023989dc2cd14cc9ae4852100f086b630314e09043b617908b82e40b6000023984132b194189604551fd8e506682e014288a439a17008582c80be00002397e2c2c394b49944632048ecc6b82f915308f83c018a09503240d40000239785e2b8945497c4692070eb06982e914508b43a416b08182ac0a2000023972742c794a09b246920b0eb06862e814788c43bc17b08e031c0ca00002396c7c2ce94d49a647d2150f286ba30415889583f818f092834c0d2000023966b42b7145c9824591ff0eac68a2e714088ac39016808c02fc0bc000023960d52c194549804662018eb86962fb14c08d43aa17208982b00b000002395abf2db95249d24822100f186b82fc14808f43c418409103080b8000023954cb2ca14dc9aa46c2078e9c68c2e514908c83a816b08a82dc0ac00002394efc2b8142494643f1f28e046682dd13d888439416b08902d00b6000 else 0x23be2ca0000000000000000000000000000000003a617b08d82e40ba000023bdd142ab14089564481fa0e846942f715009143c417a09383140ce000023bd7352c394a89a248120e8ee86b630314b88bc3ba17d08c82f40bc000023bd1722b2940c94e44f1fe8e7467a2df13d88a039c16808a02e00b8000023bcb812cc14ac99e4762060eb06a22f814d08d43b6185094832c0ae000023bc57d2d415449de49621d8f7c6f031415b897c3f019609203100c0000023bbfa22bf949c98a45f2020e9c6a02f714a88e83b817c09783500de000023bb9862e01574a084a821f0f586e031015609243c617b08f82fc0cc000023bb3a52c1148c99446d2030ec46a82ef14a88ec3c418709002f80ba000023bade12ae942494a4541fc0e8066a2df13d086837c15b08082a4098000023ba7d62d195349da4872128ef86b62f415389303ce18809403280c2000023ba1f92be94609704591fa8e4466a2de14508b839417008c031c0c4000023b9c112c494b49a046520a0eb46982e914108a03a017008882c00ac000023b961e2ca94e89a847720b8ec06c62fd15089083c819009102f00be000023b904c2bf149c98646b2070ec469e2ee143088c39217309083240c4000023b8a3f2d395189c04832120f046c0302153892c3d618f09783340d6000023b84862a9140c9624521f80e686642dd13d08a039a16808282b80b4000023b7eb62ba946c97a4571fc8e6c6782e614008b83a216f08a82e00c4000023b78b22d315449e44852178f506ee31615a09603ea19b09c03300c4000023b72c22c794b89a44782078ea46a62f614508d83aa17908f02e80b4000023b6cd32c514ac99846c2058ea86962ef14608a039e16d08a82d00b6000023b67062b894389644521f78e486682d513b08943a017208c83040be000023b61342b4145097c4562008e7c6822e414388ac3aa17808802a80a6000023b5b542c014ac9a647420f0f086c630815a09543d618b09203040d0000023b55852b7943c96244f1f10e086522c8132083435e15707b82840ac000023b4f722dd95609e848a21a8f646fe31515d89783fa1a009883280cc000023b49782ca94d09b047820a0ed86a430414c08e03b016f08a02e00ba000023b43982c394b098c46b2000e706882ea14588b03ac179085029c0a2000023b3db22ca94d89ae46c2060eb869c2e114208a83ac17308882e40b8000023b37ef2b4142c9784692040eb46a230015189303cc18008f02d80b2000023b32122c514a498445c2048e986942f414a08bc38e16f08782c80b6000023b2c312c1146896c45e2028eac6a42f314a08c43aa17e08c02e00b2000023b265d2bb944497645d1fc0e846802db142888438c15d08102b80b4000023b20872b814609784621fe0e686722d713e888439616d08f02d40ac000023b1a8f2c794bc99e4802130f106b82fd15289003ca18e095830c0b0000023b14c32b3145097c45e1ff0e9c69e2fc14e89103d6186093033c0d4000023b0ec12d115049b24812108ef46ae2f314b88f83c218109302fc0ba000023b08d22cc94e89b84792138f146d830015409303da18908e82f80c0000023b030f2b0940495245a2000ec86982e513d08b439e17308682d00b6000023afd1e2c094ac98c47020c0edc69e2f814e88d43ac17c09302f80ca000023af7252c814a899646d2078ea06942f514d090c3ea18b09a83240c0000023af13a2c614d09a847920b8ec46b02f014c88e439c17908f02d40c4000023aeb5e2bc145c9704561fe0e7c6922e614288bc39617008482b40b0000023ae5892be948099446b2040ee46c030415009043ba17509102f80ce000023adfa12ca14c49b047a20a8ef86ac2f815489043ce188094831c0d4000023ad9bd2c494a09a846b2068edc6a82fd14c08dc3c618609a83240c8000023ad3e62bd94689664612000e7c6822f314708cc3b418109283180cc000023acdfa2c694cc9a646e20b0f006c230615209283ea192097031c0d0000023ac8082cb94e09cc4972168f346e431315a895c3d618808f82e00b4000)))))))))

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



private theorem b364513 : covered 364513 364605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364605 : covered 364605 364697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364697 : covered 364697 364789 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364789 : covered 364789 364881 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364881 : covered 364881 364973 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364973 : covered 364973 365066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365066 : covered 365066 365158 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365158 : covered 365158 365250 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365250 : covered 365250 365342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365342 : covered 365342 365435 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365435 : covered 365435 365527 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365527 : covered 365527 365619 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365619 : covered 365619 365711 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365711 : covered 365711 365804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365804 : covered 365804 365896 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365896 : covered 365896 365988 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b365988 : covered 365988 366080 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366080 : covered 366080 366172 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366172 : covered 366172 366264 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366264 : covered 366264 366356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366356 : covered 366356 366448 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366448 : covered 366448 366541 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366541 : covered 366541 366633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366633 : covered 366633 366725 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366725 : covered 366725 366817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366817 : covered 366817 366910 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b366910 : covered 366910 367002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367002 : covered 367002 367094 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367094 : covered 367094 367186 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367186 : covered 367186 367279 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367279 : covered 367279 367371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367371 : covered 367371 367463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367463 : covered 367463 367555 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367555 : covered 367555 367647 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367647 : covered 367647 367739 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367739 : covered 367739 367831 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367831 : covered 367831 367923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b367923 : covered 367923 368016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368016 : covered 368016 368108 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368108 : covered 368108 368200 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368200 : covered 368200 368292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368292 : covered 368292 368385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368385 : covered 368385 368477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368477 : covered 368477 368569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368569 : covered 368569 368661 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368661 : covered 368661 368754 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368754 : covered 368754 368846 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368846 : covered 368846 368938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b368938 : covered 368938 369030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369030 : covered 369030 369122 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369122 : covered 369122 369214 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369214 : covered 369214 369306 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369306 : covered 369306 369398 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369398 : covered 369398 369491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369491 : covered 369491 369583 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369583 : covered 369583 369675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369675 : covered 369675 369767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369767 : covered 369767 369860 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369860 : covered 369860 369952 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b369952 : covered 369952 370044 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370044 : covered 370044 370136 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370136 : covered 370136 370229 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370229 : covered 370229 370321 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370321 : covered 370321 370413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370413 : covered 370413 370505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370505 : covered 370505 370597 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370597 : covered 370597 370689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370689 : covered 370689 370781 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370781 : covered 370781 370873 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370873 : covered 370873 370966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b370966 : covered 370966 371058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371058 : covered 371058 371150 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371150 : covered 371150 371242 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371242 : covered 371242 371335 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371335 : covered 371335 371427 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371427 : covered 371427 371519 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371519 : covered 371519 371611 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371611 : covered 371611 371704 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371704 : covered 371704 371796 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371796 : covered 371796 371888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371888 : covered 371888 371980 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b371980 : covered 371980 372072 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372072 : covered 372072 372164 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372164 : covered 372164 372256 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372256 : covered 372256 372348 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372348 : covered 372348 372441 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372441 : covered 372441 372533 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372533 : covered 372533 372625 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372625 : covered 372625 372717 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372717 : covered 372717 372810 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372810 : covered 372810 372902 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372902 : covered 372902 372994 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b372994 : covered 372994 373086 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373086 : covered 373086 373179 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373179 : covered 373179 373271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373271 : covered 373271 373363 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373363 : covered 373363 373455 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373455 : covered 373455 373547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373547 : covered 373547 373639 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373639 : covered 373639 373731 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373731 : covered 373731 373823 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373823 : covered 373823 373916 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b373916 : covered 373916 374008 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374008 : covered 374008 374100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374100 : covered 374100 374192 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374192 : covered 374192 374285 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374285 : covered 374285 374377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374377 : covered 374377 374469 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374469 : covered 374469 374561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374561 : covered 374561 374654 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374654 : covered 374654 374746 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374746 : covered 374746 374838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374838 : covered 374838 374930 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b374930 : covered 374930 375022 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375022 : covered 375022 375114 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375114 : covered 375114 375206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375206 : covered 375206 375298 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375298 : covered 375298 375391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375391 : covered 375391 375483 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375483 : covered 375483 375575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375575 : covered 375575 375667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375667 : covered 375667 375760 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375760 : covered 375760 375852 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375852 : covered 375852 375944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b375944 : covered 375944 376036 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376036 : covered 376036 376129 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376129 : covered 376129 376221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376221 : covered 376221 376313 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376313 : covered 376313 376405 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376405 : covered 376405 376498 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376498 : covered 376498 376590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376590 : covered 376590 376682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376682 : covered 376682 376774 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376774 : covered 376774 376867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376867 : covered 376867 376959 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b376959 : covered 376959 377051 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377051 : covered 377051 377143 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377143 : covered 377143 377236 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377236 : covered 377236 377328 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377328 : covered 377328 377420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377420 : covered 377420 377512 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b377512 : covered 377512 377605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 364513 377605 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b364513 b364605) (joinCoverage b364697 b364789)) (joinCoverage (joinCoverage b364881 b364973) (joinCoverage b365066 b365158))) (joinCoverage (joinCoverage (joinCoverage b365250 b365342) (joinCoverage b365435 b365527)) (joinCoverage (joinCoverage b365619 b365711) (joinCoverage b365804 (joinCoverage b365896 b365988))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b366080 b366172) (joinCoverage b366264 b366356)) (joinCoverage (joinCoverage b366448 b366541) (joinCoverage b366633 (joinCoverage b366725 b366817)))) (joinCoverage (joinCoverage (joinCoverage b366910 b367002) (joinCoverage b367094 b367186)) (joinCoverage (joinCoverage b367279 b367371) (joinCoverage b367463 (joinCoverage b367555 b367647)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b367739 b367831) (joinCoverage b367923 b368016)) (joinCoverage (joinCoverage b368108 b368200) (joinCoverage b368292 (joinCoverage b368385 b368477)))) (joinCoverage (joinCoverage (joinCoverage b368569 b368661) (joinCoverage b368754 b368846)) (joinCoverage (joinCoverage b368938 b369030) (joinCoverage b369122 (joinCoverage b369214 b369306))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b369398 b369491) (joinCoverage b369583 b369675)) (joinCoverage (joinCoverage b369767 b369860) (joinCoverage b369952 (joinCoverage b370044 b370136)))) (joinCoverage (joinCoverage (joinCoverage b370229 b370321) (joinCoverage b370413 b370505)) (joinCoverage (joinCoverage b370597 b370689) (joinCoverage b370781 (joinCoverage b370873 b370966))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b371058 b371150) (joinCoverage b371242 b371335)) (joinCoverage (joinCoverage b371427 b371519) (joinCoverage b371611 b371704))) (joinCoverage (joinCoverage (joinCoverage b371796 b371888) (joinCoverage b371980 b372072)) (joinCoverage (joinCoverage b372164 b372256) (joinCoverage b372348 (joinCoverage b372441 b372533))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b372625 b372717) (joinCoverage b372810 b372902)) (joinCoverage (joinCoverage b372994 b373086) (joinCoverage b373179 (joinCoverage b373271 b373363)))) (joinCoverage (joinCoverage (joinCoverage b373455 b373547) (joinCoverage b373639 b373731)) (joinCoverage (joinCoverage b373823 b373916) (joinCoverage b374008 (joinCoverage b374100 b374192)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b374285 b374377) (joinCoverage b374469 b374561)) (joinCoverage (joinCoverage b374654 b374746) (joinCoverage b374838 (joinCoverage b374930 b375022)))) (joinCoverage (joinCoverage (joinCoverage b375114 b375206) (joinCoverage b375298 b375391)) (joinCoverage (joinCoverage b375483 b375575) (joinCoverage b375667 (joinCoverage b375760 b375852))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b375944 b376036) (joinCoverage b376129 b376221)) (joinCoverage (joinCoverage b376313 b376405) (joinCoverage b376498 (joinCoverage b376590 b376682)))) (joinCoverage (joinCoverage (joinCoverage b376774 b376867) (joinCoverage b376959 b377051)) (joinCoverage (joinCoverage b377143 b377236) (joinCoverage b377328 (joinCoverage b377420 b377512))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 364513 ≤ index 700000000/512 := by decide +kernel
private theorem starting_value : fast 700000000=36252931 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 700000000=36252931) (n : ℕ) (low : 700000000≤n) (bound : n≤725000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=700000000
    · rw [first,anchor]
      exact starting_value
    · have past : 700000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤725000000 by omega)
        have within : index n / 512 < 377605 := by omega
        have lower : index 700000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤725000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ700000000To725000000
