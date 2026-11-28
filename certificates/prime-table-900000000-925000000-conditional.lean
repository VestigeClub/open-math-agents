import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ900000000To925000000

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




private def radical : ℕ := 0xf8e9304585f0bf51734f96e606c9e6dfc8ce72966aecf9321b31486e06486a5b07cf659016c2e81acafc65c003e814d9753ae516e48121340c668589eae59da76a9c282575713c729a4e1fb97345c0e531807972d43ba769e5f36dfc78417394b7faf1c2b34e47c7703d4a115e8311e8d48f194475bd030c61d35d3fc87ea1dbba21d3bf37d695b8a39771323ec01877e70a4f0c9c9c577435a46fce755713540b8d594f8aedaae23580928b78a0ac12d0da50909768e37970e3dd0f17458caf43bc881b66768b4a1482c6d35aed2e8f2098fca07bb5cbe5de8c32dd27df0dead9fdf3a1281e32e47d3c5dc697a07018bd885825299578523efd038857cbff5864473ae4f74533a68cbaa43f8814b7f58d2d482970e79da80bcd2583648c2c63de6b2810a5f7672c07cbc18e559507d1eecd1475ea72097090812d8e7fcea7a224832980d53ccb7af7c1f662a93d0c1287335b1bbc11c90dc9d753b230e28c5d2403de321e89e97a8a26b46c14a4fd4a9419cd5d777630f4af3002cff87f75d925e2c71aa4fde773fe714b723015bed7de9ce7f721b41ecc933b81d6dd941b01e43c02d8b176bdc3c4393c147a70a35e99b35a1396ddd4a1f0c937887d38666a020fb58bc5f2f52c6d267ecd2c7890205f7139299fdde5d40e365734322d61da0103761b5065921179721fe8a0a069750af678c9615ceedbd35c4d14b47da643bcfecefe5192a855515612e168577fff3440aa932b234ecfbc340d21c2082afae5a02004db6aeee87a94f1e74b0830137cd516ccb42ed33957e9fbdf7ef433013094999a039b3b1f346c0e9ea90f0142cdcc47f5c9a5f4713c1214ffc1f07230aa927d18be6a0be13e3411e10700d660fc986a94577668df6f932a9736fbc17a20c5e3e8e94f6e38d12c4e9f967f4e86b4d2c55a30b91770f06e9c0cc458ef12ee7647a6be488c6c88b008afcdf6f1f4cc4df94eeb202dc56b7ae1ebd5e0d6cf1bcfc6ea95b1b05f41f08d9f5601290535cc205f84055d7e1836808ce7b5187d0aa6aaa9499f73921b7aa2b6e66155ec48d33ce2147bbacf60a0c25265e96ceb4d3c950c26b3556be9984869ed1854e01e286eed11531a33fe23ba5852a0a66efc16a603a4a31533531b1a1fceb6f9ade2af939c0b568bff65dc7160b154a4802e60299863d04622e152c6591f9ce9f67548c5fb6ca329ce69c6a80799362a38fbff60885a54ae60c97d0d6a9acc1f77226b2b716e881c3997aadcd5f86651f9049c4f5a1c1e3d210b896a65db608fea6be32c08eda593d2391e7edad313e9e9734f3451e6eba8e7ae4fc1553639c209f95e87a60ef869d847ecf29a9feef867ac7b1c752cf34415aa826f54c15a6f63b6cedc85f23cc2d11b75ca06ab3962ec217d0b47bd2eee684a22422983a08b149ae393ab7e392935ec2762440766d264e251450e1a1c71e43f935c05681ea97851bc2256bd09c0c756053c3d8609330db2f0b93738a1f86ac4a9c62b1f57f18828b4d4ac0d95cdd9056485d260e9a52bd8c36f0b46867f30c11d69f7b5cac7cdde809fd52f21135f12a11aa3d0d2cf8f633b34ed1907f3d16605c7a8db536eb69277a68dbf023acb2cc239ddcf55be56bf1659dc89ae328ad7bb5fb7e9c7b0290dad8046cad5d51760c4dc0be026304601f9fd72e6902c14812526a1e197e238eb062ccbca6732c80f69498402d3b25804d13e00ee18ec0a244953fed68b14567fe660dc5c241c19df5833f942b682fef859b56e3c029cd15be3ade99e5fc32803314712d67f3874f9c7c940d9be97fe693b8629675861d671a82714738266b4b2f535d3efe82d1c4dcefb743d438a3f537dd46acbe50b42af7e59ac17894e9307f32812a0c286b7d94b7213d75112ab20ba5937fe353b247c97fe3a7adf3539d870f287b48a4f6a56e92c1b7b080bbe71f580c83c79401eafb145043808b88633ea100bb07a66f7b89203309ae47668f2dda3a967d8cb9583dac1c5c5ce2ed5466bfd3134695869e4abb8510b5c0e5f7bf1dea8d530fc9d41236c5571eb17021fdee5928aae386b4d2823017162ea2a71c47f1f577a67f7cdfcb72f60ac8056c32d7d70ac52514eef6d86d254bfcec2692362d4f0da1d25ac76fcecd3d4ad75c103481ab32e19a514aa4ae07835713a81f43966c367eaa1b00e3a0cb5c4e40967b9c9bf813755a2edbb731f03d1d0dd9cddb4040808039402de11af318e8b5c09fcbec7f07013005ee9821fd7a2f6161b790ab94812c94f5976c00ff31aefead52f9d8ac23846c7868559512f9104d5b542b89f17bc68287795251de134b6e7bd4e8e33b9a9d2b4805c4bef960115497f1fefb460bddebe613f10a90819fcb1d1629fd152d09c81a99b430b0230a15e73847d7e9117fffa2f05403b54a1115e74b8602c924b2ae7b355c1cdf03e9eaeaf0631ff77a6df936cf7bd24e1d9195acd3d347e58aaf5fa16193ccab3c792a0f96894b1851f55eed4f2c82c109a14a09ba170dea8c6f8e75300ef83d4afd6666871abacdad5b36139e744c86a40ecaa2ba944506c7b219dd6f9a87dd7f38f74f2b35419f4e1671e276231c0baaed01e35aba4a88afa74fc23e529de34f187aef8b8410e00afd680d23952dda5344824e283e5d5a60267cb1b7b2e2d8521b2e1e9dfa44addaf6be88d690a7ac436dd5041ed40d3fc1305d0ec9e9a238e8c786cb5fedc5e2ef30a3adc3dd2504a8d57a46ba4c39dfa67f82ba63104c7502a4b86608353fe340bfd4e156f9ef4e388cadb41fcdffa8681d624d3bf33062a563fa3a7fb542f22751f1b50dfa88230c03323e0ac6d667c59ef4da0811165e8d13aaa159a26a01601f1fc8a145698b7899fd47f9be857451287e35e785892b97e904b71fd68f4dec3ba45a906ee7dfe74acd2300c3b2c5fe0755b6db071de1ff201a2f2bf6472dc9a62224fea51382fbea1c71b7c5c1d64bd02cfab36bfebf5aaa50bb8c201d35a54425a6c7b515f4abf2aef5ac36269079a93e1e3215e025a3c8e66cf01a65973acd38ab284bb63fb7981ccd93e33059258aff55782943d1067d9deff27b7584aca53fc9135d59470503337dd5c459db0637041e7e754a1b364665c0147f094d54d8a8fdca85bc991993c80d8df1a998abc3c3fcc670bb329936cc2111682974d911f11f4f07f649969c9c5675a0502024c6613154856cf1189d7b7ea966a6861ffcfcc13e5c334a7acc6193f66fbb7e172868a151c8010b1d8183e171b8b8ffe1c337b443990a4e52966594fd81ba96296f8c70e3fb4f435ad7da8a234b7ccb012494e017d1614a23b3bdcffba167fe6d7fd08302b389784b811691f46cf00e0335d6b35f56f975a889facce11efc3ced7ac3cbc1c9d7e0ec086701cf2503fb48bb4d35a32472794efac8e68521a9c19abe9f67aa1305fc1cdbe1b7c026474d46b2ce52e5c8ddb1bdcc02e4769a4cd5b3119b6e83587c12036d920091cbc94a40583c9dc4999bc6c4f24525c68fe08a69cb9f737c4def264977a949f4cf55e50883230debca97c458bc043c2e90ac460b516a2b8fc72a7ba346e8dbe603c5e37910aebac9f930065a83dbaae4e37144da845d09a6bf18f00a0ae4b0eac7fbcc06d0aa6e35273558f9e949d552800c24b9f2d5694713a28960f80fb69b5b566e9d5c8668086cd249370d7efe173f9b57b9c8d35f8aa9b0c18a986f3b897d272ee062df7ab8c0825741dec49a76b43257d92016107bdbbe93ae4c0143ffaad8957eeaa329c4e42c53b1a3f22d69fb8f1796ba2b6e90d6f5a8a14b9fc450b45aa4a754daffd75bb151e0d4ebd0c8807031401c1d214784f67ec5eb53a0d82192f97bd51d9e963ad98bfd4b72622cbfbb8e2e774f5889b2f62cb4c7a31c7ea799c5896925cc661773fb0e94c827c7caf6949f50a52d82428edb4a44a6423cb4409fa3b834bbc75fabf4309315be287a2d60677140aa0e141ed3f858e44e2a3379becc21e00ffd2e6dbc8f69d1e20d4e349ba7b0b31986af02b39a710a0ad7f4ac974cda5c2655b3ee059ca89bd9f33678701d854f43d219ea4a398be612c6d2c7169d536d47943361683bdf0853f13f99dfeb7560f9ea4d43fa1bc4474e11ffc6068c559ee2a6fb83fa11aa4e998e7675555911a5e63ff5978a0f20b29082a9077d55a6aa4b43dafce8b818caaeb8dfadc93a4bc798d07a11a8236be933d5c96c8502d37ae45ae0221b84d0c9db59b7c5788a20151a4e0fa1c9605670caceddba9defae12ab6e8b44bf3987110b7a5b96d240ee23d2c05ddb354fd7077d8bca0753de468c71c74ed980b306e13946ffa33680e425dac1173a2e41f603b801af34c620b1eca1ffb3709a17336d2fd3a64222f13a4da293fa7fa128af948d0445a0f8009d14341811734479f5c4385ba5d4f5ce52b430d94e3fd9a29832e28e18e92726e2ed3bb515fcc74e340d02e2b31751cdc4d250fdd0a72e4434e8573cdc7aa24326df8051e4f2d51bd29a1b0bfe5c84bf5de781c138101ba76d2e1b170f0ecf756255f4ee68fd90ccac2ef3a9a62a45f5d2ca8ff6888cd5c932bd4e1da30847f9acd8707d8fa70f59b25d40d2e7a2aa6f6638f291ccb430c19ee1b1cf8478453472d48f110014dc790dcbe3fd30d07ebbcb70a0747d1deaaa20b29f80a09b6a8f9e8ee6c36331fbd6aac693869a1892636883e4c1e3a023de0f12c73a4105c864929dd5a3794d94b1d259aff2e2cd1881d477e79747aa095b06a89d24f7f86d2731ecc645e1bde85ec1a6fa5b97272453d8d4cc5e20a098db5def09e365db0c870a55b9b8047b0fd982bdb49dec92c33ee9fb4c342f42d6c56ae23c6ec9a09611b379589f1cca4ea429afb58351c41778c544541356559e07d29cfaf82b7da36aee3f7ca9fa1dcc784c1357706fabf118ceeb6f89535d35798a2cf64435afeaf61e63fbf55d6fc8f1e513e04efe6bb37c1e175f463d46b05974a556dbd3f2c38d2d6eb31135b21b653007ffdd5ac0c3d502bdf9cccd72140a1a1dc8613a6c52e3ac4c14b66510cfff20c68ab0cc0f099031c8335837be1383642e8d1f7d6643936035c445a9a534287834c3ce67806f88549281e7688bfe37913ba30604a2528cddb0fb27797d7f4aa3729cbffc3ecce1b5cf6cda8dffe6d8db4ba747d08517fe332fd2a7b7e1a0a852d11850b70f284cf4a479bf05c9776b40b9ce402dfd4a1804e3e07435c0caecf97a5e7cb9fd4a3e5242f1dcb110807a38556fb4ea2b600fa20ee4c6f46304bdee155aa2bf603de94ec2dd08bbbde20a4f0032713d3df797e84e38883497905dbbef408cc2575f9cd30c620b18b94e15670bacc8a5ed87c825e4218532f036faa9117a53dadcc63b717a37f22dca78c9086602478c5c59dea4e57c06143195931cde824e0683c35e80bbdcb80535fdebab4e792e2a58b460ce0e3663ed48fa80c43f51a99d05ee619e4d60660cf6ca5ab287b24fac2d24ba92707a1b70515e757816dd62523ce54249ce052250a0b025896738a16e2f24f47845e8b72bfee1c0063f1e21851d935149207bd0998a2bd9fcbfd911d10679485556916b5bb5206bdfcb780b941058b74d18b69fe16e2796e8352951dbe6b5c64bfa8de49764be3ccf798b1dafb945e49dfbd4bb9da93f62b67a5df0d5f9679de9ad47f6c4e3ba8ba63c1e738d34d76ae4324138ced31812f25243a8b60eacaa78e2f37d107f8d672448524ce93d3fcbc8cc5df9411f5e4a386aea91e0c58f693b3f8af4bcf0c61327f14050ec95b3a7e6e7b7dd17a09f8de1d2260da3c9f73956c6fb9469bd5a4471030f04cf4e507a17e1fe8da6d25cbc654e560259c5c6a23ade9b160fd0090817f613987e280408160181b50e1939cb34d86b70a256de025a8880c423093027beaf0ceb884739dc7d8f76d22bd50b35ac615b56139198ed9fbb5e8b9c4f676fac62b0d064c0f12d08e154e0f774cfe0c936ce60ae41b8dd0d8f3ef9d1740f89df1da96b8fa8219f6cfeef0a2a861bf72ae535d506ac503c4fd8b1773259aa32fbdc395e54c0a5b27e7879187296a93196c36cbf4483d7f5f13cc9f338a31d12cd536019b75567cf7586660d08b007d3c82e2b768eb941b02fd36f5df43bd07f902fb71a0cff6551f0024b0d7b9221b49415761f9445c60721bc6dde8d7b3bbb3b17724f04ea9b81f2a285e499d78b967231a64b8a84379c470ab6cb14b1cbc7c884b6a9c47bfbd860df07b572b56d2d97af7927bca750a6b677dc404b136e050d23dac18fa1cf9455973f36fd33d4796f3b36b08311d5bc2ba6fc3bf1dba4590b929c8540e2fd19cfb34ef4e87b2ff86aca85d2788e438a6e300231f62dd620c4c70965bec29dbb1da2eb5ef8f8d0c85dcd9f937a1406b2de6fdbe1990582e930d8bfa08f022e44eb65a900fdd33f7852b50297b427a39ac8c09d847ddb8bf3959a04450db5b29515351b09372f06945a0c1f6e5b0ef73da6ac8b11fcf774254b843ba428c185c2061e1bd6613f56909099c31623a2d45185530accaa8a1629d59a7c4accb8856b54a4dbd27ee1d1a5c47639d546b5d6a88b2bd435a4cd42bcfaae99d064a46cea1d240211c53eca4bc7ee62dfbc7407666e797b31b92f085cc09b6984d06a2d26c863bcf4228fc36cb058bfa161f55923d6afa824da553b98c18cced2fe6f577a01b7291286eb812681cccebbc225295c2d480d8c4838da0c1ea3271b5223d3e1194202a2c3de9d52fc144fb93d7a387247f61b100e834db4a4386c20cddd0c99929036853eccdcbcbff8b9ced2bcf8f04325cf780d1aa7f31af2cb1dcb3ec8c57a24dadbd97fa2e55cb1ea2e9b907032329babdb4c0c371002022f7a79634ca486a2310756a8c3893628aa0e00cbb5750dd3ce65811e20709c73e8149db0c40b47c1cf8b4db3ee9ed1127a33766f284f2a02c9088a699c86197e1d9c166e2fa6fc23edbd33d06f4ec17cde94ee1dfa7b3fa0019d68f5dbbc77402cd8ff4a22fe73826e5c3d7313338a7bc48f7a49166914581bc673d07dedb6c244400bc763031c2bba5c8ad1855c23a2c6114021a9404e986d8d0b718a8bc3090bcd5cf5d6a000054c424c8dcbf449401390f5aa06fd7f524fbc54dbd0304615e4bfaa7210c177bd741e80255c406dfd3c9821323f11857f308fdbffac9a6031bb2decac180edf8921281dbba510f5a0b9a2bcc48608ec0aefc436f5d42c4b5a78decd51d8907e25af832492d06e964acab84713152eb3ddfdde5437e89976564eaf260dbcca17499430a48e41159cc1e6113d6579b71248b1e1e62d716372d94af115a8996b69ce48706bd202abf86eeb7323a964e3552a792e2f19622b415846e4576c0faa47e15b05c76c0fc59b539b041c8fe342358b9aa700e431c37c5ac98d5e19aa30e0f49bd4c57a456cb7e5b10df491454884a21c61aed1ff5eb47f620728bc8664529028fba7a5ee98d6da9213bf992a067d0e476f83aa22e93d7b2081f77d3720adff91c965f66552ddfaaa4219f76e5b9f430c93b34dff3f416c955a970b02760b6051177aa4fb8568ac69056933cfb01ebac675dae9ff57fc2e181e5fce89067aa89560a627f19184d6be95faebc3b8af74f369d52b5e7734a7a2822b7b847ac41d6eacff9583713940d908e0de8bda14d9cfb6a9c5f7e2b816ed109ff5c448e40fbfe105cdc4fc22d2

private def light (n : ℕ) : Bool :=
  if n≤174 then decide n.Prime else n.gcd 6425425663347064733166342506526881458348150508160426541851455077080468607287618805557105047805861775775912692278116502462953528378524937389131268196460620409529506610362739317326974626432136901748478076969280322196922086635340638923811068556323532935233826663322108954882867200000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤30413) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 174 = 6425425663347064733166342506526881458348150508160426541851455077080468607287618805557105047805861775775912692278116502462953528378524937389131268196460620409529506610362739317326974626432136901748478076969280322196922086635340638923811068556323532935233826663322108954882867200000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 174 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤30413 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 59 := by unfold smallValid; decide +kernel

private theorem sp59 : smallValid 59 59 := by unfold smallValid; decide +kernel

private theorem sp118 : smallValid 118 59 := by unfold smallValid; decide +kernel

private theorem sp177 : smallValid 177 60 := by unfold smallValid; decide +kernel

private theorem sp237 : smallValid 237 59 := by unfold smallValid; decide +kernel

private theorem sp296 : smallValid 296 60 := by unfold smallValid; decide +kernel

private theorem sp356 : smallValid 356 59 := by unfold smallValid; decide +kernel

private theorem sp415 : smallValid 415 60 := by unfold smallValid; decide +kernel

private theorem sp475 : smallValid 475 59 := by unfold smallValid; decide +kernel

private theorem sp534 : smallValid 534 59 := by unfold smallValid; decide +kernel

private theorem sp593 : smallValid 593 59 := by unfold smallValid; decide +kernel

private theorem sp652 : smallValid 652 60 := by unfold smallValid; decide +kernel

private theorem sp712 : smallValid 712 59 := by unfold smallValid; decide +kernel

private theorem sp771 : smallValid 771 60 := by unfold smallValid; decide +kernel

private theorem sp831 : smallValid 831 59 := by unfold smallValid; decide +kernel

private theorem sp890 : smallValid 890 60 := by unfold smallValid; decide +kernel

private theorem sp950 : smallValid 950 59 := by unfold smallValid; decide +kernel

private theorem sp1009 : smallValid 1009 59 := by unfold smallValid; decide +kernel

private theorem sp1068 : smallValid 1068 59 := by unfold smallValid; decide +kernel

private theorem sp1127 : smallValid 1127 60 := by unfold smallValid; decide +kernel

private theorem sp1187 : smallValid 1187 59 := by unfold smallValid; decide +kernel

private theorem sp1246 : smallValid 1246 60 := by unfold smallValid; decide +kernel

private theorem sp1306 : smallValid 1306 59 := by unfold smallValid; decide +kernel

private theorem sp1365 : smallValid 1365 60 := by unfold smallValid; decide +kernel

private theorem sp1425 : smallValid 1425 59 := by unfold smallValid; decide +kernel

private theorem sp1484 : smallValid 1484 59 := by unfold smallValid; decide +kernel

private theorem sp1543 : smallValid 1543 59 := by unfold smallValid; decide +kernel

private theorem sp1602 : smallValid 1602 60 := by unfold smallValid; decide +kernel

private theorem sp1662 : smallValid 1662 59 := by unfold smallValid; decide +kernel

private theorem sp1721 : smallValid 1721 60 := by unfold smallValid; decide +kernel

private theorem sp1781 : smallValid 1781 59 := by unfold smallValid; decide +kernel

private theorem sp1840 : smallValid 1840 60 := by unfold smallValid; decide +kernel

private theorem sp1900 : smallValid 1900 59 := by unfold smallValid; decide +kernel

private theorem sp1959 : smallValid 1959 59 := by unfold smallValid; decide +kernel

private theorem sp2018 : smallValid 2018 59 := by unfold smallValid; decide +kernel

private theorem sp2077 : smallValid 2077 60 := by unfold smallValid; decide +kernel

private theorem sp2137 : smallValid 2137 59 := by unfold smallValid; decide +kernel

private theorem sp2196 : smallValid 2196 60 := by unfold smallValid; decide +kernel

private theorem sp2256 : smallValid 2256 59 := by unfold smallValid; decide +kernel

private theorem sp2315 : smallValid 2315 60 := by unfold smallValid; decide +kernel

private theorem sp2375 : smallValid 2375 59 := by unfold smallValid; decide +kernel

private theorem sp2434 : smallValid 2434 59 := by unfold smallValid; decide +kernel

private theorem sp2493 : smallValid 2493 59 := by unfold smallValid; decide +kernel

private theorem sp2552 : smallValid 2552 60 := by unfold smallValid; decide +kernel

private theorem sp2612 : smallValid 2612 59 := by unfold smallValid; decide +kernel

private theorem sp2671 : smallValid 2671 60 := by unfold smallValid; decide +kernel

private theorem sp2731 : smallValid 2731 59 := by unfold smallValid; decide +kernel

private theorem sp2790 : smallValid 2790 60 := by unfold smallValid; decide +kernel

private theorem sp2850 : smallValid 2850 59 := by unfold smallValid; decide +kernel

private theorem sp2909 : smallValid 2909 59 := by unfold smallValid; decide +kernel

private theorem sp2968 : smallValid 2968 59 := by unfold smallValid; decide +kernel

private theorem sp3027 : smallValid 3027 60 := by unfold smallValid; decide +kernel

private theorem sp3087 : smallValid 3087 59 := by unfold smallValid; decide +kernel

private theorem sp3146 : smallValid 3146 60 := by unfold smallValid; decide +kernel

private theorem sp3206 : smallValid 3206 59 := by unfold smallValid; decide +kernel

private theorem sp3265 : smallValid 3265 60 := by unfold smallValid; decide +kernel

private theorem sp3325 : smallValid 3325 59 := by unfold smallValid; decide +kernel

private theorem sp3384 : smallValid 3384 60 := by unfold smallValid; decide +kernel

private theorem sp3444 : smallValid 3444 59 := by unfold smallValid; decide +kernel

private theorem sp3503 : smallValid 3503 60 := by unfold smallValid; decide +kernel

private theorem sp3563 : smallValid 3563 59 := by unfold smallValid; decide +kernel

private theorem sp3622 : smallValid 3622 60 := by unfold smallValid; decide +kernel

private theorem sp3682 : smallValid 3682 59 := by unfold smallValid; decide +kernel

private theorem sp3741 : smallValid 3741 60 := by unfold smallValid; decide +kernel

private theorem sp3801 : smallValid 3801 59 := by unfold smallValid; decide +kernel

private theorem sp3860 : smallValid 3860 59 := by unfold smallValid; decide +kernel

private theorem sp3919 : smallValid 3919 59 := by unfold smallValid; decide +kernel

private theorem sp3978 : smallValid 3978 60 := by unfold smallValid; decide +kernel

private theorem sp4038 : smallValid 4038 59 := by unfold smallValid; decide +kernel

private theorem sp4097 : smallValid 4097 60 := by unfold smallValid; decide +kernel

private theorem sp4157 : smallValid 4157 59 := by unfold smallValid; decide +kernel

private theorem sp4216 : smallValid 4216 60 := by unfold smallValid; decide +kernel

private theorem sp4276 : smallValid 4276 59 := by unfold smallValid; decide +kernel

private theorem sp4335 : smallValid 4335 59 := by unfold smallValid; decide +kernel

private theorem sp4394 : smallValid 4394 59 := by unfold smallValid; decide +kernel

private theorem sp4453 : smallValid 4453 60 := by unfold smallValid; decide +kernel

private theorem sp4513 : smallValid 4513 59 := by unfold smallValid; decide +kernel

private theorem sp4572 : smallValid 4572 60 := by unfold smallValid; decide +kernel

private theorem sp4632 : smallValid 4632 59 := by unfold smallValid; decide +kernel

private theorem sp4691 : smallValid 4691 60 := by unfold smallValid; decide +kernel

private theorem sp4751 : smallValid 4751 59 := by unfold smallValid; decide +kernel

private theorem sp4810 : smallValid 4810 59 := by unfold smallValid; decide +kernel

private theorem sp4869 : smallValid 4869 59 := by unfold smallValid; decide +kernel

private theorem sp4928 : smallValid 4928 60 := by unfold smallValid; decide +kernel

private theorem sp4988 : smallValid 4988 59 := by unfold smallValid; decide +kernel

private theorem sp5047 : smallValid 5047 60 := by unfold smallValid; decide +kernel

private theorem sp5107 : smallValid 5107 59 := by unfold smallValid; decide +kernel

private theorem sp5166 : smallValid 5166 60 := by unfold smallValid; decide +kernel

private theorem sp5226 : smallValid 5226 59 := by unfold smallValid; decide +kernel

private theorem sp5285 : smallValid 5285 60 := by unfold smallValid; decide +kernel

private theorem sp5345 : smallValid 5345 59 := by unfold smallValid; decide +kernel

private theorem sp5404 : smallValid 5404 60 := by unfold smallValid; decide +kernel

private theorem sp5464 : smallValid 5464 59 := by unfold smallValid; decide +kernel

private theorem sp5523 : smallValid 5523 60 := by unfold smallValid; decide +kernel

private theorem sp5583 : smallValid 5583 59 := by unfold smallValid; decide +kernel

private theorem sp5642 : smallValid 5642 60 := by unfold smallValid; decide +kernel

private theorem sp5702 : smallValid 5702 59 := by unfold smallValid; decide +kernel

private theorem sp5761 : smallValid 5761 59 := by unfold smallValid; decide +kernel

private theorem sp5820 : smallValid 5820 59 := by unfold smallValid; decide +kernel

private theorem sp5879 : smallValid 5879 60 := by unfold smallValid; decide +kernel

private theorem sp5939 : smallValid 5939 59 := by unfold smallValid; decide +kernel

private theorem sp5998 : smallValid 5998 60 := by unfold smallValid; decide +kernel

private theorem sp6058 : smallValid 6058 59 := by unfold smallValid; decide +kernel

private theorem sp6117 : smallValid 6117 60 := by unfold smallValid; decide +kernel

private theorem sp6177 : smallValid 6177 59 := by unfold smallValid; decide +kernel

private theorem sp6236 : smallValid 6236 59 := by unfold smallValid; decide +kernel

private theorem sp6295 : smallValid 6295 59 := by unfold smallValid; decide +kernel

private theorem sp6354 : smallValid 6354 60 := by unfold smallValid; decide +kernel

private theorem sp6414 : smallValid 6414 59 := by unfold smallValid; decide +kernel

private theorem sp6473 : smallValid 6473 60 := by unfold smallValid; decide +kernel

private theorem sp6533 : smallValid 6533 59 := by unfold smallValid; decide +kernel

private theorem sp6592 : smallValid 6592 60 := by unfold smallValid; decide +kernel

private theorem sp6652 : smallValid 6652 59 := by unfold smallValid; decide +kernel

private theorem sp6711 : smallValid 6711 59 := by unfold smallValid; decide +kernel

private theorem sp6770 : smallValid 6770 59 := by unfold smallValid; decide +kernel

private theorem sp6829 : smallValid 6829 60 := by unfold smallValid; decide +kernel

private theorem sp6889 : smallValid 6889 59 := by unfold smallValid; decide +kernel

private theorem sp6948 : smallValid 6948 60 := by unfold smallValid; decide +kernel

private theorem sp7008 : smallValid 7008 59 := by unfold smallValid; decide +kernel

private theorem sp7067 : smallValid 7067 60 := by unfold smallValid; decide +kernel

private theorem sp7127 : smallValid 7127 59 := by unfold smallValid; decide +kernel

private theorem sp7186 : smallValid 7186 60 := by unfold smallValid; decide +kernel

private theorem sp7246 : smallValid 7246 59 := by unfold smallValid; decide +kernel

private theorem sp7305 : smallValid 7305 60 := by unfold smallValid; decide +kernel

private theorem sp7365 : smallValid 7365 59 := by unfold smallValid; decide +kernel

private theorem sp7424 : smallValid 7424 60 := by unfold smallValid; decide +kernel

private theorem sp7484 : smallValid 7484 59 := by unfold smallValid; decide +kernel

private theorem sp7543 : smallValid 7543 60 := by unfold smallValid; decide +kernel

private theorem sp7603 : smallValid 7603 59 := by unfold smallValid; decide +kernel

private theorem sp7662 : smallValid 7662 59 := by unfold smallValid; decide +kernel

private theorem sp7721 : smallValid 7721 59 := by unfold smallValid; decide +kernel

private theorem sp7780 : smallValid 7780 60 := by unfold smallValid; decide +kernel

private theorem sp7840 : smallValid 7840 59 := by unfold smallValid; decide +kernel

private theorem sp7899 : smallValid 7899 60 := by unfold smallValid; decide +kernel

private theorem sp7959 : smallValid 7959 59 := by unfold smallValid; decide +kernel

private theorem sp8018 : smallValid 8018 60 := by unfold smallValid; decide +kernel

private theorem sp8078 : smallValid 8078 59 := by unfold smallValid; decide +kernel

private theorem sp8137 : smallValid 8137 59 := by unfold smallValid; decide +kernel

private theorem sp8196 : smallValid 8196 59 := by unfold smallValid; decide +kernel

private theorem sp8255 : smallValid 8255 60 := by unfold smallValid; decide +kernel

private theorem sp8315 : smallValid 8315 59 := by unfold smallValid; decide +kernel

private theorem sp8374 : smallValid 8374 60 := by unfold smallValid; decide +kernel

private theorem sp8434 : smallValid 8434 59 := by unfold smallValid; decide +kernel

private theorem sp8493 : smallValid 8493 60 := by unfold smallValid; decide +kernel

private theorem sp8553 : smallValid 8553 59 := by unfold smallValid; decide +kernel

private theorem sp8612 : smallValid 8612 59 := by unfold smallValid; decide +kernel

private theorem sp8671 : smallValid 8671 59 := by unfold smallValid; decide +kernel

private theorem sp8730 : smallValid 8730 60 := by unfold smallValid; decide +kernel

private theorem sp8790 : smallValid 8790 59 := by unfold smallValid; decide +kernel

private theorem sp8849 : smallValid 8849 60 := by unfold smallValid; decide +kernel

private theorem sp8909 : smallValid 8909 59 := by unfold smallValid; decide +kernel

private theorem sp8968 : smallValid 8968 60 := by unfold smallValid; decide +kernel

private theorem sp9028 : smallValid 9028 59 := by unfold smallValid; decide +kernel

private theorem sp9087 : smallValid 9087 60 := by unfold smallValid; decide +kernel

private theorem sp9147 : smallValid 9147 59 := by unfold smallValid; decide +kernel

private theorem sp9206 : smallValid 9206 60 := by unfold smallValid; decide +kernel

private theorem sp9266 : smallValid 9266 59 := by unfold smallValid; decide +kernel

private theorem sp9325 : smallValid 9325 60 := by unfold smallValid; decide +kernel

private theorem sp9385 : smallValid 9385 59 := by unfold smallValid; decide +kernel

private theorem sp9444 : smallValid 9444 60 := by unfold smallValid; decide +kernel

private theorem sp9504 : smallValid 9504 59 := by unfold smallValid; decide +kernel

private theorem sp9563 : smallValid 9563 59 := by unfold smallValid; decide +kernel

private theorem sp9622 : smallValid 9622 59 := by unfold smallValid; decide +kernel

private theorem sp9681 : smallValid 9681 60 := by unfold smallValid; decide +kernel

private theorem sp9741 : smallValid 9741 59 := by unfold smallValid; decide +kernel

private theorem sp9800 : smallValid 9800 60 := by unfold smallValid; decide +kernel

private theorem sp9860 : smallValid 9860 59 := by unfold smallValid; decide +kernel

private theorem sp9919 : smallValid 9919 60 := by unfold smallValid; decide +kernel

private theorem sp9979 : smallValid 9979 59 := by unfold smallValid; decide +kernel

private theorem sp10038 : smallValid 10038 59 := by unfold smallValid; decide +kernel

private theorem sp10097 : smallValid 10097 59 := by unfold smallValid; decide +kernel

private theorem sp10156 : smallValid 10156 60 := by unfold smallValid; decide +kernel

private theorem sp10216 : smallValid 10216 59 := by unfold smallValid; decide +kernel

private theorem sp10275 : smallValid 10275 60 := by unfold smallValid; decide +kernel

private theorem sp10335 : smallValid 10335 59 := by unfold smallValid; decide +kernel

private theorem sp10394 : smallValid 10394 60 := by unfold smallValid; decide +kernel

private theorem sp10454 : smallValid 10454 59 := by unfold smallValid; decide +kernel

private theorem sp10513 : smallValid 10513 59 := by unfold smallValid; decide +kernel

private theorem sp10572 : smallValid 10572 59 := by unfold smallValid; decide +kernel

private theorem sp10631 : smallValid 10631 60 := by unfold smallValid; decide +kernel

private theorem sp10691 : smallValid 10691 59 := by unfold smallValid; decide +kernel

private theorem sp10750 : smallValid 10750 60 := by unfold smallValid; decide +kernel

private theorem sp10810 : smallValid 10810 59 := by unfold smallValid; decide +kernel

private theorem sp10869 : smallValid 10869 60 := by unfold smallValid; decide +kernel

private theorem sp10929 : smallValid 10929 59 := by unfold smallValid; decide +kernel

private theorem sp10988 : smallValid 10988 60 := by unfold smallValid; decide +kernel

private theorem sp11048 : smallValid 11048 59 := by unfold smallValid; decide +kernel

private theorem sp11107 : smallValid 11107 60 := by unfold smallValid; decide +kernel

private theorem sp11167 : smallValid 11167 59 := by unfold smallValid; decide +kernel

private theorem sp11226 : smallValid 11226 60 := by unfold smallValid; decide +kernel

private theorem sp11286 : smallValid 11286 59 := by unfold smallValid; decide +kernel

private theorem sp11345 : smallValid 11345 60 := by unfold smallValid; decide +kernel

private theorem sp11405 : smallValid 11405 59 := by unfold smallValid; decide +kernel

private theorem sp11464 : smallValid 11464 59 := by unfold smallValid; decide +kernel

private theorem sp11523 : smallValid 11523 59 := by unfold smallValid; decide +kernel

private theorem sp11582 : smallValid 11582 60 := by unfold smallValid; decide +kernel

private theorem sp11642 : smallValid 11642 59 := by unfold smallValid; decide +kernel

private theorem sp11701 : smallValid 11701 60 := by unfold smallValid; decide +kernel

private theorem sp11761 : smallValid 11761 59 := by unfold smallValid; decide +kernel

private theorem sp11820 : smallValid 11820 60 := by unfold smallValid; decide +kernel

private theorem sp11880 : smallValid 11880 59 := by unfold smallValid; decide +kernel

private theorem sp11939 : smallValid 11939 59 := by unfold smallValid; decide +kernel

private theorem sp11998 : smallValid 11998 59 := by unfold smallValid; decide +kernel

private theorem sp12057 : smallValid 12057 60 := by unfold smallValid; decide +kernel

private theorem sp12117 : smallValid 12117 59 := by unfold smallValid; decide +kernel

private theorem sp12176 : smallValid 12176 60 := by unfold smallValid; decide +kernel

private theorem sp12236 : smallValid 12236 59 := by unfold smallValid; decide +kernel

private theorem sp12295 : smallValid 12295 60 := by unfold smallValid; decide +kernel

private theorem sp12355 : smallValid 12355 59 := by unfold smallValid; decide +kernel

private theorem sp12414 : smallValid 12414 59 := by unfold smallValid; decide +kernel

private theorem sp12473 : smallValid 12473 59 := by unfold smallValid; decide +kernel

private theorem sp12532 : smallValid 12532 60 := by unfold smallValid; decide +kernel

private theorem sp12592 : smallValid 12592 59 := by unfold smallValid; decide +kernel

private theorem sp12651 : smallValid 12651 60 := by unfold smallValid; decide +kernel

private theorem sp12711 : smallValid 12711 59 := by unfold smallValid; decide +kernel

private theorem sp12770 : smallValid 12770 60 := by unfold smallValid; decide +kernel

private theorem sp12830 : smallValid 12830 59 := by unfold smallValid; decide +kernel

private theorem sp12889 : smallValid 12889 60 := by unfold smallValid; decide +kernel

private theorem sp12949 : smallValid 12949 59 := by unfold smallValid; decide +kernel

private theorem sp13008 : smallValid 13008 60 := by unfold smallValid; decide +kernel

private theorem sp13068 : smallValid 13068 59 := by unfold smallValid; decide +kernel

private theorem sp13127 : smallValid 13127 60 := by unfold smallValid; decide +kernel

private theorem sp13187 : smallValid 13187 59 := by unfold smallValid; decide +kernel

private theorem sp13246 : smallValid 13246 60 := by unfold smallValid; decide +kernel

private theorem sp13306 : smallValid 13306 59 := by unfold smallValid; decide +kernel

private theorem sp13365 : smallValid 13365 59 := by unfold smallValid; decide +kernel

private theorem sp13424 : smallValid 13424 59 := by unfold smallValid; decide +kernel

private theorem sp13483 : smallValid 13483 60 := by unfold smallValid; decide +kernel

private theorem sp13543 : smallValid 13543 59 := by unfold smallValid; decide +kernel

private theorem sp13602 : smallValid 13602 60 := by unfold smallValid; decide +kernel

private theorem sp13662 : smallValid 13662 59 := by unfold smallValid; decide +kernel

private theorem sp13721 : smallValid 13721 60 := by unfold smallValid; decide +kernel

private theorem sp13781 : smallValid 13781 59 := by unfold smallValid; decide +kernel

private theorem sp13840 : smallValid 13840 59 := by unfold smallValid; decide +kernel

private theorem sp13899 : smallValid 13899 59 := by unfold smallValid; decide +kernel

private theorem sp13958 : smallValid 13958 60 := by unfold smallValid; decide +kernel

private theorem sp14018 : smallValid 14018 59 := by unfold smallValid; decide +kernel

private theorem sp14077 : smallValid 14077 60 := by unfold smallValid; decide +kernel

private theorem sp14137 : smallValid 14137 59 := by unfold smallValid; decide +kernel

private theorem sp14196 : smallValid 14196 60 := by unfold smallValid; decide +kernel

private theorem sp14256 : smallValid 14256 59 := by unfold smallValid; decide +kernel

private theorem sp14315 : smallValid 14315 59 := by unfold smallValid; decide +kernel

private theorem sp14374 : smallValid 14374 59 := by unfold smallValid; decide +kernel

private theorem sp14433 : smallValid 14433 60 := by unfold smallValid; decide +kernel

private theorem sp14493 : smallValid 14493 59 := by unfold smallValid; decide +kernel

private theorem sp14552 : smallValid 14552 60 := by unfold smallValid; decide +kernel

private theorem sp14612 : smallValid 14612 59 := by unfold smallValid; decide +kernel

private theorem sp14671 : smallValid 14671 60 := by unfold smallValid; decide +kernel

private theorem sp14731 : smallValid 14731 59 := by unfold smallValid; decide +kernel

private theorem sp14790 : smallValid 14790 60 := by unfold smallValid; decide +kernel

private theorem sp14850 : smallValid 14850 59 := by unfold smallValid; decide +kernel

private theorem sp14909 : smallValid 14909 60 := by unfold smallValid; decide +kernel

private theorem sp14969 : smallValid 14969 59 := by unfold smallValid; decide +kernel

private theorem sp15028 : smallValid 15028 60 := by unfold smallValid; decide +kernel

private theorem sp15088 : smallValid 15088 59 := by unfold smallValid; decide +kernel

private theorem sp15147 : smallValid 15147 60 := by unfold smallValid; decide +kernel

private theorem sp15207 : smallValid 15207 59 := by unfold smallValid; decide +kernel

private theorem sp15266 : smallValid 15266 59 := by unfold smallValid; decide +kernel

private theorem sp15325 : smallValid 15325 59 := by unfold smallValid; decide +kernel

private theorem sp15384 : smallValid 15384 60 := by unfold smallValid; decide +kernel

private theorem sp15444 : smallValid 15444 59 := by unfold smallValid; decide +kernel

private theorem sp15503 : smallValid 15503 60 := by unfold smallValid; decide +kernel

private theorem sp15563 : smallValid 15563 59 := by unfold smallValid; decide +kernel

private theorem sp15622 : smallValid 15622 60 := by unfold smallValid; decide +kernel

private theorem sp15682 : smallValid 15682 59 := by unfold smallValid; decide +kernel

private theorem sp15741 : smallValid 15741 59 := by unfold smallValid; decide +kernel

private theorem sp15800 : smallValid 15800 59 := by unfold smallValid; decide +kernel

private theorem sp15859 : smallValid 15859 60 := by unfold smallValid; decide +kernel

private theorem sp15919 : smallValid 15919 59 := by unfold smallValid; decide +kernel

private theorem sp15978 : smallValid 15978 60 := by unfold smallValid; decide +kernel

private theorem sp16038 : smallValid 16038 59 := by unfold smallValid; decide +kernel

private theorem sp16097 : smallValid 16097 60 := by unfold smallValid; decide +kernel

private theorem sp16157 : smallValid 16157 59 := by unfold smallValid; decide +kernel

private theorem sp16216 : smallValid 16216 59 := by unfold smallValid; decide +kernel

private theorem sp16275 : smallValid 16275 59 := by unfold smallValid; decide +kernel

private theorem sp16334 : smallValid 16334 60 := by unfold smallValid; decide +kernel

private theorem sp16394 : smallValid 16394 59 := by unfold smallValid; decide +kernel

private theorem sp16453 : smallValid 16453 60 := by unfold smallValid; decide +kernel

private theorem sp16513 : smallValid 16513 59 := by unfold smallValid; decide +kernel

private theorem sp16572 : smallValid 16572 60 := by unfold smallValid; decide +kernel

private theorem sp16632 : smallValid 16632 59 := by unfold smallValid; decide +kernel

private theorem sp16691 : smallValid 16691 59 := by unfold smallValid; decide +kernel

private theorem sp16750 : smallValid 16750 59 := by unfold smallValid; decide +kernel

private theorem sp16809 : smallValid 16809 60 := by unfold smallValid; decide +kernel

private theorem sp16869 : smallValid 16869 59 := by unfold smallValid; decide +kernel

private theorem sp16928 : smallValid 16928 60 := by unfold smallValid; decide +kernel

private theorem sp16988 : smallValid 16988 59 := by unfold smallValid; decide +kernel

private theorem sp17047 : smallValid 17047 60 := by unfold smallValid; decide +kernel

private theorem sp17107 : smallValid 17107 59 := by unfold smallValid; decide +kernel

private theorem sp17166 : smallValid 17166 59 := by unfold smallValid; decide +kernel

private theorem sp17225 : smallValid 17225 59 := by unfold smallValid; decide +kernel

private theorem sp17284 : smallValid 17284 60 := by unfold smallValid; decide +kernel

private theorem sp17344 : smallValid 17344 59 := by unfold smallValid; decide +kernel

private theorem sp17403 : smallValid 17403 60 := by unfold smallValid; decide +kernel

private theorem sp17463 : smallValid 17463 59 := by unfold smallValid; decide +kernel

private theorem sp17522 : smallValid 17522 60 := by unfold smallValid; decide +kernel

private theorem sp17582 : smallValid 17582 59 := by unfold smallValid; decide +kernel

private theorem sp17641 : smallValid 17641 59 := by unfold smallValid; decide +kernel

private theorem sp17700 : smallValid 17700 59 := by unfold smallValid; decide +kernel

private theorem sp17759 : smallValid 17759 60 := by unfold smallValid; decide +kernel

private theorem sp17819 : smallValid 17819 59 := by unfold smallValid; decide +kernel

private theorem sp17878 : smallValid 17878 60 := by unfold smallValid; decide +kernel

private theorem sp17938 : smallValid 17938 59 := by unfold smallValid; decide +kernel

private theorem sp17997 : smallValid 17997 60 := by unfold smallValid; decide +kernel

private theorem sp18057 : smallValid 18057 59 := by unfold smallValid; decide +kernel

private theorem sp18116 : smallValid 18116 59 := by unfold smallValid; decide +kernel

private theorem sp18175 : smallValid 18175 59 := by unfold smallValid; decide +kernel

private theorem sp18234 : smallValid 18234 60 := by unfold smallValid; decide +kernel

private theorem sp18294 : smallValid 18294 59 := by unfold smallValid; decide +kernel

private theorem sp18353 : smallValid 18353 60 := by unfold smallValid; decide +kernel

private theorem sp18413 : smallValid 18413 59 := by unfold smallValid; decide +kernel

private theorem sp18472 : smallValid 18472 60 := by unfold smallValid; decide +kernel

private theorem sp18532 : smallValid 18532 59 := by unfold smallValid; decide +kernel

private theorem sp18591 : smallValid 18591 60 := by unfold smallValid; decide +kernel

private theorem sp18651 : smallValid 18651 59 := by unfold smallValid; decide +kernel

private theorem sp18710 : smallValid 18710 60 := by unfold smallValid; decide +kernel

private theorem sp18770 : smallValid 18770 59 := by unfold smallValid; decide +kernel

private theorem sp18829 : smallValid 18829 60 := by unfold smallValid; decide +kernel

private theorem sp18889 : smallValid 18889 59 := by unfold smallValid; decide +kernel

private theorem sp18948 : smallValid 18948 60 := by unfold smallValid; decide +kernel

private theorem sp19008 : smallValid 19008 59 := by unfold smallValid; decide +kernel

private theorem sp19067 : smallValid 19067 59 := by unfold smallValid; decide +kernel

private theorem sp19126 : smallValid 19126 59 := by unfold smallValid; decide +kernel

private theorem sp19185 : smallValid 19185 60 := by unfold smallValid; decide +kernel

private theorem sp19245 : smallValid 19245 59 := by unfold smallValid; decide +kernel

private theorem sp19304 : smallValid 19304 60 := by unfold smallValid; decide +kernel

private theorem sp19364 : smallValid 19364 59 := by unfold smallValid; decide +kernel

private theorem sp19423 : smallValid 19423 60 := by unfold smallValid; decide +kernel

private theorem sp19483 : smallValid 19483 59 := by unfold smallValid; decide +kernel

private theorem sp19542 : smallValid 19542 59 := by unfold smallValid; decide +kernel

private theorem sp19601 : smallValid 19601 59 := by unfold smallValid; decide +kernel

private theorem sp19660 : smallValid 19660 60 := by unfold smallValid; decide +kernel

private theorem sp19720 : smallValid 19720 59 := by unfold smallValid; decide +kernel

private theorem sp19779 : smallValid 19779 60 := by unfold smallValid; decide +kernel

private theorem sp19839 : smallValid 19839 59 := by unfold smallValid; decide +kernel

private theorem sp19898 : smallValid 19898 60 := by unfold smallValid; decide +kernel

private theorem sp19958 : smallValid 19958 59 := by unfold smallValid; decide +kernel

private theorem sp20017 : smallValid 20017 59 := by unfold smallValid; decide +kernel

private theorem sp20076 : smallValid 20076 59 := by unfold smallValid; decide +kernel

private theorem sp20135 : smallValid 20135 60 := by unfold smallValid; decide +kernel

private theorem sp20195 : smallValid 20195 59 := by unfold smallValid; decide +kernel

private theorem sp20254 : smallValid 20254 60 := by unfold smallValid; decide +kernel

private theorem sp20314 : smallValid 20314 59 := by unfold smallValid; decide +kernel

private theorem sp20373 : smallValid 20373 60 := by unfold smallValid; decide +kernel

private theorem sp20433 : smallValid 20433 59 := by unfold smallValid; decide +kernel

private theorem sp20492 : smallValid 20492 60 := by unfold smallValid; decide +kernel

private theorem sp20552 : smallValid 20552 59 := by unfold smallValid; decide +kernel

private theorem sp20611 : smallValid 20611 60 := by unfold smallValid; decide +kernel

private theorem sp20671 : smallValid 20671 59 := by unfold smallValid; decide +kernel

private theorem sp20730 : smallValid 20730 60 := by unfold smallValid; decide +kernel

private theorem sp20790 : smallValid 20790 59 := by unfold smallValid; decide +kernel

private theorem sp20849 : smallValid 20849 60 := by unfold smallValid; decide +kernel

private theorem sp20909 : smallValid 20909 59 := by unfold smallValid; decide +kernel

private theorem sp20968 : smallValid 20968 59 := by unfold smallValid; decide +kernel

private theorem sp21027 : smallValid 21027 59 := by unfold smallValid; decide +kernel

private theorem sp21086 : smallValid 21086 60 := by unfold smallValid; decide +kernel

private theorem sp21146 : smallValid 21146 59 := by unfold smallValid; decide +kernel

private theorem sp21205 : smallValid 21205 60 := by unfold smallValid; decide +kernel

private theorem sp21265 : smallValid 21265 59 := by unfold smallValid; decide +kernel

private theorem sp21324 : smallValid 21324 60 := by unfold smallValid; decide +kernel

private theorem sp21384 : smallValid 21384 59 := by unfold smallValid; decide +kernel

private theorem sp21443 : smallValid 21443 59 := by unfold smallValid; decide +kernel

private theorem sp21502 : smallValid 21502 59 := by unfold smallValid; decide +kernel

private theorem sp21561 : smallValid 21561 60 := by unfold smallValid; decide +kernel

private theorem sp21621 : smallValid 21621 59 := by unfold smallValid; decide +kernel

private theorem sp21680 : smallValid 21680 60 := by unfold smallValid; decide +kernel

private theorem sp21740 : smallValid 21740 59 := by unfold smallValid; decide +kernel

private theorem sp21799 : smallValid 21799 60 := by unfold smallValid; decide +kernel

private theorem sp21859 : smallValid 21859 59 := by unfold smallValid; decide +kernel

private theorem sp21918 : smallValid 21918 59 := by unfold smallValid; decide +kernel

private theorem sp21977 : smallValid 21977 59 := by unfold smallValid; decide +kernel

private theorem sp22036 : smallValid 22036 60 := by unfold smallValid; decide +kernel

private theorem sp22096 : smallValid 22096 59 := by unfold smallValid; decide +kernel

private theorem sp22155 : smallValid 22155 60 := by unfold smallValid; decide +kernel

private theorem sp22215 : smallValid 22215 59 := by unfold smallValid; decide +kernel

private theorem sp22274 : smallValid 22274 60 := by unfold smallValid; decide +kernel

private theorem sp22334 : smallValid 22334 59 := by unfold smallValid; decide +kernel

private theorem sp22393 : smallValid 22393 60 := by unfold smallValid; decide +kernel

private theorem sp22453 : smallValid 22453 59 := by unfold smallValid; decide +kernel

private theorem sp22512 : smallValid 22512 60 := by unfold smallValid; decide +kernel

private theorem sp22572 : smallValid 22572 59 := by unfold smallValid; decide +kernel

private theorem sp22631 : smallValid 22631 60 := by unfold smallValid; decide +kernel

private theorem sp22691 : smallValid 22691 59 := by unfold smallValid; decide +kernel

private theorem sp22750 : smallValid 22750 60 := by unfold smallValid; decide +kernel

private theorem sp22810 : smallValid 22810 59 := by unfold smallValid; decide +kernel

private theorem sp22869 : smallValid 22869 59 := by unfold smallValid; decide +kernel

private theorem sp22928 : smallValid 22928 59 := by unfold smallValid; decide +kernel

private theorem sp22987 : smallValid 22987 60 := by unfold smallValid; decide +kernel

private theorem sp23047 : smallValid 23047 59 := by unfold smallValid; decide +kernel

private theorem sp23106 : smallValid 23106 60 := by unfold smallValid; decide +kernel

private theorem sp23166 : smallValid 23166 59 := by unfold smallValid; decide +kernel

private theorem sp23225 : smallValid 23225 60 := by unfold smallValid; decide +kernel

private theorem sp23285 : smallValid 23285 59 := by unfold smallValid; decide +kernel

private theorem sp23344 : smallValid 23344 59 := by unfold smallValid; decide +kernel

private theorem sp23403 : smallValid 23403 59 := by unfold smallValid; decide +kernel

private theorem sp23462 : smallValid 23462 60 := by unfold smallValid; decide +kernel

private theorem sp23522 : smallValid 23522 59 := by unfold smallValid; decide +kernel

private theorem sp23581 : smallValid 23581 60 := by unfold smallValid; decide +kernel

private theorem sp23641 : smallValid 23641 59 := by unfold smallValid; decide +kernel

private theorem sp23700 : smallValid 23700 60 := by unfold smallValid; decide +kernel

private theorem sp23760 : smallValid 23760 59 := by unfold smallValid; decide +kernel

private theorem sp23819 : smallValid 23819 59 := by unfold smallValid; decide +kernel

private theorem sp23878 : smallValid 23878 59 := by unfold smallValid; decide +kernel

private theorem sp23937 : smallValid 23937 60 := by unfold smallValid; decide +kernel

private theorem sp23997 : smallValid 23997 59 := by unfold smallValid; decide +kernel

private theorem sp24056 : smallValid 24056 60 := by unfold smallValid; decide +kernel

private theorem sp24116 : smallValid 24116 59 := by unfold smallValid; decide +kernel

private theorem sp24175 : smallValid 24175 60 := by unfold smallValid; decide +kernel

private theorem sp24235 : smallValid 24235 59 := by unfold smallValid; decide +kernel

private theorem sp24294 : smallValid 24294 60 := by unfold smallValid; decide +kernel

private theorem sp24354 : smallValid 24354 59 := by unfold smallValid; decide +kernel

private theorem sp24413 : smallValid 24413 60 := by unfold smallValid; decide +kernel

private theorem sp24473 : smallValid 24473 59 := by unfold smallValid; decide +kernel

private theorem sp24532 : smallValid 24532 60 := by unfold smallValid; decide +kernel

private theorem sp24592 : smallValid 24592 59 := by unfold smallValid; decide +kernel

private theorem sp24651 : smallValid 24651 60 := by unfold smallValid; decide +kernel

private theorem sp24711 : smallValid 24711 59 := by unfold smallValid; decide +kernel

private theorem sp24770 : smallValid 24770 59 := by unfold smallValid; decide +kernel

private theorem sp24829 : smallValid 24829 59 := by unfold smallValid; decide +kernel

private theorem sp24888 : smallValid 24888 60 := by unfold smallValid; decide +kernel

private theorem sp24948 : smallValid 24948 59 := by unfold smallValid; decide +kernel

private theorem sp25007 : smallValid 25007 60 := by unfold smallValid; decide +kernel

private theorem sp25067 : smallValid 25067 59 := by unfold smallValid; decide +kernel

private theorem sp25126 : smallValid 25126 60 := by unfold smallValid; decide +kernel

private theorem sp25186 : smallValid 25186 59 := by unfold smallValid; decide +kernel

private theorem sp25245 : smallValid 25245 59 := by unfold smallValid; decide +kernel

private theorem sp25304 : smallValid 25304 59 := by unfold smallValid; decide +kernel

private theorem sp25363 : smallValid 25363 60 := by unfold smallValid; decide +kernel

private theorem sp25423 : smallValid 25423 59 := by unfold smallValid; decide +kernel

private theorem sp25482 : smallValid 25482 60 := by unfold smallValid; decide +kernel

private theorem sp25542 : smallValid 25542 59 := by unfold smallValid; decide +kernel

private theorem sp25601 : smallValid 25601 60 := by unfold smallValid; decide +kernel

private theorem sp25661 : smallValid 25661 59 := by unfold smallValid; decide +kernel

private theorem sp25720 : smallValid 25720 59 := by unfold smallValid; decide +kernel

private theorem sp25779 : smallValid 25779 59 := by unfold smallValid; decide +kernel

private theorem sp25838 : smallValid 25838 60 := by unfold smallValid; decide +kernel

private theorem sp25898 : smallValid 25898 59 := by unfold smallValid; decide +kernel

private theorem sp25957 : smallValid 25957 60 := by unfold smallValid; decide +kernel

private theorem sp26017 : smallValid 26017 59 := by unfold smallValid; decide +kernel

private theorem sp26076 : smallValid 26076 60 := by unfold smallValid; decide +kernel

private theorem sp26136 : smallValid 26136 59 := by unfold smallValid; decide +kernel

private theorem sp26195 : smallValid 26195 60 := by unfold smallValid; decide +kernel

private theorem sp26255 : smallValid 26255 59 := by unfold smallValid; decide +kernel

private theorem sp26314 : smallValid 26314 60 := by unfold smallValid; decide +kernel

private theorem sp26374 : smallValid 26374 59 := by unfold smallValid; decide +kernel

private theorem sp26433 : smallValid 26433 60 := by unfold smallValid; decide +kernel

private theorem sp26493 : smallValid 26493 59 := by unfold smallValid; decide +kernel

private theorem sp26552 : smallValid 26552 60 := by unfold smallValid; decide +kernel

private theorem sp26612 : smallValid 26612 59 := by unfold smallValid; decide +kernel

private theorem sp26671 : smallValid 26671 59 := by unfold smallValid; decide +kernel

private theorem sp26730 : smallValid 26730 59 := by unfold smallValid; decide +kernel

private theorem sp26789 : smallValid 26789 60 := by unfold smallValid; decide +kernel

private theorem sp26849 : smallValid 26849 59 := by unfold smallValid; decide +kernel

private theorem sp26908 : smallValid 26908 60 := by unfold smallValid; decide +kernel

private theorem sp26968 : smallValid 26968 59 := by unfold smallValid; decide +kernel

private theorem sp27027 : smallValid 27027 60 := by unfold smallValid; decide +kernel

private theorem sp27087 : smallValid 27087 59 := by unfold smallValid; decide +kernel

private theorem sp27146 : smallValid 27146 59 := by unfold smallValid; decide +kernel

private theorem sp27205 : smallValid 27205 59 := by unfold smallValid; decide +kernel

private theorem sp27264 : smallValid 27264 60 := by unfold smallValid; decide +kernel

private theorem sp27324 : smallValid 27324 59 := by unfold smallValid; decide +kernel

private theorem sp27383 : smallValid 27383 60 := by unfold smallValid; decide +kernel

private theorem sp27443 : smallValid 27443 59 := by unfold smallValid; decide +kernel

private theorem sp27502 : smallValid 27502 60 := by unfold smallValid; decide +kernel

private theorem sp27562 : smallValid 27562 59 := by unfold smallValid; decide +kernel

private theorem sp27621 : smallValid 27621 59 := by unfold smallValid; decide +kernel

private theorem sp27680 : smallValid 27680 59 := by unfold smallValid; decide +kernel

private theorem sp27739 : smallValid 27739 60 := by unfold smallValid; decide +kernel

private theorem sp27799 : smallValid 27799 59 := by unfold smallValid; decide +kernel

private theorem sp27858 : smallValid 27858 60 := by unfold smallValid; decide +kernel

private theorem sp27918 : smallValid 27918 59 := by unfold smallValid; decide +kernel

private theorem sp27977 : smallValid 27977 60 := by unfold smallValid; decide +kernel

private theorem sp28037 : smallValid 28037 59 := by unfold smallValid; decide +kernel

private theorem sp28096 : smallValid 28096 60 := by unfold smallValid; decide +kernel

private theorem sp28156 : smallValid 28156 59 := by unfold smallValid; decide +kernel

private theorem sp28215 : smallValid 28215 60 := by unfold smallValid; decide +kernel

private theorem sp28275 : smallValid 28275 59 := by unfold smallValid; decide +kernel

private theorem sp28334 : smallValid 28334 60 := by unfold smallValid; decide +kernel

private theorem sp28394 : smallValid 28394 59 := by unfold smallValid; decide +kernel

private theorem sp28453 : smallValid 28453 60 := by unfold smallValid; decide +kernel

private theorem sp28513 : smallValid 28513 59 := by unfold smallValid; decide +kernel

private theorem sp28572 : smallValid 28572 59 := by unfold smallValid; decide +kernel

private theorem sp28631 : smallValid 28631 59 := by unfold smallValid; decide +kernel

private theorem sp28690 : smallValid 28690 60 := by unfold smallValid; decide +kernel

private theorem sp28750 : smallValid 28750 59 := by unfold smallValid; decide +kernel

private theorem sp28809 : smallValid 28809 60 := by unfold smallValid; decide +kernel

private theorem sp28869 : smallValid 28869 59 := by unfold smallValid; decide +kernel

private theorem sp28928 : smallValid 28928 60 := by unfold smallValid; decide +kernel

private theorem sp28988 : smallValid 28988 59 := by unfold smallValid; decide +kernel

private theorem sp29047 : smallValid 29047 59 := by unfold smallValid; decide +kernel

private theorem sp29106 : smallValid 29106 59 := by unfold smallValid; decide +kernel

private theorem sp29165 : smallValid 29165 60 := by unfold smallValid; decide +kernel

private theorem sp29225 : smallValid 29225 59 := by unfold smallValid; decide +kernel

private theorem sp29284 : smallValid 29284 60 := by unfold smallValid; decide +kernel

private theorem sp29344 : smallValid 29344 59 := by unfold smallValid; decide +kernel

private theorem sp29403 : smallValid 29403 60 := by unfold smallValid; decide +kernel

private theorem sp29463 : smallValid 29463 59 := by unfold smallValid; decide +kernel

private theorem sp29522 : smallValid 29522 59 := by unfold smallValid; decide +kernel

private theorem sp29581 : smallValid 29581 59 := by unfold smallValid; decide +kernel

private theorem sp29640 : smallValid 29640 60 := by unfold smallValid; decide +kernel

private theorem sp29700 : smallValid 29700 59 := by unfold smallValid; decide +kernel

private theorem sp29759 : smallValid 29759 60 := by unfold smallValid; decide +kernel

private theorem sp29819 : smallValid 29819 59 := by unfold smallValid; decide +kernel

private theorem sp29878 : smallValid 29878 60 := by unfold smallValid; decide +kernel

private theorem sp29938 : smallValid 29938 59 := by unfold smallValid; decide +kernel

private theorem sp29997 : smallValid 29997 60 := by unfold smallValid; decide +kernel

private theorem sp30057 : smallValid 30057 59 := by unfold smallValid; decide +kernel

private theorem sp30116 : smallValid 30116 60 := by unfold smallValid; decide +kernel

private theorem sp30176 : smallValid 30176 59 := by unfold smallValid; decide +kernel

private theorem sp30235 : smallValid 30235 60 := by unfold smallValid; decide +kernel

private theorem sp30295 : smallValid 30295 59 := by unfold smallValid; decide +kernel

private theorem sp30354 : smallValid 30354 60 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤30413) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 30414 := (joinSmall (lo:=0) (a:=15207) (b:=15207) (joinSmall (lo:=0) (a:=7603) (b:=7604) (joinSmall (lo:=0) (a:=3801) (b:=3802) (joinSmall (lo:=0) (a:=1900) (b:=1901) (joinSmall (lo:=0) (a:=950) (b:=950) (joinSmall (lo:=0) (a:=475) (b:=475) (joinSmall (lo:=0) (a:=237) (b:=238) (joinSmall (lo:=0) (a:=118) (b:=119) (joinSmall (lo:=0) (a:=59) (b:=59) sp0 sp59) (joinSmall (lo:=118) (a:=59) (b:=60) sp118 sp177)) (joinSmall (lo:=237) (a:=119) (b:=119) (joinSmall (lo:=237) (a:=59) (b:=60) sp237 sp296) (joinSmall (lo:=356) (a:=59) (b:=60) sp356 sp415))) (joinSmall (lo:=475) (a:=237) (b:=238) (joinSmall (lo:=475) (a:=118) (b:=119) (joinSmall (lo:=475) (a:=59) (b:=59) sp475 sp534) (joinSmall (lo:=593) (a:=59) (b:=60) sp593 sp652)) (joinSmall (lo:=712) (a:=119) (b:=119) (joinSmall (lo:=712) (a:=59) (b:=60) sp712 sp771) (joinSmall (lo:=831) (a:=59) (b:=60) sp831 sp890)))) (joinSmall (lo:=950) (a:=475) (b:=475) (joinSmall (lo:=950) (a:=237) (b:=238) (joinSmall (lo:=950) (a:=118) (b:=119) (joinSmall (lo:=950) (a:=59) (b:=59) sp950 sp1009) (joinSmall (lo:=1068) (a:=59) (b:=60) sp1068 sp1127)) (joinSmall (lo:=1187) (a:=119) (b:=119) (joinSmall (lo:=1187) (a:=59) (b:=60) sp1187 sp1246) (joinSmall (lo:=1306) (a:=59) (b:=60) sp1306 sp1365))) (joinSmall (lo:=1425) (a:=237) (b:=238) (joinSmall (lo:=1425) (a:=118) (b:=119) (joinSmall (lo:=1425) (a:=59) (b:=59) sp1425 sp1484) (joinSmall (lo:=1543) (a:=59) (b:=60) sp1543 sp1602)) (joinSmall (lo:=1662) (a:=119) (b:=119) (joinSmall (lo:=1662) (a:=59) (b:=60) sp1662 sp1721) (joinSmall (lo:=1781) (a:=59) (b:=60) sp1781 sp1840))))) (joinSmall (lo:=1900) (a:=950) (b:=951) (joinSmall (lo:=1900) (a:=475) (b:=475) (joinSmall (lo:=1900) (a:=237) (b:=238) (joinSmall (lo:=1900) (a:=118) (b:=119) (joinSmall (lo:=1900) (a:=59) (b:=59) sp1900 sp1959) (joinSmall (lo:=2018) (a:=59) (b:=60) sp2018 sp2077)) (joinSmall (lo:=2137) (a:=119) (b:=119) (joinSmall (lo:=2137) (a:=59) (b:=60) sp2137 sp2196) (joinSmall (lo:=2256) (a:=59) (b:=60) sp2256 sp2315))) (joinSmall (lo:=2375) (a:=237) (b:=238) (joinSmall (lo:=2375) (a:=118) (b:=119) (joinSmall (lo:=2375) (a:=59) (b:=59) sp2375 sp2434) (joinSmall (lo:=2493) (a:=59) (b:=60) sp2493 sp2552)) (joinSmall (lo:=2612) (a:=119) (b:=119) (joinSmall (lo:=2612) (a:=59) (b:=60) sp2612 sp2671) (joinSmall (lo:=2731) (a:=59) (b:=60) sp2731 sp2790)))) (joinSmall (lo:=2850) (a:=475) (b:=476) (joinSmall (lo:=2850) (a:=237) (b:=238) (joinSmall (lo:=2850) (a:=118) (b:=119) (joinSmall (lo:=2850) (a:=59) (b:=59) sp2850 sp2909) (joinSmall (lo:=2968) (a:=59) (b:=60) sp2968 sp3027)) (joinSmall (lo:=3087) (a:=119) (b:=119) (joinSmall (lo:=3087) (a:=59) (b:=60) sp3087 sp3146) (joinSmall (lo:=3206) (a:=59) (b:=60) sp3206 sp3265))) (joinSmall (lo:=3325) (a:=238) (b:=238) (joinSmall (lo:=3325) (a:=119) (b:=119) (joinSmall (lo:=3325) (a:=59) (b:=60) sp3325 sp3384) (joinSmall (lo:=3444) (a:=59) (b:=60) sp3444 sp3503)) (joinSmall (lo:=3563) (a:=119) (b:=119) (joinSmall (lo:=3563) (a:=59) (b:=60) sp3563 sp3622) (joinSmall (lo:=3682) (a:=59) (b:=60) sp3682 sp3741)))))) (joinSmall (lo:=3801) (a:=1901) (b:=1901) (joinSmall (lo:=3801) (a:=950) (b:=951) (joinSmall (lo:=3801) (a:=475) (b:=475) (joinSmall (lo:=3801) (a:=237) (b:=238) (joinSmall (lo:=3801) (a:=118) (b:=119) (joinSmall (lo:=3801) (a:=59) (b:=59) sp3801 sp3860) (joinSmall (lo:=3919) (a:=59) (b:=60) sp3919 sp3978)) (joinSmall (lo:=4038) (a:=119) (b:=119) (joinSmall (lo:=4038) (a:=59) (b:=60) sp4038 sp4097) (joinSmall (lo:=4157) (a:=59) (b:=60) sp4157 sp4216))) (joinSmall (lo:=4276) (a:=237) (b:=238) (joinSmall (lo:=4276) (a:=118) (b:=119) (joinSmall (lo:=4276) (a:=59) (b:=59) sp4276 sp4335) (joinSmall (lo:=4394) (a:=59) (b:=60) sp4394 sp4453)) (joinSmall (lo:=4513) (a:=119) (b:=119) (joinSmall (lo:=4513) (a:=59) (b:=60) sp4513 sp4572) (joinSmall (lo:=4632) (a:=59) (b:=60) sp4632 sp4691)))) (joinSmall (lo:=4751) (a:=475) (b:=476) (joinSmall (lo:=4751) (a:=237) (b:=238) (joinSmall (lo:=4751) (a:=118) (b:=119) (joinSmall (lo:=4751) (a:=59) (b:=59) sp4751 sp4810) (joinSmall (lo:=4869) (a:=59) (b:=60) sp4869 sp4928)) (joinSmall (lo:=4988) (a:=119) (b:=119) (joinSmall (lo:=4988) (a:=59) (b:=60) sp4988 sp5047) (joinSmall (lo:=5107) (a:=59) (b:=60) sp5107 sp5166))) (joinSmall (lo:=5226) (a:=238) (b:=238) (joinSmall (lo:=5226) (a:=119) (b:=119) (joinSmall (lo:=5226) (a:=59) (b:=60) sp5226 sp5285) (joinSmall (lo:=5345) (a:=59) (b:=60) sp5345 sp5404)) (joinSmall (lo:=5464) (a:=119) (b:=119) (joinSmall (lo:=5464) (a:=59) (b:=60) sp5464 sp5523) (joinSmall (lo:=5583) (a:=59) (b:=60) sp5583 sp5642))))) (joinSmall (lo:=5702) (a:=950) (b:=951) (joinSmall (lo:=5702) (a:=475) (b:=475) (joinSmall (lo:=5702) (a:=237) (b:=238) (joinSmall (lo:=5702) (a:=118) (b:=119) (joinSmall (lo:=5702) (a:=59) (b:=59) sp5702 sp5761) (joinSmall (lo:=5820) (a:=59) (b:=60) sp5820 sp5879)) (joinSmall (lo:=5939) (a:=119) (b:=119) (joinSmall (lo:=5939) (a:=59) (b:=60) sp5939 sp5998) (joinSmall (lo:=6058) (a:=59) (b:=60) sp6058 sp6117))) (joinSmall (lo:=6177) (a:=237) (b:=238) (joinSmall (lo:=6177) (a:=118) (b:=119) (joinSmall (lo:=6177) (a:=59) (b:=59) sp6177 sp6236) (joinSmall (lo:=6295) (a:=59) (b:=60) sp6295 sp6354)) (joinSmall (lo:=6414) (a:=119) (b:=119) (joinSmall (lo:=6414) (a:=59) (b:=60) sp6414 sp6473) (joinSmall (lo:=6533) (a:=59) (b:=60) sp6533 sp6592)))) (joinSmall (lo:=6652) (a:=475) (b:=476) (joinSmall (lo:=6652) (a:=237) (b:=238) (joinSmall (lo:=6652) (a:=118) (b:=119) (joinSmall (lo:=6652) (a:=59) (b:=59) sp6652 sp6711) (joinSmall (lo:=6770) (a:=59) (b:=60) sp6770 sp6829)) (joinSmall (lo:=6889) (a:=119) (b:=119) (joinSmall (lo:=6889) (a:=59) (b:=60) sp6889 sp6948) (joinSmall (lo:=7008) (a:=59) (b:=60) sp7008 sp7067))) (joinSmall (lo:=7127) (a:=238) (b:=238) (joinSmall (lo:=7127) (a:=119) (b:=119) (joinSmall (lo:=7127) (a:=59) (b:=60) sp7127 sp7186) (joinSmall (lo:=7246) (a:=59) (b:=60) sp7246 sp7305)) (joinSmall (lo:=7365) (a:=119) (b:=119) (joinSmall (lo:=7365) (a:=59) (b:=60) sp7365 sp7424) (joinSmall (lo:=7484) (a:=59) (b:=60) sp7484 sp7543))))))) (joinSmall (lo:=7603) (a:=3802) (b:=3802) (joinSmall (lo:=7603) (a:=1901) (b:=1901) (joinSmall (lo:=7603) (a:=950) (b:=951) (joinSmall (lo:=7603) (a:=475) (b:=475) (joinSmall (lo:=7603) (a:=237) (b:=238) (joinSmall (lo:=7603) (a:=118) (b:=119) (joinSmall (lo:=7603) (a:=59) (b:=59) sp7603 sp7662) (joinSmall (lo:=7721) (a:=59) (b:=60) sp7721 sp7780)) (joinSmall (lo:=7840) (a:=119) (b:=119) (joinSmall (lo:=7840) (a:=59) (b:=60) sp7840 sp7899) (joinSmall (lo:=7959) (a:=59) (b:=60) sp7959 sp8018))) (joinSmall (lo:=8078) (a:=237) (b:=238) (joinSmall (lo:=8078) (a:=118) (b:=119) (joinSmall (lo:=8078) (a:=59) (b:=59) sp8078 sp8137) (joinSmall (lo:=8196) (a:=59) (b:=60) sp8196 sp8255)) (joinSmall (lo:=8315) (a:=119) (b:=119) (joinSmall (lo:=8315) (a:=59) (b:=60) sp8315 sp8374) (joinSmall (lo:=8434) (a:=59) (b:=60) sp8434 sp8493)))) (joinSmall (lo:=8553) (a:=475) (b:=476) (joinSmall (lo:=8553) (a:=237) (b:=238) (joinSmall (lo:=8553) (a:=118) (b:=119) (joinSmall (lo:=8553) (a:=59) (b:=59) sp8553 sp8612) (joinSmall (lo:=8671) (a:=59) (b:=60) sp8671 sp8730)) (joinSmall (lo:=8790) (a:=119) (b:=119) (joinSmall (lo:=8790) (a:=59) (b:=60) sp8790 sp8849) (joinSmall (lo:=8909) (a:=59) (b:=60) sp8909 sp8968))) (joinSmall (lo:=9028) (a:=238) (b:=238) (joinSmall (lo:=9028) (a:=119) (b:=119) (joinSmall (lo:=9028) (a:=59) (b:=60) sp9028 sp9087) (joinSmall (lo:=9147) (a:=59) (b:=60) sp9147 sp9206)) (joinSmall (lo:=9266) (a:=119) (b:=119) (joinSmall (lo:=9266) (a:=59) (b:=60) sp9266 sp9325) (joinSmall (lo:=9385) (a:=59) (b:=60) sp9385 sp9444))))) (joinSmall (lo:=9504) (a:=950) (b:=951) (joinSmall (lo:=9504) (a:=475) (b:=475) (joinSmall (lo:=9504) (a:=237) (b:=238) (joinSmall (lo:=9504) (a:=118) (b:=119) (joinSmall (lo:=9504) (a:=59) (b:=59) sp9504 sp9563) (joinSmall (lo:=9622) (a:=59) (b:=60) sp9622 sp9681)) (joinSmall (lo:=9741) (a:=119) (b:=119) (joinSmall (lo:=9741) (a:=59) (b:=60) sp9741 sp9800) (joinSmall (lo:=9860) (a:=59) (b:=60) sp9860 sp9919))) (joinSmall (lo:=9979) (a:=237) (b:=238) (joinSmall (lo:=9979) (a:=118) (b:=119) (joinSmall (lo:=9979) (a:=59) (b:=59) sp9979 sp10038) (joinSmall (lo:=10097) (a:=59) (b:=60) sp10097 sp10156)) (joinSmall (lo:=10216) (a:=119) (b:=119) (joinSmall (lo:=10216) (a:=59) (b:=60) sp10216 sp10275) (joinSmall (lo:=10335) (a:=59) (b:=60) sp10335 sp10394)))) (joinSmall (lo:=10454) (a:=475) (b:=476) (joinSmall (lo:=10454) (a:=237) (b:=238) (joinSmall (lo:=10454) (a:=118) (b:=119) (joinSmall (lo:=10454) (a:=59) (b:=59) sp10454 sp10513) (joinSmall (lo:=10572) (a:=59) (b:=60) sp10572 sp10631)) (joinSmall (lo:=10691) (a:=119) (b:=119) (joinSmall (lo:=10691) (a:=59) (b:=60) sp10691 sp10750) (joinSmall (lo:=10810) (a:=59) (b:=60) sp10810 sp10869))) (joinSmall (lo:=10929) (a:=238) (b:=238) (joinSmall (lo:=10929) (a:=119) (b:=119) (joinSmall (lo:=10929) (a:=59) (b:=60) sp10929 sp10988) (joinSmall (lo:=11048) (a:=59) (b:=60) sp11048 sp11107)) (joinSmall (lo:=11167) (a:=119) (b:=119) (joinSmall (lo:=11167) (a:=59) (b:=60) sp11167 sp11226) (joinSmall (lo:=11286) (a:=59) (b:=60) sp11286 sp11345)))))) (joinSmall (lo:=11405) (a:=1901) (b:=1901) (joinSmall (lo:=11405) (a:=950) (b:=951) (joinSmall (lo:=11405) (a:=475) (b:=475) (joinSmall (lo:=11405) (a:=237) (b:=238) (joinSmall (lo:=11405) (a:=118) (b:=119) (joinSmall (lo:=11405) (a:=59) (b:=59) sp11405 sp11464) (joinSmall (lo:=11523) (a:=59) (b:=60) sp11523 sp11582)) (joinSmall (lo:=11642) (a:=119) (b:=119) (joinSmall (lo:=11642) (a:=59) (b:=60) sp11642 sp11701) (joinSmall (lo:=11761) (a:=59) (b:=60) sp11761 sp11820))) (joinSmall (lo:=11880) (a:=237) (b:=238) (joinSmall (lo:=11880) (a:=118) (b:=119) (joinSmall (lo:=11880) (a:=59) (b:=59) sp11880 sp11939) (joinSmall (lo:=11998) (a:=59) (b:=60) sp11998 sp12057)) (joinSmall (lo:=12117) (a:=119) (b:=119) (joinSmall (lo:=12117) (a:=59) (b:=60) sp12117 sp12176) (joinSmall (lo:=12236) (a:=59) (b:=60) sp12236 sp12295)))) (joinSmall (lo:=12355) (a:=475) (b:=476) (joinSmall (lo:=12355) (a:=237) (b:=238) (joinSmall (lo:=12355) (a:=118) (b:=119) (joinSmall (lo:=12355) (a:=59) (b:=59) sp12355 sp12414) (joinSmall (lo:=12473) (a:=59) (b:=60) sp12473 sp12532)) (joinSmall (lo:=12592) (a:=119) (b:=119) (joinSmall (lo:=12592) (a:=59) (b:=60) sp12592 sp12651) (joinSmall (lo:=12711) (a:=59) (b:=60) sp12711 sp12770))) (joinSmall (lo:=12830) (a:=238) (b:=238) (joinSmall (lo:=12830) (a:=119) (b:=119) (joinSmall (lo:=12830) (a:=59) (b:=60) sp12830 sp12889) (joinSmall (lo:=12949) (a:=59) (b:=60) sp12949 sp13008)) (joinSmall (lo:=13068) (a:=119) (b:=119) (joinSmall (lo:=13068) (a:=59) (b:=60) sp13068 sp13127) (joinSmall (lo:=13187) (a:=59) (b:=60) sp13187 sp13246))))) (joinSmall (lo:=13306) (a:=950) (b:=951) (joinSmall (lo:=13306) (a:=475) (b:=475) (joinSmall (lo:=13306) (a:=237) (b:=238) (joinSmall (lo:=13306) (a:=118) (b:=119) (joinSmall (lo:=13306) (a:=59) (b:=59) sp13306 sp13365) (joinSmall (lo:=13424) (a:=59) (b:=60) sp13424 sp13483)) (joinSmall (lo:=13543) (a:=119) (b:=119) (joinSmall (lo:=13543) (a:=59) (b:=60) sp13543 sp13602) (joinSmall (lo:=13662) (a:=59) (b:=60) sp13662 sp13721))) (joinSmall (lo:=13781) (a:=237) (b:=238) (joinSmall (lo:=13781) (a:=118) (b:=119) (joinSmall (lo:=13781) (a:=59) (b:=59) sp13781 sp13840) (joinSmall (lo:=13899) (a:=59) (b:=60) sp13899 sp13958)) (joinSmall (lo:=14018) (a:=119) (b:=119) (joinSmall (lo:=14018) (a:=59) (b:=60) sp14018 sp14077) (joinSmall (lo:=14137) (a:=59) (b:=60) sp14137 sp14196)))) (joinSmall (lo:=14256) (a:=475) (b:=476) (joinSmall (lo:=14256) (a:=237) (b:=238) (joinSmall (lo:=14256) (a:=118) (b:=119) (joinSmall (lo:=14256) (a:=59) (b:=59) sp14256 sp14315) (joinSmall (lo:=14374) (a:=59) (b:=60) sp14374 sp14433)) (joinSmall (lo:=14493) (a:=119) (b:=119) (joinSmall (lo:=14493) (a:=59) (b:=60) sp14493 sp14552) (joinSmall (lo:=14612) (a:=59) (b:=60) sp14612 sp14671))) (joinSmall (lo:=14731) (a:=238) (b:=238) (joinSmall (lo:=14731) (a:=119) (b:=119) (joinSmall (lo:=14731) (a:=59) (b:=60) sp14731 sp14790) (joinSmall (lo:=14850) (a:=59) (b:=60) sp14850 sp14909)) (joinSmall (lo:=14969) (a:=119) (b:=119) (joinSmall (lo:=14969) (a:=59) (b:=60) sp14969 sp15028) (joinSmall (lo:=15088) (a:=59) (b:=60) sp15088 sp15147)))))))) (joinSmall (lo:=15207) (a:=7603) (b:=7604) (joinSmall (lo:=15207) (a:=3801) (b:=3802) (joinSmall (lo:=15207) (a:=1900) (b:=1901) (joinSmall (lo:=15207) (a:=950) (b:=950) (joinSmall (lo:=15207) (a:=475) (b:=475) (joinSmall (lo:=15207) (a:=237) (b:=238) (joinSmall (lo:=15207) (a:=118) (b:=119) (joinSmall (lo:=15207) (a:=59) (b:=59) sp15207 sp15266) (joinSmall (lo:=15325) (a:=59) (b:=60) sp15325 sp15384)) (joinSmall (lo:=15444) (a:=119) (b:=119) (joinSmall (lo:=15444) (a:=59) (b:=60) sp15444 sp15503) (joinSmall (lo:=15563) (a:=59) (b:=60) sp15563 sp15622))) (joinSmall (lo:=15682) (a:=237) (b:=238) (joinSmall (lo:=15682) (a:=118) (b:=119) (joinSmall (lo:=15682) (a:=59) (b:=59) sp15682 sp15741) (joinSmall (lo:=15800) (a:=59) (b:=60) sp15800 sp15859)) (joinSmall (lo:=15919) (a:=119) (b:=119) (joinSmall (lo:=15919) (a:=59) (b:=60) sp15919 sp15978) (joinSmall (lo:=16038) (a:=59) (b:=60) sp16038 sp16097)))) (joinSmall (lo:=16157) (a:=475) (b:=475) (joinSmall (lo:=16157) (a:=237) (b:=238) (joinSmall (lo:=16157) (a:=118) (b:=119) (joinSmall (lo:=16157) (a:=59) (b:=59) sp16157 sp16216) (joinSmall (lo:=16275) (a:=59) (b:=60) sp16275 sp16334)) (joinSmall (lo:=16394) (a:=119) (b:=119) (joinSmall (lo:=16394) (a:=59) (b:=60) sp16394 sp16453) (joinSmall (lo:=16513) (a:=59) (b:=60) sp16513 sp16572))) (joinSmall (lo:=16632) (a:=237) (b:=238) (joinSmall (lo:=16632) (a:=118) (b:=119) (joinSmall (lo:=16632) (a:=59) (b:=59) sp16632 sp16691) (joinSmall (lo:=16750) (a:=59) (b:=60) sp16750 sp16809)) (joinSmall (lo:=16869) (a:=119) (b:=119) (joinSmall (lo:=16869) (a:=59) (b:=60) sp16869 sp16928) (joinSmall (lo:=16988) (a:=59) (b:=60) sp16988 sp17047))))) (joinSmall (lo:=17107) (a:=950) (b:=951) (joinSmall (lo:=17107) (a:=475) (b:=475) (joinSmall (lo:=17107) (a:=237) (b:=238) (joinSmall (lo:=17107) (a:=118) (b:=119) (joinSmall (lo:=17107) (a:=59) (b:=59) sp17107 sp17166) (joinSmall (lo:=17225) (a:=59) (b:=60) sp17225 sp17284)) (joinSmall (lo:=17344) (a:=119) (b:=119) (joinSmall (lo:=17344) (a:=59) (b:=60) sp17344 sp17403) (joinSmall (lo:=17463) (a:=59) (b:=60) sp17463 sp17522))) (joinSmall (lo:=17582) (a:=237) (b:=238) (joinSmall (lo:=17582) (a:=118) (b:=119) (joinSmall (lo:=17582) (a:=59) (b:=59) sp17582 sp17641) (joinSmall (lo:=17700) (a:=59) (b:=60) sp17700 sp17759)) (joinSmall (lo:=17819) (a:=119) (b:=119) (joinSmall (lo:=17819) (a:=59) (b:=60) sp17819 sp17878) (joinSmall (lo:=17938) (a:=59) (b:=60) sp17938 sp17997)))) (joinSmall (lo:=18057) (a:=475) (b:=476) (joinSmall (lo:=18057) (a:=237) (b:=238) (joinSmall (lo:=18057) (a:=118) (b:=119) (joinSmall (lo:=18057) (a:=59) (b:=59) sp18057 sp18116) (joinSmall (lo:=18175) (a:=59) (b:=60) sp18175 sp18234)) (joinSmall (lo:=18294) (a:=119) (b:=119) (joinSmall (lo:=18294) (a:=59) (b:=60) sp18294 sp18353) (joinSmall (lo:=18413) (a:=59) (b:=60) sp18413 sp18472))) (joinSmall (lo:=18532) (a:=238) (b:=238) (joinSmall (lo:=18532) (a:=119) (b:=119) (joinSmall (lo:=18532) (a:=59) (b:=60) sp18532 sp18591) (joinSmall (lo:=18651) (a:=59) (b:=60) sp18651 sp18710)) (joinSmall (lo:=18770) (a:=119) (b:=119) (joinSmall (lo:=18770) (a:=59) (b:=60) sp18770 sp18829) (joinSmall (lo:=18889) (a:=59) (b:=60) sp18889 sp18948)))))) (joinSmall (lo:=19008) (a:=1901) (b:=1901) (joinSmall (lo:=19008) (a:=950) (b:=951) (joinSmall (lo:=19008) (a:=475) (b:=475) (joinSmall (lo:=19008) (a:=237) (b:=238) (joinSmall (lo:=19008) (a:=118) (b:=119) (joinSmall (lo:=19008) (a:=59) (b:=59) sp19008 sp19067) (joinSmall (lo:=19126) (a:=59) (b:=60) sp19126 sp19185)) (joinSmall (lo:=19245) (a:=119) (b:=119) (joinSmall (lo:=19245) (a:=59) (b:=60) sp19245 sp19304) (joinSmall (lo:=19364) (a:=59) (b:=60) sp19364 sp19423))) (joinSmall (lo:=19483) (a:=237) (b:=238) (joinSmall (lo:=19483) (a:=118) (b:=119) (joinSmall (lo:=19483) (a:=59) (b:=59) sp19483 sp19542) (joinSmall (lo:=19601) (a:=59) (b:=60) sp19601 sp19660)) (joinSmall (lo:=19720) (a:=119) (b:=119) (joinSmall (lo:=19720) (a:=59) (b:=60) sp19720 sp19779) (joinSmall (lo:=19839) (a:=59) (b:=60) sp19839 sp19898)))) (joinSmall (lo:=19958) (a:=475) (b:=476) (joinSmall (lo:=19958) (a:=237) (b:=238) (joinSmall (lo:=19958) (a:=118) (b:=119) (joinSmall (lo:=19958) (a:=59) (b:=59) sp19958 sp20017) (joinSmall (lo:=20076) (a:=59) (b:=60) sp20076 sp20135)) (joinSmall (lo:=20195) (a:=119) (b:=119) (joinSmall (lo:=20195) (a:=59) (b:=60) sp20195 sp20254) (joinSmall (lo:=20314) (a:=59) (b:=60) sp20314 sp20373))) (joinSmall (lo:=20433) (a:=238) (b:=238) (joinSmall (lo:=20433) (a:=119) (b:=119) (joinSmall (lo:=20433) (a:=59) (b:=60) sp20433 sp20492) (joinSmall (lo:=20552) (a:=59) (b:=60) sp20552 sp20611)) (joinSmall (lo:=20671) (a:=119) (b:=119) (joinSmall (lo:=20671) (a:=59) (b:=60) sp20671 sp20730) (joinSmall (lo:=20790) (a:=59) (b:=60) sp20790 sp20849))))) (joinSmall (lo:=20909) (a:=950) (b:=951) (joinSmall (lo:=20909) (a:=475) (b:=475) (joinSmall (lo:=20909) (a:=237) (b:=238) (joinSmall (lo:=20909) (a:=118) (b:=119) (joinSmall (lo:=20909) (a:=59) (b:=59) sp20909 sp20968) (joinSmall (lo:=21027) (a:=59) (b:=60) sp21027 sp21086)) (joinSmall (lo:=21146) (a:=119) (b:=119) (joinSmall (lo:=21146) (a:=59) (b:=60) sp21146 sp21205) (joinSmall (lo:=21265) (a:=59) (b:=60) sp21265 sp21324))) (joinSmall (lo:=21384) (a:=237) (b:=238) (joinSmall (lo:=21384) (a:=118) (b:=119) (joinSmall (lo:=21384) (a:=59) (b:=59) sp21384 sp21443) (joinSmall (lo:=21502) (a:=59) (b:=60) sp21502 sp21561)) (joinSmall (lo:=21621) (a:=119) (b:=119) (joinSmall (lo:=21621) (a:=59) (b:=60) sp21621 sp21680) (joinSmall (lo:=21740) (a:=59) (b:=60) sp21740 sp21799)))) (joinSmall (lo:=21859) (a:=475) (b:=476) (joinSmall (lo:=21859) (a:=237) (b:=238) (joinSmall (lo:=21859) (a:=118) (b:=119) (joinSmall (lo:=21859) (a:=59) (b:=59) sp21859 sp21918) (joinSmall (lo:=21977) (a:=59) (b:=60) sp21977 sp22036)) (joinSmall (lo:=22096) (a:=119) (b:=119) (joinSmall (lo:=22096) (a:=59) (b:=60) sp22096 sp22155) (joinSmall (lo:=22215) (a:=59) (b:=60) sp22215 sp22274))) (joinSmall (lo:=22334) (a:=238) (b:=238) (joinSmall (lo:=22334) (a:=119) (b:=119) (joinSmall (lo:=22334) (a:=59) (b:=60) sp22334 sp22393) (joinSmall (lo:=22453) (a:=59) (b:=60) sp22453 sp22512)) (joinSmall (lo:=22572) (a:=119) (b:=119) (joinSmall (lo:=22572) (a:=59) (b:=60) sp22572 sp22631) (joinSmall (lo:=22691) (a:=59) (b:=60) sp22691 sp22750))))))) (joinSmall (lo:=22810) (a:=3802) (b:=3802) (joinSmall (lo:=22810) (a:=1901) (b:=1901) (joinSmall (lo:=22810) (a:=950) (b:=951) (joinSmall (lo:=22810) (a:=475) (b:=475) (joinSmall (lo:=22810) (a:=237) (b:=238) (joinSmall (lo:=22810) (a:=118) (b:=119) (joinSmall (lo:=22810) (a:=59) (b:=59) sp22810 sp22869) (joinSmall (lo:=22928) (a:=59) (b:=60) sp22928 sp22987)) (joinSmall (lo:=23047) (a:=119) (b:=119) (joinSmall (lo:=23047) (a:=59) (b:=60) sp23047 sp23106) (joinSmall (lo:=23166) (a:=59) (b:=60) sp23166 sp23225))) (joinSmall (lo:=23285) (a:=237) (b:=238) (joinSmall (lo:=23285) (a:=118) (b:=119) (joinSmall (lo:=23285) (a:=59) (b:=59) sp23285 sp23344) (joinSmall (lo:=23403) (a:=59) (b:=60) sp23403 sp23462)) (joinSmall (lo:=23522) (a:=119) (b:=119) (joinSmall (lo:=23522) (a:=59) (b:=60) sp23522 sp23581) (joinSmall (lo:=23641) (a:=59) (b:=60) sp23641 sp23700)))) (joinSmall (lo:=23760) (a:=475) (b:=476) (joinSmall (lo:=23760) (a:=237) (b:=238) (joinSmall (lo:=23760) (a:=118) (b:=119) (joinSmall (lo:=23760) (a:=59) (b:=59) sp23760 sp23819) (joinSmall (lo:=23878) (a:=59) (b:=60) sp23878 sp23937)) (joinSmall (lo:=23997) (a:=119) (b:=119) (joinSmall (lo:=23997) (a:=59) (b:=60) sp23997 sp24056) (joinSmall (lo:=24116) (a:=59) (b:=60) sp24116 sp24175))) (joinSmall (lo:=24235) (a:=238) (b:=238) (joinSmall (lo:=24235) (a:=119) (b:=119) (joinSmall (lo:=24235) (a:=59) (b:=60) sp24235 sp24294) (joinSmall (lo:=24354) (a:=59) (b:=60) sp24354 sp24413)) (joinSmall (lo:=24473) (a:=119) (b:=119) (joinSmall (lo:=24473) (a:=59) (b:=60) sp24473 sp24532) (joinSmall (lo:=24592) (a:=59) (b:=60) sp24592 sp24651))))) (joinSmall (lo:=24711) (a:=950) (b:=951) (joinSmall (lo:=24711) (a:=475) (b:=475) (joinSmall (lo:=24711) (a:=237) (b:=238) (joinSmall (lo:=24711) (a:=118) (b:=119) (joinSmall (lo:=24711) (a:=59) (b:=59) sp24711 sp24770) (joinSmall (lo:=24829) (a:=59) (b:=60) sp24829 sp24888)) (joinSmall (lo:=24948) (a:=119) (b:=119) (joinSmall (lo:=24948) (a:=59) (b:=60) sp24948 sp25007) (joinSmall (lo:=25067) (a:=59) (b:=60) sp25067 sp25126))) (joinSmall (lo:=25186) (a:=237) (b:=238) (joinSmall (lo:=25186) (a:=118) (b:=119) (joinSmall (lo:=25186) (a:=59) (b:=59) sp25186 sp25245) (joinSmall (lo:=25304) (a:=59) (b:=60) sp25304 sp25363)) (joinSmall (lo:=25423) (a:=119) (b:=119) (joinSmall (lo:=25423) (a:=59) (b:=60) sp25423 sp25482) (joinSmall (lo:=25542) (a:=59) (b:=60) sp25542 sp25601)))) (joinSmall (lo:=25661) (a:=475) (b:=476) (joinSmall (lo:=25661) (a:=237) (b:=238) (joinSmall (lo:=25661) (a:=118) (b:=119) (joinSmall (lo:=25661) (a:=59) (b:=59) sp25661 sp25720) (joinSmall (lo:=25779) (a:=59) (b:=60) sp25779 sp25838)) (joinSmall (lo:=25898) (a:=119) (b:=119) (joinSmall (lo:=25898) (a:=59) (b:=60) sp25898 sp25957) (joinSmall (lo:=26017) (a:=59) (b:=60) sp26017 sp26076))) (joinSmall (lo:=26136) (a:=238) (b:=238) (joinSmall (lo:=26136) (a:=119) (b:=119) (joinSmall (lo:=26136) (a:=59) (b:=60) sp26136 sp26195) (joinSmall (lo:=26255) (a:=59) (b:=60) sp26255 sp26314)) (joinSmall (lo:=26374) (a:=119) (b:=119) (joinSmall (lo:=26374) (a:=59) (b:=60) sp26374 sp26433) (joinSmall (lo:=26493) (a:=59) (b:=60) sp26493 sp26552)))))) (joinSmall (lo:=26612) (a:=1901) (b:=1901) (joinSmall (lo:=26612) (a:=950) (b:=951) (joinSmall (lo:=26612) (a:=475) (b:=475) (joinSmall (lo:=26612) (a:=237) (b:=238) (joinSmall (lo:=26612) (a:=118) (b:=119) (joinSmall (lo:=26612) (a:=59) (b:=59) sp26612 sp26671) (joinSmall (lo:=26730) (a:=59) (b:=60) sp26730 sp26789)) (joinSmall (lo:=26849) (a:=119) (b:=119) (joinSmall (lo:=26849) (a:=59) (b:=60) sp26849 sp26908) (joinSmall (lo:=26968) (a:=59) (b:=60) sp26968 sp27027))) (joinSmall (lo:=27087) (a:=237) (b:=238) (joinSmall (lo:=27087) (a:=118) (b:=119) (joinSmall (lo:=27087) (a:=59) (b:=59) sp27087 sp27146) (joinSmall (lo:=27205) (a:=59) (b:=60) sp27205 sp27264)) (joinSmall (lo:=27324) (a:=119) (b:=119) (joinSmall (lo:=27324) (a:=59) (b:=60) sp27324 sp27383) (joinSmall (lo:=27443) (a:=59) (b:=60) sp27443 sp27502)))) (joinSmall (lo:=27562) (a:=475) (b:=476) (joinSmall (lo:=27562) (a:=237) (b:=238) (joinSmall (lo:=27562) (a:=118) (b:=119) (joinSmall (lo:=27562) (a:=59) (b:=59) sp27562 sp27621) (joinSmall (lo:=27680) (a:=59) (b:=60) sp27680 sp27739)) (joinSmall (lo:=27799) (a:=119) (b:=119) (joinSmall (lo:=27799) (a:=59) (b:=60) sp27799 sp27858) (joinSmall (lo:=27918) (a:=59) (b:=60) sp27918 sp27977))) (joinSmall (lo:=28037) (a:=238) (b:=238) (joinSmall (lo:=28037) (a:=119) (b:=119) (joinSmall (lo:=28037) (a:=59) (b:=60) sp28037 sp28096) (joinSmall (lo:=28156) (a:=59) (b:=60) sp28156 sp28215)) (joinSmall (lo:=28275) (a:=119) (b:=119) (joinSmall (lo:=28275) (a:=59) (b:=60) sp28275 sp28334) (joinSmall (lo:=28394) (a:=59) (b:=60) sp28394 sp28453))))) (joinSmall (lo:=28513) (a:=950) (b:=951) (joinSmall (lo:=28513) (a:=475) (b:=475) (joinSmall (lo:=28513) (a:=237) (b:=238) (joinSmall (lo:=28513) (a:=118) (b:=119) (joinSmall (lo:=28513) (a:=59) (b:=59) sp28513 sp28572) (joinSmall (lo:=28631) (a:=59) (b:=60) sp28631 sp28690)) (joinSmall (lo:=28750) (a:=119) (b:=119) (joinSmall (lo:=28750) (a:=59) (b:=60) sp28750 sp28809) (joinSmall (lo:=28869) (a:=59) (b:=60) sp28869 sp28928))) (joinSmall (lo:=28988) (a:=237) (b:=238) (joinSmall (lo:=28988) (a:=118) (b:=119) (joinSmall (lo:=28988) (a:=59) (b:=59) sp28988 sp29047) (joinSmall (lo:=29106) (a:=59) (b:=60) sp29106 sp29165)) (joinSmall (lo:=29225) (a:=119) (b:=119) (joinSmall (lo:=29225) (a:=59) (b:=60) sp29225 sp29284) (joinSmall (lo:=29344) (a:=59) (b:=60) sp29344 sp29403)))) (joinSmall (lo:=29463) (a:=475) (b:=476) (joinSmall (lo:=29463) (a:=237) (b:=238) (joinSmall (lo:=29463) (a:=118) (b:=119) (joinSmall (lo:=29463) (a:=59) (b:=59) sp29463 sp29522) (joinSmall (lo:=29581) (a:=59) (b:=60) sp29581 sp29640)) (joinSmall (lo:=29700) (a:=119) (b:=119) (joinSmall (lo:=29700) (a:=59) (b:=60) sp29700 sp29759) (joinSmall (lo:=29819) (a:=59) (b:=60) sp29819 sp29878))) (joinSmall (lo:=29938) (a:=238) (b:=238) (joinSmall (lo:=29938) (a:=119) (b:=119) (joinSmall (lo:=29938) (a:=59) (b:=60) sp29938 sp29997) (joinSmall (lo:=30057) (a:=59) (b:=60) sp30057 sp30116)) (joinSmall (lo:=30176) (a:=119) (b:=119) (joinSmall (lo:=30176) (a:=59) (b:=60) sp30176 sp30235) (joinSmall (lo:=30295) (a:=59) (b:=60) sp30295 sp30354)))))))))
  have good : (List.range 30414).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 925000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 30413 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 30413 := by
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


private def packet (i : ℕ) : ℕ := (if i < 235 then (if i < 117 then (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 10 then (if i < 8 then 0 else (if i < 9 then 0 else 0)) else (if i < 12 then (if i < 11 then 0 else 0) else (if i < 13 then 0 else 0)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0 else (if i < 16 then 0 else 0)) else (if i < 19 then (if i < 18 then 0 else 0) else (if i < 20 then 0 else 0))) else (if i < 25 then (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else 0)) else (if i < 27 then (if i < 26 then 0 else 0) else (if i < 28 then 0 else 0))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then 0 else (if i < 31 then 0 else 0)) else (if i < 34 then (if i < 33 then 0 else 0) else (if i < 35 then 0 else 0))) else (if i < 39 then (if i < 37 then 0 else (if i < 38 then 0 else 0)) else (if i < 41 then (if i < 40 then 0 else 0) else (if i < 42 then 0 else 0)))) else (if i < 50 then (if i < 46 then (if i < 44 then 0 else (if i < 45 then 0 else 0)) else (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else 0))) else (if i < 54 then (if i < 52 then (if i < 51 then 0 else 0) else (if i < 53 then 0 else 0)) else (if i < 56 then (if i < 55 then 0 else 0) else (if i < 57 then 0 else 0)))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then 0 else (if i < 60 then 0 else 0)) else (if i < 63 then (if i < 62 then 0 else 0) else (if i < 64 then 0 else 0))) else (if i < 68 then (if i < 66 then 0 else (if i < 67 then 0 else 0)) else (if i < 70 then (if i < 69 then 0 else 0) else (if i < 71 then 0 else 0)))) else (if i < 79 then (if i < 75 then (if i < 73 then 0 else (if i < 74 then 0 else 0)) else (if i < 77 then (if i < 76 then 0 else 0) else (if i < 78 then 0 else 0))) else (if i < 83 then (if i < 81 then (if i < 80 then 0 else 0) else (if i < 82 then 0 else 0)) else (if i < 85 then (if i < 84 then 0 else 0) else (if i < 86 then 0 else 0))))) else (if i < 102 then (if i < 94 then (if i < 90 then (if i < 88 then 0 else (if i < 89 then 0 else 0)) else (if i < 92 then (if i < 91 then 0 else 0) else (if i < 93 then 0 else 0))) else (if i < 98 then (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else 0)) else (if i < 100 then (if i < 99 then 0 else 0) else (if i < 101 then 0 else 0)))) else (if i < 109 then (if i < 105 then (if i < 103 then 0 else (if i < 104 then 0 else 0)) else (if i < 107 then (if i < 106 then 0 else 0) else (if i < 108 then 0 else 0))) else (if i < 113 then (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0 else 0)) else (if i < 115 then (if i < 114 then 0 else 0) else (if i < 116 then 0 else 0))))))) else (if i < 176 then (if i < 146 then (if i < 131 then (if i < 124 then (if i < 120 then (if i < 118 then 0 else (if i < 119 then 0 else 0)) else (if i < 122 then (if i < 121 then 0 else 0) else (if i < 123 then 0 else 0))) else (if i < 127 then (if i < 125 then 0 else (if i < 126 then 0 else 0)) else (if i < 129 then (if i < 128 then 0 else 0) else (if i < 130 then 0 else 0)))) else (if i < 138 then (if i < 134 then (if i < 132 then 0 else (if i < 133 then 0 else 0)) else (if i < 136 then (if i < 135 then 0 else 0) else (if i < 137 then 0 else 0))) else (if i < 142 then (if i < 140 then (if i < 139 then 0 else 0) else (if i < 141 then 0 else 0)) else (if i < 144 then (if i < 143 then 0 else 0) else (if i < 145 then 0 else 0))))) else (if i < 161 then (if i < 153 then (if i < 149 then (if i < 147 then 0 else (if i < 148 then 0 else 0)) else (if i < 151 then (if i < 150 then 0 else 0) else (if i < 152 then 0 else 0))) else (if i < 157 then (if i < 155 then (if i < 154 then 0 else 0) else (if i < 156 then 0 else 0)) else (if i < 159 then (if i < 158 then 0 else 0) else (if i < 160 then 0 else 0)))) else (if i < 168 then (if i < 164 then (if i < 162 then 0 else (if i < 163 then 0 else 0)) else (if i < 166 then (if i < 165 then 0 else 0) else (if i < 167 then 0 else 0))) else (if i < 172 then (if i < 170 then (if i < 169 then 0 else 0) else (if i < 171 then 0 else 0)) else (if i < 174 then (if i < 173 then 0 else 0) else (if i < 175 then 0 else 0)))))) else (if i < 205 then (if i < 190 then (if i < 183 then (if i < 179 then (if i < 177 then 0 else (if i < 178 then 0 else 0)) else (if i < 181 then (if i < 180 then 0 else 0) else (if i < 182 then 0 else 0))) else (if i < 186 then (if i < 184 then 0 else (if i < 185 then 0 else 0)) else (if i < 188 then (if i < 187 then 0 else 0) else (if i < 189 then 0 else 0)))) else (if i < 197 then (if i < 193 then (if i < 191 then 0 else (if i < 192 then 0 else 0)) else (if i < 195 then (if i < 194 then 0 else 0) else (if i < 196 then 0 else 0))) else (if i < 201 then (if i < 199 then (if i < 198 then 0 else 0) else (if i < 200 then 0 else 0)) else (if i < 203 then (if i < 202 then 0 else 0) else (if i < 204 then 0 else 0))))) else (if i < 220 then (if i < 212 then (if i < 208 then (if i < 206 then 0 else (if i < 207 then 0 else 0)) else (if i < 210 then (if i < 209 then 0 else 0) else (if i < 211 then 0 else 0))) else (if i < 216 then (if i < 214 then (if i < 213 then 0 else 0) else (if i < 215 then 0 else 0)) else (if i < 218 then (if i < 217 then 0 else 0) else (if i < 219 then 0 else 0)))) else (if i < 227 then (if i < 223 then (if i < 221 then 0 else (if i < 222 then 0 else 0)) else (if i < 225 then (if i < 224 then 0 else 0) else (if i < 226 then 0 else 0))) else (if i < 231 then (if i < 229 then (if i < 228 then 0 else 0) else (if i < 230 then 0 else 0)) else (if i < 233 then (if i < 232 then 0 else 0) else (if i < 234 then 0 else 0)))))))) else (if i < 353 then (if i < 294 then (if i < 264 then (if i < 249 then (if i < 242 then (if i < 238 then (if i < 236 then 0 else (if i < 237 then 0 else 0)) else (if i < 240 then (if i < 239 then 0 else 0) else (if i < 241 then 0 else 0))) else (if i < 245 then (if i < 243 then 0 else (if i < 244 then 0 else 0)) else (if i < 247 then (if i < 246 then 0 else 0) else (if i < 248 then 0 else 0)))) else (if i < 256 then (if i < 252 then (if i < 250 then 0 else (if i < 251 then 0 else 0)) else (if i < 254 then (if i < 253 then 0 else 0) else (if i < 255 then 0 else 0))) else (if i < 260 then (if i < 258 then (if i < 257 then 0 else 0) else (if i < 259 then 0 else 0)) else (if i < 262 then (if i < 261 then 0 else 0) else (if i < 263 then 0 else 0))))) else (if i < 279 then (if i < 271 then (if i < 267 then (if i < 265 then 0 else (if i < 266 then 0 else 0)) else (if i < 269 then (if i < 268 then 0 else 0) else (if i < 270 then 0 else 0))) else (if i < 275 then (if i < 273 then (if i < 272 then 0 else 0) else (if i < 274 then 0 else 0)) else (if i < 277 then (if i < 276 then 0 else 0) else (if i < 278 then 0 else 0)))) else (if i < 286 then (if i < 282 then (if i < 280 then 0 else (if i < 281 then 0 else 0)) else (if i < 284 then (if i < 283 then 0 else 0) else (if i < 285 then 0 else 0))) else (if i < 290 then (if i < 288 then (if i < 287 then 0 else 0) else (if i < 289 then 0 else 0)) else (if i < 292 then (if i < 291 then 0 else 0) else (if i < 293 then 0 else 0)))))) else (if i < 323 then (if i < 308 then (if i < 301 then (if i < 297 then (if i < 295 then 0 else (if i < 296 then 0 else 0)) else (if i < 299 then (if i < 298 then 0 else 0) else (if i < 300 then 0 else 0))) else (if i < 304 then (if i < 302 then 0 else (if i < 303 then 0 else 0)) else (if i < 306 then (if i < 305 then 0 else 0) else (if i < 307 then 0 else 0)))) else (if i < 315 then (if i < 311 then (if i < 309 then 0 else (if i < 310 then 0 else 0)) else (if i < 313 then (if i < 312 then 0 else 0) else (if i < 314 then 0 else 0))) else (if i < 319 then (if i < 317 then (if i < 316 then 0 else 0) else (if i < 318 then 0 else 0)) else (if i < 321 then (if i < 320 then 0 else 0) else (if i < 322 then 0 else 0))))) else (if i < 338 then (if i < 330 then (if i < 326 then (if i < 324 then 0 else (if i < 325 then 0 else 0)) else (if i < 328 then (if i < 327 then 0 else 0) else (if i < 329 then 0 else 0))) else (if i < 334 then (if i < 332 then (if i < 331 then 0 else 0) else (if i < 333 then 0 else 0)) else (if i < 336 then (if i < 335 then 0 else 0) else (if i < 337 then 0 else 0)))) else (if i < 345 then (if i < 341 then (if i < 339 then 0 else (if i < 340 then 0 else 0)) else (if i < 343 then (if i < 342 then 0 else 0) else (if i < 344 then 0 else 0))) else (if i < 349 then (if i < 347 then (if i < 346 then 0 else 0) else (if i < 348 then 0 else 0)) else (if i < 351 then (if i < 350 then 0 else 0) else (if i < 352 then 0 else 0))))))) else (if i < 412 then (if i < 382 then (if i < 367 then (if i < 360 then (if i < 356 then (if i < 354 then 0 else (if i < 355 then 0 else 0)) else (if i < 358 then (if i < 357 then 0 else 0) else (if i < 359 then 0 else 0))) else (if i < 363 then (if i < 361 then 0 else (if i < 362 then 0 else 0)) else (if i < 365 then (if i < 364 then 0 else 0) else (if i < 366 then 0 else 0)))) else (if i < 374 then (if i < 370 then (if i < 368 then 0 else (if i < 369 then 0 else 0)) else (if i < 372 then (if i < 371 then 0 else 0) else (if i < 373 then 0 else 0))) else (if i < 378 then (if i < 376 then (if i < 375 then 0 else 0) else (if i < 377 then 0 else 0)) else (if i < 380 then (if i < 379 then 0 else 0) else (if i < 381 then 0 else 0))))) else (if i < 397 then (if i < 389 then (if i < 385 then (if i < 383 then 0 else (if i < 384 then 0 else 0)) else (if i < 387 then (if i < 386 then 0 else 0) else (if i < 388 then 0 else 0))) else (if i < 393 then (if i < 391 then (if i < 390 then 0 else 0) else (if i < 392 then 0 else 0)) else (if i < 395 then (if i < 394 then 0 else 0) else (if i < 396 then 0 else 0)))) else (if i < 404 then (if i < 400 then (if i < 398 then 0 else (if i < 399 then 0 else 0)) else (if i < 402 then (if i < 401 then 0 else 0) else (if i < 403 then 0 else 0))) else (if i < 408 then (if i < 406 then (if i < 405 then 0 else 0) else (if i < 407 then 0 else 0)) else (if i < 410 then (if i < 409 then 0 else 0) else (if i < 411 then 0 else 0)))))) else (if i < 441 then (if i < 426 then (if i < 419 then (if i < 415 then (if i < 413 then 0 else (if i < 414 then 0 else 0)) else (if i < 417 then (if i < 416 then 0 else 0) else (if i < 418 then 0 else 0))) else (if i < 422 then (if i < 420 then 0 else (if i < 421 then 0 else 0)) else (if i < 424 then (if i < 423 then 0 else 0) else (if i < 425 then 0 else 0)))) else (if i < 433 then (if i < 429 then (if i < 427 then 0 else (if i < 428 then 0 else 0)) else (if i < 431 then (if i < 430 then 0 else 0) else (if i < 432 then 0 else 0))) else (if i < 437 then (if i < 435 then (if i < 434 then 0 else 0) else (if i < 436 then 0 else 0)) else (if i < 439 then (if i < 438 then 0 else 0) else (if i < 440 then 0 else 0))))) else (if i < 456 then (if i < 448 then (if i < 444 then (if i < 442 then 0 else (if i < 443 then 0 else 0)) else (if i < 446 then (if i < 445 then 0 else 0) else (if i < 447 then 0 else 0))) else (if i < 452 then (if i < 450 then (if i < 449 then 0 else 0) else (if i < 451 then 0 else 0)) else (if i < 454 then (if i < 453 then 0 else 0) else (if i < 455 then 0 else 0)))) else (if i < 463 then (if i < 459 then (if i < 457 then 0 else (if i < 458 then 0x2be5ded2c0949c98e46b1fe0e8468c2e614788ac38416908882c80bc00002be57f82d094cc9964712078eec6b830214e08f83c017f09303040d200002be521e2bc947496c45d2048ea06882e914788d83b017808d82fc0bc00002be4c472c014a498c46a2030e8c68a2e614a08c439816b08182c80bc00002be46872b0145095844c1f78e5867a2dd141887c39617008c82d40b200002be40822ca150c9b447a2090eac6b630015309083c018309503040c400002be3abc2b614349624532008e7c6942f214688e03ac17108602ec0d000002be34d52c514a09a446e2048ea869a2ea14608a038c16d08802dc0ac00002be2ef92c294dc9bc47620d0ef06b02f814f89343e018808d83040cc00002be293f2af93f895644d1f58df463e2c6139886c38016b08e02f40d800002be23852ac13d49364321ed8e2065c2cb13e086037815908382a00b800002be1da52c294ac9a046c2080eb46a62f114c88f83b818209083080b400002be17d52c1148c98a4652050ec06ac2ed140888c38616b08302a40a800002be120b2bc146896c4551f38e2865e2d3138089c38417208d02e00b400002be0c332bc946497a4682058ea86922ec14688d83b417f09503240bc00002be06572c0149499e4692070eac69a2ec14908c83aa18009002f80c400002be004c2d515089c84832110f146e630e152091c3be18109082f40a800002bdfa7b2b5145495c4562020eb869c2e813d088c39016d08582d40b800002bdf4bd2a993f493c4391ee0e2c64a2d313e886437615b08782cc0a200002bdeeff2b614609764682068eb869e2f1142889039e17008c03080c800002bde96e29713548ec41e1e28de06402c1137883c37816908482d40ae00002bde38c2c494909a446e2070ea06922e514808cc3be17f09202e40c600002bdddba2bc94849844632070ec06c02f614a08c03ae17108b82f00c000002bdd80a2ab13e09324391f00e0c65c2d713e086c39016f08a02dc0ac00002bdd2342bb947897a46a2068edc6b42f414f08e03be17d08902f40c400002bdcc622b514609684612098ed86962f614908e03c417d08f83200ca00002bdc6a22b114389584531f68e6067c2de143088c37816408182c40b600002bdc0d42ba944c9724642008e886a22f214d08dc3ac16c08b02f80d200002bdbb152ae140494044b1fb8e4466c2e314288d03ae186092031c0ba00002bdb51d2c994d09b447a2150f286ca30815108fc3c618109383280cc00002bdaf542bb145496c44a1f18e2467c2e614388d439c17c08e03100ba00002bda99c2ae142495244b1fb8e706822e814308d03a417008b82d40b400002bda3f32a813dc9344351ed0ddc6402c3139086c38215807c82b80a000002bd9e1d2b8940896245b2008e7067a2db140087c38416708402d80b200002bd98342c314c89904652028eb06922e914908c03ae17a08f82fc0b600002bd92682b994609784591fb8eb06842e514988c439416608782e00b200002bd8c922b9147c99c47720a8ed86a02e714908d43aa16b08502ac0a600002bd86af2c394b899446d2088ed06b42f014888c43a817208d03080cc00002bd80c92c194c49ae47a20f0f046aa2fa14d08f43b819009a833c0d000002bd7b042ba945c96a4551fe0e8c69c2ed148889839617108702e80b800002bd753e2b494549764652000e6867a2e4141088839016b08702dc0c800002bd6f692b6943096c4571fd8e806822d814408a838e17008c03000be00002bd699b2b593fc94e4561fc0e886862de14008903a015a08102b80b200002bd63b72c294909864612028e9069a2f114688d43aa16c08a82e80b600002bd5dff2a993989264391f48e506802dc13f88b03a217408982e80ce00002bd583a2b194249564451f28e2064a2d213d885438c16c08402cc0ae00002bd526f2ad94009584481fa8e606722e614588c03b417b08982e40c200002bd4c822c4948c98c4622058ec06862e114308a438415b07e82a009e00002bd46af2b6143c9564512018ea46962f814988bc3a416a08502d00bc00002bd40d42be945c9864621fd0e746962e914288b039c17a08b83140c600002bd3add2ca15009b647820b0ed46942ea14608a039216c08e82d80bc00002bd35112af940095444d1fd0e9c67a2e114688bc3a017608902d00ae00002bd2f562b2942095e4591fe8e9067a2ea14488b43c617d08e02d40b600002bd29872bd94c099846a2058ea069a2ea14788b83b017d08f02d80b800002bd23bd2b794489704531f80e586842e2141089039217008882c00b200002bd1e0e2aa13cc94a44a1f18e1c65e2cb139885837416708302b40ac00002bd184e2b314289844692050eb86aa2f514a08d838e16c08e02f80bc00002bd127f2b9144095e4592018e846922eb145088c39216f08682e80b200002bd0cad2b7142c95c44d1f40e486802e114588b039e17609003000d800002bd06e72b494409624501f60e586902f214c08d03a216708402dc0b400002bd011b2bf94589764581fd8e5465c2c913c885438e15d08682dc0b200002bcfb452bf94b49984672090ec06a22fe15509203d218b09083080ca00002bcf5902ab940095044d1f70e5866a2e314188bc3a617308682e00ac00002bcefbf2bb946c97e46d2060eb068e2e914488c83ae17a08a82dc0be000 else 0x2bfd2672c4149c9ae4802138f146bc2f714e88fc3ba18209383040d000002bfcc982b7945c9784551fe0e806942f414588d839a17208c030c0be00002bfc6d92a913b092c4341ee0e0c65e2e414508b039816508902e00c400002bfc1022bf147c97645b2028e9c6a22ef14b88f83b417e08d82f80b800002bfbb3a2b4943497245c2068eb06942f614908d83b018609783380b200002bfb55a2bb948098e4602020ec06ba30514f89003c017908c82e00cc00002bfafae2aa93f093643e1ef0dec65c2d713e088838416c08782cc0a600002bfaa0b2a113a09404391f50e6c67c2e113e087438416a08582cc0b400002bfa4482b2144097c4632028ed06b22fa14f89203d818e09b031c0c400002bf9e6b2c2947c98246b2078ec46aa2f314a88cc39a17608602dc0d600002bf987a2cd94b499a47120a8ee86c031015a09383b417808f82dc0d000002bf92df2a1139490a42d1ee8e206622d614088903a016f090831c0e000002bf8d162b794609704571fe0eac6a42e414688cc3a417608b82e80ac00002bf874a2b8146898c4612008e846862ec13f089839417008882e00be00002bf819f2aa13e493043c1f18e1465a2d0135085838617408882f40bc00002bf7bde2b614409604552008ea46962e814908bc3a217908e03000c200002bf76042bf94709904642028e986a02f614c090c3c818809503400ca00002bf70232c3949099e4702050ea46982f014608b43a818509382f40aa00002bf6a3a2ca94e49b047b20d0eec6a22f314c08c83bc17a08c02f80c000002bf646b2be948c97c4652068eb06a62f114a08b03aa17008f03100b600002bf5ea92b394149584541fe0e6066e2db13d086838416208702fc0ac00002bf58d42bb146098a46e2050eac6b02f114c08dc3bc17b08b03040cc00002bf52f32c514a498e4652018e8468c2e214508d43c818209003180c000002bf4d1d2c3149097e4541f80e606822dd14188a038a16f08d02cc0aa00002bf47532b2942c9664551fc8e646722d913d884c39016308702f00b200002bf41682c714b09a64682028e786962ef14789003b816c08d82e80b000002bf3b982ba14389664591fd8e746822e714688d03ac17a08d82dc0bc00002bf35aa2c814bc9a04742040ea468c2e414208a83a617308882d80b600002bf30052a793d092a4441f68e346662d813a888c38a16308b82ec0c000002bf2a002d81560a0049921b0f706f630d151092c3c217708e82fc0c400002bf24602a2139c93643e1f90e606762e114488bc3bc18209403200e000002bf1e982b8945096a4551fc0e5866a2e2141888439417408f03040b600002bf18cd2b5142894644a1f88e8c67c2ec14688bc3aa17508702f00c200002bf12dd2c714d49b047b2098ed06a02ed14908d83a416608982c00b000002bf0d3d2a593c093843e1ee0df46502d613e88c839216808c02f40b800002bf07412cc95089be4862128ee06bc2fc14d08fc3ac17b08802cc0ac00002bf01782b214209584401f58e7468c2ef13f08b83b017d08f02f00ae00002befb9d2ba147097045a2020eb86a22ed14989003cc17d08b82c009c00002bef5b42c514c49944722050ea86bc2f414a08f03c818a08e03100be00002beefd82c194b098a4641fe0ea86a22e514888b839617e08c03040ce00002beea332ab93fc9364371f08e286622e013e084837615d08582c40a200002bee4652b614309484451fb8e2c66a2db139883035c15607f82940ac00002bede8c2bb146496c4511f50e646822df141088439417708a02d80a800002bed8be2b6145897245b2000e706742da14588e03ac186096031c0ce00002bed2d92c514b097e4652000ea46902f314a08c43ac16f08a02d00b400002becd2f2a913bc92443a1f10e3066c2d313a088839617808b02e80ca00002bec71e2d894f89ca47520d0f086d22fe14988dc3a216a08802d80ae00002bec1212d014f49bc4872108f146c430b15809383dc18e098030c0cc00002bebb2d2d315549ea4912180f6c6e830615288f03c618509303300bc00002beb5752ac94009584522000e686882eb14a08f03c018009082f80c200002beafa82b9949c98045c1fd0e686822e914708ac39a17b08d02bc0b600002bea9e82b9944c95e4491f88e506742eb14688a038e16808782e00bc00002bea40c2bf948c99046a2080ec46ba2e914688a438c17808f03080c600002be9e2a2bd14749764531fc0e546722d5139087c38c16d08a02d40b400002be98432c3149c9a44702088ee86962ef14d08d83ba17b08b02f80b200002be92772bd94889864712058e7868a2e1142086838416a08a02e00b000002be8cd629d139492a4341ee8e146722df14308a839616a08502c00b600002be86f42c0948c99045c2020ebc6ac2f014188c43ac17e08c02f80be00002be81112c0947897a45d1fe0e8c68a2ec14708e43aa17308d02f00bc00002be7b242ca94c898445c1fd0e746782e314808d83c2186090830c0d000002be756e2ac941095044f1f78e746942ea14688fc3b617909002ec0c200002be6fa02ad941895e44c1f80e846802e0141887039016808c02dc0a800002be69c52c594dc9d84892140f006d031315509143c218308e82f40b200002be63cf2bf148c99646820c0edc6a22f114c890c3d618809403480d6000)) else (if i < 461 then (if i < 460 then 0x2c146cf2d995349ec49721e0f406ea30e15609343ca189091831c0d600002c141142ac943095045f2010e7c68a2de14188a039817708f03140c400002c13b2c2c714e89aa47b20e0f086d830714b08c03a217308b02c40ba00002c135562bb948c98846d2048e7c67e2e414308a439216908c02f00c200002c12f742c194ac9924672040e946822e714808c43b416f08d02e40a000002c129c52ad93f89484421f30e4866c2e614508b43aa17f09503240be00002c123c32ce94d89c44842128f286d830315409203c218109203040ce00002c11dc92d194fc9d44862140ef06b82f414f88f43aa17708d82e00a800002c1182d2a013608fe4221e30dac6142b012e884838615e08882ec0a200002c112492bd945097c4622040ea869a2ef14408c039a17008902d00ac00002c10c612c1149098c46e20b0ef06b82fa14d09343f2196095031c0da00002c106842c614c89984792048ec069c2fd148888439217208d83040c000002c100f329e13a49164271e78dd46582cd13e088836415708082c00a800002c0fb252b994489784652018ea46922e914408b03a216b08e02d40ae00002c0f5572bb148098046c2000eb067e2df14808ac3a417709082ec0b200002c0ef982b2942895c4521ff0e646762ee14288b83b818d092831c0ce00002c0e9a82cb14d89a44682068e986962f114188d03a416d08c02e00aa00002c0e3be2c014a89944692010e9c6a42f014688dc3a018309282fc0b800002c0de122a713c493c4461ec8e306582d913e08a439416f08c02f80be00002c0d8312bd94a096c45a1fb0e506902ef14a88e03bc18109283080c200002c0d2692ba94749a447120b0ec46962f314488b03b217908b02d80b800002c0cc8f2ba944495644e1f90e286702e0140888439817708b82cc0be00002c0c6c32b8947897c45c2008eb06802e813f885837216408582d00a600002c0c0db2c194a098246c2020e8868a2ec14508cc3b817109103080ba00002c0bb172b514289784571fb0e946982f314a08a839216808582b40a800002c0b5502b4945898a4601fc8e646922ee14a88dc3ce18109203180c400002c0af4a2d415089c648120b0f106d42fc14508a43b017f08b02f40b200002c0a9b729c938492043f1f48e0865a2cd137083436415e08302f40c400002c0a3e02b9142c95244d1f90e4c67c2e0141088c37e16208682a80aa00002c09e302ae941c96044a1f38e286542cb13a082836a15a07f02c40b800002c098582c1148c97e45b1f98e546782e614588d83bc18008902b80aa00002c092762bf947c9944652098ed86a62f814f89283e018909182e40c600002c08ca22b5140c93a4441ef0e3464e2d513d88983a216c08d02d80b400002c086af2c794d09b847920c0ebc6b82ff14f88c43aa17708f82fc0b800002c080df2b9144495e4591f90e386722e314688e039417108e02e40b600002c07aec2ca14f89ae47420b8f006ae2f914e88e039217308f82f80c800002c074f42c6148499047120c0ee06b82ff14f09143b618309183300d000002c06f022ca149498a4682038eb46aa2ff14f88f83a617508b82e00aa00002c0693d2b513e494243d1f10e3464e2d713e88983a417908702c40ae00002c0636e2b8946895445c1ff8e986962e914b88e43be17c09102f40ca00002c05d742cb94fc9b44842108f106ba30115009203c418608e02e40c400002c057b12b3942496a4591ff8e9c6aa2f514b08f83b417909282fc0bc00002c051c42c214ec9ae4722098ec06a230114b88f43aa17b09283100c400002c04be22c5946899446d2068ebc6782d813f08b039c17408702b80c000002c0461f2b3940c95644d1fc8e946942f514f08d83b017708d03040ca00002c040452c394789884581fe8e7c67c2f314508c43a817108d83000be00002c03a6d2b714089584531ff0e9c6a62f714d08f03d6193097831c0be00002c034bc2ac14109624602068ed06b82f414a08d03b218209503180c200002c02ef12ba945c9764571fe8e7c6942f214788cc39e16f08e82d80c800002c0291b2bf94a899245c2000e9068c2e614188a839a17608e82f40bc00002c0235c2b694389644542000e706922f914989043c418009182f80c800002c01d8f2b894489744531f98e6c6782dc14288a03a017408b82d80b800002c017a12c9947098c4652090ec06b230714f89143c417d09083300d200002c011d92b2943096245b2008e806862f414b88c83b017f08e03040ca00002c00c4829c93a892e4431f50e2464e2cd138088039216c08e02f40ce00002c006722ba94589704552020e9467c2ea14708e43ba17208902f80c200002c000cf2a2139891c43b1ec0e206662d213c887839416c08b82d40a600002bffaf92bf947c9864522028eb86a22ea146889839617908f82e40ac00002bff5252ba14389624572010ea86a62f414888e83aa17908f83380d400002bfef652b514289664531f90e646822e113e089038216408702e80b800002bfe9862c514a097c4611ff0e906982ed14488d03a616808502b80b000002bfe3c42b2140c94644b1f78e5c66e2db138888039c17908882e00c600002bfddf22ba94549764531fc8e906962f614d88e03c417f08e03180c600002bfd8382b3143097045a2068eac6aa2f414f08f43bc17d09483180c0000 else 0x2c2bae02bc147897c4612030e7066c2d413d086438816b08e02e80c800002c2b5222b5147096e4511f90e9069a2ea14808d43aa17608f83180cc00002c2af642ad94049444471f10e186362ba12f882c37a16308502b80a000002c2a9a12b894289584511fb8e6468a2e514588c83c417f08c02d40a400002c2a3bd2bd94b89aa47120c0ee46962ef14788d03a818009b03240c200002c29df62b4142c9684511fb8e546642ec14b08bc3a816808902f00b400002c2984b2a9140095644d2030e7c67a2e2142887c39017108982ac0a600002c292822b8946c97c4631fc0e406542d014088c03c218008f83380c600002c28ca82c114b49a246b2060eb469e2ee14b08c83b218208b82d80be00002c286cf2be94a499646a2040ea068a2e814708b4390179092030c0cc00002c280f92be149c9924692060ec86a02fc14b08c83a017d08802f40c200002c27b052ce150c9d248d2148f0c6d230f156890c3c218d092031c0c800002c275422b114349784661fd8e9068e2f414708b83aa17709283040c800002c26f872b8140c9624521f70e586682dd13908683a017b08a02e40a800002c2698f2ce14ec9c64882150f186da311156092c3ce17d09103180c800002c263c02b6942c95c4511f80e686642df14408c039c17608882d40b600002c25dfd2b3943495245b1ff0e8869e2eb14908f83c616f08702d80c600002c258382b2941495a4501fa0e7066e2eb14b08e83ba17e08e02e80aa00002c252612bf14a898e46d2070ef86c630114d88fc3c418709282f40c400002c24c802c1149c9844642010e846762d614288bc39e17508b82e80bc00002c2468d2c914a49a047920f0f306c230114b08d83a617808d02cc0b600002c240dc2b013e493643e1f70e586782e214408c43b817d08c02a80aa00002c23b022b914609924682038e8c68c2e314388a838217009102dc0ce00002c235432b194189604541fe8e906862e114208a839c16808682c40b400002c22fbe297937490841f1df8d8c61a2bc130084037a16207f82a409800002c229e22bc14c899847220b0ee46a42ee14488b43a217908b82dc0ba00002c223cd2d695509e64992158f246d030b15589483de18909503480ce00002c21dda2c794dc99a4742090ed46ba2ff15109203c818009282ec0ba00002c217f62c5149899447420b8ee06b22f614d88ec3b817c090831c0ca00002c212272bc144896e4551fd8e7467c2e8143088c39016e08602c80a600002c20c472c3149498a4692038eb86922f6144888c38817008702c00a200002c206762b8945096c4521fb8e606802ea14988dc3ac16e08c82ec0b600002c200a32ba945897846a2050ef06d0309157098440419a097032c0d200002c1fac62c214c899e46a1fd8e646842ee14a88b43ae17208a02cc0bc00002c1f4ec2c1145498446020a8ed06922ef14b88bc3a017108e82dc0b600002c1ef0b2bd946495a4551fd8e9c6902f314608bc3a417908b02dc0b000002c1e92f2bc144496c4592020ea06a02ee143889c39a16d08c02c809e00002c1e3732b314089504501ff8ea86ae2f615009243d217908f02f40c800002c1dd682d195209ca4742088ebc6aa2fe15009103c617c09183040c400002c1d77e2c494889964662038e9469a2e914608d03a6180090830c0ce00002c1d1b42b3141c95c45d1fe8ea068a2e614988e83b817908f02fc0c200002c1cbb12d314e49c84832120f186e430d15809083d618909082f40ba00002c1c5b12ce14f89bc47b20a8ebc69c2e614488c43ae18609703280be00002c1c0002ab142494e4451f98e806762dd143889439c16a08802cc0be00002c1ba3f2b314389644561fe0e9868c2ed14b88d03a017108a82d80b600002c1b4802b4940c94443f1f00e1c6562d2141088438816b08882dc0be00002c1aeb32b6946c9824642040eb06aa2fb15008f03a017b09182f40b600002c1a8d32c394989a447920d8f006c42ff14b09083c419109803400c600002c1a30c2b8943895e4521f90e3865e2df14088b4394170084828c09a00002c19d312ba946c96c45e1ff0e786a42f715089143c018108c03100d600002c197842a913d495044e1fb0e706702dd143887837816808802f40b600002c191a42bf947897e4591fe0e4467a2d514688c43ae17909303300d400002c18bdc2b1140895044d1f50e0c66a2dc14008a839217408f83000c600002c1862d2a593c09364491f90e646842ec14388b039c17508882f40c200002c180672ba945c9784531fc0e8867c2eb14a89003b417d09083040be00002c17a5a2d315049be48220e8ecc69c2f7144889439016c08502e40b800002c174942b614449744622008e8c6722e014508b03ae18308b83040ba00002c16f1429013249024131e10db861a2ab12b87f035414307a82900a600002c169662ab141093443a1f18e386542c6133882c36a15808702f80ac00002c163c12a313c090c4361ee8e146582d213f888439017208602d40aa00002c15e142a793f496644b1f38e0c63c2cc134086838016a08902c80ac00002c158742a013848f84111e40dcc63c2b812f882836a158083828c0b600002c152ac2b4140c94e4541fc8e686742d513e888838617108d02d00b400002c14cdc2b7943c97c4622040eb86882f514708c03b017808f03140c6000) else (if i < 462 then 0x2c42fe52b8946898e46b20a0ef86aa2f814d08e83c6189097831c0c400002c42a082c3146c97a4591f88e6c68c2df14188a03aa18109202f80b800002c424242c494c09984672040ecc6ac2e813d087037a16908e82f40ba00002c41ea0296938c9224301ea8de464e2d013b888c38616908682d00a000002c418d92ba146098645c1fa8e606702d713d085837c16a08902cc0a200002c413202b194589764531f48e206682d713d887038616f08582f00c000002c40d632b314249544501f48e446702de14288a439416e08f82d40ac00002c407792c594b099446e2008eac6ba30715289043bc18c09182f80b000002c4018e2c1149498e46b2088ec06a830115689303e218b096831c0b600002c3fbbf2b5942897a4562020e886782e114788d03b017d08d03200ce00002c3f5f72b2942096844d1fe0e7068e2e0142889c3a817408c83000bc00002c3f0572a493a090a4201e30d906282bc134882c36c15c07e828409e00002c3ea942b0141094443e1f58e106702e013e886838615b08082b00b600002c3e4b82bd14a499846b2070e8c69a2f314808b03a817c08b02d40b200002c3deca2c794b49944642068e9c6942e014188a83aa18509583180c600002c3d8fa2b414689924602028e7467a2d513a088839616f08c82f00ba00002c3d3392b2141c95a4511fc8e3c6622d413a087838c16f08702c80b200002c3cd6c2bb143894a4471f30e446682df14088bc3b017108702ac09e00002c3c7902c5948499246c2068ef06bc2ed14c88d83aa17308602c00a200002c3c1e22a713e093c4411f50e3466c2d913f889039416a08a82e40ae00002c3bbf72c894b899a46e2038ed46b42f214808bc3a817b09183100cc00002c3b60d2c1946495c4561fd0e8c69a2f6145889037e16708b02e40a600002c3b0132c914b89ae4702078ea869e2ee14a08e03be17808d02e80c400002c3aa3d2b994749704682058e7c69a2f614708bc3b417a08a02ec0ae00002c3a4892b093f49404441f88e4066a2ce134887838217008b02c00b200002c39e9d2c2949c9764592000e9c69a2e814708c43a417808902d00b000002c398c72bf94949ae4772088eb46a82f714b88d83a817708f02e80b800002c392db2c594989a046f2038e9c6982ee14a88e839817108c82e40a600002c38d012c014b899c4732118ef06c02f914b88cc3c4186098832c0c800002c387542a993cc9264331e60de463e2c613b087038e16c08602c80be00002c381852b513e89404491f90e6867e2db13f88c839e16c08f02f40ce00002c37bc02b0940094044f1fc8e7c6842ec14808d83b818008f02e00bc00002c375c42d014fc9d04922180f406dc30a15508f03c4189090830c0b400002c36ffe2b714349684531fe0e746802e814a08dc3a617208c02e00be00002c36a6129e137090a42c1ec8e146582d013b087c39816b08782e40c400002c364652c994c89b247f20d8efc6c22fa14a08d439c16e08803040c800002c35eac2b093fc9524461fe8e5867a2e614708cc3aa18509083100b000002c358ec2b1940c94e44a1ee0e0c64a2ca134082434014c07b829409e00002c352ed2cd94e099a47520a0eb86a82ff14e89103b618008e82e00b400002c34d142ba946497c4652090edc6a42f414b88ac39417408702c00b200002c347492b1940c94444c1fc0e646902e3141888438c16308982d80b200002c341512ce95209d248d2110f106d430515609183be18809082fc0c400002c33b9a2b2142c96844b1fa8e6c6902f714e08dc3a617009302fc0ca00002c335c12bd946c96e4521fd0e506662d313f887437415607c826809c00002c32ff02bf94689744611ff8e806742dd14008a83a216f08c82dc0ba00002c329dc2d995509dc48d2120f0c6cc2ff14d88d43c818d09683200c400002c323fd2c394ac9984632030ea469c2e314088c03aa17e090830c0ca00002c31e472ac141094844b1f68e6466a2d713c885836c15f08402cc0a600002c318692bf14b899e4732070ee46c42f614b88f43c6181092033c0d000002c312802c7149097445b1fe8e886a42fb14c88c03aa17a09403080c000002c30cb12b7143095e4531ff0e7068a2e514a88f03c818108d02d00b000002c306da2c294a499246a2038ea06942e214288a438816508903000ba00002c301082bb945c9724662078ee06aa2ee14b88c43b217a08a82ec0ac00002c2fb3e2ba14749784682010e7068e2ea14b08e43c217b08e82fc0c600002c2f5722b214589664501fa0e806902e9145889c3a617308e031c0ca00002c2efa62b8144096e4551f70e546822df144887c39416c08882c80ba00002c2e9af2c714d09c04802110f0c6ba30415188f03c818a08f02f80c200002c2e3cf2c2944c9564511f88e5c6782d6142089038e16808802bc09a00002c2de032b6146898045f2040e8c6942e514888d03b217308c83140c600002c2d80d2c694c09a647820b0efc6bc2f914c08e03b0181097034c0d000002c2d2382b5143c9784621fb0e9067c2e513c887039817609102f00c800002c2cc5a2c714a899e4702060e8c6a42fb14f88fc3c818609002f80b600002c2c6612cb14e09a247220b0f086aa2f214608a038216508002a80a000002c2c0a82ae141c95844f1ff8e946982f214b88f03b617709003000b6000 else 0x2c5a5622b5942895e4531fb0e786782e414608cc39c16f08582b00b200002c59fb22a813d893e4411fa0e5068c2df13b888839016808302d40ba00002c599c72c514d09a24682058eb46b82ef14688c839017208882c80aa00002c594142b314309604571fc8e906902f414888a038816c08682e40b400002c58e222ce951c9da4892170f446c830014b89083d018a097030c0be00002c5883d2c614bc99c47b20d8efc6b630915109143d018b09303040be00002c582852b0944096a4571ff0eb46a62ee14d08e43ac17108a82f40ce00002c57cbd2b2141895244c1f60e046562d413f88a03a018009003140d000002c576e32c1948c98a4772088ecc6c42f414f88d83b617408b02d80c400002c570ff2bc145c9724541fb8e446822ed14a08cc3ba17608e83040ca00002c56b072cf14cc99c4692090ed86c030515109183d4190098031c0c000002c565062cb94dc9a246c2070ea06b22f914e88f03b417308a82e00a800002c55f342b7943496a45a2000e806962e014308a03a417908e82d40b600002c559582b914609724692050ea46882e314608a439015b08382bc0c400002c553872b794549624612048ea86922e013f088c39017108b82d40c400002c54dca2b0140893a4421f10de46362ce138885038215e08082b00cc00002c548142ab94009324391f80e546762df14508bc3a417808f82e00aa00002c542362b894a099a4732070eb069a2f514e88f03b818008f83040d400002c53c782b3944496445c1fe8e9067e2e214608bc39616b08902b40aa00002c536bb2b0140495244c1fc8e8c6942e813e88b43a817908d82ec0be00002c530c32cd14d899446b2040ec06be30815288ec3d018109483100c200002c52af62b3942494e4511fb0e986922fa15289243de18309403180b400002c524fe2ce14f09ac46e2088eb469a2f014e89043cc18409283100be00002c51f292ba144896c4652080ecc6962f114c08d03b017208a02ec0c800002c519642b413fc94844e1f80e4c65c2dd13f888c38816f08c02e00ac00002c513a92ae940894a44c1f50e586682d113e888c3ac17808e02e40ae00002c50dd52c0148898e46b2020e706682d113e889039816f08a82ec0c200002c507f52be946097a45b1fd8eac68c2e514508a83b617708882d40a200002c5021d2b7946898a4552010e9c6882f314b08c83aa17908282d80ba00002c4fc312cc14b89a247e2098edc6aa2f914b08e83b418208e83140c200002c4f6562c814a09a846e2068eb469c2f414b88fc3c817409083200c800002c4f08f2b3142495e4542010e9c6a62fd14809083b417408a02cc0bc00002c4ead32b3140c9424511f78e386842d1139888c38416908982d00ba00002c4e4df2c994ac99045b1fb8e746a02f414a08cc39e17108c02dc0c200002c4ded52d014fc9aa4732070ed86ae2ef14f092c3c419509483080d200002c4d8fc2b8140c95844b1fd0e546802e014508cc3a217e08e02e00bc00002c4d3272bd147098a45c1fd0e8c6742ef14588f83c017c08f02ec0a600002c4cd452bf147097c45b2018ea468e2ed14b88d439416d08c82f00be00002c4c7522c914dc9b84822138f1c6da31615309183ba18309283180ce00002c4c15e2c494ac98a4642050e7867c2d413f088038416b08302cc0b200002c4bb802bf148497e4571fd8e8866c2d2145889039a16d08602f80b400002c4b5b72b013f09624561fa8e6467e2df14508a83a016d08b82e40be00002c4afb32cd94d89aa46c2020eb46a02ef14708a039e16e08882a00ac00002c4a9ea2b394489824602000e6465e2e113e08a43ae17908a02d80b800002c4a40b2bd94649664511f48e3c65c2db14408bc39817809183000c000002c49e3d2b1941494644a1f40e4466e2d813b088c38416d08e02fc0c400002c498992a3138c8ec41b1e30db86142af12e07d034814807a02800a200002c492e62b1940894c44e1fb0e746862e814808dc3ae17b08602e00b600002c48d0d2bb944c96a4592028ea468c2eb14608b439a17208f03040c400002c4872b2c294909a64732078edc6c22fd15408f03ba17808c83100c000002c4814d2bf94789784642078eb869c2f814a88f03b017a09383300cc00002c47b8c2b4943897446a20e0ec46922ea14688cc3b617608e02e00ae00002c475af2be94709764632030e706842ee14a08e03ce17d09103240c000002c46fda2bf14989a847f2160f1c6cc30b15889283ca18609102f00c200002c46a2f2a5939c91e4341e98ddc6422ce13b085837615907f82b00bc00002c464432c394989a04702080eb06a02f114a08e83b018009003000ca00002c45e7a2b9947c99047e2140f206ce30215509283ce18609103140cc00002c458ad2b9146497e4692048e9869a2f814c08f83bc18409383180d200002c452cb2c414bc9964642058eac69c2f214d08ec3a417408f02d80b400002c44d122ae143895644b1f40e106622d113e887438616d08b02e40bc00002c4473d2b594109504441f50e2c6522d1135085437816808202d40ac00002c441472ce14f49c24882128f186c8308153890c3c218008d02e00be00002c43b772b8145896e4552010e986982f114708e43b818609082e80c200002c435a92ba944c96e4611fd8e746622ca135885838816a08702cc0aa000))) else (if i < 467 then (if i < 465 then (if i < 464 then 0x2c71a812b094249744652078ec06b230214d89043bc18209382fc0be00002c714bf2b214389684581fc0e906842e813c88a43a818209103300d800002c70eda2c414ac99c4662088ecc6b02f614608c83a017208882d80ba00002c708fe2c194b09ac47b2128f106b62ec14a88d83b216a08b02cc0b200002c7034e2a793d493a43e1f50e446702e214708b43a417909183180b600002c6fd5a2cd14c89ae46e20a0ee46b02f214788d43a017408a02c40bc00002c6f7812b9948c97845d1fe8e6c67e2e2145089838616508682bc0ae00002c6f1922c414a499846c2058ecc6aa2fd14708d439617208d82f40ba00002c6ebca2b0941c9464491f70e646882e9141888c38c16708e03180be00002c6e5f02bb144496045a2040e8469a2ef14d08b839a17c090830c0c000002c6e0082bf147497845e1ff8e8868e2e3144087839a17008802e00ae00002c6da362c494d89a24672070e8c6862e5145089038c16708302ac0b400002c6d4432c8148899847c20f8f106c02f814b88f03cc18809603180c800002c6ce802b113d49424351ec8df46442c8137087838c16f08c02d40b600002c6c8902ca14e89b447c20d0edc69c2f214808a439216508982dc0ac00002c6c2cd2ab13d492443a1ed8dd06382c5133887039016b08502cc0c800002c6bcfa2b7942c9504551f98e846a82ef14888ec3bc17e08c82d80b600002c6b7122cc14dc9b647720c0ebc6942e413f086c39016b08382cc0aa00002c6b1382c314a49a447720c0eec6b830214e88d43b018309503340ca00002c6ab442d114dc9a647520d0f006e631b15d89483e019109683280c600002c6a5a02a313c493c4441f80e2865a2ce13c089438015a08502c40b800002c69faf2cb94f49a84802178f146d030b15609183c017308b82dc0b400002c699fb2a793e494c4501f90e346502c7138883837215908202b80b000002c694322af14049444431f38e606622db13d088439017908f02f00b200002c68e4f2bf14c099c47a2078ebc69c2f014488b439816e08e82fc0cc00002c688852b6941c95845b1fb8e9068c2e814408a039e17108b83080c400002c682ce2ae140c93043a1f50e286762ea14308b83ac17908a02cc0b000002c67cd42ce14e89c64862140f0c6c230b15388e83c418308e02fc0c200002c676f42c2949499446c2030e7865e2d2138886038c17208a82e40b800002c671042cc15089ac47520c0f0c6bc30614c08e43be17c09282dc0ba00002c66b5d2a513c492642e1e38da46342cd13a886038816508602d40c200002c665902bc944095444d1f50e446802e6143889c3a017308803180ca00002c65fb82bf148498c4692078eb46942e814308b83b017909002f80c400002c659e62b6944897046a2070e9c6882df14788a43a417c08902e80c200002c654052c394c09944772070e906842e314308a439016b08b02b00ac00002c64e612a813cc9324361eb8e1464a2d314308a038816108182d00b800002c6485c2ce14fc9ac47820f0f086bc30315088e43b818409002f80b600002c642a72ac93e89244361f30e386782e214288b439817108602e00be00002c63cde2b9945896e4632008e846a02f814608c039c17708c02c80b000002c637122b514449704602000e9c6942e714408b43a617208d02e80ac00002c6312e2c2149098246920a0ef46aa2fc15109143be17f08d030c0ba00002c62b532bd946498e46a2068ec06a82f314908d03b418209082ec0c200002c625572c914c49a84722098ef46c42f914c08f83ba18308c83100d600002c61f762bd14749504431fa0ea86922ef14188a43a017308502b40b200002c619be2ae13fc9604521fb0e7c6822e514888f03b218309002fc0cc00002c613e92bf946c9aa4722098eb469c2f514b88d83ba17008982e40c400002c60e252b294309664581f78e4c66c2d513e089439a16d08e02dc0b600002c608542b9146497445e1fe0e686702e114508a839016e08902d80be00002c602722bf946c9804641fc8e9066e2e414188b039e16e084029c0a400002c5fc992c1149499646a20c0ed86a02ea14c08ec3c018008902dc0aa00002c5f6b22c794a099246b2090e906802f314d88dc39a17808602c80aa00002c5f0bf2c614cc9c447320c0eec6b62fd14f08c43c018008d82d40ba00002c5eb0f2a9942c9744632040e9867e2e214288a83b017808782e40b400002c5e5352ba14649924622060ed06b62fb14c08f43c618109083080bc00002c5df7f2ae940c9284441f48e0c65c2d914708a439016e08a82d00be00002c5d9b02b9148099047620d0ef86b22fa14a08b439e17108a02dc0ce00002c5d3fd2a813d092a43f1f98e7467e2f514788b03a417508902e00b800002c5ce072c914d49c647c20d8ed86c02fe15089343d818d09703300d400002c5c8282c294689884652088ed86982ee14e88f83c018508b02e00ac00002c5c26c2b114109644451f50dfc6662dd142089039416c08a82f00cc00002c5bc6f2c894bc99247820b0edc6b42f414d08fc3c017d08c03040ca00002c5b69d2be14689724521fb0e306722e614408ac39616508483000c600002c5b0d22b6146897c45c1fd8e9c69e2fb15009343e018308f031c0d000002c5ab282a813c09304301e98dd865c2d514388943a418008f03100c0000 else 0x2c88e822c694bc9a447c20c0f086dc306156092c3d618508f83040cc00002c888ac2be14a89b847c20c8ed86a82e7144086c39c17c08c82dc0a800002c882c12c214a89aa47420e8f046c630114f89143d418e097031c0b600002c87cf42b5946495c4541f78e346762e314908e43b217d08a82d80d600002c877202c114809a847620a0f086c430a15609243c617808c03080be00002c871372c0147c97244a1f50e506822de14408b43a817808f83140bc00002c86b662be146496445b1f80e306662d6139087838e16b08a82e00c600002c865942b9946898445c1f98e706742d713c884038617708902c40aa00002c85fb52bd94789684541fc0e8068e2e113e084437416307c82800b400002c859e42b5943495c44a1fa8e6c6662d814008dc3aa17b08a82c809c00002c854032ba146c9764612020e8c6a02f915109243dc18909283180ce00002c84e182c314a49964682068eac6922ea14c08e83aa17a09303280c200002c848562b314109564511fc0e5c6862f214288c03b017109283440d600002c842bb2a093909244371ed8e0c6562cc139887036a15407c829c0a800002c83d0e2a693e093e44e1ff0ea068a2eb14508d43a016a08802fc0b400002c8376b2a513bc9224311e90e1864a2cd13d085837215507e02940b600002c8317d2c714fc9ba47820c0ee86b62f814f88e439e16e08b03100be00002c82bba2b6147097245c1fd0e806882ed14a88e03b817d08e82e40b400002c825da2c494949864591fd8e8468a2df14688a83a017408682dc0ae00002c820172b4143098246420b8f006ac2f414a88f43b817308282d40b800002c81a302c294a49724551fd0e746782d9137085c37415407f82cc0bc00002c814692b5943c9644511fb8e6868a2ea144089c3ae17a08982dc0ca00002c80e872c714c09aa46f2078e946982fa14b88f83c218608f83100b200002c808712d815149ba47120c8efc6b82fe14e88ec3c418c09703240ba00002c802b72ac94009504531fa8e3c66a2d513e886438616808482d80c000002c7fd032b014349584451f98e6c67a2ea14708c03a816e08702d40a600002c7f7372b694609724612000e9c6962ee13f88b03a417708b82ec0c000002c7f1672b4942c96845f2018e5c6762dc14588ac3aa17108902ec0d400002c7eba92b294289584531fb8e7869c2f514888bc3b217708982dc0b000002c7e5ec2a893e095044d1f88e6c68a2eb14608a839817c08c02d80be00002c7e01d2b714649824692000ea06ac2f314c89243c818e09903340d600002c7da472c194c89a247920c0f006c82f915289203d018f09202fc0c400002c7d4a52a513bc92a43c1f50e3c66e2db14108a039a17308983000ac00002c7cf0629e13b49224371f38e406742e6140889c38c16e08f02d00ae00002c7c9432af93f095844c1f98e4c6702e0141084035215a08682c80aa00002c7c3682be94989924692030eb869e2e614908f83b017e091031c0d400002c7bdd529f137090e4301e98e046482d413d088c39e17708b82d40a200002c7b8142b2140c9504471ec0e386562d413e88a838c16a08682c40b200002c7b2432b9143495844a1f80e406682da13d08983a017008582a40a600002c7ac7c2b294309684571ff8e906962f514608b43a017808c02d80b800002c7a6822c614d09a447320c0eac6ac2f314788d83ac17d08c83080cc00002c7a0c22b3142896244f1fd8e5467a2e714988c039a17108782ec0a000002c79ae02bf947898845d2030e8468e2eb140886837216a08882f40c400002c794f62bf946c97a4642070ea867e2e3141889c3a817608e02f40aa00002c78f1a2c1148099246f20b8ef06b62f614608e43b4184095030c0be00002c789442b214489684561fc8e786782d914388a839216d08b82f80bc00002c783612c714d89be47b20b8ef86b02f714b89103c418c095030c0c600002c77d942ba147899646b2050ed86962f214c08cc3c017c08b02d40bc00002c777c92ba944c9624501fd0e2c66a2de14888dc3b217d09283200c600002c771fa2b4142894e44b1f78e4c65c2d0138086c37e16508602c00b200002c76c1f2c2949897645f2080eb869e2e514308c83b017b09303000be00002c766452c2949898a46e20d8ed86b22f814988e03be17d092030c0c000002c760442d915149e448d2138f186d030115809103c818409683180c800002c75a682bd946496c4571fd8e7c6982e814808ac39c17408b82e40bc00002c754792c794cc99846d2058e946962e714388ac39216e08a03040c600002c74e9b2bc947c98a45f2058eb46a02ed14988dc3b217c08e83040c400002c748cb2bb147099847620d0ed86ba302153892c3d418109282f40bc00002c742f02c0949499c46e2090eb469c2ed14888ac39616b084029409800002c73d3b2ae13f895444c1f98e3865a2d613f888037c17208d82fc0ae00002c737812b093f093c44b1f80e5867c2e213c883836e16108382ac0aa00002c731b62b6145096045d2000e8468a2df145088439617d08c83080b000002c72bfd2b0943c96645f2020e9067c2eb14a08d83aa17d08d02c40be00002c726152c294a899e4692088eb06982f814a88a839c17a08903040c400002c720322be146896044c1f78e606662db140888038c16a08b02f80c2000) else (if i < 466 then 0x2ca03922c894d89984612060e9c68a2e214608a039816f08802d00be00002c9fdc72af940494243e1f20e306522d8140088438016708082c00a400002c9f7c52d3151c9e649721d8f7c6e630e15208ec3ba17e08d02e40ce00002c9f1b82d615209be48b2180f146ce30115609483fc19809a03100de00002c9ebd62c314b49a847f21a8f8070031615689403de19009a03640da00002c9e6122b8944498445f2000e8068c2e914108b039a17508a82d40b600002c9e0612af13cc93e4411f48e346542cc136085037215f07c02c80a200002c9da7a2c714b89a047220f8ef46b430114b08d83b017a08a82f80b600002c9d4a72b594649764642058ed06962e514708dc3c818f09803380e200002c9cee62b6944c9724581fc8e8868a2df14588c43a816d08b02f80b200002c9c9132c0149c9b04732088ef06b42fd15189083a216f08982d80b000002c9c33b2b8146c99046e2030eac68c2e114588a039816e08c83040cc00002c9bd582c614b89a447420a0ed06b030215308f83c418209203040b400002c9b78a2b714489664541f80e586802e2141089c39817f09383400da00002c9b1ba2bf94389724612060eb06a62f914f08f03aa17008782d40b400002c9abe92c1147c9804712038e946922e914688c83ae18009082f40c600002c9a62a2b1941895e4541fc0e8068a2e614288cc3b418708e83140c800002c9a0552bb94a499445e2038e846942ef14808a03b017c08f82fc0ca00002c99a7c2bd147c99a47220c8ee46b02fd14c08e43a417708f02e40b000002c994a02c214c09b447320e8edc6a82f714c88ec3c417f08a02bc0b400002c98ebe2be94609764531f98e6865c2d213a886c38015c08402b809800002c988e72b8145097245f2030e8c6782df13e086c37e16f08882b40a400002c9832e2af140c9464471fa0e606862dd14588ac3a417908d82cc0b000002c97d5f2b4943895e44b1f90e6069a2f014d89003b418208e03100c400002c9778a2be14589804682028eb06922e914988d439416b08903140c400002c971982cf94fc9b647520c0ef46bc2f9147089c3a617809182f00c600002c96be42a593d49404361f60e506822e714988e83a617708e03080ba00002c9660f2b9946098e4632050eb06a22f814588b43a217809382fc0a800002c9604b2b393f89544491f58e286622dc14108c039817208702dc0bc00002c95a822b114049524491f58e446642ca137885437815908382a40a200002c9547b2d214f89c647d20d0ed06b42f914a08b839216808602e40b400002c94ed52a4138890e4381ef0e246622d3138088c39e17508e02f00ac00002c9490f2b394209584501f98e606662d613e08a438a16508582dc0a200002c9435d2b394149544521fa8e486602d713d087c39616908302c40b200002c93d6e2cb14e49a64702088edc6b22fe15189083c017a08d83080c400002c937892c514c49a446c20c0edc69c2f414c88d03bc18408a02dc0b200002c931a72c394ac99e47720e8efc6ac2f214d08b439216c08b02e00c600002c92bf42ae94109564481f10e4065a2ce13c085837416a08902f40be00002c926212bf14649784592018ebc68c2ea14488b43ae18209002d80c400002c9203e2c3949898e4692010eac69e2f214808b83a217c09002e40a600002c91a5a2be946c9944651fe8e9c6a82ea14008a439216908982e00b800002c9149a2af944095c4561fa0e606722d313a086838416608082ac0aa00002c90eea2a713c891e42f1ee0e1c63c2bc134084036015608102b409c00002c908d62da15489d44882138f1c6d230415209243bc18209403000c000002c9031f2b3943496245d2048ea468a2f414788b83a216808a02d00b200002c8fd4a2c0946896a4501f58e3866c2d913e087c39416608702e40b600002c8f7602c514bc9a647c2120f046b42fd15589103d018508982cc0b200002c8f1952b6141095a4511fc0e886962e3141089439e16808582b80a200002c8ebd62aa940094e4501f70e346882e714688b839816708682c00ac00002c8e6172b214349544451f80e686722e413f889c39216908a02d00b600002c8e0392c1949c97a4652070f146c230614f08e83c018b093030c0c000002c8da772ac13f89464491f38e346542d713c089c3a617e08682b80a200002c8d4782c894b09b247820f0ef46ae30114c08f83b418509303000b600002c8ce932ce94f89b24772050ee46b630c15989583e018e09503140d400002c8c8bf2bc946497c4652020e946742da14008bc3a017608e03180c800002c8c3082b194209404491f80e746782e214288a439216908902dc0c200002c8bd022ce95009c247a20c8ee46d431415408f83c618c09583140c200002c8b7342b2140c96c4511fa8e586702db13e88a838216a08982c40c200002c8b1532bf14849784632090ec069c2f114b08e03a017408c02d80b800002c8ab872b6946499246820a0ed46bc30514e08dc3ae17a09003100ca00002c8a5b52ba942896c4562008e8c6802e314508c03b417b08d82d40a200002c8a00f2a593e093a4411f38e2c64a2cd139085c37216108582ac0b600002c89a592ab13e89424511f48e2065e2d413b888837816c08402f80bc00002c8947f2bf149c99c47820b8efc6a82fd14a889c39216407d829c0ba000 else 0x2cb76cb2af94509804582018e846882e414888a039216a08882f00c000002cb70e72c014bc99a46e2090ec46922e614408cc39c16b08582a009a00002cb6b1d2b214109704622020e846762dc13e089039e17508882e80b200002cb65572bb943895e4491fb8e506662d513e88a039617008182ac0ae00002cb5f7b2c2949c98645e2030e8c68c2ea14408cc39617208a83080c400002cb59c82af14189544461f60df864a2cd13a087038c16808202e00b200002cb53fb2b3143095e4571fe0e786862ed14e88f03ba18308c02e80ae00002cb4e422b394289404531fa8e706962ea13e086c37a16b08682c40b400002cb48832ad140494a4401ed8e246402c0136884836816a08882c80bc00002cb42bb2b1140093c4471f80e5866e2df14188bc3a617708c82cc0ac00002cb3cf82af943095c4581f88e4c64c2cf138087038017808a82dc0c000002cb370c2c8149097845f2038eac6a22ff14b88e03d219309002d80a600002cb31792a093c492e43f1ef0de463c2cb138084437215907f02940a400002cb2bc62a893c492a4361eb8de06422c5139885038016908902c00be00002cb25f72bf94c899e46d2090eb868c2f614c08d838c17208c02ec0c200002cb203c2b013d092c4421f28df464c2d2138885838216c08983100c400002cb1a632b9949098246e2000eb469e2ef14988e83b217e09683200d400002cb14922c294b899446d2098ec86ac2f214808e03b218409403080c800002cb0eab2c794e89a047820e8ef46c62fd14a08c03a217608a02f40ba00002cb08bb2c494ac99a46d2010e986922ec14588a83a617708d02f40cc00002cb031a29f937090e42b1e58da861a2bf132884036e16108402e80ba00002cafd502b1144c96a4511f98e5066c2e714508fc3c0182093832c0d200002caf7a42a4139890c4331ef0e106522d7138086c37415f08082ac0a600002caf1b82c714c49a24732120f1c6d230415309243d018208d02e80b200002caebde2bf14889924632048ee46c030414f09103b018308c83140c400002cae61e2af942494e4491fc0e706842ec14a88d039417108b82f40ae00002cae07b2a093bc9284391f60e4c66a2de13f087839416508502dc0c200002cadaa52bc14689724652038ec46922df14208ac39216908c82d40c200002cad4d92b5143496644c1fd8eac6a82f814a08d03a217508802d00b600002cacf0a2b6145496044c1f40e286442c3135885437615d07f829c0b400002cac91c2c694d49ba47c20f0ef06b430515309083cc18809283040b800002cac36d2ae13f094844d1f98e706882e614688b839816708402bc0a200002cabd802c794a89764621fe8e606762d813e889437c16508582d40c600002cab7982c3948c9824602000ea06a22ef14508a838e161082026c0a400002cab1ed2a913d49344351ed8de864e2d413d88a03a416a08782c80b600002caac252b7142c95e44c1f30e1863e2cb138083837016108782cc0b400002caa6562bf947496c4672070efc6c02f814908e83b217c08f831c0c400002caa0662cf14f09c647f2130f286d230314e88b83a817908c82f00be00002ca9abb2a693d094243f1f28df863e2d013f088c38816207c828c0a400002ca94e92b7945497e4662028eb86be30c15589403d418509383080ce00002ca8ef72c614ac9a646d20c8ef46c82fe15209043b617c09003000b800002ca89322b4145097845f2008e7c67e2e314888d03a616e08c82f80c200002ca836c2b6942095244e1fb8e906842f214688bc39c17108602e00b200002ca7dd329d939c90a4251e18db062c2be133085437215408282ac0ae00002ca77ff2c094689804622018eb86902d413b086037617208582a00a800002ca720d2c414c899c4612098ef06ac2f214888d038c16808382c00b400002ca6c282c614a49a647220a8edc6b22f714a090c3de18609503300c800002ca663f2c414c499e46c2038e7c68c2e114388d43a617008782bc0be00002ca60602bf149c9a64732048e9869e2f514d89083b818408b82d40a600002ca5ab22aa14009364481fc0e746882df14708bc3b017408c03140ce00002ca54ea2b614289544551ff8e806822dd143887c39017408c02d00ba00002ca4f3a2a813cc9324411f38e3c6642d614088b439617508c02d40c000002ca496f2b7945495a45d1fe8ea06ac2f714f89143b417808a02d40be00002ca43962c514649744521fd0e6c6782df140889839417408f02dc0b000002ca3dc02bf14609604481f78e5065e2cc137082436c16008482b00ba00002ca37e32c2149c9a046f2078ec86b230115108c03b617208802ac0ae00002ca32422a213b49184311f48e2065a2cf13c08803a017808b83040ce00002ca2c752b414389744541fc0e7c6982ed14788b439a16f08802c40ac00002ca269d2b4142c95c4541ff0e886a02eb14488b038c16208802e80c200002ca20cd2bc948c9824682080eb86922f614d88fc3c617a090832c0da00002ca1b002b8949899246a2048eec6ba2fc14e88f83cc18609403340d000002ca151a2c0949898245b2008e9c6882f1144888839216b08602b80b200002ca0f452bd148498a46b20e8f086ce30c15889603ce18709283280c000002ca09822b414209604531fa8e886822dc14188ac3a817608f03180bc000)) else (if i < 469 then (if i < 468 then 0x2ccebe52b8946897846d20a8eac6b02f214b08e43ac17908e03180b200002cce61c2b2144c97245a2028e886922e214888bc3a617009203180d400002cce0532b3144c96845c2040eb86a62f114b08e439c17008c82f40b600002ccda7a2c214a499845e1ff0e7868a2ee14688d83b818409203040bc00002ccd4a72ba146c98245c2010ec069a2ea14888b03a618609203100b800002ccceeb2b4146896245e2008e8868a2eb14608f43ca18909783380cc00002ccc8f42cb94d89be48020c0f1c6d42fb14c08cc39816a08602bc0bc00002ccc3092c5148c98c4662088eac6a02e714888e03a817108b82fc0cc00002ccbd3d2ba144497845d1fd8ea069c2f114d08f43c017408f02f80ba00002ccb75f2bc947498e4722058eb069e2f114808cc39216e08882e80ae00002ccb18f2bc94749744571fd0e586722e7140088038016508782c80cc00002ccaba12c914c49b847c20a8ef46ca2f914c88f83ac17c09283140ca00002cca5cc2b8944c9764642028ea06922e314888b839217408d031c0d800002cca0152ad94109464481f40e0c6422d013e088c38c16008782d40ac00002cc9a372ba947c98445f1fc8e8c68c2eb15089103ca18909383240ba00002cc944d2cb94e49c447c20f0ef86c030515789183ae17b09102d80cc00002cc8e952b0941892e4491f40e4c67c2e014688e039817808d83180d200002cc88942d595049a647b20f8f086ba2f614e88f03ca17e09502f00c600002cc82962cf14dc9b447b2060e9c69e2f614988c03b817c08e030c0c000002cc7cd72b6140c95044d1fa0e5c6722e5146089038e16c08b82f00b200002cc77172b914449784571fa8e7c6882e914988c839a16c08a02e80b800002cc711c2c714ec9b247d2100f046d230a15989203cc18508c02d80b400002cc6b6c2ab13fc94a44e1fb8e4066a2db13e885839216708a02d80c400002cc659c2bb947c99246b2060ed86c02fe14c08c439c17108903100d800002cc5fd52b7947c98e4672070ebc6b82fc14788e43b618408c02fc0ca00002cc5a0d2b0943c9544511fe8e8468c2f414c08e03bc18a09203040bc00002cc543b2c1149098e46b20a0ee06b22f314308a43a817708882f80b000002cc4e902a393a492e43b1f48e0064e2ce13c884037c15d07d82d00b000002cc48b02bf949899247120b0ed46b22ff14e09183be18509082f80c200002cc42ec2b4943897045a2028e946962e414808bc39816b08682b40a800002cc3ce02de9564a0a4a72250f5c6f431d16289603f019a09282e40c000002cc37112ba949099a46a2008e706862e414508cc39617b08e03180d800002cc31522b3143096645c2010ea06882e2140087438816908182c00b000002cc2b9e2ab940c9524501fa8e746602d313b886039216508602e40b800002cc25ca2bf94ac9904692090ea067e2e314408bc38c16b08e02e00c000002cc1ff32bb145496e4591fb8e5c66c2d513e08a038e17108902c80b400002cc1a2c2b6947c97245f2000e7c66e2d3137881434a15a08102bc0ae00002cc14542b414409624632020ec06a82fc14e09043c018008f83240be00002cc0e822c0949898a45c1fc8e646762e914308d83a017a093830c0b600002cc08642db15749ec4922148f206e230e158892c3de18309203400de00002cc02932b8145c96645c2028e806882ee14688ac39416608382cc0b800002cbfcb22bf947c99c46e2080ec469e2eb14388b039817508f02ec0b600002cbf6ee2b213e89304341ed0df86642d813e8874390166080029c0a400002cbf10f2bf946497a4612018e746522d413e088037a16108602d40b600002cbeb3f2b894689724631fd0e8c6902ef14888d03a417a08a02ac0b600002cbe5642bc949499446a20a8ef86ae2f914b88fc3ba18109003100c400002cbdf732cd14f49b84862118f3c6e231115709403d218c09483140ce00002cbd9dc2a213b892e4391f08e2466c2dd140088838016108802d80ba00002cbd40d2b3942093e4431f78e5066a2da13a087037e16c08102e00ba00002cbce4d2b4144c96045a2008e946962ec140889c3b617909082f00ae00002cbc8742be144c94a4491f78e6467e2e5146887838c16608602e80ba00002cbc2a02bb947c96645b1fb8e6868e2ec14388c439617008682b40a800002cbbcc92be94c499c4662080ec068c2e414588bc3a217808d02dc0ba00002cbb6e92bf149498e4662010e7c6822e9143089c39217309003040c000002cbb0f62d094f89c04832100eec6ca30e15789343de18c09483200c800002cbab112c714b499c46a2040ea86962ee14a88d43c017508802cc09a00002cba5282bf94a49aa47420e8ee06b830a14e89003c2181094030c0c800002cb9f6a2b3941494c44d1fd8e686822e614688a838816e08902c00b600002cb99902be94489684581f78e406682d3140086c39016508c831c0d600002cb93d12af13f09424471f48e2c64a2d013a086838a15b08402bc09a00002cb8e022b9942c95845a2008ea06802e614888c83b617f09403140ca00002cb881f2c2148c9804591fd0e5065c2d0138888838816908382b40a600002cb822d2d115189d047620d8f206b2301153093c3e018a09403340d200002cb7c802ad14049524411ed8e0c6722dc13b886437e15d08402b80a4000 else 0x2ce60202b7942c9584581ff8e686762dd14288cc3b417609002e80b600002ce5a562b7142c9624621fe8e986a62f714b88f03be18109003040ba00002ce54812b7946c98e47620e0ef86be2fa14d08c83c0185090031c0b200002ce4eca2af14149664511f40e4c6542d613f087c3a016a08902d40ac00002ce48f72bb14689724662040e8869e2ea14388b439616e08782d00bc00002ce43362b7146897e4602058ebc6962f414b09003be17f08a02d00ca00002ce3d6d2b1141094a44d1f30e546862d713c888439416408282c00ae00002ce37782cd94fc9c64782118f086a62f914708b83b817608a83100c400002ce31d62a713ac9344441f58e6468e2e614689283c818809882fc0d200002ce2c072b794349604531f98e5c6742d9144889038416b08482b00ac00002ce26092d115109d64832108f1c6ca2fd15088e83d418708f02ec0a800002ce20632a493709004211e50e046342c1135886837a15c08102b40ae00002ce1a622d514fc9c44852158f106be30015589203ca17908e03000b800002ce14902b8144495644c1f60e4866a2d913f087c39217308a02e40b800002ce0eb42bf94a49964742090ebc6ac2f314d88d83ba17c08d82d40b400002ce08d72c114dc9aa4732110ec86a62e314708e83b218709703140b800002ce030b2be148c98a46c20c8f106be30414f08f43bc18709082f40b400002cdfd432b1941096e4582018e946a02f2146889439e17508d82ec0be00002cdf76a2c1147898247420a8edc6a82f214c08ec3a817908b82e80b000002cdf19e2b914509724712088eec6ac2f514e88c83a417908f03200c800002cdebe42ac94109524461f58e5c6662e814388b839c17008d82ec0c400002cde6112b7144495c4541fb8e9469e30014d08e83b017b09183080b800002cde0342bd14789784612030eb46962f914f89043ac17008902f80b200002cdda592b9947497445e2030ea46ae2f914c08e03cc18409283140ce00002cdd4ae2a893f094044a1f88e5c6722e614a88cc3ca18f09783440d400002cdcedc2bf949c9904671ff0e786802e714608b43a417308a02c80ba00002cdc92f2a813b09164331f18df86362c7137086838817308d82d00be00002cdc3a2295134c8e041c1e00d8c6102ba12d082837015f08702a009c00002cdbdd22bd147897e45b1ff0e7c67e2e414088a43a217b08c82c80b200002cdb7fa2be94909a047220d8f006cc2fe14d88ec3b217a08f82d80b800002cdb2362b7145097445c1f98e6467a2dd13e887838416808782c80b400002cdac822ae94089404411f50e306642df140886837c16508082b80b400002cda6ae2be94949864611fd8e8467e2df14508a439016b08682c80b600002cda0c92bf94a89964692080eb86a62fc14e89403ea1a009983300d200002cd9ae32c7949499847120a0f006d630715309043a417f09482dc0b800002cd950f2bb94449624571ff8ea06aa2f714e88b83b418d09683200ca00002cd8f302bf149897e45a1ff0eb068c2e314808cc3b617408b82cc0c200002cd89612b6143c95445c2000e8468e2ed14908cc3ae17c08c82f80ba00002cd837c2c014809884611fe0e846862ef14808e03c617908c83140c800002cd7d9d2c514a89b647d2108efc6aa2fa14d090c3b618208f02f80c600002cd77b32c3148c98e4612090ea86a02fc15308e43bc17908802f80c200002cd71d52c1948096a4611fd8e5c6762e314608bc3a817d08f82d40c000002cd6bfa2c114b899646c20c0ee46c62fc15188f43c218d09583100d000002cd66242b8945497e4601fe0e5c6822de13f886838c16608602b00ac00002cd60322c514bc9aa47a2100f046c830b15709443ec18a094830c0d800002cd5a782aa13ec9384411f08dfc6502d213d888c39616908802e80b400002cd54b02b4144897e4631ff8e6c6822ec14708d03b818b09383000b400002cd4ecf2c1149498e4662018ea46942ee14a08d83a417c09002dc0ae00002cd48f02c294a89b04662088ef86bc30714f08f43b817c09002fc0aa00002cd43502a3939c91e43e1ef0e286602d513f887c39217308b02f40ca00002cd3d952b3943096a45a1ff8e986a62f514d88c03bc17908d03280c400002cd37b52c3949097c4652040eac67c2e314088a438e16908502cc0b800002cd31d32c0947898846b2038e6469a2f514e09043be17908d83000be00002cd2c1b2b0141c9424481f78e446742d914088b038216308702e00ae00002cd26582b7147098a45f1fe8e746942f314808b43a217909082dc0bc00002cd20602ce94f49be4832118f0c6c630814f88c03ae17408f03140c400002cd1a652cf151c9d648220c0eec6ac30115208f83d218b093831c0b800002cd148b2c1148c9704561fb8e486842e714588e03b418309403200c200002cd0eae2bc147097a4591fc0e886762e314108b038e16a08982b80b000002cd08f52ac93e892c4371f28e2c65a2d613d086038216508502b00aa00002cd03362a993ac90c42a1e38dc46282be132083836a16f08b02e40ca00002ccfd622bc947c98e4612010e946a02f114908d83a217609103140c000002ccf79d2bb944497846a1ff0e886882ed14688dc3a616d09183040b200002ccf1b72c294c49aa47c20a8f1c6e0316155893c3d219109383300c8000) else (if i < 470 then 0x2cfd37c2b4944495c44c1fb8e686782e1143889038816b08782bc0c000002cfcdae2b594489524481f98e6c67c2ec14588bc39817b08d83180b000002cfc7cb2c4149099446c20a8ec46aa2fe15008f43a417d08a82ec0c200002cfc1ef2bf94b899c46b2050e8467c2d713a088c37c16a08c83180cc00002cfbc3f2a693b091442c1f08e3c66a2e414408c03ae16c08b02ec0b600002cfb64e2c494d09b247220a8f206ce30b15809383ea18308f831c0c400002cfb0862b814349544501f80e3c6602d313e088039217208702940a600002cfaac52ac13c894444c1f48e1864e2cd135885838616408902d40aa00002cfa4fd2b3141895044a1fa8e706882d714288983a617908882a40a400002cf9f1f2bd949499246a2088ed46b430214f08e83b818e08e02d40b200002cf995f2ae93e494043c1f20e4c6602e314608b43a817a08e03080be00002cf93aa2ac140093a4461f38e506602e013f08a03aa17608d82e80b800002cf8dce2c214a89a246c2070ed06b82ee14988c43a016b08902cc0ae00002cf880e2b994509624551fc8e906882ee143089839216b08382c00ba00002cf821a2ce15009b047c2168f5c6f031915309303cc18d09303300d400002cf7c162d395389dc48d2138f206da30c14e09243da18409403200d000002cf765a2b194109524491f90e4c66e2db145089037c16308802ac0ac00002cf70f328512e08c64021d40d205f42a512287a432e14b07b826c09e00002cf6b1b2bf14589684541fc8e3c6722e8143887838216208782f00b200002cf653d2cb14d49ca4812110f286d830a15789243d618809403080c800002cf5f732b9145498045b1ff8e646682c913c08a838616a08202d80b600002cf59b62ae93fc93643c1f18e046662da13d888439c17708802d40bc00002cf53ed2b594489744541f88e686602d013f88c839217308b82e00b000002cf4e1f2c0148c9664561fa0e646742d8142089438016508702c00a600002cf484c2b2142c95a4521f90e5866c2cd13a088439617408c02ec0aa00002cf42772c1149899646c2030ea468a2ef14b88ac3a418109483240b600002cf3c762d3952c9d64852148f186de31415908f83be18609483200c800002cf36f0299938c9084221e70db46442c3135081c37c16207f82880a800002cf30f92d094d099e47420d0ee46c22f814e88f03be17d09183080c800002cf2b3d2b794889804682088e9468c2f314688b439817809082e00bc00002cf256d2bf94a499e4682058ec869c2ed14d88e43ac17908582d00ac00002cf1fc32a893fc9424441f18e5467a2e313b886437e16707f82940aa00002cf19e62c714f09c647b2090ec46a22ed14708b83aa17a08c82e40be00002cf13fe2c5149c9884602018e8c6942f514f88d83bc18009803180c000002cf0e152cc94d89a047220c0ee06b02fb14f090c3ca18a09203300d800002cf084b2af943496e45d1fc0e9068e2ec14b88fc3a217d09082f00ac00002cf02a22aa13c492e4411f00e0864a2c613d087c38a16e08e02d40b200002cefcc22c914c89a04632028ea06962f114308ac39c17208e82f40bc00002cef6e02c194ac98446a2050ea86a02e914388c83b017708a83140b200002cef1042bd94a899046a2038eac69a2ea141089c38616608482a40b000002ceeb3b2b8142493a4501fd0e7866c2da14709003dc18409203180c400002cee55a2c694d09b047a20f8f006be30715309183d618d09b83100ca00002cedf6b2cc94ec9a846d2110f146ca30115308d43a617408c02dc0c000002ced9c12a493d094444a1f80e406662d813e886c39415b08682b409800002ced3fe2b3942896e4551fc0ea869e2e614708d439617408d82f40b800002cece332b594309564521f78e4065c2d513c88803a417c08e83140cc00002cec8582c1148498a4672000e846782ea14708bc3ae17808b82f00c200002cec2bb2a593d893843d1f68e2467c2e014088ac39e16f08682f00c400002cebcfe2ab93c89284401ef0e0c6402c813c086838617708f82fc0b600002ceb71f2c114e89ae47a20c0eb86ae2f614b88b83b617e091030c0c600002ceb16e2ac13e093a4391f38e3466a2de141088c38216e08802bc0a800002ceab7f2ce95109d848220e8f1c6cc30514e08d83c017909102f40b800002cea5bd2b214349724642020e7c6902e3149891c3bc180091831c0c400002cea01d2a213548f84271e30db06202ab12a882035c15d08302c40b400002ce9a552b3143495c44e1f78e3c65e2ce136085836615f08482bc0a400002ce94802bb148898e4601fd8e9068a2f314a08c03a416608482f40aa00002ce8eb82ad142096a45d1fc8e786762e813f889438e16c08b82f40cc00002ce88df2c0149899046620c8ef46bc2f7153092c3ca17d09002ec0c200002ce82f52c4949899846d2088ec069a2ee14508b03a817208b82f80ba00002ce7d122c3949c9884671fb0e7c68e2e514508b03c418709202f80c400002ce774f2b2144096a4572020e8c6942ef14688a43ac17a08982d80c000002ce71a22ac13c891a4311f00e386842e414408c03bc18209183240c800002ce6bc32bf148498645b1ff8e946842e213f888039618309403100c800002ce65f02b6941895c4541fb0e5c6682de14208c83a817308c82dc0bc000 else 0x2d0878a00000000000002078eac69e2ef14e08f43ce18809683440d200002d0819e2ca14a499647220b0ec46b62f814f89003ca18209202fc0c200002d07bde2b3142c9624591fc8e646722e213f088437216108682c40b000002d0763a2a493bc91c4341eb8dc46262c3137887037c15b08382c40c600002d070822ad13e493243e1f18de06362bf134085c38616608702e80bc00002d06aa02c214689864692048ed46a02e914508b03a616c08b82f40b800002d064cd2be945498a4611ff0e886942e6146889c39416408902e00b200002d05f042b8141c95a4481f98e7068a2e8141889438a16908482d80b600002d059362bb94609904631ff8ea46882e414108a439016c08982ec0b400002d053762b714709804571fd8e9869e2fe14b08f43c217b08d82f80bc00002d04da82bb147097c4632050eb86962e8140887437c16208302a009600002d047d72b2143c96645c2000ec06b02f414388c43b418008c82c40a800002d042192ad14149604461f50e306522d313a085435815007e82a00b000002d03c432b6945c9644501f98e7c6742e314408e03a417108a82d80bc00002d036712b6943c96c44b1fa0e4467c2dc13e088437216508b82fc0b600002d030882c6149c99a4752068eb46902f214e88f03b218309282f80d000002d02ab02bc146c9844571fc8e546742cf135083037a15e08602c80be00002d024b12ce14f09b647f20b8f046ce30a15108d439817a08b82d40b000002d01ef52b5141894c4491fa0e6867a2e414088b439816e08902d809e00002d0192b2b2142896645d1fc0e7469a2f614b88d03b617d09403400c800002d013852ac13e892c4351f30e406662d2139085838216e08d02f00be00002d00dab2b8145897c4602018ea06a82fd14a88f03b218109103040c800002d007b52c915049b447420d8f006c42f314908c43b817a08e831c0c600002d002002af14149504471f58e4468e2ee14988cc3ac17008702e80ba00002cffc2c2bf948c96e4592018e9867a2d9139885837c16408a02f40ba00002cff66c2b214309584541f90e806822e714a08ac3a417308b82e40be00002cff0662d815249c847f20e0f106ba2f914d08d83ac17708c02e80ae00002cfeaa72b2941894a4451f58e686702d814688b039417808f83080c600002cfe4db2b5945496e45a1fc8e6065e2da141888839817508a03000cc00002cfdefd2c394949704571fc0e746802d113c886438c16b08502a80a000002cfd9432b1945496a45a2038eb86942e814308a439616b08902cc0b0000)))))))))

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



private theorem b468714 : covered 468714 468832 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b468832 : covered 468832 468949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b468949 : covered 468949 469067 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b469067 : covered 469067 469184 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b469184 : covered 469184 469302 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b469302 : covered 469302 469420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b469420 : covered 469420 469538 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b469538 : covered 469538 469655 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b469655 : covered 469655 469773 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b469773 : covered 469773 469890 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b469890 : covered 469890 470008 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470008 : covered 470008 470125 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470125 : covered 470125 470243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470243 : covered 470243 470361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470361 : covered 470361 470479 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470479 : covered 470479 470596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470596 : covered 470596 470714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470714 : covered 470714 470831 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470831 : covered 470831 470949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b470949 : covered 470949 471066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b471066 : covered 471066 471184 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b471184 : covered 471184 471302 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b471302 : covered 471302 471420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b471420 : covered 471420 471537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b471537 : covered 471537 471655 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b471655 : covered 471655 471772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b471772 : covered 471772 471890 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b471890 : covered 471890 472007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472007 : covered 472007 472125 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472125 : covered 472125 472243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472243 : covered 472243 472361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472361 : covered 472361 472478 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472478 : covered 472478 472596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472596 : covered 472596 472713 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472713 : covered 472713 472831 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472831 : covered 472831 472948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b472948 : covered 472948 473066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b473066 : covered 473066 473184 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b473184 : covered 473184 473302 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b473302 : covered 473302 473419 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b473419 : covered 473419 473537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b473537 : covered 473537 473654 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b473654 : covered 473654 473772 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b473772 : covered 473772 473889 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b473889 : covered 473889 474007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474007 : covered 474007 474125 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474125 : covered 474125 474243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474243 : covered 474243 474360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474360 : covered 474360 474478 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474478 : covered 474478 474595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474595 : covered 474595 474713 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474713 : covered 474713 474830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474830 : covered 474830 474948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b474948 : covered 474948 475066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b475066 : covered 475066 475184 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b475184 : covered 475184 475301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b475301 : covered 475301 475419 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b475419 : covered 475419 475536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b475536 : covered 475536 475654 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b475654 : covered 475654 475771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b475771 : covered 475771 475889 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b475889 : covered 475889 476007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476007 : covered 476007 476125 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476125 : covered 476125 476242 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476242 : covered 476242 476360 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476360 : covered 476360 476477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476477 : covered 476477 476595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476595 : covered 476595 476712 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476712 : covered 476712 476830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476830 : covered 476830 476948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b476948 : covered 476948 477066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b477066 : covered 477066 477183 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b477183 : covered 477183 477301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b477301 : covered 477301 477418 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b477418 : covered 477418 477536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b477536 : covered 477536 477653 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b477653 : covered 477653 477771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b477771 : covered 477771 477889 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b477889 : covered 477889 478007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478007 : covered 478007 478124 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478124 : covered 478124 478242 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478242 : covered 478242 478359 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478359 : covered 478359 478477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478477 : covered 478477 478594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478594 : covered 478594 478712 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478712 : covered 478712 478830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478830 : covered 478830 478948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b478948 : covered 478948 479065 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b479065 : covered 479065 479183 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b479183 : covered 479183 479300 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b479300 : covered 479300 479418 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b479418 : covered 479418 479535 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b479535 : covered 479535 479653 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b479653 : covered 479653 479771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b479771 : covered 479771 479889 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b479889 : covered 479889 480006 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480006 : covered 480006 480124 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480124 : covered 480124 480241 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480241 : covered 480241 480359 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480359 : covered 480359 480476 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480476 : covered 480476 480594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480594 : covered 480594 480712 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480712 : covered 480712 480830 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480830 : covered 480830 480947 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b480947 : covered 480947 481065 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b481065 : covered 481065 481182 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b481182 : covered 481182 481300 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b481300 : covered 481300 481417 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b481417 : covered 481417 481535 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b481535 : covered 481535 481653 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b481653 : covered 481653 481771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 468714 481771 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b468714 (joinCoverage b468832 b468949)) (joinCoverage b469067 (joinCoverage b469184 b469302))) (joinCoverage (joinCoverage b469420 (joinCoverage b469538 b469655)) (joinCoverage (joinCoverage b469773 b469890) (joinCoverage b470008 b470125)))) (joinCoverage (joinCoverage (joinCoverage b470243 (joinCoverage b470361 b470479)) (joinCoverage (joinCoverage b470596 b470714) (joinCoverage b470831 b470949))) (joinCoverage (joinCoverage b471066 (joinCoverage b471184 b471302)) (joinCoverage (joinCoverage b471420 b471537) (joinCoverage b471655 b471772))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b471890 (joinCoverage b472007 b472125)) (joinCoverage (joinCoverage b472243 b472361) (joinCoverage b472478 b472596))) (joinCoverage (joinCoverage b472713 (joinCoverage b472831 b472948)) (joinCoverage (joinCoverage b473066 b473184) (joinCoverage b473302 b473419)))) (joinCoverage (joinCoverage (joinCoverage b473537 (joinCoverage b473654 b473772)) (joinCoverage (joinCoverage b473889 b474007) (joinCoverage b474125 b474243))) (joinCoverage (joinCoverage b474360 (joinCoverage b474478 b474595)) (joinCoverage (joinCoverage b474713 b474830) (joinCoverage b474948 b475066)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b475184 (joinCoverage b475301 b475419)) (joinCoverage (joinCoverage b475536 b475654) (joinCoverage b475771 b475889))) (joinCoverage (joinCoverage b476007 (joinCoverage b476125 b476242)) (joinCoverage (joinCoverage b476360 b476477) (joinCoverage b476595 b476712)))) (joinCoverage (joinCoverage (joinCoverage b476830 (joinCoverage b476948 b477066)) (joinCoverage (joinCoverage b477183 b477301) (joinCoverage b477418 b477536))) (joinCoverage (joinCoverage b477653 (joinCoverage b477771 b477889)) (joinCoverage (joinCoverage b478007 b478124) (joinCoverage b478242 b478359))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b478477 (joinCoverage b478594 b478712)) (joinCoverage (joinCoverage b478830 b478948) (joinCoverage b479065 b479183))) (joinCoverage (joinCoverage b479300 (joinCoverage b479418 b479535)) (joinCoverage (joinCoverage b479653 b479771) (joinCoverage b479889 b480006)))) (joinCoverage (joinCoverage (joinCoverage b480124 (joinCoverage b480241 b480359)) (joinCoverage (joinCoverage b480476 b480594) (joinCoverage b480712 b480830))) (joinCoverage (joinCoverage b480947 (joinCoverage b481065 b481182)) (joinCoverage (joinCoverage b481300 b481417) (joinCoverage b481535 b481653)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 468714 ≤ index 900000000/512 := by decide +kernel
private theorem starting_value : fast 900000000=46009215 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 900000000=46009215) (n : ℕ) (low : 900000000≤n) (bound : n≤925000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=900000000
    · rw [first,anchor]
      exact starting_value
    · have past : 900000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤925000000 by omega)
        have within : index n / 512 < 481771 := by omega
        have lower : index 900000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤925000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ900000000To925000000
