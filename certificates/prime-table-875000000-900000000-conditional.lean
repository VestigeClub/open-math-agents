import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ875000000To900000000

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




private def radical : ℕ := 0x197749c2c86bbd71b490f57ddc5d88feb9e792b1f30781e95ab4ff4ffd6777feb3120f1269b0d69f88eaa09fc6e96045564b12b30429a4954446b68fc3e75233e2b0aaf5f4a9a090f8aa06abb2a4b06d86b7bcfc1b30643ec46fd4b9a4604c4f87826f18d28b8118d4840f1bb5be99f46f6e26071c14582e1f952bdf09b04d92a6bb009f27e233a7c1ea4745cf6b3e5a755ba54ce96a35e87ee535d21f2deb36c66e5db456eba25558df91a10f90c6395e49071fedd059051218ce41bfe23282ab35c00385a2d06895b56a74a52c7e79b643a8c7c3a85e8ce15e0fc081d4f507359e7debadbb4f7f44c4bd12e8d4d91d031ab23b24d17050ab25b35aa2e30479febfa3c6947e22088695b9cad797b28ade61db0b35baba06a1d3d6f1ca86b9d56e230abe91dc2a159b7fbef894c23904c09ce78edd8bd302d80f0bec0c9463855e7b1e4fc31a985289658fdb479a862bc2dbd571c44adf771291a1d158101f692105f8d005d58ec45488c37bb04575917e73d0c34c74cf5d2c1463ef7da19e5e7e1fd638ff2770ab3457716f6f0fff77e387a98411ba2ed001c99402e9e876a17201cb7c77137afd3dd9a7175181b45fa6e991d83308adb8fe67eb720a334afe060d6e0ba3cf092fa409f34f2b97466bbfb6990f4f58dc5bd879d4cef5a00588bf9b2a7ed9fbf33b3387016662789eab65542ec980426a982cc10d936ea02671d4b894edcfe48250054642c5d5cb4212918c59145ffe86acc8097729431344077749be5d43e2941e10b244251756ed041ad42b4976c7558ee9c0247749d65d1013c98f276bbaed760217e4f5921ac20da2c1ae38bd6209cf380d3ab1b0f7c4177a7486ae2780684266c165b427cd67f6a8309896eb7cdb3e813ff515fc78ff7ea92e32819bb03d3691ee04e80772f8457b4472d808841692962208f36c9ec49f9d52f69c293e5d3fce1f6209131c8cdcb7a6d836da141844da1cbee23b8316d7e6bc749cd9f05e4e034d969e75f2bdec1e69f1f1106d5611c824d4c219cf7eda6fe237526429b399671f67b7214ad949bdc16c89235d9f7790cc5f8a66a2bd98f28ebeddeeb4198b48884dd1e8aa0dde6c207bf396283b818522842ed8ede9a59a47b7cf251700a9f21037ea693229b4d12561140ef22150ab96d8040039487ede369e97803f750eb44c591b03c6402364fefcf721fc94058fda0e6a161c5b8e705f41654ba1de74812c6eb53bcdcd70740043681f6c785803b71e50bb0a24ee1d4e62f0d2033bb5348f7bff004fbbb990acbeb442dc8271d8e011b4936d9704d115454c34152a9bdf52c7d355c34d35247ef26f5a1f112945aa5b42abdcd028dfbee131ab71f679dfc6a59de7815d9257f259aff83ee0d215efa923c90390e1aa9f52405c57794b095c9a98a5028d673d0d3b10c35060d052906a70e3d83f74803cf486e897b8f4fe8f6d8f35ac5324b4672f8ed02444bc762024dccf96e3d05f1bb55fdfaa887e9077cc4a85ca8507e09f029258d608b283748b7bda1883c304e8f3458c58c9adb0375c4e5b3d4e932989a2f5d5e99560f92dbf2b75645423a1fa53bbdcde6beccc9cb6b675951082e470967d98f84f266a6eabc609cd0d31a6de1b4f170f60d024dceee569536268da95ef3406e6cf34ce093f47fd0f990c716d8b4fecc85d79eb924e7368bfc24a727526d28228b3174938604b3bf2e3ad4be92913abbbd110fb88f804eb6b9dc0d12e6443c675599636141a50ada2165f82bd135ab2249ee1f370cba9d9200cae2cf2ad5eabece5230cc351c38e68b5eca50c6c371f40b44e43e81a53aa8ef3520f63576d3b23382c10394c2723ef38c52c65bcc0059890deee37399a32e3950bc8e7c7dc75eade3a650d426d04a75fe90f959afd96924e01568e1d7a7f0446ab39d67d8e85fc5c58e671b17a101fa358d697d2c36154b787119b1ca9c492b64d98e7579345d790c05239c2c7d921b620103383cbce24f22b4ab15977cd8f8d8e8dee55c086ad6c8bd8ba9a7cd7955057dfa6fd99be88c03e050d6a0cceb99cad8fa517ecf06e3a3dfffb0474716b4e7b6da5b0f206d27a7590fe04f7e7513026448295f5edb82fb3b79bfb99185c87b43777bf93d5338f5c0e5e022fa26259f8920b23d2bc21ed33ed711b7410fc04c9dfb217139abcb7144c4bd4a8f66b199b28697dd210809af12fc64147326abcf421696b41239d507e1e69c3c84703f7bfa4c6549a711c2ed25eeef7993106df79ed8700f542a86d06df30530f49c3fe38328d18d5723fd5475027a42fad82f7c5626821aee48e8ebc22f70f92fcaf7ad6f84c08e99f0a11c019e46cbd808200b30b781e887fd47c536317a963821fab71dfd39638ab087bc8393ffac9ec2f7848d7e2bb02d03e1b3afe2bf8d85df3a0dd4cd3b1428fe006a18cfc88b14b4b5d08c5ee54e956e429beb8108ebafc4d134cd32fc83224b115d3e4ed2e74b4b6f3995a87ee3757b67686d0a5c89863c6bca5ceeef5a7d78141f73b19e655d8368adfcb8e2f709b9764b64e65c505bf1c4bf5fad8162c31c3e8c357065155f966e9f214d2bca8aaca2b2dc8730fd98b40df616b8bf94060915cdbd5570b59d09369c376ce564107716bdb42557210e4d64b6617d44d4b0928f723aa69a595f05ecae5467564ab20eff65ce14a442d54eddacb68c9d38b6576e37c96467f57cd1970c7ce291721cfa33e56337b16055416d5e090bbe53dd7db70664f45c3d285ff281ce664c7dba95c3637b7c1cf0e14c113f8a353c19ba2fd281699c04cb78ceebc46ad4e9d0e329538c095fd8aa20f43596bdfae4e8b365a20f9b527c09f5558c322f3cec8271c838f3dd18c13ff3a94a8b2c213a3497ec2332875177ffcc5cd5275138853d9283d2bd2357536e60b10941ea19f787060ce27edd9e9fe338ac70797607b98f4915414aeb1497ae46d1a97062863222e1cc8566df9f67f0d406362091368148c61e7cb2e3d0e77bedf73a8fb0cecb6442f73b8f818277b7e3b7ed36803be8444ab99ff50d6638c4ba04bef26156686cd21a95a122a2d84e903d12aa378c9ca66db4f287f6f6fc280363a0009ed8416b2d3cd40d60994d26c3a83a76ad0f706698476c8fa1c754cdf3a1b798ee52089bac9ae2f211c8a18cafd4f7d16076122efdb0204f7cb73f8af4be44710aa2ed989a383a2f259511db7a3451d7dcc9d74ebd2feab7b370c2d27fdf72d96868dc5f77002d3ed8f341bf3c2d0e2739c532f5a6e8e514765cec30698275db690e2bb54eaf2f6484e90a5ca22e797e3ff42da0d2cacb30c8892b9bf7fcd4cdefac4c230bff70dce4dd7ea9887e176761f6f5becfea82f76bed80b787c9374c1aa429f995ab57123bdf89494e3ace29d8e21b61c439ceef1f1a4d78e2eadf9785492403575b37f784f9ccd884a206cd21b32ff040a5adf7b6414722417c3401dba3a06c28f60255da0d2adea65a0cc0fb208ef8bd42c179b2e12b0de9ac651feecdc8aecda6143c8cf7f9cd7b5356e387d54eb2fdf8283667d688b2c092f2300431e480273dc06320e3b1c01f890e45fbf3c64729a7e5dc47d276d3ec8c957ccf130e243ee53f64ea5594af60091946859251ac5dcc98752238e2f6c19f97b8ae8f5118a203906909977bfaa5082abd5fc8b14453765c5c3e692df810ed239cc9033250a9d80e1deb45eccfd0633eb77eeee3078aa58e3e378a5902beafae0b128d932010ae2c3f5892126adf4ca785d99886a9216da5181a6e5a79f19fbc6d3b9f63a215ec8678a0a988cbad99a1cc95894d17ab308b5ba660271ab6f2d85ee471bfec9c6726146b66b5bc5e380fed8e991737e1be5923c57a1cd4401bbd6e447aacd77e0a9d534f4aade3077db501155f4fc693f9fe870174ca9bcb2f0d143d92e2c65a5d50fc045a5549918154b694121599235c9910406bf52c25fec32fd4fc1d14bb805047f048a7fe31f560c43347be73ddbf03631d8a2fe0165e1c9e3974c6617f6e35f66e86c1747e31a216c72207dce40d718d21965984a60b6945ae753a21bdbf23be4c061211f6b6c728c7f111e5d770594818c91edfa98dd6ef55ee19a1f3dd5e687131aa3bfecb6512238426deef8a5429d3617a78851fcf07c7a3d219406cda84e9ea683847e93ec6bc9acc46ebaefa4ea3fda62de717c7ff37d0c2541f5db830cb4db4fa66b40c47bb2c6169593f768d37f2393d00ee0ca64fc5c7710eeabd9c33c18d8fe529f0e056da6ab52dcb4ec5005f259afc7960e286d2045ba2bc706b726dd4b1813fa9407022a25c4467cd480132ed9265fd8dadf93bad51f8d9e2141ac1ab1d84e94ae3cf5eef94ce35fd9ae0c9d551a5c5788bc92e3bb547ae3a03661f8c3750b03cf901bb2a8ead1e094ab7c07c428829a98b6cb49de0be794a72242c6c27c63a30e5763f0f3eae463428f86068bc707bdba80f650c05c74ea4e0ab67e2070f85873d2a83c302e08f3a77f114d3b6ef4c6d068044d023a645680244a09a2fc62d11113cd6494d5c00ef953dd88b554c3a0593e1d0529cf714abd944b3865ec8c6269a66765064f31a6df2b7835f0ee515596cd6897bce14eef0880181d2e432c48c60800d325c37184fd2386da377d2f046a74f69fc9da10e76248440ef174582a54826528ff67f0d14961df21e2c42a12b1e11bddd68bd4dcf0a5c3fdf0f6c09909a14313d287652f0b97f28e9fca59e7f831898a77eaa07793232cbbd4536611b707592e26bada8004a4beaf95c85b9eb7e5329d142ea38a2d176f674a1564baf54098edc7cee97101eadbca27cc09cf6d38b9da029a44d5e58869d180371c62d91d72b7b6a7bdbebbe445dd3830b1fab37245205e5f6311fa8c94f4198233df31f3289d1d56155eacd4c56c6d2ef3eec5ea120b2ab7a7b36a93371c85890e7ecceb86a857971c7c397432d923beaca945d3348cf3246e5b2902f2df64434ccb050dc40d7235659f6f318f9a4ba8920f5b08852da819b489330cae6d0c55613de53566e59bda5836ce7e13ea4d23df39f74a8e3e0423d72e188e966500892ffa4ae3e5ffdfdea7ce2bd567d1ca83af8877528f20a9e5c58d478a74b271378059363184f0c35249436cf92fa25495350d54a833afa0d751ecd879b79e37af438f0b25eb5c2ab68f17686736e1a0ef246276c066122b5a866a769887d99f51298def1a39f09b9f627507754fdc8af96491c9c69ed7d4af9e991b7be721868ec58982d032fb99cc52e1b0875265ebb1345bdcf908f3c6b625538b0444b189908d3bc73f610df3e15d0dafcc87cdd34020e315e7156bd5b7b57ad1df7d280c9382534905f378544c6e90cb4f086b9cd2d4cdaca993ca6665a301f8073807980c78d28f0c24b2eeda6119f0e7c4b15ba286458dfa5c2c80959ca77bca860a8a0d6d054be92056a1314a8ac9f5aa0ce22532c2aecd95d83313d51e572a3103bc03787854b06df7213b258c01ff94246d23b6e585ef79908c2e303884407bb6961070114f236cd708c57215b8665e76576896f2e3a53a213d4c237385544ffe2b901aef03f2190da8e86e5b2e2de73cbe7cdc655766c384ca61a62d2bdcaa52e96dd8f8c82a35fcdbb97de84da12eefc57cd32884e0c38ae4377f1165faf27e82adcf78d05853f9e14a85332b450b1c527acdc530364d7c39f9149af07eb4f1f01f1ca1574418a6624e256dd06781bc1a20232c5e6d666b7e554bf1dbb6e3ca44139ee803ecfc85b24066fea144809f99e3b296662e559adc4d36229275cd6291090889c1202ce7a7e48500e114d9ec498dad7afeebc06aaab952bc2f1214d78bcf0cb3d460f61dc07deaf4041228c53e6d1df620eeb08a59edaee0f4268e5f9916f1004002e38a467ab8b7dd01fcf5cda822f6057cd817d994f60a43c2e0ce59b8e883e7229e6e2e272fdda85afc09bda808f6f0760813f58312579558a4c997a1ba934122b96100df70a87a4ff6a96dbb6b95e811b356b8cb468d2b3f1a90982e038f650b165a66ce09b9b970579eb1481c3600666318df43dafcdb22c19a81e5f3069a3c209750b1c1d486529add5f55a930abbc863f4ca5b019b5151fcd81ecfb252a6040d96b6cf0e389c3aacd89f775ca05b431f45d19374d673bd0ea6fdcf2b301d8a0af3e9df24fcd8b4aff91dd00439d274042e7c2f3502ae768d37b789f622e0b3e677b885633a0fc1b354bd62a0db59e3c179f9b093bc9e1f6a59d04fd1c63ba0eb12911b519deb2d1079af3a4e7f4ad4396d994bda3c27193c07bd84c4de5bb5507d9f1ed6ea6e446ccddf8b03e09d669fe982ac2ad14cf66ced25fc3961abbc94c56e6ca0a8533ecb762bb85c34c5e89dad55b2ddc07a8bb861891f82d01298335b78036c24378223111c211ddc378196dc091c0bb09bedad429a024832d1dfc3fb34eb2859bcd94a49f1df35f1b46ce21db8944ede3aa7c1ea0aaabf5adadd500da4d8a8c269f08895ceeed5534feaf0a945fdf15c16fa71273273011bb11ef5e4d46ff139a8f082289e7287a37ef703559036c688dbbb4f5f143e5370a79ae9b0fb6b19cb4c2f0ade223a3db1d539ffe1049aef2cec66f6f04f1ce061c134e71e22ca6fe20af9c8ec6326afbbe5bb3efb90eb27c6e61c4b225603f13987edeba022030f291a4329327043d616f81c874a0d02c215c1b0b65010c1c1d2eab0dd176c334207071c5e542a94a871d28b940713f77fe130d796981b5032e783ae6856135b70a34fe10458997bd4aa4cbd872f500e5cd7fd788c271ddade604ee789ec40b9e5b7af28d957f4d312d2a91184ea772c017a6efaaadf3f17d8bdf0f2b9d05c2df1f46af462c5bb08084be2de051f439a9029f83d9e416c0bd0e92eec395330e95b747afd29387db1a66d9916920d2915dfb9da664fa90f6d4175fb3dd14c46b11a44e53241d00b788b4caa290250b74e99cd84512161e267505046ccfb81f22f6a03e6e2af9b9de3b2422b60f48b94533642a63235961a76c53e95f500670df1f5ad82a3ba589a68ae6dbab8502c89c56a3af25c26e17c406e65eee93da0930b9cc497d5c13b23f64b32950ca13473740330c4f5b8e927faa40316d38f044bfff18e3d15de081a37246430fe23a52b3fd12bbf0b693632d11a6cc32e2f7eaf03aa60a533f37adeca51013cf6e5e323002f1778363eea5a6ae2535a9d0c1d83a6988e1a47ef1248e7ee1aad7cfd39ebfb2b87643a2bafd5caa3491d4e5fe40f1dd910269a9d9683a0735c0d94f26c1f08cdcb1e112f58778795340eaa9b44f6f3ed46c57ebd973a11bc35f51be57aeb6a4e4eabb906979e49381e67d8089a25795c6696fb50bb1dce79a39d01332f322c4a844903763b7074f01e2f10855b79f31b413b76f2ffcfbae5790593c0a04c2bddb1563d2e882a590816bf1e19eddb99cae35a627128f26cd4f02b180c18ba52720afc4d51452c177786a0c608291f5a56e1966fadc7b3181c092759d18aa785f26dd92606a2d799b1b985469aaa916d9731c7561b49357e904c8abc296c929a5e8595addfbc714e7ab6478f93e8c73434574805baf85aae3a5ca220c4fb7fca26

private def light (n : ℕ) : Bool :=
  if n≤173 then decide n.Prime else n.gcd 36927733697396923753829554635211962404299715564140382424433649868278555214296659802052327860953228596413291334931704037143411082635200789592708437910693220744422451783693904122568819692138717826140678603271725989637483256524946200711557865266227200777205900363920166407372800000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤30000) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 173 = 36927733697396923753829554635211962404299715564140382424433649868278555214296659802052327860953228596413291334931704037143411082635200789592708437910693220744422451783693904122568819692138717826140678603271725989637483256524946200711557865266227200777205900363920166407372800000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 173 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤30000 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 58 := by unfold smallValid; decide +kernel

private theorem sp58 : smallValid 58 59 := by unfold smallValid; decide +kernel

private theorem sp117 : smallValid 117 58 := by unfold smallValid; decide +kernel

private theorem sp175 : smallValid 175 59 := by unfold smallValid; decide +kernel

private theorem sp234 : smallValid 234 58 := by unfold smallValid; decide +kernel

private theorem sp292 : smallValid 292 59 := by unfold smallValid; decide +kernel

private theorem sp351 : smallValid 351 58 := by unfold smallValid; decide +kernel

private theorem sp409 : smallValid 409 59 := by unfold smallValid; decide +kernel

private theorem sp468 : smallValid 468 58 := by unfold smallValid; decide +kernel

private theorem sp526 : smallValid 526 59 := by unfold smallValid; decide +kernel

private theorem sp585 : smallValid 585 58 := by unfold smallValid; decide +kernel

private theorem sp643 : smallValid 643 59 := by unfold smallValid; decide +kernel

private theorem sp702 : smallValid 702 58 := by unfold smallValid; decide +kernel

private theorem sp760 : smallValid 760 59 := by unfold smallValid; decide +kernel

private theorem sp819 : smallValid 819 59 := by unfold smallValid; decide +kernel

private theorem sp878 : smallValid 878 59 := by unfold smallValid; decide +kernel

private theorem sp937 : smallValid 937 58 := by unfold smallValid; decide +kernel

private theorem sp995 : smallValid 995 59 := by unfold smallValid; decide +kernel

private theorem sp1054 : smallValid 1054 58 := by unfold smallValid; decide +kernel

private theorem sp1112 : smallValid 1112 59 := by unfold smallValid; decide +kernel

private theorem sp1171 : smallValid 1171 58 := by unfold smallValid; decide +kernel

private theorem sp1229 : smallValid 1229 59 := by unfold smallValid; decide +kernel

private theorem sp1288 : smallValid 1288 59 := by unfold smallValid; decide +kernel

private theorem sp1347 : smallValid 1347 59 := by unfold smallValid; decide +kernel

private theorem sp1406 : smallValid 1406 58 := by unfold smallValid; decide +kernel

private theorem sp1464 : smallValid 1464 59 := by unfold smallValid; decide +kernel

private theorem sp1523 : smallValid 1523 58 := by unfold smallValid; decide +kernel

private theorem sp1581 : smallValid 1581 59 := by unfold smallValid; decide +kernel

private theorem sp1640 : smallValid 1640 58 := by unfold smallValid; decide +kernel

private theorem sp1698 : smallValid 1698 59 := by unfold smallValid; decide +kernel

private theorem sp1757 : smallValid 1757 59 := by unfold smallValid; decide +kernel

private theorem sp1816 : smallValid 1816 59 := by unfold smallValid; decide +kernel

private theorem sp1875 : smallValid 1875 58 := by unfold smallValid; decide +kernel

private theorem sp1933 : smallValid 1933 59 := by unfold smallValid; decide +kernel

private theorem sp1992 : smallValid 1992 58 := by unfold smallValid; decide +kernel

private theorem sp2050 : smallValid 2050 59 := by unfold smallValid; decide +kernel

private theorem sp2109 : smallValid 2109 58 := by unfold smallValid; decide +kernel

private theorem sp2167 : smallValid 2167 59 := by unfold smallValid; decide +kernel

private theorem sp2226 : smallValid 2226 58 := by unfold smallValid; decide +kernel

private theorem sp2284 : smallValid 2284 59 := by unfold smallValid; decide +kernel

private theorem sp2343 : smallValid 2343 58 := by unfold smallValid; decide +kernel

private theorem sp2401 : smallValid 2401 59 := by unfold smallValid; decide +kernel

private theorem sp2460 : smallValid 2460 58 := by unfold smallValid; decide +kernel

private theorem sp2518 : smallValid 2518 59 := by unfold smallValid; decide +kernel

private theorem sp2577 : smallValid 2577 58 := by unfold smallValid; decide +kernel

private theorem sp2635 : smallValid 2635 59 := by unfold smallValid; decide +kernel

private theorem sp2694 : smallValid 2694 59 := by unfold smallValid; decide +kernel

private theorem sp2753 : smallValid 2753 59 := by unfold smallValid; decide +kernel

private theorem sp2812 : smallValid 2812 58 := by unfold smallValid; decide +kernel

private theorem sp2870 : smallValid 2870 59 := by unfold smallValid; decide +kernel

private theorem sp2929 : smallValid 2929 58 := by unfold smallValid; decide +kernel

private theorem sp2987 : smallValid 2987 59 := by unfold smallValid; decide +kernel

private theorem sp3046 : smallValid 3046 58 := by unfold smallValid; decide +kernel

private theorem sp3104 : smallValid 3104 59 := by unfold smallValid; decide +kernel

private theorem sp3163 : smallValid 3163 59 := by unfold smallValid; decide +kernel

private theorem sp3222 : smallValid 3222 59 := by unfold smallValid; decide +kernel

private theorem sp3281 : smallValid 3281 58 := by unfold smallValid; decide +kernel

private theorem sp3339 : smallValid 3339 59 := by unfold smallValid; decide +kernel

private theorem sp3398 : smallValid 3398 58 := by unfold smallValid; decide +kernel

private theorem sp3456 : smallValid 3456 59 := by unfold smallValid; decide +kernel

private theorem sp3515 : smallValid 3515 58 := by unfold smallValid; decide +kernel

private theorem sp3573 : smallValid 3573 59 := by unfold smallValid; decide +kernel

private theorem sp3632 : smallValid 3632 59 := by unfold smallValid; decide +kernel

private theorem sp3691 : smallValid 3691 59 := by unfold smallValid; decide +kernel

private theorem sp3750 : smallValid 3750 58 := by unfold smallValid; decide +kernel

private theorem sp3808 : smallValid 3808 59 := by unfold smallValid; decide +kernel

private theorem sp3867 : smallValid 3867 58 := by unfold smallValid; decide +kernel

private theorem sp3925 : smallValid 3925 59 := by unfold smallValid; decide +kernel

private theorem sp3984 : smallValid 3984 58 := by unfold smallValid; decide +kernel

private theorem sp4042 : smallValid 4042 59 := by unfold smallValid; decide +kernel

private theorem sp4101 : smallValid 4101 58 := by unfold smallValid; decide +kernel

private theorem sp4159 : smallValid 4159 59 := by unfold smallValid; decide +kernel

private theorem sp4218 : smallValid 4218 58 := by unfold smallValid; decide +kernel

private theorem sp4276 : smallValid 4276 59 := by unfold smallValid; decide +kernel

private theorem sp4335 : smallValid 4335 58 := by unfold smallValid; decide +kernel

private theorem sp4393 : smallValid 4393 59 := by unfold smallValid; decide +kernel

private theorem sp4452 : smallValid 4452 58 := by unfold smallValid; decide +kernel

private theorem sp4510 : smallValid 4510 59 := by unfold smallValid; decide +kernel

private theorem sp4569 : smallValid 4569 59 := by unfold smallValid; decide +kernel

private theorem sp4628 : smallValid 4628 59 := by unfold smallValid; decide +kernel

private theorem sp4687 : smallValid 4687 58 := by unfold smallValid; decide +kernel

private theorem sp4745 : smallValid 4745 59 := by unfold smallValid; decide +kernel

private theorem sp4804 : smallValid 4804 58 := by unfold smallValid; decide +kernel

private theorem sp4862 : smallValid 4862 59 := by unfold smallValid; decide +kernel

private theorem sp4921 : smallValid 4921 58 := by unfold smallValid; decide +kernel

private theorem sp4979 : smallValid 4979 59 := by unfold smallValid; decide +kernel

private theorem sp5038 : smallValid 5038 59 := by unfold smallValid; decide +kernel

private theorem sp5097 : smallValid 5097 59 := by unfold smallValid; decide +kernel

private theorem sp5156 : smallValid 5156 58 := by unfold smallValid; decide +kernel

private theorem sp5214 : smallValid 5214 59 := by unfold smallValid; decide +kernel

private theorem sp5273 : smallValid 5273 58 := by unfold smallValid; decide +kernel

private theorem sp5331 : smallValid 5331 59 := by unfold smallValid; decide +kernel

private theorem sp5390 : smallValid 5390 58 := by unfold smallValid; decide +kernel

private theorem sp5448 : smallValid 5448 59 := by unfold smallValid; decide +kernel

private theorem sp5507 : smallValid 5507 59 := by unfold smallValid; decide +kernel

private theorem sp5566 : smallValid 5566 59 := by unfold smallValid; decide +kernel

private theorem sp5625 : smallValid 5625 58 := by unfold smallValid; decide +kernel

private theorem sp5683 : smallValid 5683 59 := by unfold smallValid; decide +kernel

private theorem sp5742 : smallValid 5742 58 := by unfold smallValid; decide +kernel

private theorem sp5800 : smallValid 5800 59 := by unfold smallValid; decide +kernel

private theorem sp5859 : smallValid 5859 58 := by unfold smallValid; decide +kernel

private theorem sp5917 : smallValid 5917 59 := by unfold smallValid; decide +kernel

private theorem sp5976 : smallValid 5976 58 := by unfold smallValid; decide +kernel

private theorem sp6034 : smallValid 6034 59 := by unfold smallValid; decide +kernel

private theorem sp6093 : smallValid 6093 58 := by unfold smallValid; decide +kernel

private theorem sp6151 : smallValid 6151 59 := by unfold smallValid; decide +kernel

private theorem sp6210 : smallValid 6210 58 := by unfold smallValid; decide +kernel

private theorem sp6268 : smallValid 6268 59 := by unfold smallValid; decide +kernel

private theorem sp6327 : smallValid 6327 58 := by unfold smallValid; decide +kernel

private theorem sp6385 : smallValid 6385 59 := by unfold smallValid; decide +kernel

private theorem sp6444 : smallValid 6444 59 := by unfold smallValid; decide +kernel

private theorem sp6503 : smallValid 6503 59 := by unfold smallValid; decide +kernel

private theorem sp6562 : smallValid 6562 58 := by unfold smallValid; decide +kernel

private theorem sp6620 : smallValid 6620 59 := by unfold smallValid; decide +kernel

private theorem sp6679 : smallValid 6679 58 := by unfold smallValid; decide +kernel

private theorem sp6737 : smallValid 6737 59 := by unfold smallValid; decide +kernel

private theorem sp6796 : smallValid 6796 58 := by unfold smallValid; decide +kernel

private theorem sp6854 : smallValid 6854 59 := by unfold smallValid; decide +kernel

private theorem sp6913 : smallValid 6913 59 := by unfold smallValid; decide +kernel

private theorem sp6972 : smallValid 6972 59 := by unfold smallValid; decide +kernel

private theorem sp7031 : smallValid 7031 58 := by unfold smallValid; decide +kernel

private theorem sp7089 : smallValid 7089 59 := by unfold smallValid; decide +kernel

private theorem sp7148 : smallValid 7148 58 := by unfold smallValid; decide +kernel

private theorem sp7206 : smallValid 7206 59 := by unfold smallValid; decide +kernel

private theorem sp7265 : smallValid 7265 58 := by unfold smallValid; decide +kernel

private theorem sp7323 : smallValid 7323 59 := by unfold smallValid; decide +kernel

private theorem sp7382 : smallValid 7382 59 := by unfold smallValid; decide +kernel

private theorem sp7441 : smallValid 7441 59 := by unfold smallValid; decide +kernel

private theorem sp7500 : smallValid 7500 58 := by unfold smallValid; decide +kernel

private theorem sp7558 : smallValid 7558 59 := by unfold smallValid; decide +kernel

private theorem sp7617 : smallValid 7617 58 := by unfold smallValid; decide +kernel

private theorem sp7675 : smallValid 7675 59 := by unfold smallValid; decide +kernel

private theorem sp7734 : smallValid 7734 58 := by unfold smallValid; decide +kernel

private theorem sp7792 : smallValid 7792 59 := by unfold smallValid; decide +kernel

private theorem sp7851 : smallValid 7851 58 := by unfold smallValid; decide +kernel

private theorem sp7909 : smallValid 7909 59 := by unfold smallValid; decide +kernel

private theorem sp7968 : smallValid 7968 58 := by unfold smallValid; decide +kernel

private theorem sp8026 : smallValid 8026 59 := by unfold smallValid; decide +kernel

private theorem sp8085 : smallValid 8085 58 := by unfold smallValid; decide +kernel

private theorem sp8143 : smallValid 8143 59 := by unfold smallValid; decide +kernel

private theorem sp8202 : smallValid 8202 58 := by unfold smallValid; decide +kernel

private theorem sp8260 : smallValid 8260 59 := by unfold smallValid; decide +kernel

private theorem sp8319 : smallValid 8319 59 := by unfold smallValid; decide +kernel

private theorem sp8378 : smallValid 8378 59 := by unfold smallValid; decide +kernel

private theorem sp8437 : smallValid 8437 58 := by unfold smallValid; decide +kernel

private theorem sp8495 : smallValid 8495 59 := by unfold smallValid; decide +kernel

private theorem sp8554 : smallValid 8554 58 := by unfold smallValid; decide +kernel

private theorem sp8612 : smallValid 8612 59 := by unfold smallValid; decide +kernel

private theorem sp8671 : smallValid 8671 58 := by unfold smallValid; decide +kernel

private theorem sp8729 : smallValid 8729 59 := by unfold smallValid; decide +kernel

private theorem sp8788 : smallValid 8788 59 := by unfold smallValid; decide +kernel

private theorem sp8847 : smallValid 8847 59 := by unfold smallValid; decide +kernel

private theorem sp8906 : smallValid 8906 58 := by unfold smallValid; decide +kernel

private theorem sp8964 : smallValid 8964 59 := by unfold smallValid; decide +kernel

private theorem sp9023 : smallValid 9023 58 := by unfold smallValid; decide +kernel

private theorem sp9081 : smallValid 9081 59 := by unfold smallValid; decide +kernel

private theorem sp9140 : smallValid 9140 58 := by unfold smallValid; decide +kernel

private theorem sp9198 : smallValid 9198 59 := by unfold smallValid; decide +kernel

private theorem sp9257 : smallValid 9257 59 := by unfold smallValid; decide +kernel

private theorem sp9316 : smallValid 9316 59 := by unfold smallValid; decide +kernel

private theorem sp9375 : smallValid 9375 58 := by unfold smallValid; decide +kernel

private theorem sp9433 : smallValid 9433 59 := by unfold smallValid; decide +kernel

private theorem sp9492 : smallValid 9492 58 := by unfold smallValid; decide +kernel

private theorem sp9550 : smallValid 9550 59 := by unfold smallValid; decide +kernel

private theorem sp9609 : smallValid 9609 58 := by unfold smallValid; decide +kernel

private theorem sp9667 : smallValid 9667 59 := by unfold smallValid; decide +kernel

private theorem sp9726 : smallValid 9726 58 := by unfold smallValid; decide +kernel

private theorem sp9784 : smallValid 9784 59 := by unfold smallValid; decide +kernel

private theorem sp9843 : smallValid 9843 58 := by unfold smallValid; decide +kernel

private theorem sp9901 : smallValid 9901 59 := by unfold smallValid; decide +kernel

private theorem sp9960 : smallValid 9960 58 := by unfold smallValid; decide +kernel

private theorem sp10018 : smallValid 10018 59 := by unfold smallValid; decide +kernel

private theorem sp10077 : smallValid 10077 58 := by unfold smallValid; decide +kernel

private theorem sp10135 : smallValid 10135 59 := by unfold smallValid; decide +kernel

private theorem sp10194 : smallValid 10194 59 := by unfold smallValid; decide +kernel

private theorem sp10253 : smallValid 10253 59 := by unfold smallValid; decide +kernel

private theorem sp10312 : smallValid 10312 58 := by unfold smallValid; decide +kernel

private theorem sp10370 : smallValid 10370 59 := by unfold smallValid; decide +kernel

private theorem sp10429 : smallValid 10429 58 := by unfold smallValid; decide +kernel

private theorem sp10487 : smallValid 10487 59 := by unfold smallValid; decide +kernel

private theorem sp10546 : smallValid 10546 58 := by unfold smallValid; decide +kernel

private theorem sp10604 : smallValid 10604 59 := by unfold smallValid; decide +kernel

private theorem sp10663 : smallValid 10663 59 := by unfold smallValid; decide +kernel

private theorem sp10722 : smallValid 10722 59 := by unfold smallValid; decide +kernel

private theorem sp10781 : smallValid 10781 58 := by unfold smallValid; decide +kernel

private theorem sp10839 : smallValid 10839 59 := by unfold smallValid; decide +kernel

private theorem sp10898 : smallValid 10898 58 := by unfold smallValid; decide +kernel

private theorem sp10956 : smallValid 10956 59 := by unfold smallValid; decide +kernel

private theorem sp11015 : smallValid 11015 58 := by unfold smallValid; decide +kernel

private theorem sp11073 : smallValid 11073 59 := by unfold smallValid; decide +kernel

private theorem sp11132 : smallValid 11132 59 := by unfold smallValid; decide +kernel

private theorem sp11191 : smallValid 11191 59 := by unfold smallValid; decide +kernel

private theorem sp11250 : smallValid 11250 58 := by unfold smallValid; decide +kernel

private theorem sp11308 : smallValid 11308 59 := by unfold smallValid; decide +kernel

private theorem sp11367 : smallValid 11367 58 := by unfold smallValid; decide +kernel

private theorem sp11425 : smallValid 11425 59 := by unfold smallValid; decide +kernel

private theorem sp11484 : smallValid 11484 58 := by unfold smallValid; decide +kernel

private theorem sp11542 : smallValid 11542 59 := by unfold smallValid; decide +kernel

private theorem sp11601 : smallValid 11601 58 := by unfold smallValid; decide +kernel

private theorem sp11659 : smallValid 11659 59 := by unfold smallValid; decide +kernel

private theorem sp11718 : smallValid 11718 58 := by unfold smallValid; decide +kernel

private theorem sp11776 : smallValid 11776 59 := by unfold smallValid; decide +kernel

private theorem sp11835 : smallValid 11835 58 := by unfold smallValid; decide +kernel

private theorem sp11893 : smallValid 11893 59 := by unfold smallValid; decide +kernel

private theorem sp11952 : smallValid 11952 58 := by unfold smallValid; decide +kernel

private theorem sp12010 : smallValid 12010 59 := by unfold smallValid; decide +kernel

private theorem sp12069 : smallValid 12069 59 := by unfold smallValid; decide +kernel

private theorem sp12128 : smallValid 12128 59 := by unfold smallValid; decide +kernel

private theorem sp12187 : smallValid 12187 58 := by unfold smallValid; decide +kernel

private theorem sp12245 : smallValid 12245 59 := by unfold smallValid; decide +kernel

private theorem sp12304 : smallValid 12304 58 := by unfold smallValid; decide +kernel

private theorem sp12362 : smallValid 12362 59 := by unfold smallValid; decide +kernel

private theorem sp12421 : smallValid 12421 58 := by unfold smallValid; decide +kernel

private theorem sp12479 : smallValid 12479 59 := by unfold smallValid; decide +kernel

private theorem sp12538 : smallValid 12538 59 := by unfold smallValid; decide +kernel

private theorem sp12597 : smallValid 12597 59 := by unfold smallValid; decide +kernel

private theorem sp12656 : smallValid 12656 58 := by unfold smallValid; decide +kernel

private theorem sp12714 : smallValid 12714 59 := by unfold smallValid; decide +kernel

private theorem sp12773 : smallValid 12773 58 := by unfold smallValid; decide +kernel

private theorem sp12831 : smallValid 12831 59 := by unfold smallValid; decide +kernel

private theorem sp12890 : smallValid 12890 58 := by unfold smallValid; decide +kernel

private theorem sp12948 : smallValid 12948 59 := by unfold smallValid; decide +kernel

private theorem sp13007 : smallValid 13007 59 := by unfold smallValid; decide +kernel

private theorem sp13066 : smallValid 13066 59 := by unfold smallValid; decide +kernel

private theorem sp13125 : smallValid 13125 58 := by unfold smallValid; decide +kernel

private theorem sp13183 : smallValid 13183 59 := by unfold smallValid; decide +kernel

private theorem sp13242 : smallValid 13242 58 := by unfold smallValid; decide +kernel

private theorem sp13300 : smallValid 13300 59 := by unfold smallValid; decide +kernel

private theorem sp13359 : smallValid 13359 58 := by unfold smallValid; decide +kernel

private theorem sp13417 : smallValid 13417 59 := by unfold smallValid; decide +kernel

private theorem sp13476 : smallValid 13476 58 := by unfold smallValid; decide +kernel

private theorem sp13534 : smallValid 13534 59 := by unfold smallValid; decide +kernel

private theorem sp13593 : smallValid 13593 58 := by unfold smallValid; decide +kernel

private theorem sp13651 : smallValid 13651 59 := by unfold smallValid; decide +kernel

private theorem sp13710 : smallValid 13710 58 := by unfold smallValid; decide +kernel

private theorem sp13768 : smallValid 13768 59 := by unfold smallValid; decide +kernel

private theorem sp13827 : smallValid 13827 58 := by unfold smallValid; decide +kernel

private theorem sp13885 : smallValid 13885 59 := by unfold smallValid; decide +kernel

private theorem sp13944 : smallValid 13944 59 := by unfold smallValid; decide +kernel

private theorem sp14003 : smallValid 14003 59 := by unfold smallValid; decide +kernel

private theorem sp14062 : smallValid 14062 58 := by unfold smallValid; decide +kernel

private theorem sp14120 : smallValid 14120 59 := by unfold smallValid; decide +kernel

private theorem sp14179 : smallValid 14179 58 := by unfold smallValid; decide +kernel

private theorem sp14237 : smallValid 14237 59 := by unfold smallValid; decide +kernel

private theorem sp14296 : smallValid 14296 58 := by unfold smallValid; decide +kernel

private theorem sp14354 : smallValid 14354 59 := by unfold smallValid; decide +kernel

private theorem sp14413 : smallValid 14413 59 := by unfold smallValid; decide +kernel

private theorem sp14472 : smallValid 14472 59 := by unfold smallValid; decide +kernel

private theorem sp14531 : smallValid 14531 58 := by unfold smallValid; decide +kernel

private theorem sp14589 : smallValid 14589 59 := by unfold smallValid; decide +kernel

private theorem sp14648 : smallValid 14648 58 := by unfold smallValid; decide +kernel

private theorem sp14706 : smallValid 14706 59 := by unfold smallValid; decide +kernel

private theorem sp14765 : smallValid 14765 58 := by unfold smallValid; decide +kernel

private theorem sp14823 : smallValid 14823 59 := by unfold smallValid; decide +kernel

private theorem sp14882 : smallValid 14882 59 := by unfold smallValid; decide +kernel

private theorem sp14941 : smallValid 14941 59 := by unfold smallValid; decide +kernel

private theorem sp15000 : smallValid 15000 58 := by unfold smallValid; decide +kernel

private theorem sp15058 : smallValid 15058 59 := by unfold smallValid; decide +kernel

private theorem sp15117 : smallValid 15117 58 := by unfold smallValid; decide +kernel

private theorem sp15175 : smallValid 15175 59 := by unfold smallValid; decide +kernel

private theorem sp15234 : smallValid 15234 58 := by unfold smallValid; decide +kernel

private theorem sp15292 : smallValid 15292 59 := by unfold smallValid; decide +kernel

private theorem sp15351 : smallValid 15351 58 := by unfold smallValid; decide +kernel

private theorem sp15409 : smallValid 15409 59 := by unfold smallValid; decide +kernel

private theorem sp15468 : smallValid 15468 58 := by unfold smallValid; decide +kernel

private theorem sp15526 : smallValid 15526 59 := by unfold smallValid; decide +kernel

private theorem sp15585 : smallValid 15585 58 := by unfold smallValid; decide +kernel

private theorem sp15643 : smallValid 15643 59 := by unfold smallValid; decide +kernel

private theorem sp15702 : smallValid 15702 58 := by unfold smallValid; decide +kernel

private theorem sp15760 : smallValid 15760 59 := by unfold smallValid; decide +kernel

private theorem sp15819 : smallValid 15819 59 := by unfold smallValid; decide +kernel

private theorem sp15878 : smallValid 15878 59 := by unfold smallValid; decide +kernel

private theorem sp15937 : smallValid 15937 58 := by unfold smallValid; decide +kernel

private theorem sp15995 : smallValid 15995 59 := by unfold smallValid; decide +kernel

private theorem sp16054 : smallValid 16054 58 := by unfold smallValid; decide +kernel

private theorem sp16112 : smallValid 16112 59 := by unfold smallValid; decide +kernel

private theorem sp16171 : smallValid 16171 58 := by unfold smallValid; decide +kernel

private theorem sp16229 : smallValid 16229 59 := by unfold smallValid; decide +kernel

private theorem sp16288 : smallValid 16288 59 := by unfold smallValid; decide +kernel

private theorem sp16347 : smallValid 16347 59 := by unfold smallValid; decide +kernel

private theorem sp16406 : smallValid 16406 58 := by unfold smallValid; decide +kernel

private theorem sp16464 : smallValid 16464 59 := by unfold smallValid; decide +kernel

private theorem sp16523 : smallValid 16523 58 := by unfold smallValid; decide +kernel

private theorem sp16581 : smallValid 16581 59 := by unfold smallValid; decide +kernel

private theorem sp16640 : smallValid 16640 58 := by unfold smallValid; decide +kernel

private theorem sp16698 : smallValid 16698 59 := by unfold smallValid; decide +kernel

private theorem sp16757 : smallValid 16757 59 := by unfold smallValid; decide +kernel

private theorem sp16816 : smallValid 16816 59 := by unfold smallValid; decide +kernel

private theorem sp16875 : smallValid 16875 58 := by unfold smallValid; decide +kernel

private theorem sp16933 : smallValid 16933 59 := by unfold smallValid; decide +kernel

private theorem sp16992 : smallValid 16992 58 := by unfold smallValid; decide +kernel

private theorem sp17050 : smallValid 17050 59 := by unfold smallValid; decide +kernel

private theorem sp17109 : smallValid 17109 58 := by unfold smallValid; decide +kernel

private theorem sp17167 : smallValid 17167 59 := by unfold smallValid; decide +kernel

private theorem sp17226 : smallValid 17226 58 := by unfold smallValid; decide +kernel

private theorem sp17284 : smallValid 17284 59 := by unfold smallValid; decide +kernel

private theorem sp17343 : smallValid 17343 58 := by unfold smallValid; decide +kernel

private theorem sp17401 : smallValid 17401 59 := by unfold smallValid; decide +kernel

private theorem sp17460 : smallValid 17460 58 := by unfold smallValid; decide +kernel

private theorem sp17518 : smallValid 17518 59 := by unfold smallValid; decide +kernel

private theorem sp17577 : smallValid 17577 58 := by unfold smallValid; decide +kernel

private theorem sp17635 : smallValid 17635 59 := by unfold smallValid; decide +kernel

private theorem sp17694 : smallValid 17694 59 := by unfold smallValid; decide +kernel

private theorem sp17753 : smallValid 17753 59 := by unfold smallValid; decide +kernel

private theorem sp17812 : smallValid 17812 58 := by unfold smallValid; decide +kernel

private theorem sp17870 : smallValid 17870 59 := by unfold smallValid; decide +kernel

private theorem sp17929 : smallValid 17929 58 := by unfold smallValid; decide +kernel

private theorem sp17987 : smallValid 17987 59 := by unfold smallValid; decide +kernel

private theorem sp18046 : smallValid 18046 58 := by unfold smallValid; decide +kernel

private theorem sp18104 : smallValid 18104 59 := by unfold smallValid; decide +kernel

private theorem sp18163 : smallValid 18163 59 := by unfold smallValid; decide +kernel

private theorem sp18222 : smallValid 18222 59 := by unfold smallValid; decide +kernel

private theorem sp18281 : smallValid 18281 58 := by unfold smallValid; decide +kernel

private theorem sp18339 : smallValid 18339 59 := by unfold smallValid; decide +kernel

private theorem sp18398 : smallValid 18398 58 := by unfold smallValid; decide +kernel

private theorem sp18456 : smallValid 18456 59 := by unfold smallValid; decide +kernel

private theorem sp18515 : smallValid 18515 58 := by unfold smallValid; decide +kernel

private theorem sp18573 : smallValid 18573 59 := by unfold smallValid; decide +kernel

private theorem sp18632 : smallValid 18632 59 := by unfold smallValid; decide +kernel

private theorem sp18691 : smallValid 18691 59 := by unfold smallValid; decide +kernel

private theorem sp18750 : smallValid 18750 58 := by unfold smallValid; decide +kernel

private theorem sp18808 : smallValid 18808 59 := by unfold smallValid; decide +kernel

private theorem sp18867 : smallValid 18867 58 := by unfold smallValid; decide +kernel

private theorem sp18925 : smallValid 18925 59 := by unfold smallValid; decide +kernel

private theorem sp18984 : smallValid 18984 58 := by unfold smallValid; decide +kernel

private theorem sp19042 : smallValid 19042 59 := by unfold smallValid; decide +kernel

private theorem sp19101 : smallValid 19101 58 := by unfold smallValid; decide +kernel

private theorem sp19159 : smallValid 19159 59 := by unfold smallValid; decide +kernel

private theorem sp19218 : smallValid 19218 58 := by unfold smallValid; decide +kernel

private theorem sp19276 : smallValid 19276 59 := by unfold smallValid; decide +kernel

private theorem sp19335 : smallValid 19335 58 := by unfold smallValid; decide +kernel

private theorem sp19393 : smallValid 19393 59 := by unfold smallValid; decide +kernel

private theorem sp19452 : smallValid 19452 58 := by unfold smallValid; decide +kernel

private theorem sp19510 : smallValid 19510 59 := by unfold smallValid; decide +kernel

private theorem sp19569 : smallValid 19569 59 := by unfold smallValid; decide +kernel

private theorem sp19628 : smallValid 19628 59 := by unfold smallValid; decide +kernel

private theorem sp19687 : smallValid 19687 58 := by unfold smallValid; decide +kernel

private theorem sp19745 : smallValid 19745 59 := by unfold smallValid; decide +kernel

private theorem sp19804 : smallValid 19804 58 := by unfold smallValid; decide +kernel

private theorem sp19862 : smallValid 19862 59 := by unfold smallValid; decide +kernel

private theorem sp19921 : smallValid 19921 58 := by unfold smallValid; decide +kernel

private theorem sp19979 : smallValid 19979 59 := by unfold smallValid; decide +kernel

private theorem sp20038 : smallValid 20038 59 := by unfold smallValid; decide +kernel

private theorem sp20097 : smallValid 20097 59 := by unfold smallValid; decide +kernel

private theorem sp20156 : smallValid 20156 58 := by unfold smallValid; decide +kernel

private theorem sp20214 : smallValid 20214 59 := by unfold smallValid; decide +kernel

private theorem sp20273 : smallValid 20273 58 := by unfold smallValid; decide +kernel

private theorem sp20331 : smallValid 20331 59 := by unfold smallValid; decide +kernel

private theorem sp20390 : smallValid 20390 58 := by unfold smallValid; decide +kernel

private theorem sp20448 : smallValid 20448 59 := by unfold smallValid; decide +kernel

private theorem sp20507 : smallValid 20507 59 := by unfold smallValid; decide +kernel

private theorem sp20566 : smallValid 20566 59 := by unfold smallValid; decide +kernel

private theorem sp20625 : smallValid 20625 58 := by unfold smallValid; decide +kernel

private theorem sp20683 : smallValid 20683 59 := by unfold smallValid; decide +kernel

private theorem sp20742 : smallValid 20742 58 := by unfold smallValid; decide +kernel

private theorem sp20800 : smallValid 20800 59 := by unfold smallValid; decide +kernel

private theorem sp20859 : smallValid 20859 58 := by unfold smallValid; decide +kernel

private theorem sp20917 : smallValid 20917 59 := by unfold smallValid; decide +kernel

private theorem sp20976 : smallValid 20976 58 := by unfold smallValid; decide +kernel

private theorem sp21034 : smallValid 21034 59 := by unfold smallValid; decide +kernel

private theorem sp21093 : smallValid 21093 58 := by unfold smallValid; decide +kernel

private theorem sp21151 : smallValid 21151 59 := by unfold smallValid; decide +kernel

private theorem sp21210 : smallValid 21210 58 := by unfold smallValid; decide +kernel

private theorem sp21268 : smallValid 21268 59 := by unfold smallValid; decide +kernel

private theorem sp21327 : smallValid 21327 58 := by unfold smallValid; decide +kernel

private theorem sp21385 : smallValid 21385 59 := by unfold smallValid; decide +kernel

private theorem sp21444 : smallValid 21444 59 := by unfold smallValid; decide +kernel

private theorem sp21503 : smallValid 21503 59 := by unfold smallValid; decide +kernel

private theorem sp21562 : smallValid 21562 58 := by unfold smallValid; decide +kernel

private theorem sp21620 : smallValid 21620 59 := by unfold smallValid; decide +kernel

private theorem sp21679 : smallValid 21679 58 := by unfold smallValid; decide +kernel

private theorem sp21737 : smallValid 21737 59 := by unfold smallValid; decide +kernel

private theorem sp21796 : smallValid 21796 58 := by unfold smallValid; decide +kernel

private theorem sp21854 : smallValid 21854 59 := by unfold smallValid; decide +kernel

private theorem sp21913 : smallValid 21913 59 := by unfold smallValid; decide +kernel

private theorem sp21972 : smallValid 21972 59 := by unfold smallValid; decide +kernel

private theorem sp22031 : smallValid 22031 58 := by unfold smallValid; decide +kernel

private theorem sp22089 : smallValid 22089 59 := by unfold smallValid; decide +kernel

private theorem sp22148 : smallValid 22148 58 := by unfold smallValid; decide +kernel

private theorem sp22206 : smallValid 22206 59 := by unfold smallValid; decide +kernel

private theorem sp22265 : smallValid 22265 58 := by unfold smallValid; decide +kernel

private theorem sp22323 : smallValid 22323 59 := by unfold smallValid; decide +kernel

private theorem sp22382 : smallValid 22382 59 := by unfold smallValid; decide +kernel

private theorem sp22441 : smallValid 22441 59 := by unfold smallValid; decide +kernel

private theorem sp22500 : smallValid 22500 58 := by unfold smallValid; decide +kernel

private theorem sp22558 : smallValid 22558 59 := by unfold smallValid; decide +kernel

private theorem sp22617 : smallValid 22617 58 := by unfold smallValid; decide +kernel

private theorem sp22675 : smallValid 22675 59 := by unfold smallValid; decide +kernel

private theorem sp22734 : smallValid 22734 58 := by unfold smallValid; decide +kernel

private theorem sp22792 : smallValid 22792 59 := by unfold smallValid; decide +kernel

private theorem sp22851 : smallValid 22851 58 := by unfold smallValid; decide +kernel

private theorem sp22909 : smallValid 22909 59 := by unfold smallValid; decide +kernel

private theorem sp22968 : smallValid 22968 58 := by unfold smallValid; decide +kernel

private theorem sp23026 : smallValid 23026 59 := by unfold smallValid; decide +kernel

private theorem sp23085 : smallValid 23085 58 := by unfold smallValid; decide +kernel

private theorem sp23143 : smallValid 23143 59 := by unfold smallValid; decide +kernel

private theorem sp23202 : smallValid 23202 58 := by unfold smallValid; decide +kernel

private theorem sp23260 : smallValid 23260 59 := by unfold smallValid; decide +kernel

private theorem sp23319 : smallValid 23319 59 := by unfold smallValid; decide +kernel

private theorem sp23378 : smallValid 23378 59 := by unfold smallValid; decide +kernel

private theorem sp23437 : smallValid 23437 58 := by unfold smallValid; decide +kernel

private theorem sp23495 : smallValid 23495 59 := by unfold smallValid; decide +kernel

private theorem sp23554 : smallValid 23554 58 := by unfold smallValid; decide +kernel

private theorem sp23612 : smallValid 23612 59 := by unfold smallValid; decide +kernel

private theorem sp23671 : smallValid 23671 58 := by unfold smallValid; decide +kernel

private theorem sp23729 : smallValid 23729 59 := by unfold smallValid; decide +kernel

private theorem sp23788 : smallValid 23788 59 := by unfold smallValid; decide +kernel

private theorem sp23847 : smallValid 23847 59 := by unfold smallValid; decide +kernel

private theorem sp23906 : smallValid 23906 58 := by unfold smallValid; decide +kernel

private theorem sp23964 : smallValid 23964 59 := by unfold smallValid; decide +kernel

private theorem sp24023 : smallValid 24023 58 := by unfold smallValid; decide +kernel

private theorem sp24081 : smallValid 24081 59 := by unfold smallValid; decide +kernel

private theorem sp24140 : smallValid 24140 58 := by unfold smallValid; decide +kernel

private theorem sp24198 : smallValid 24198 59 := by unfold smallValid; decide +kernel

private theorem sp24257 : smallValid 24257 59 := by unfold smallValid; decide +kernel

private theorem sp24316 : smallValid 24316 59 := by unfold smallValid; decide +kernel

private theorem sp24375 : smallValid 24375 58 := by unfold smallValid; decide +kernel

private theorem sp24433 : smallValid 24433 59 := by unfold smallValid; decide +kernel

private theorem sp24492 : smallValid 24492 58 := by unfold smallValid; decide +kernel

private theorem sp24550 : smallValid 24550 59 := by unfold smallValid; decide +kernel

private theorem sp24609 : smallValid 24609 58 := by unfold smallValid; decide +kernel

private theorem sp24667 : smallValid 24667 59 := by unfold smallValid; decide +kernel

private theorem sp24726 : smallValid 24726 58 := by unfold smallValid; decide +kernel

private theorem sp24784 : smallValid 24784 59 := by unfold smallValid; decide +kernel

private theorem sp24843 : smallValid 24843 58 := by unfold smallValid; decide +kernel

private theorem sp24901 : smallValid 24901 59 := by unfold smallValid; decide +kernel

private theorem sp24960 : smallValid 24960 58 := by unfold smallValid; decide +kernel

private theorem sp25018 : smallValid 25018 59 := by unfold smallValid; decide +kernel

private theorem sp25077 : smallValid 25077 58 := by unfold smallValid; decide +kernel

private theorem sp25135 : smallValid 25135 59 := by unfold smallValid; decide +kernel

private theorem sp25194 : smallValid 25194 59 := by unfold smallValid; decide +kernel

private theorem sp25253 : smallValid 25253 59 := by unfold smallValid; decide +kernel

private theorem sp25312 : smallValid 25312 58 := by unfold smallValid; decide +kernel

private theorem sp25370 : smallValid 25370 59 := by unfold smallValid; decide +kernel

private theorem sp25429 : smallValid 25429 58 := by unfold smallValid; decide +kernel

private theorem sp25487 : smallValid 25487 59 := by unfold smallValid; decide +kernel

private theorem sp25546 : smallValid 25546 58 := by unfold smallValid; decide +kernel

private theorem sp25604 : smallValid 25604 59 := by unfold smallValid; decide +kernel

private theorem sp25663 : smallValid 25663 59 := by unfold smallValid; decide +kernel

private theorem sp25722 : smallValid 25722 59 := by unfold smallValid; decide +kernel

private theorem sp25781 : smallValid 25781 58 := by unfold smallValid; decide +kernel

private theorem sp25839 : smallValid 25839 59 := by unfold smallValid; decide +kernel

private theorem sp25898 : smallValid 25898 58 := by unfold smallValid; decide +kernel

private theorem sp25956 : smallValid 25956 59 := by unfold smallValid; decide +kernel

private theorem sp26015 : smallValid 26015 58 := by unfold smallValid; decide +kernel

private theorem sp26073 : smallValid 26073 59 := by unfold smallValid; decide +kernel

private theorem sp26132 : smallValid 26132 59 := by unfold smallValid; decide +kernel

private theorem sp26191 : smallValid 26191 59 := by unfold smallValid; decide +kernel

private theorem sp26250 : smallValid 26250 58 := by unfold smallValid; decide +kernel

private theorem sp26308 : smallValid 26308 59 := by unfold smallValid; decide +kernel

private theorem sp26367 : smallValid 26367 58 := by unfold smallValid; decide +kernel

private theorem sp26425 : smallValid 26425 59 := by unfold smallValid; decide +kernel

private theorem sp26484 : smallValid 26484 58 := by unfold smallValid; decide +kernel

private theorem sp26542 : smallValid 26542 59 := by unfold smallValid; decide +kernel

private theorem sp26601 : smallValid 26601 58 := by unfold smallValid; decide +kernel

private theorem sp26659 : smallValid 26659 59 := by unfold smallValid; decide +kernel

private theorem sp26718 : smallValid 26718 58 := by unfold smallValid; decide +kernel

private theorem sp26776 : smallValid 26776 59 := by unfold smallValid; decide +kernel

private theorem sp26835 : smallValid 26835 58 := by unfold smallValid; decide +kernel

private theorem sp26893 : smallValid 26893 59 := by unfold smallValid; decide +kernel

private theorem sp26952 : smallValid 26952 58 := by unfold smallValid; decide +kernel

private theorem sp27010 : smallValid 27010 59 := by unfold smallValid; decide +kernel

private theorem sp27069 : smallValid 27069 59 := by unfold smallValid; decide +kernel

private theorem sp27128 : smallValid 27128 59 := by unfold smallValid; decide +kernel

private theorem sp27187 : smallValid 27187 58 := by unfold smallValid; decide +kernel

private theorem sp27245 : smallValid 27245 59 := by unfold smallValid; decide +kernel

private theorem sp27304 : smallValid 27304 58 := by unfold smallValid; decide +kernel

private theorem sp27362 : smallValid 27362 59 := by unfold smallValid; decide +kernel

private theorem sp27421 : smallValid 27421 58 := by unfold smallValid; decide +kernel

private theorem sp27479 : smallValid 27479 59 := by unfold smallValid; decide +kernel

private theorem sp27538 : smallValid 27538 59 := by unfold smallValid; decide +kernel

private theorem sp27597 : smallValid 27597 59 := by unfold smallValid; decide +kernel

private theorem sp27656 : smallValid 27656 58 := by unfold smallValid; decide +kernel

private theorem sp27714 : smallValid 27714 59 := by unfold smallValid; decide +kernel

private theorem sp27773 : smallValid 27773 58 := by unfold smallValid; decide +kernel

private theorem sp27831 : smallValid 27831 59 := by unfold smallValid; decide +kernel

private theorem sp27890 : smallValid 27890 58 := by unfold smallValid; decide +kernel

private theorem sp27948 : smallValid 27948 59 := by unfold smallValid; decide +kernel

private theorem sp28007 : smallValid 28007 59 := by unfold smallValid; decide +kernel

private theorem sp28066 : smallValid 28066 59 := by unfold smallValid; decide +kernel

private theorem sp28125 : smallValid 28125 58 := by unfold smallValid; decide +kernel

private theorem sp28183 : smallValid 28183 59 := by unfold smallValid; decide +kernel

private theorem sp28242 : smallValid 28242 58 := by unfold smallValid; decide +kernel

private theorem sp28300 : smallValid 28300 59 := by unfold smallValid; decide +kernel

private theorem sp28359 : smallValid 28359 58 := by unfold smallValid; decide +kernel

private theorem sp28417 : smallValid 28417 59 := by unfold smallValid; decide +kernel

private theorem sp28476 : smallValid 28476 59 := by unfold smallValid; decide +kernel

private theorem sp28535 : smallValid 28535 59 := by unfold smallValid; decide +kernel

private theorem sp28594 : smallValid 28594 58 := by unfold smallValid; decide +kernel

private theorem sp28652 : smallValid 28652 59 := by unfold smallValid; decide +kernel

private theorem sp28711 : smallValid 28711 58 := by unfold smallValid; decide +kernel

private theorem sp28769 : smallValid 28769 59 := by unfold smallValid; decide +kernel

private theorem sp28828 : smallValid 28828 58 := by unfold smallValid; decide +kernel

private theorem sp28886 : smallValid 28886 59 := by unfold smallValid; decide +kernel

private theorem sp28945 : smallValid 28945 59 := by unfold smallValid; decide +kernel

private theorem sp29004 : smallValid 29004 59 := by unfold smallValid; decide +kernel

private theorem sp29063 : smallValid 29063 58 := by unfold smallValid; decide +kernel

private theorem sp29121 : smallValid 29121 59 := by unfold smallValid; decide +kernel

private theorem sp29180 : smallValid 29180 58 := by unfold smallValid; decide +kernel

private theorem sp29238 : smallValid 29238 59 := by unfold smallValid; decide +kernel

private theorem sp29297 : smallValid 29297 58 := by unfold smallValid; decide +kernel

private theorem sp29355 : smallValid 29355 59 := by unfold smallValid; decide +kernel

private theorem sp29414 : smallValid 29414 59 := by unfold smallValid; decide +kernel

private theorem sp29473 : smallValid 29473 59 := by unfold smallValid; decide +kernel

private theorem sp29532 : smallValid 29532 58 := by unfold smallValid; decide +kernel

private theorem sp29590 : smallValid 29590 59 := by unfold smallValid; decide +kernel

private theorem sp29649 : smallValid 29649 58 := by unfold smallValid; decide +kernel

private theorem sp29707 : smallValid 29707 59 := by unfold smallValid; decide +kernel

private theorem sp29766 : smallValid 29766 58 := by unfold smallValid; decide +kernel

private theorem sp29824 : smallValid 29824 59 := by unfold smallValid; decide +kernel

private theorem sp29883 : smallValid 29883 59 := by unfold smallValid; decide +kernel

private theorem sp29942 : smallValid 29942 59 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤30000) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 30001 := (joinSmall (lo:=0) (a:=15000) (b:=15001) (joinSmall (lo:=0) (a:=7500) (b:=7500) (joinSmall (lo:=0) (a:=3750) (b:=3750) (joinSmall (lo:=0) (a:=1875) (b:=1875) (joinSmall (lo:=0) (a:=937) (b:=938) (joinSmall (lo:=0) (a:=468) (b:=469) (joinSmall (lo:=0) (a:=234) (b:=234) (joinSmall (lo:=0) (a:=117) (b:=117) (joinSmall (lo:=0) (a:=58) (b:=59) sp0 sp58) (joinSmall (lo:=117) (a:=58) (b:=59) sp117 sp175)) (joinSmall (lo:=234) (a:=117) (b:=117) (joinSmall (lo:=234) (a:=58) (b:=59) sp234 sp292) (joinSmall (lo:=351) (a:=58) (b:=59) sp351 sp409))) (joinSmall (lo:=468) (a:=234) (b:=235) (joinSmall (lo:=468) (a:=117) (b:=117) (joinSmall (lo:=468) (a:=58) (b:=59) sp468 sp526) (joinSmall (lo:=585) (a:=58) (b:=59) sp585 sp643)) (joinSmall (lo:=702) (a:=117) (b:=118) (joinSmall (lo:=702) (a:=58) (b:=59) sp702 sp760) (joinSmall (lo:=819) (a:=59) (b:=59) sp819 sp878)))) (joinSmall (lo:=937) (a:=469) (b:=469) (joinSmall (lo:=937) (a:=234) (b:=235) (joinSmall (lo:=937) (a:=117) (b:=117) (joinSmall (lo:=937) (a:=58) (b:=59) sp937 sp995) (joinSmall (lo:=1054) (a:=58) (b:=59) sp1054 sp1112)) (joinSmall (lo:=1171) (a:=117) (b:=118) (joinSmall (lo:=1171) (a:=58) (b:=59) sp1171 sp1229) (joinSmall (lo:=1288) (a:=59) (b:=59) sp1288 sp1347))) (joinSmall (lo:=1406) (a:=234) (b:=235) (joinSmall (lo:=1406) (a:=117) (b:=117) (joinSmall (lo:=1406) (a:=58) (b:=59) sp1406 sp1464) (joinSmall (lo:=1523) (a:=58) (b:=59) sp1523 sp1581)) (joinSmall (lo:=1640) (a:=117) (b:=118) (joinSmall (lo:=1640) (a:=58) (b:=59) sp1640 sp1698) (joinSmall (lo:=1757) (a:=59) (b:=59) sp1757 sp1816))))) (joinSmall (lo:=1875) (a:=937) (b:=938) (joinSmall (lo:=1875) (a:=468) (b:=469) (joinSmall (lo:=1875) (a:=234) (b:=234) (joinSmall (lo:=1875) (a:=117) (b:=117) (joinSmall (lo:=1875) (a:=58) (b:=59) sp1875 sp1933) (joinSmall (lo:=1992) (a:=58) (b:=59) sp1992 sp2050)) (joinSmall (lo:=2109) (a:=117) (b:=117) (joinSmall (lo:=2109) (a:=58) (b:=59) sp2109 sp2167) (joinSmall (lo:=2226) (a:=58) (b:=59) sp2226 sp2284))) (joinSmall (lo:=2343) (a:=234) (b:=235) (joinSmall (lo:=2343) (a:=117) (b:=117) (joinSmall (lo:=2343) (a:=58) (b:=59) sp2343 sp2401) (joinSmall (lo:=2460) (a:=58) (b:=59) sp2460 sp2518)) (joinSmall (lo:=2577) (a:=117) (b:=118) (joinSmall (lo:=2577) (a:=58) (b:=59) sp2577 sp2635) (joinSmall (lo:=2694) (a:=59) (b:=59) sp2694 sp2753)))) (joinSmall (lo:=2812) (a:=469) (b:=469) (joinSmall (lo:=2812) (a:=234) (b:=235) (joinSmall (lo:=2812) (a:=117) (b:=117) (joinSmall (lo:=2812) (a:=58) (b:=59) sp2812 sp2870) (joinSmall (lo:=2929) (a:=58) (b:=59) sp2929 sp2987)) (joinSmall (lo:=3046) (a:=117) (b:=118) (joinSmall (lo:=3046) (a:=58) (b:=59) sp3046 sp3104) (joinSmall (lo:=3163) (a:=59) (b:=59) sp3163 sp3222))) (joinSmall (lo:=3281) (a:=234) (b:=235) (joinSmall (lo:=3281) (a:=117) (b:=117) (joinSmall (lo:=3281) (a:=58) (b:=59) sp3281 sp3339) (joinSmall (lo:=3398) (a:=58) (b:=59) sp3398 sp3456)) (joinSmall (lo:=3515) (a:=117) (b:=118) (joinSmall (lo:=3515) (a:=58) (b:=59) sp3515 sp3573) (joinSmall (lo:=3632) (a:=59) (b:=59) sp3632 sp3691)))))) (joinSmall (lo:=3750) (a:=1875) (b:=1875) (joinSmall (lo:=3750) (a:=937) (b:=938) (joinSmall (lo:=3750) (a:=468) (b:=469) (joinSmall (lo:=3750) (a:=234) (b:=234) (joinSmall (lo:=3750) (a:=117) (b:=117) (joinSmall (lo:=3750) (a:=58) (b:=59) sp3750 sp3808) (joinSmall (lo:=3867) (a:=58) (b:=59) sp3867 sp3925)) (joinSmall (lo:=3984) (a:=117) (b:=117) (joinSmall (lo:=3984) (a:=58) (b:=59) sp3984 sp4042) (joinSmall (lo:=4101) (a:=58) (b:=59) sp4101 sp4159))) (joinSmall (lo:=4218) (a:=234) (b:=235) (joinSmall (lo:=4218) (a:=117) (b:=117) (joinSmall (lo:=4218) (a:=58) (b:=59) sp4218 sp4276) (joinSmall (lo:=4335) (a:=58) (b:=59) sp4335 sp4393)) (joinSmall (lo:=4452) (a:=117) (b:=118) (joinSmall (lo:=4452) (a:=58) (b:=59) sp4452 sp4510) (joinSmall (lo:=4569) (a:=59) (b:=59) sp4569 sp4628)))) (joinSmall (lo:=4687) (a:=469) (b:=469) (joinSmall (lo:=4687) (a:=234) (b:=235) (joinSmall (lo:=4687) (a:=117) (b:=117) (joinSmall (lo:=4687) (a:=58) (b:=59) sp4687 sp4745) (joinSmall (lo:=4804) (a:=58) (b:=59) sp4804 sp4862)) (joinSmall (lo:=4921) (a:=117) (b:=118) (joinSmall (lo:=4921) (a:=58) (b:=59) sp4921 sp4979) (joinSmall (lo:=5038) (a:=59) (b:=59) sp5038 sp5097))) (joinSmall (lo:=5156) (a:=234) (b:=235) (joinSmall (lo:=5156) (a:=117) (b:=117) (joinSmall (lo:=5156) (a:=58) (b:=59) sp5156 sp5214) (joinSmall (lo:=5273) (a:=58) (b:=59) sp5273 sp5331)) (joinSmall (lo:=5390) (a:=117) (b:=118) (joinSmall (lo:=5390) (a:=58) (b:=59) sp5390 sp5448) (joinSmall (lo:=5507) (a:=59) (b:=59) sp5507 sp5566))))) (joinSmall (lo:=5625) (a:=937) (b:=938) (joinSmall (lo:=5625) (a:=468) (b:=469) (joinSmall (lo:=5625) (a:=234) (b:=234) (joinSmall (lo:=5625) (a:=117) (b:=117) (joinSmall (lo:=5625) (a:=58) (b:=59) sp5625 sp5683) (joinSmall (lo:=5742) (a:=58) (b:=59) sp5742 sp5800)) (joinSmall (lo:=5859) (a:=117) (b:=117) (joinSmall (lo:=5859) (a:=58) (b:=59) sp5859 sp5917) (joinSmall (lo:=5976) (a:=58) (b:=59) sp5976 sp6034))) (joinSmall (lo:=6093) (a:=234) (b:=235) (joinSmall (lo:=6093) (a:=117) (b:=117) (joinSmall (lo:=6093) (a:=58) (b:=59) sp6093 sp6151) (joinSmall (lo:=6210) (a:=58) (b:=59) sp6210 sp6268)) (joinSmall (lo:=6327) (a:=117) (b:=118) (joinSmall (lo:=6327) (a:=58) (b:=59) sp6327 sp6385) (joinSmall (lo:=6444) (a:=59) (b:=59) sp6444 sp6503)))) (joinSmall (lo:=6562) (a:=469) (b:=469) (joinSmall (lo:=6562) (a:=234) (b:=235) (joinSmall (lo:=6562) (a:=117) (b:=117) (joinSmall (lo:=6562) (a:=58) (b:=59) sp6562 sp6620) (joinSmall (lo:=6679) (a:=58) (b:=59) sp6679 sp6737)) (joinSmall (lo:=6796) (a:=117) (b:=118) (joinSmall (lo:=6796) (a:=58) (b:=59) sp6796 sp6854) (joinSmall (lo:=6913) (a:=59) (b:=59) sp6913 sp6972))) (joinSmall (lo:=7031) (a:=234) (b:=235) (joinSmall (lo:=7031) (a:=117) (b:=117) (joinSmall (lo:=7031) (a:=58) (b:=59) sp7031 sp7089) (joinSmall (lo:=7148) (a:=58) (b:=59) sp7148 sp7206)) (joinSmall (lo:=7265) (a:=117) (b:=118) (joinSmall (lo:=7265) (a:=58) (b:=59) sp7265 sp7323) (joinSmall (lo:=7382) (a:=59) (b:=59) sp7382 sp7441))))))) (joinSmall (lo:=7500) (a:=3750) (b:=3750) (joinSmall (lo:=7500) (a:=1875) (b:=1875) (joinSmall (lo:=7500) (a:=937) (b:=938) (joinSmall (lo:=7500) (a:=468) (b:=469) (joinSmall (lo:=7500) (a:=234) (b:=234) (joinSmall (lo:=7500) (a:=117) (b:=117) (joinSmall (lo:=7500) (a:=58) (b:=59) sp7500 sp7558) (joinSmall (lo:=7617) (a:=58) (b:=59) sp7617 sp7675)) (joinSmall (lo:=7734) (a:=117) (b:=117) (joinSmall (lo:=7734) (a:=58) (b:=59) sp7734 sp7792) (joinSmall (lo:=7851) (a:=58) (b:=59) sp7851 sp7909))) (joinSmall (lo:=7968) (a:=234) (b:=235) (joinSmall (lo:=7968) (a:=117) (b:=117) (joinSmall (lo:=7968) (a:=58) (b:=59) sp7968 sp8026) (joinSmall (lo:=8085) (a:=58) (b:=59) sp8085 sp8143)) (joinSmall (lo:=8202) (a:=117) (b:=118) (joinSmall (lo:=8202) (a:=58) (b:=59) sp8202 sp8260) (joinSmall (lo:=8319) (a:=59) (b:=59) sp8319 sp8378)))) (joinSmall (lo:=8437) (a:=469) (b:=469) (joinSmall (lo:=8437) (a:=234) (b:=235) (joinSmall (lo:=8437) (a:=117) (b:=117) (joinSmall (lo:=8437) (a:=58) (b:=59) sp8437 sp8495) (joinSmall (lo:=8554) (a:=58) (b:=59) sp8554 sp8612)) (joinSmall (lo:=8671) (a:=117) (b:=118) (joinSmall (lo:=8671) (a:=58) (b:=59) sp8671 sp8729) (joinSmall (lo:=8788) (a:=59) (b:=59) sp8788 sp8847))) (joinSmall (lo:=8906) (a:=234) (b:=235) (joinSmall (lo:=8906) (a:=117) (b:=117) (joinSmall (lo:=8906) (a:=58) (b:=59) sp8906 sp8964) (joinSmall (lo:=9023) (a:=58) (b:=59) sp9023 sp9081)) (joinSmall (lo:=9140) (a:=117) (b:=118) (joinSmall (lo:=9140) (a:=58) (b:=59) sp9140 sp9198) (joinSmall (lo:=9257) (a:=59) (b:=59) sp9257 sp9316))))) (joinSmall (lo:=9375) (a:=937) (b:=938) (joinSmall (lo:=9375) (a:=468) (b:=469) (joinSmall (lo:=9375) (a:=234) (b:=234) (joinSmall (lo:=9375) (a:=117) (b:=117) (joinSmall (lo:=9375) (a:=58) (b:=59) sp9375 sp9433) (joinSmall (lo:=9492) (a:=58) (b:=59) sp9492 sp9550)) (joinSmall (lo:=9609) (a:=117) (b:=117) (joinSmall (lo:=9609) (a:=58) (b:=59) sp9609 sp9667) (joinSmall (lo:=9726) (a:=58) (b:=59) sp9726 sp9784))) (joinSmall (lo:=9843) (a:=234) (b:=235) (joinSmall (lo:=9843) (a:=117) (b:=117) (joinSmall (lo:=9843) (a:=58) (b:=59) sp9843 sp9901) (joinSmall (lo:=9960) (a:=58) (b:=59) sp9960 sp10018)) (joinSmall (lo:=10077) (a:=117) (b:=118) (joinSmall (lo:=10077) (a:=58) (b:=59) sp10077 sp10135) (joinSmall (lo:=10194) (a:=59) (b:=59) sp10194 sp10253)))) (joinSmall (lo:=10312) (a:=469) (b:=469) (joinSmall (lo:=10312) (a:=234) (b:=235) (joinSmall (lo:=10312) (a:=117) (b:=117) (joinSmall (lo:=10312) (a:=58) (b:=59) sp10312 sp10370) (joinSmall (lo:=10429) (a:=58) (b:=59) sp10429 sp10487)) (joinSmall (lo:=10546) (a:=117) (b:=118) (joinSmall (lo:=10546) (a:=58) (b:=59) sp10546 sp10604) (joinSmall (lo:=10663) (a:=59) (b:=59) sp10663 sp10722))) (joinSmall (lo:=10781) (a:=234) (b:=235) (joinSmall (lo:=10781) (a:=117) (b:=117) (joinSmall (lo:=10781) (a:=58) (b:=59) sp10781 sp10839) (joinSmall (lo:=10898) (a:=58) (b:=59) sp10898 sp10956)) (joinSmall (lo:=11015) (a:=117) (b:=118) (joinSmall (lo:=11015) (a:=58) (b:=59) sp11015 sp11073) (joinSmall (lo:=11132) (a:=59) (b:=59) sp11132 sp11191)))))) (joinSmall (lo:=11250) (a:=1875) (b:=1875) (joinSmall (lo:=11250) (a:=937) (b:=938) (joinSmall (lo:=11250) (a:=468) (b:=469) (joinSmall (lo:=11250) (a:=234) (b:=234) (joinSmall (lo:=11250) (a:=117) (b:=117) (joinSmall (lo:=11250) (a:=58) (b:=59) sp11250 sp11308) (joinSmall (lo:=11367) (a:=58) (b:=59) sp11367 sp11425)) (joinSmall (lo:=11484) (a:=117) (b:=117) (joinSmall (lo:=11484) (a:=58) (b:=59) sp11484 sp11542) (joinSmall (lo:=11601) (a:=58) (b:=59) sp11601 sp11659))) (joinSmall (lo:=11718) (a:=234) (b:=235) (joinSmall (lo:=11718) (a:=117) (b:=117) (joinSmall (lo:=11718) (a:=58) (b:=59) sp11718 sp11776) (joinSmall (lo:=11835) (a:=58) (b:=59) sp11835 sp11893)) (joinSmall (lo:=11952) (a:=117) (b:=118) (joinSmall (lo:=11952) (a:=58) (b:=59) sp11952 sp12010) (joinSmall (lo:=12069) (a:=59) (b:=59) sp12069 sp12128)))) (joinSmall (lo:=12187) (a:=469) (b:=469) (joinSmall (lo:=12187) (a:=234) (b:=235) (joinSmall (lo:=12187) (a:=117) (b:=117) (joinSmall (lo:=12187) (a:=58) (b:=59) sp12187 sp12245) (joinSmall (lo:=12304) (a:=58) (b:=59) sp12304 sp12362)) (joinSmall (lo:=12421) (a:=117) (b:=118) (joinSmall (lo:=12421) (a:=58) (b:=59) sp12421 sp12479) (joinSmall (lo:=12538) (a:=59) (b:=59) sp12538 sp12597))) (joinSmall (lo:=12656) (a:=234) (b:=235) (joinSmall (lo:=12656) (a:=117) (b:=117) (joinSmall (lo:=12656) (a:=58) (b:=59) sp12656 sp12714) (joinSmall (lo:=12773) (a:=58) (b:=59) sp12773 sp12831)) (joinSmall (lo:=12890) (a:=117) (b:=118) (joinSmall (lo:=12890) (a:=58) (b:=59) sp12890 sp12948) (joinSmall (lo:=13007) (a:=59) (b:=59) sp13007 sp13066))))) (joinSmall (lo:=13125) (a:=937) (b:=938) (joinSmall (lo:=13125) (a:=468) (b:=469) (joinSmall (lo:=13125) (a:=234) (b:=234) (joinSmall (lo:=13125) (a:=117) (b:=117) (joinSmall (lo:=13125) (a:=58) (b:=59) sp13125 sp13183) (joinSmall (lo:=13242) (a:=58) (b:=59) sp13242 sp13300)) (joinSmall (lo:=13359) (a:=117) (b:=117) (joinSmall (lo:=13359) (a:=58) (b:=59) sp13359 sp13417) (joinSmall (lo:=13476) (a:=58) (b:=59) sp13476 sp13534))) (joinSmall (lo:=13593) (a:=234) (b:=235) (joinSmall (lo:=13593) (a:=117) (b:=117) (joinSmall (lo:=13593) (a:=58) (b:=59) sp13593 sp13651) (joinSmall (lo:=13710) (a:=58) (b:=59) sp13710 sp13768)) (joinSmall (lo:=13827) (a:=117) (b:=118) (joinSmall (lo:=13827) (a:=58) (b:=59) sp13827 sp13885) (joinSmall (lo:=13944) (a:=59) (b:=59) sp13944 sp14003)))) (joinSmall (lo:=14062) (a:=469) (b:=469) (joinSmall (lo:=14062) (a:=234) (b:=235) (joinSmall (lo:=14062) (a:=117) (b:=117) (joinSmall (lo:=14062) (a:=58) (b:=59) sp14062 sp14120) (joinSmall (lo:=14179) (a:=58) (b:=59) sp14179 sp14237)) (joinSmall (lo:=14296) (a:=117) (b:=118) (joinSmall (lo:=14296) (a:=58) (b:=59) sp14296 sp14354) (joinSmall (lo:=14413) (a:=59) (b:=59) sp14413 sp14472))) (joinSmall (lo:=14531) (a:=234) (b:=235) (joinSmall (lo:=14531) (a:=117) (b:=117) (joinSmall (lo:=14531) (a:=58) (b:=59) sp14531 sp14589) (joinSmall (lo:=14648) (a:=58) (b:=59) sp14648 sp14706)) (joinSmall (lo:=14765) (a:=117) (b:=118) (joinSmall (lo:=14765) (a:=58) (b:=59) sp14765 sp14823) (joinSmall (lo:=14882) (a:=59) (b:=59) sp14882 sp14941)))))))) (joinSmall (lo:=15000) (a:=7500) (b:=7501) (joinSmall (lo:=15000) (a:=3750) (b:=3750) (joinSmall (lo:=15000) (a:=1875) (b:=1875) (joinSmall (lo:=15000) (a:=937) (b:=938) (joinSmall (lo:=15000) (a:=468) (b:=469) (joinSmall (lo:=15000) (a:=234) (b:=234) (joinSmall (lo:=15000) (a:=117) (b:=117) (joinSmall (lo:=15000) (a:=58) (b:=59) sp15000 sp15058) (joinSmall (lo:=15117) (a:=58) (b:=59) sp15117 sp15175)) (joinSmall (lo:=15234) (a:=117) (b:=117) (joinSmall (lo:=15234) (a:=58) (b:=59) sp15234 sp15292) (joinSmall (lo:=15351) (a:=58) (b:=59) sp15351 sp15409))) (joinSmall (lo:=15468) (a:=234) (b:=235) (joinSmall (lo:=15468) (a:=117) (b:=117) (joinSmall (lo:=15468) (a:=58) (b:=59) sp15468 sp15526) (joinSmall (lo:=15585) (a:=58) (b:=59) sp15585 sp15643)) (joinSmall (lo:=15702) (a:=117) (b:=118) (joinSmall (lo:=15702) (a:=58) (b:=59) sp15702 sp15760) (joinSmall (lo:=15819) (a:=59) (b:=59) sp15819 sp15878)))) (joinSmall (lo:=15937) (a:=469) (b:=469) (joinSmall (lo:=15937) (a:=234) (b:=235) (joinSmall (lo:=15937) (a:=117) (b:=117) (joinSmall (lo:=15937) (a:=58) (b:=59) sp15937 sp15995) (joinSmall (lo:=16054) (a:=58) (b:=59) sp16054 sp16112)) (joinSmall (lo:=16171) (a:=117) (b:=118) (joinSmall (lo:=16171) (a:=58) (b:=59) sp16171 sp16229) (joinSmall (lo:=16288) (a:=59) (b:=59) sp16288 sp16347))) (joinSmall (lo:=16406) (a:=234) (b:=235) (joinSmall (lo:=16406) (a:=117) (b:=117) (joinSmall (lo:=16406) (a:=58) (b:=59) sp16406 sp16464) (joinSmall (lo:=16523) (a:=58) (b:=59) sp16523 sp16581)) (joinSmall (lo:=16640) (a:=117) (b:=118) (joinSmall (lo:=16640) (a:=58) (b:=59) sp16640 sp16698) (joinSmall (lo:=16757) (a:=59) (b:=59) sp16757 sp16816))))) (joinSmall (lo:=16875) (a:=937) (b:=938) (joinSmall (lo:=16875) (a:=468) (b:=469) (joinSmall (lo:=16875) (a:=234) (b:=234) (joinSmall (lo:=16875) (a:=117) (b:=117) (joinSmall (lo:=16875) (a:=58) (b:=59) sp16875 sp16933) (joinSmall (lo:=16992) (a:=58) (b:=59) sp16992 sp17050)) (joinSmall (lo:=17109) (a:=117) (b:=117) (joinSmall (lo:=17109) (a:=58) (b:=59) sp17109 sp17167) (joinSmall (lo:=17226) (a:=58) (b:=59) sp17226 sp17284))) (joinSmall (lo:=17343) (a:=234) (b:=235) (joinSmall (lo:=17343) (a:=117) (b:=117) (joinSmall (lo:=17343) (a:=58) (b:=59) sp17343 sp17401) (joinSmall (lo:=17460) (a:=58) (b:=59) sp17460 sp17518)) (joinSmall (lo:=17577) (a:=117) (b:=118) (joinSmall (lo:=17577) (a:=58) (b:=59) sp17577 sp17635) (joinSmall (lo:=17694) (a:=59) (b:=59) sp17694 sp17753)))) (joinSmall (lo:=17812) (a:=469) (b:=469) (joinSmall (lo:=17812) (a:=234) (b:=235) (joinSmall (lo:=17812) (a:=117) (b:=117) (joinSmall (lo:=17812) (a:=58) (b:=59) sp17812 sp17870) (joinSmall (lo:=17929) (a:=58) (b:=59) sp17929 sp17987)) (joinSmall (lo:=18046) (a:=117) (b:=118) (joinSmall (lo:=18046) (a:=58) (b:=59) sp18046 sp18104) (joinSmall (lo:=18163) (a:=59) (b:=59) sp18163 sp18222))) (joinSmall (lo:=18281) (a:=234) (b:=235) (joinSmall (lo:=18281) (a:=117) (b:=117) (joinSmall (lo:=18281) (a:=58) (b:=59) sp18281 sp18339) (joinSmall (lo:=18398) (a:=58) (b:=59) sp18398 sp18456)) (joinSmall (lo:=18515) (a:=117) (b:=118) (joinSmall (lo:=18515) (a:=58) (b:=59) sp18515 sp18573) (joinSmall (lo:=18632) (a:=59) (b:=59) sp18632 sp18691)))))) (joinSmall (lo:=18750) (a:=1875) (b:=1875) (joinSmall (lo:=18750) (a:=937) (b:=938) (joinSmall (lo:=18750) (a:=468) (b:=469) (joinSmall (lo:=18750) (a:=234) (b:=234) (joinSmall (lo:=18750) (a:=117) (b:=117) (joinSmall (lo:=18750) (a:=58) (b:=59) sp18750 sp18808) (joinSmall (lo:=18867) (a:=58) (b:=59) sp18867 sp18925)) (joinSmall (lo:=18984) (a:=117) (b:=117) (joinSmall (lo:=18984) (a:=58) (b:=59) sp18984 sp19042) (joinSmall (lo:=19101) (a:=58) (b:=59) sp19101 sp19159))) (joinSmall (lo:=19218) (a:=234) (b:=235) (joinSmall (lo:=19218) (a:=117) (b:=117) (joinSmall (lo:=19218) (a:=58) (b:=59) sp19218 sp19276) (joinSmall (lo:=19335) (a:=58) (b:=59) sp19335 sp19393)) (joinSmall (lo:=19452) (a:=117) (b:=118) (joinSmall (lo:=19452) (a:=58) (b:=59) sp19452 sp19510) (joinSmall (lo:=19569) (a:=59) (b:=59) sp19569 sp19628)))) (joinSmall (lo:=19687) (a:=469) (b:=469) (joinSmall (lo:=19687) (a:=234) (b:=235) (joinSmall (lo:=19687) (a:=117) (b:=117) (joinSmall (lo:=19687) (a:=58) (b:=59) sp19687 sp19745) (joinSmall (lo:=19804) (a:=58) (b:=59) sp19804 sp19862)) (joinSmall (lo:=19921) (a:=117) (b:=118) (joinSmall (lo:=19921) (a:=58) (b:=59) sp19921 sp19979) (joinSmall (lo:=20038) (a:=59) (b:=59) sp20038 sp20097))) (joinSmall (lo:=20156) (a:=234) (b:=235) (joinSmall (lo:=20156) (a:=117) (b:=117) (joinSmall (lo:=20156) (a:=58) (b:=59) sp20156 sp20214) (joinSmall (lo:=20273) (a:=58) (b:=59) sp20273 sp20331)) (joinSmall (lo:=20390) (a:=117) (b:=118) (joinSmall (lo:=20390) (a:=58) (b:=59) sp20390 sp20448) (joinSmall (lo:=20507) (a:=59) (b:=59) sp20507 sp20566))))) (joinSmall (lo:=20625) (a:=937) (b:=938) (joinSmall (lo:=20625) (a:=468) (b:=469) (joinSmall (lo:=20625) (a:=234) (b:=234) (joinSmall (lo:=20625) (a:=117) (b:=117) (joinSmall (lo:=20625) (a:=58) (b:=59) sp20625 sp20683) (joinSmall (lo:=20742) (a:=58) (b:=59) sp20742 sp20800)) (joinSmall (lo:=20859) (a:=117) (b:=117) (joinSmall (lo:=20859) (a:=58) (b:=59) sp20859 sp20917) (joinSmall (lo:=20976) (a:=58) (b:=59) sp20976 sp21034))) (joinSmall (lo:=21093) (a:=234) (b:=235) (joinSmall (lo:=21093) (a:=117) (b:=117) (joinSmall (lo:=21093) (a:=58) (b:=59) sp21093 sp21151) (joinSmall (lo:=21210) (a:=58) (b:=59) sp21210 sp21268)) (joinSmall (lo:=21327) (a:=117) (b:=118) (joinSmall (lo:=21327) (a:=58) (b:=59) sp21327 sp21385) (joinSmall (lo:=21444) (a:=59) (b:=59) sp21444 sp21503)))) (joinSmall (lo:=21562) (a:=469) (b:=469) (joinSmall (lo:=21562) (a:=234) (b:=235) (joinSmall (lo:=21562) (a:=117) (b:=117) (joinSmall (lo:=21562) (a:=58) (b:=59) sp21562 sp21620) (joinSmall (lo:=21679) (a:=58) (b:=59) sp21679 sp21737)) (joinSmall (lo:=21796) (a:=117) (b:=118) (joinSmall (lo:=21796) (a:=58) (b:=59) sp21796 sp21854) (joinSmall (lo:=21913) (a:=59) (b:=59) sp21913 sp21972))) (joinSmall (lo:=22031) (a:=234) (b:=235) (joinSmall (lo:=22031) (a:=117) (b:=117) (joinSmall (lo:=22031) (a:=58) (b:=59) sp22031 sp22089) (joinSmall (lo:=22148) (a:=58) (b:=59) sp22148 sp22206)) (joinSmall (lo:=22265) (a:=117) (b:=118) (joinSmall (lo:=22265) (a:=58) (b:=59) sp22265 sp22323) (joinSmall (lo:=22382) (a:=59) (b:=59) sp22382 sp22441))))))) (joinSmall (lo:=22500) (a:=3750) (b:=3751) (joinSmall (lo:=22500) (a:=1875) (b:=1875) (joinSmall (lo:=22500) (a:=937) (b:=938) (joinSmall (lo:=22500) (a:=468) (b:=469) (joinSmall (lo:=22500) (a:=234) (b:=234) (joinSmall (lo:=22500) (a:=117) (b:=117) (joinSmall (lo:=22500) (a:=58) (b:=59) sp22500 sp22558) (joinSmall (lo:=22617) (a:=58) (b:=59) sp22617 sp22675)) (joinSmall (lo:=22734) (a:=117) (b:=117) (joinSmall (lo:=22734) (a:=58) (b:=59) sp22734 sp22792) (joinSmall (lo:=22851) (a:=58) (b:=59) sp22851 sp22909))) (joinSmall (lo:=22968) (a:=234) (b:=235) (joinSmall (lo:=22968) (a:=117) (b:=117) (joinSmall (lo:=22968) (a:=58) (b:=59) sp22968 sp23026) (joinSmall (lo:=23085) (a:=58) (b:=59) sp23085 sp23143)) (joinSmall (lo:=23202) (a:=117) (b:=118) (joinSmall (lo:=23202) (a:=58) (b:=59) sp23202 sp23260) (joinSmall (lo:=23319) (a:=59) (b:=59) sp23319 sp23378)))) (joinSmall (lo:=23437) (a:=469) (b:=469) (joinSmall (lo:=23437) (a:=234) (b:=235) (joinSmall (lo:=23437) (a:=117) (b:=117) (joinSmall (lo:=23437) (a:=58) (b:=59) sp23437 sp23495) (joinSmall (lo:=23554) (a:=58) (b:=59) sp23554 sp23612)) (joinSmall (lo:=23671) (a:=117) (b:=118) (joinSmall (lo:=23671) (a:=58) (b:=59) sp23671 sp23729) (joinSmall (lo:=23788) (a:=59) (b:=59) sp23788 sp23847))) (joinSmall (lo:=23906) (a:=234) (b:=235) (joinSmall (lo:=23906) (a:=117) (b:=117) (joinSmall (lo:=23906) (a:=58) (b:=59) sp23906 sp23964) (joinSmall (lo:=24023) (a:=58) (b:=59) sp24023 sp24081)) (joinSmall (lo:=24140) (a:=117) (b:=118) (joinSmall (lo:=24140) (a:=58) (b:=59) sp24140 sp24198) (joinSmall (lo:=24257) (a:=59) (b:=59) sp24257 sp24316))))) (joinSmall (lo:=24375) (a:=937) (b:=938) (joinSmall (lo:=24375) (a:=468) (b:=469) (joinSmall (lo:=24375) (a:=234) (b:=234) (joinSmall (lo:=24375) (a:=117) (b:=117) (joinSmall (lo:=24375) (a:=58) (b:=59) sp24375 sp24433) (joinSmall (lo:=24492) (a:=58) (b:=59) sp24492 sp24550)) (joinSmall (lo:=24609) (a:=117) (b:=117) (joinSmall (lo:=24609) (a:=58) (b:=59) sp24609 sp24667) (joinSmall (lo:=24726) (a:=58) (b:=59) sp24726 sp24784))) (joinSmall (lo:=24843) (a:=234) (b:=235) (joinSmall (lo:=24843) (a:=117) (b:=117) (joinSmall (lo:=24843) (a:=58) (b:=59) sp24843 sp24901) (joinSmall (lo:=24960) (a:=58) (b:=59) sp24960 sp25018)) (joinSmall (lo:=25077) (a:=117) (b:=118) (joinSmall (lo:=25077) (a:=58) (b:=59) sp25077 sp25135) (joinSmall (lo:=25194) (a:=59) (b:=59) sp25194 sp25253)))) (joinSmall (lo:=25312) (a:=469) (b:=469) (joinSmall (lo:=25312) (a:=234) (b:=235) (joinSmall (lo:=25312) (a:=117) (b:=117) (joinSmall (lo:=25312) (a:=58) (b:=59) sp25312 sp25370) (joinSmall (lo:=25429) (a:=58) (b:=59) sp25429 sp25487)) (joinSmall (lo:=25546) (a:=117) (b:=118) (joinSmall (lo:=25546) (a:=58) (b:=59) sp25546 sp25604) (joinSmall (lo:=25663) (a:=59) (b:=59) sp25663 sp25722))) (joinSmall (lo:=25781) (a:=234) (b:=235) (joinSmall (lo:=25781) (a:=117) (b:=117) (joinSmall (lo:=25781) (a:=58) (b:=59) sp25781 sp25839) (joinSmall (lo:=25898) (a:=58) (b:=59) sp25898 sp25956)) (joinSmall (lo:=26015) (a:=117) (b:=118) (joinSmall (lo:=26015) (a:=58) (b:=59) sp26015 sp26073) (joinSmall (lo:=26132) (a:=59) (b:=59) sp26132 sp26191)))))) (joinSmall (lo:=26250) (a:=1875) (b:=1876) (joinSmall (lo:=26250) (a:=937) (b:=938) (joinSmall (lo:=26250) (a:=468) (b:=469) (joinSmall (lo:=26250) (a:=234) (b:=234) (joinSmall (lo:=26250) (a:=117) (b:=117) (joinSmall (lo:=26250) (a:=58) (b:=59) sp26250 sp26308) (joinSmall (lo:=26367) (a:=58) (b:=59) sp26367 sp26425)) (joinSmall (lo:=26484) (a:=117) (b:=117) (joinSmall (lo:=26484) (a:=58) (b:=59) sp26484 sp26542) (joinSmall (lo:=26601) (a:=58) (b:=59) sp26601 sp26659))) (joinSmall (lo:=26718) (a:=234) (b:=235) (joinSmall (lo:=26718) (a:=117) (b:=117) (joinSmall (lo:=26718) (a:=58) (b:=59) sp26718 sp26776) (joinSmall (lo:=26835) (a:=58) (b:=59) sp26835 sp26893)) (joinSmall (lo:=26952) (a:=117) (b:=118) (joinSmall (lo:=26952) (a:=58) (b:=59) sp26952 sp27010) (joinSmall (lo:=27069) (a:=59) (b:=59) sp27069 sp27128)))) (joinSmall (lo:=27187) (a:=469) (b:=469) (joinSmall (lo:=27187) (a:=234) (b:=235) (joinSmall (lo:=27187) (a:=117) (b:=117) (joinSmall (lo:=27187) (a:=58) (b:=59) sp27187 sp27245) (joinSmall (lo:=27304) (a:=58) (b:=59) sp27304 sp27362)) (joinSmall (lo:=27421) (a:=117) (b:=118) (joinSmall (lo:=27421) (a:=58) (b:=59) sp27421 sp27479) (joinSmall (lo:=27538) (a:=59) (b:=59) sp27538 sp27597))) (joinSmall (lo:=27656) (a:=234) (b:=235) (joinSmall (lo:=27656) (a:=117) (b:=117) (joinSmall (lo:=27656) (a:=58) (b:=59) sp27656 sp27714) (joinSmall (lo:=27773) (a:=58) (b:=59) sp27773 sp27831)) (joinSmall (lo:=27890) (a:=117) (b:=118) (joinSmall (lo:=27890) (a:=58) (b:=59) sp27890 sp27948) (joinSmall (lo:=28007) (a:=59) (b:=59) sp28007 sp28066))))) (joinSmall (lo:=28125) (a:=938) (b:=938) (joinSmall (lo:=28125) (a:=469) (b:=469) (joinSmall (lo:=28125) (a:=234) (b:=235) (joinSmall (lo:=28125) (a:=117) (b:=117) (joinSmall (lo:=28125) (a:=58) (b:=59) sp28125 sp28183) (joinSmall (lo:=28242) (a:=58) (b:=59) sp28242 sp28300)) (joinSmall (lo:=28359) (a:=117) (b:=118) (joinSmall (lo:=28359) (a:=58) (b:=59) sp28359 sp28417) (joinSmall (lo:=28476) (a:=59) (b:=59) sp28476 sp28535))) (joinSmall (lo:=28594) (a:=234) (b:=235) (joinSmall (lo:=28594) (a:=117) (b:=117) (joinSmall (lo:=28594) (a:=58) (b:=59) sp28594 sp28652) (joinSmall (lo:=28711) (a:=58) (b:=59) sp28711 sp28769)) (joinSmall (lo:=28828) (a:=117) (b:=118) (joinSmall (lo:=28828) (a:=58) (b:=59) sp28828 sp28886) (joinSmall (lo:=28945) (a:=59) (b:=59) sp28945 sp29004)))) (joinSmall (lo:=29063) (a:=469) (b:=469) (joinSmall (lo:=29063) (a:=234) (b:=235) (joinSmall (lo:=29063) (a:=117) (b:=117) (joinSmall (lo:=29063) (a:=58) (b:=59) sp29063 sp29121) (joinSmall (lo:=29180) (a:=58) (b:=59) sp29180 sp29238)) (joinSmall (lo:=29297) (a:=117) (b:=118) (joinSmall (lo:=29297) (a:=58) (b:=59) sp29297 sp29355) (joinSmall (lo:=29414) (a:=59) (b:=59) sp29414 sp29473))) (joinSmall (lo:=29532) (a:=234) (b:=235) (joinSmall (lo:=29532) (a:=117) (b:=117) (joinSmall (lo:=29532) (a:=58) (b:=59) sp29532 sp29590) (joinSmall (lo:=29649) (a:=58) (b:=59) sp29649 sp29707)) (joinSmall (lo:=29766) (a:=117) (b:=118) (joinSmall (lo:=29766) (a:=58) (b:=59) sp29766 sp29824) (joinSmall (lo:=29883) (a:=59) (b:=59) sp29883 sp29942)))))))))
  have good : (List.range 30001).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 900000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 30000 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 30000 := by
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


private def packet (i : ℕ) : ℕ := (if i < 229 then (if i < 114 then (if i < 57 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 10 then (if i < 8 then 0 else (if i < 9 then 0 else 0)) else (if i < 12 then (if i < 11 then 0 else 0) else (if i < 13 then 0 else 0)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0 else (if i < 16 then 0 else 0)) else (if i < 19 then (if i < 18 then 0 else 0) else (if i < 20 then 0 else 0))) else (if i < 24 then (if i < 22 then 0 else (if i < 23 then 0 else 0)) else (if i < 26 then (if i < 25 then 0 else 0) else (if i < 27 then 0 else 0))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then 0 else (if i < 30 then 0 else 0)) else (if i < 33 then (if i < 32 then 0 else 0) else (if i < 34 then 0 else 0))) else (if i < 38 then (if i < 36 then 0 else (if i < 37 then 0 else 0)) else (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0)))) else (if i < 49 then (if i < 45 then (if i < 43 then 0 else (if i < 44 then 0 else 0)) else (if i < 47 then (if i < 46 then 0 else 0) else (if i < 48 then 0 else 0))) else (if i < 53 then (if i < 51 then (if i < 50 then 0 else 0) else (if i < 52 then 0 else 0)) else (if i < 55 then (if i < 54 then 0 else 0) else (if i < 56 then 0 else 0)))))) else (if i < 85 then (if i < 71 then (if i < 64 then (if i < 60 then (if i < 58 then 0 else (if i < 59 then 0 else 0)) else (if i < 62 then (if i < 61 then 0 else 0) else (if i < 63 then 0 else 0))) else (if i < 67 then (if i < 65 then 0 else (if i < 66 then 0 else 0)) else (if i < 69 then (if i < 68 then 0 else 0) else (if i < 70 then 0 else 0)))) else (if i < 78 then (if i < 74 then (if i < 72 then 0 else (if i < 73 then 0 else 0)) else (if i < 76 then (if i < 75 then 0 else 0) else (if i < 77 then 0 else 0))) else (if i < 81 then (if i < 79 then 0 else (if i < 80 then 0 else 0)) else (if i < 83 then (if i < 82 then 0 else 0) else (if i < 84 then 0 else 0))))) else (if i < 99 then (if i < 92 then (if i < 88 then (if i < 86 then 0 else (if i < 87 then 0 else 0)) else (if i < 90 then (if i < 89 then 0 else 0) else (if i < 91 then 0 else 0))) else (if i < 95 then (if i < 93 then 0 else (if i < 94 then 0 else 0)) else (if i < 97 then (if i < 96 then 0 else 0) else (if i < 98 then 0 else 0)))) else (if i < 106 then (if i < 102 then (if i < 100 then 0 else (if i < 101 then 0 else 0)) else (if i < 104 then (if i < 103 then 0 else 0) else (if i < 105 then 0 else 0))) else (if i < 110 then (if i < 108 then (if i < 107 then 0 else 0) else (if i < 109 then 0 else 0)) else (if i < 112 then (if i < 111 then 0 else 0) else (if i < 113 then 0 else 0))))))) else (if i < 171 then (if i < 142 then (if i < 128 then (if i < 121 then (if i < 117 then (if i < 115 then 0 else (if i < 116 then 0 else 0)) else (if i < 119 then (if i < 118 then 0 else 0) else (if i < 120 then 0 else 0))) else (if i < 124 then (if i < 122 then 0 else (if i < 123 then 0 else 0)) else (if i < 126 then (if i < 125 then 0 else 0) else (if i < 127 then 0 else 0)))) else (if i < 135 then (if i < 131 then (if i < 129 then 0 else (if i < 130 then 0 else 0)) else (if i < 133 then (if i < 132 then 0 else 0) else (if i < 134 then 0 else 0))) else (if i < 138 then (if i < 136 then 0 else (if i < 137 then 0 else 0)) else (if i < 140 then (if i < 139 then 0 else 0) else (if i < 141 then 0 else 0))))) else (if i < 156 then (if i < 149 then (if i < 145 then (if i < 143 then 0 else (if i < 144 then 0 else 0)) else (if i < 147 then (if i < 146 then 0 else 0) else (if i < 148 then 0 else 0))) else (if i < 152 then (if i < 150 then 0 else (if i < 151 then 0 else 0)) else (if i < 154 then (if i < 153 then 0 else 0) else (if i < 155 then 0 else 0)))) else (if i < 163 then (if i < 159 then (if i < 157 then 0 else (if i < 158 then 0 else 0)) else (if i < 161 then (if i < 160 then 0 else 0) else (if i < 162 then 0 else 0))) else (if i < 167 then (if i < 165 then (if i < 164 then 0 else 0) else (if i < 166 then 0 else 0)) else (if i < 169 then (if i < 168 then 0 else 0) else (if i < 170 then 0 else 0)))))) else (if i < 200 then (if i < 185 then (if i < 178 then (if i < 174 then (if i < 172 then 0 else (if i < 173 then 0 else 0)) else (if i < 176 then (if i < 175 then 0 else 0) else (if i < 177 then 0 else 0))) else (if i < 181 then (if i < 179 then 0 else (if i < 180 then 0 else 0)) else (if i < 183 then (if i < 182 then 0 else 0) else (if i < 184 then 0 else 0)))) else (if i < 192 then (if i < 188 then (if i < 186 then 0 else (if i < 187 then 0 else 0)) else (if i < 190 then (if i < 189 then 0 else 0) else (if i < 191 then 0 else 0))) else (if i < 196 then (if i < 194 then (if i < 193 then 0 else 0) else (if i < 195 then 0 else 0)) else (if i < 198 then (if i < 197 then 0 else 0) else (if i < 199 then 0 else 0))))) else (if i < 214 then (if i < 207 then (if i < 203 then (if i < 201 then 0 else (if i < 202 then 0 else 0)) else (if i < 205 then (if i < 204 then 0 else 0) else (if i < 206 then 0 else 0))) else (if i < 210 then (if i < 208 then 0 else (if i < 209 then 0 else 0)) else (if i < 212 then (if i < 211 then 0 else 0) else (if i < 213 then 0 else 0)))) else (if i < 221 then (if i < 217 then (if i < 215 then 0 else (if i < 216 then 0 else 0)) else (if i < 219 then (if i < 218 then 0 else 0) else (if i < 220 then 0 else 0))) else (if i < 225 then (if i < 223 then (if i < 222 then 0 else 0) else (if i < 224 then 0 else 0)) else (if i < 227 then (if i < 226 then 0 else 0) else (if i < 228 then 0 else 0)))))))) else (if i < 343 then (if i < 286 then (if i < 257 then (if i < 243 then (if i < 236 then (if i < 232 then (if i < 230 then 0 else (if i < 231 then 0 else 0)) else (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else 0))) else (if i < 239 then (if i < 237 then 0 else (if i < 238 then 0 else 0)) else (if i < 241 then (if i < 240 then 0 else 0) else (if i < 242 then 0 else 0)))) else (if i < 250 then (if i < 246 then (if i < 244 then 0 else (if i < 245 then 0 else 0)) else (if i < 248 then (if i < 247 then 0 else 0) else (if i < 249 then 0 else 0))) else (if i < 253 then (if i < 251 then 0 else (if i < 252 then 0 else 0)) else (if i < 255 then (if i < 254 then 0 else 0) else (if i < 256 then 0 else 0))))) else (if i < 271 then (if i < 264 then (if i < 260 then (if i < 258 then 0 else (if i < 259 then 0 else 0)) else (if i < 262 then (if i < 261 then 0 else 0) else (if i < 263 then 0 else 0))) else (if i < 267 then (if i < 265 then 0 else (if i < 266 then 0 else 0)) else (if i < 269 then (if i < 268 then 0 else 0) else (if i < 270 then 0 else 0)))) else (if i < 278 then (if i < 274 then (if i < 272 then 0 else (if i < 273 then 0 else 0)) else (if i < 276 then (if i < 275 then 0 else 0) else (if i < 277 then 0 else 0))) else (if i < 282 then (if i < 280 then (if i < 279 then 0 else 0) else (if i < 281 then 0 else 0)) else (if i < 284 then (if i < 283 then 0 else 0) else (if i < 285 then 0 else 0)))))) else (if i < 314 then (if i < 300 then (if i < 293 then (if i < 289 then (if i < 287 then 0 else (if i < 288 then 0 else 0)) else (if i < 291 then (if i < 290 then 0 else 0) else (if i < 292 then 0 else 0))) else (if i < 296 then (if i < 294 then 0 else (if i < 295 then 0 else 0)) else (if i < 298 then (if i < 297 then 0 else 0) else (if i < 299 then 0 else 0)))) else (if i < 307 then (if i < 303 then (if i < 301 then 0 else (if i < 302 then 0 else 0)) else (if i < 305 then (if i < 304 then 0 else 0) else (if i < 306 then 0 else 0))) else (if i < 310 then (if i < 308 then 0 else (if i < 309 then 0 else 0)) else (if i < 312 then (if i < 311 then 0 else 0) else (if i < 313 then 0 else 0))))) else (if i < 328 then (if i < 321 then (if i < 317 then (if i < 315 then 0 else (if i < 316 then 0 else 0)) else (if i < 319 then (if i < 318 then 0 else 0) else (if i < 320 then 0 else 0))) else (if i < 324 then (if i < 322 then 0 else (if i < 323 then 0 else 0)) else (if i < 326 then (if i < 325 then 0 else 0) else (if i < 327 then 0 else 0)))) else (if i < 335 then (if i < 331 then (if i < 329 then 0 else (if i < 330 then 0 else 0)) else (if i < 333 then (if i < 332 then 0 else 0) else (if i < 334 then 0 else 0))) else (if i < 339 then (if i < 337 then (if i < 336 then 0 else 0) else (if i < 338 then 0 else 0)) else (if i < 341 then (if i < 340 then 0 else 0) else (if i < 342 then 0 else 0))))))) else (if i < 400 then (if i < 371 then (if i < 357 then (if i < 350 then (if i < 346 then (if i < 344 then 0 else (if i < 345 then 0 else 0)) else (if i < 348 then (if i < 347 then 0 else 0) else (if i < 349 then 0 else 0))) else (if i < 353 then (if i < 351 then 0 else (if i < 352 then 0 else 0)) else (if i < 355 then (if i < 354 then 0 else 0) else (if i < 356 then 0 else 0)))) else (if i < 364 then (if i < 360 then (if i < 358 then 0 else (if i < 359 then 0 else 0)) else (if i < 362 then (if i < 361 then 0 else 0) else (if i < 363 then 0 else 0))) else (if i < 367 then (if i < 365 then 0 else (if i < 366 then 0 else 0)) else (if i < 369 then (if i < 368 then 0 else 0) else (if i < 370 then 0 else 0))))) else (if i < 385 then (if i < 378 then (if i < 374 then (if i < 372 then 0 else (if i < 373 then 0 else 0)) else (if i < 376 then (if i < 375 then 0 else 0) else (if i < 377 then 0 else 0))) else (if i < 381 then (if i < 379 then 0 else (if i < 380 then 0 else 0)) else (if i < 383 then (if i < 382 then 0 else 0) else (if i < 384 then 0 else 0)))) else (if i < 392 then (if i < 388 then (if i < 386 then 0 else (if i < 387 then 0 else 0)) else (if i < 390 then (if i < 389 then 0 else 0) else (if i < 391 then 0 else 0))) else (if i < 396 then (if i < 394 then (if i < 393 then 0 else 0) else (if i < 395 then 0 else 0)) else (if i < 398 then (if i < 397 then 0 else 0) else (if i < 399 then 0 else 0)))))) else (if i < 429 then (if i < 414 then (if i < 407 then (if i < 403 then (if i < 401 then 0 else (if i < 402 then 0 else 0)) else (if i < 405 then (if i < 404 then 0 else 0) else (if i < 406 then 0 else 0))) else (if i < 410 then (if i < 408 then 0 else (if i < 409 then 0 else 0)) else (if i < 412 then (if i < 411 then 0 else 0) else (if i < 413 then 0 else 0)))) else (if i < 421 then (if i < 417 then (if i < 415 then 0 else (if i < 416 then 0 else 0)) else (if i < 419 then (if i < 418 then 0 else 0) else (if i < 420 then 0 else 0))) else (if i < 425 then (if i < 423 then (if i < 422 then 0 else 0) else (if i < 424 then 0 else 0)) else (if i < 427 then (if i < 426 then 0 else 0) else (if i < 428 then 0 else 0))))) else (if i < 443 then (if i < 436 then (if i < 432 then (if i < 430 then 0 else (if i < 431 then 0 else 0)) else (if i < 434 then (if i < 433 then 0 else 0) else (if i < 435 then 0 else 0))) else (if i < 439 then (if i < 437 then 0 else (if i < 438 then 0 else 0)) else (if i < 441 then (if i < 440 then 0 else 0) else (if i < 442 then 0 else 0)))) else (if i < 450 then (if i < 446 then (if i < 444 then 0 else (if i < 445 then 0 else 0x2ace7ae2bd147c9964722090ef46e631e16509803fa18d09703380c200002ace1eb2b014209524521f58e5c6862e614208d038a17008b02cc0ac00002acdc0d2c314dc9b047320c0ee46bc2fe15089083d818a09203400c600002acd63e2bd14589684541fe0e846822da13e886037415d08002a80a400002acd0892ad93f49304421f50dfc65a2d714288ac3a017107f02c40b800002accace2ac93e891c4301ee0e006362c5136082036815b07b82980b000002acc4f02b8944095044b1f60e7067e2eb142889838e15d08602e80a600002acbf022c0946c9884692020e846822db13f889838e17008982c00b400002acb9312b5941495a4551f70e5467e2e214308bc39a17008f032c0bc00002acb36f2b2943097e4571f80e606702da14088cc3ac17c08f02f40be00002acadad2b0941c9504451f20e306562d514188a439e17b08c82dc0b200002aca7cf2bb147498c4672038eb06b230415189003ac17c08e03000c800002aca1ec2c494a898a45e1f90e346602d513a888838416908802b80a200002ac9c022c0148497e45c2008e8067c2e014408b438c16d08a82e40b400002ac961b2bc946c9604521fc8e8067a2ea14588c83a217a08a83040b600002ac90392bf949c99a4682038ea06982e914a08f43b417808f83000c200002ac8a5d2c714cc99846b2030eb86a42f714508b839e17008682c80ba00002ac849a2b1144896c4632028eb868c2f214988f43bc17b09282f40a600002ac7ee92ac941896044d1fc8e946862ee14b88c83a016c08902dc0b000002ac79162ba147099a4672050ecc6a42f014a88dc3b617208882f80b400002ac735c2b094049444461f20e246702d413c886839217708982e00bc00002ac6db92a2939892a4331ef0e0c66c2da141888839c16008482bc0be00002ac67c12cb94f89944602048eb46842e614688d83ae17708f83140bc00002ac61fd2b2941c96644c1f88e4066c2db13e088c38e16708b82d40b400002ac5c242be948097a4521f90e5466a2d013c886038616b08902e80c400002ac56702a713cc9444421f30e006522ca139087c36214f08082b00ac00002ac50d929d93a492a4431f70e4465a2ce13a887037e16708b02dc0a400002ac4ae72c4948498c45f2000ea469e2e714608e03b017509182fc0be00002ac45102bd146097045e1fc8e7468a2eb14788983a617b08d82f80b000002ac3f662a613a89224331e90dec6322c112f881436415b08482dc0b200002ac39962b8141c96645c2058e986962fb14f08e43be17a08b02cc0b800002ac33a02c994e49ba47f2118f046b830315409003ca18209003100bc00002ac2db42c614c49904732068eac6a02f814f88e83b017508682b40a800002ac27c32c914c098e4622038e9069e2e614d08dc3b217c08d82f40ca00002ac21ee2b9944c96e4582030e8c68e2db13b089438015e08902e80c200002ac1c132bb148c9a647920b8f006b62fd15008f03a417208e02f40b000002ac165a2af93c09384521fc0e6c67a2e213e085039617008b02d40bc00002ac108a2b8945c96c4561f90e4466c2df13d089838e17208f03380de00002ac0ae32a3139492042c1e78dec6462d013b887439017709083100d000002ac04f62c3149c98c4642088ee06ce30315008ec3c217b08e02e80d400002abff152bb146c98a46a2028ea869a2e8141889c39016308702a80b600002abf9702a313fc9444461f80e686842e414408b439817c08b02f40c600002abf3c72a993cc92243a1ef0e206502d3137088438416908802a80b600002abee0a2ad140094a4401f30e1865c2cf13e089c38817608902c40c400002abe82a2bf14b898e4622078ed06ae2fa14d08ac39c17c08d02f40b000002abe2542bb143896c4571fb0e6c6622e513d088039c16f08702f80c000002abdc672c694a098c46d2068ecc6a62f314c88e03be18408f02fc0cc00002abd6c429e935c9084211e48de06422c813d887c38016407e02ac09600002abd0ea2bd947096a45d2020ed068c2e614408b83aa17308d02f40ba00002abcb002c514bc98445f2050eac6a22f515108cc3ae17208703040ca00002abc54a2b214149464401f10e346662d313a887c38e16808c82ec0b200002abbf422d4150c9c648020e8ebc6b02f114b88e03a016f08982d40cc00002abb97e2b3141c96a4511fb8e846822e614a08b03a617008b82d80ac00002abb3d82af942895a44c1f48e246602d313e086c39616e08b82e40bc00002abae0d2bd14949a64782058ec86a82e914e08ec3b817b08782f00ca00002aba85f2ac93e49484551fc8e5c6842df13d889039417208902c80bc00002aba2652cc14d09c247d20d8ee46a82fe14d89043bc186096030c0ba00002ab9c7c2c814e09ac47f2138ef46b230015108f03be186094832c0c000002ab96d22a813d493043c1ef8dec64e2c513b085436a16308082c00a200002ab910f2b194209564511f58e286582db13a884437216508a82f80c000002ab8b442b8142c9644561ff8e4468e2f314d88d83d218409203080de00002ab85782b294509564552000e9c6922eb146088838415c08802c00c000002ab7f962c0146897a4602020e9468a2f814888c039a17109102f00b400002ab79c52b6143c9784612050ecc6aa2f014788d038e17108382d40b2000)) else (if i < 448 then (if i < 447 then 0x2ae5c7c2c2149c98c45c1ff0e8c6822e814808b43aa18009103000b600002ae56aa2b314289544541f90e406622d013c887436c15a08402cc09600002ae50ce2c214b899a47a20b0ec06922ec14808cc38416f08502ac0ac00002ae4ab22df95589e049221b0f386be2f2144889838a16b08582e00a800002ae44eb2b4144496445b2008eb06a42f514788b83a417708e82ec0c200002ae3f2d2ae142896045c1fd8e886982ee14588c03aa17f08f030c0ca00002ae395a2bc145098c4561ff8e8c6602d213f88b43a817509083080ca00002ae33692cd94fc9ca48b21b8f6c6f031b15c89783ee18e09603200d000002ae2da82b4944c97645b2028ea06982f414b08e43b417608902e00aa00002ae27c42bf947c98a4622028ee869c2f014a08e03aa17c08c83000c200002ae21d22ce15389f049421a0f2c6d430c15589443e8191090830c0c200002ae1c0b2ba94849844631fe8e6c67e2e4141089439617008a82f00d400002ae16482b2142896e45f2070eb46982e614308c43b018e09683140ca00002ae107b2b894549704571f88e646642dc14108a839216a08382ac0a600002ae0ab92b0141094a4552028ed869e2ef14988d83c417908802ec0c800002ae04cd2cb14e49c248520c0ed86ca30d159091c3b617b09103280c600002adfefc2b9143896844f2008e8868e2f114988e83c017908a02f40b400002adf92e2b3144495644f1fc0e7c68c2ea144088437816407c82940a600002adf3552b9144098645e2020ea06822e813c887838416608602dc0c800002aded7e2bf146c97245e2018ea86962e514088743a217308b83380d000002ade7af2be946097a4601f90e806862ec146889839817608802bc0b800002ade1ed2b4142494e4441f78e606722d2142889c39816f08b82d00b800002addc122bd947499a4822108ef46ac2fd14788b03a217608a82fc0ba00002add62c2c614b098c4591fe8e7c6862e914788a039c17909302fc0c800002add05e2b9145497e4652030e9c6982f414b88dc3cc17f091831c0c400002adca5b2d515089bc4832118f146ce30615009003ba18808f02fc0ae00002adc4902b7944095c4521fb0e4c6642dd14108b838416b08702c80ba00002adbeaa2c894d09b847f2118eec6b02f214d88dc3bc18109083080d600002adb8d52c014909a647820d0ed06c2304153893c3c418409483080bc00002adb3392a2939092243b1ed0e046422c4138087039216a08102d00a400002adad562cb94d09ae47920b0e9468e2e8143888c38c17308d02c40a400002ada7942b4944896e46c2030eac6a62ea146889039e16d08602d40b400002ada1ae2be94c89964662038eb06a82f414b88e43b216808282b80b000002ad9bc22bd146898646920b8f006bc2f714b08e03b418b09b033c0c400002ad961e2a493c89264341e90e0864e2ce13c087438416308602d00b400002ad903d2c794b098c4712090ec86a82f614908f03b617c08902cc0bc00002ad8a9a2a413e49544471f50e5868e2e714808d43a817308f03240d200002ad84af2c2949c9ae48d2188f646f831315989203d418c09303280d400002ad7ec12c914cc9a246b2088ed869c2ec14a08e83b417108783100d400002ad78ee2b9146897245c2008e7c67e2dd13f08a038e167085828c0a200002ad73122bc94689744541fc0e506682d913d886037815c08402ac09e00002ad6d342bd147c9844612038e9869a2e814508b039817108883000b200002ad67452c894f09b847420e8ef46cc31115889383c818209682fc0b000002ad61782b5942c97245b1fc0e7c67e2e7148088839817408d83080be00002ad5b8e2c594a89a247b20f0f286c030414f09003bc18109102f00ca00002ad55ec2a493cc93243e1ee0df06342bc133882034e14807d02b00ba00002ad504b2a913d492043f1f80e546722eb141889839416908202b00a600002ad4a7a2c0945498646b20f0ee86ce30a15789343e619009203280e200002ad44942bb14809884672060ed869a2ea14a88c83ba17708c02fc0bc00002ad3ed52b3144097444b1f70e5c6822dd13f888c39e17508a02ec0be00002ad390d2bb144496845a1fe8e7c67e2d8141089038816108682e40bc00002ad333c2b394509764551fb0e846782e714888c83a417c08d03000be00002ad2d5d2be144095844c1fc0e5065e2d3139084837e16008302e80c000002ad278c2ba946496644d1fa8e486802db13d087437416c08a02c00ba00002ad21a32c5149899646f20c8f146d830f15a09583de19709683240ca00002ad1bcb2bc147c9824642088ec867a2df14008803a216d08d82e00ae00002ad16182ad140094044b1f68e3866a2e414588d83b417608b03100c800002ad10612af143895c44f1fa0e946b230315008fc3be17408f031c0ae00002ad0a872c3149c99e47120b0ef46be2f714b08ec3d2189095031c0d200002ad04c22b194189624541ff8ea869e2eb14208a839216d08c82e80b600002acff092b414089384411f60e1c6442cb136884c36615807c02a00a400002acf9422b3941495844c1fe0e9867e2e314788d43b018609303000d000002acf34d2cf95209b846d2050ea868c2ec14708e03be17b09103040ba00002aced832bc149098a4642008e946802e714588c838e17008902e80aa000 else 0x2afd0d12ae93e49304461f40e386602e1140886039c17b08b02d80bc00002afcb172ab140495044d1f70e206622dc13b08a83a017308a82ec0c400002afc54f2b393d094c44c1f78e586662db139086839216c08b82e40c200002afbf842b9943896c4611ff8e746822ea14408c03b017708d83300c800002afb9b42ba947498845e2078e906ac2ff14c88d83aa17a08c02f80a600002afb3c72c814d89b046a20c8eb86982f214c88f83ba18009202fc0be00002afadea2c414749824642018ea069a2e214608d03b817b08982e80cc00002afa8222af941095244d1f90e5c66c2d713d886c37e16108582a40ae00002afa2552ba946897a4632050e906802ee14488d43ae17f08f83180ca00002af9cd529493408ea4261df0d8862e2b7131883c37215e08002cc0bc00002af97082be148499045b2008e846a22ec14e88dc3c2188092030c0c800002af91122ce94f49b446e2060ea46962ee144888c37e16508382cc0ae00002af8b4a2b894449644511f78e406962f214808ac39e17509283180d600002af85832b794409544552028e886822e713e088c39a17208802c40c000002af7fba2bf94709764672058eb46a22f314788b038a16508002bc0ac00002af7a012af13f49424551f98e4466c2ea14808ec3c018208d82f00ae00002af74362ae940c94e4512018e886a22f0148889839617608b82e00ae00002af6e652bb14649664611ff8e3865c2ca137085037816308802e40b800002af68ba2ae13f495444c1f98e486742d313d889439c17608782cc0ac00002af62f12b2140c95644b1f70e6c67e2d913e086c37a16d08782ac0a800002af5d0c2c514c49ac47d20c8ee06b62ff15089243d218109083140dc00002af573a2bc14989864622008e946782dc140089437a15d08182c80aa00002af51542c4147c9664602068eb869c2e8143889c39c16708782f00bc00002af4b762c2148c98e46b2078ecc6ac2eb14d89103aa17f08f03100a000002af45bd2b4142094e4481f18e0c6502cc13e089038a16508282d80c400002af40012b5942496e4581fb8e7468a2e314688b83a017308982b40ba00002af3a1d2c5946c97645a2010e586822df144089439616e08a82cc0b400002af344b2bc944c9804622000e906982ec14188a439417008a82bc09c00002af2e832ba14689604612048e9868a2e314588d839a17508382cc0b200002af28bb2b3141c9504531fc8e8c69c2ee14788c83b817908f02f80a200002af22dc2bf147497a45c2070eb86922ee14b88fc3b417908d82dc0b400002af1d152b694689884632010e6c6862e513d088437e16f08982dc0bc00002af17252c694949904622030ed869c2f714408b039a17208c02d00ba00002af113b2c614ec9b047c2100ee86c630115288fc3c017709383380be00002af0b572c594a09884662070ebc6aa2f915389043d018409002c80a200002af05a62ae943896c4521fe0e986842e614388c039c17d09203280c200002aeffd92bb145497a4692038eac68e2ec14708b439a16f08582e00ae00002aef9e02ce94f09ba47e20d8ef06bc30315709203d218709183140d600002aef4082bf94649904682020eac6842e8147089839817308b02fc0c200002aeee162c6149c9a647420a0ed06b82f714a88dc3ac17a09483180b000002aee8522b6145c96a4601fc8e7c68c2e514508ac3a017108a03080c000002aee2a42aa93dc92e4431ee0e206522d513e887038a16708802e80c200002aedcca2c814849844632010e8467a2d213f887838616c08382d00ae00002aed70d2b0941894c4471f88e4065e2d313a084836a16e08802e80b600002aed11e2c814b099646d20d8ee86a630515409183ce17b08c82f80b600002aecb662b294009524491f28e206622d213e886837815e07c828008a00002aec58b2bf149498646a2080edc6ac2f414d89103b817608f02f80c000002aebfc12b6942c9524632020e8466a2d013a888438815407e82a009c00002aeb9ee2bf947099e46a2090f006b02f9154891c3c018809283140c000002aeb3fc2c714e09a84732068ec46a02f215188f43cc18d09603580ce00002aeae1f2c014a09824632048e706702e713c882436415e081029409000002aea8412c0949898845f2000e9c6922ee142888438816908682c40b800002aea28c2aa13bc9284351f00e246382bb135880c35615d08182a00a200002ae9c8f2cd95009c84842118f346cc30a152892c3c018109102e40c200002ae96f32a293c493844c1fe0e986a22f214708d039a17e08e83040d400002ae91502a893dc9304361eb8e2065c2c6139085437616808102b80aa00002ae8b582c594989844682008e9069c2f714b88d83ae17008d02e80bc00002ae85822bf946496c45a2010e946842e814008c439617408b02ec0c200002ae7fac2bc94a098c4602010ec46a02f314588c839a16908082a80b600002ae79b12d015189c84892120f186e431015689303c218409183000aa00002ae73c92c714cc9984652000e946902f314c08f43c6192096831c0d000002ae6dfc2ba14649724531fd0e846862e213a889c39a17808902d00ae00002ae68162c714dc9bc47420b0ee86c030315509203cc19509303100c400002ae625a2af14289604571fa0e6067c2db13d88943a416f08b02e40b4000) else (if i < 449 then 0x2b1461a2d014e89bc4792098eec6b62fc14c88cc3aa17c08c83000c000002b1403a2c2148897a4682050ec46b82f915009083c218509203080c200002b13a5d2c0147c99846c2080ea469c2e0141086c37a16808582b40a800002b1346f2c994e89c047220b8eec6c02fa14a88c03ac17d08b02f80c600002b12ea52b2942895e4522028ecc6be2f214908e83aa161083828c0a800002b128a42cf14e89d84842138f046c42f714f08dc3b617e08c02c00a200002b122d62b7945c98c46d2030eac68c2e914708c83b217908c02d00ac00002b11cff2bf145495444f1f58e406622d814488d03b018c09603340ba00002b1173d2b894689744631fe0eb469a2ed14e88f43aa18509483100b400002b1116d2b714389664601ff0ea068a2ea14888c83ae17508882cc0c000002b10b822c294c09be48620e8efc6b22ef14488bc3a017809203100c800002b105a62bd949099646d2020eac6a82e614a08ac39616d08c02d80b000002b0fff02a893e891c4411f48e406722df14588bc3b617408a82e00b000002b0f9f02d495089c44832100f106b830815609043ba17808b02f40bc00002b0f40b2c814f49ca47e2138f0c6d430815189243d218609583380da00002b0ee512b2141895a44a1f48e3c6662dd144088038a15d08082b00c400002b0e8812be147097445a1fe8e8c6a22f014e08bc3a616e08482cc0b800002b0e29c2c4947096645b2028e8c6842f414a88c43b418409182e80c800002b0dcf82ad140495243c1f08e1864e2cb139886037815907e82ac0ac00002b0d70d2c694c89aa4782088ec86982f015008f43c217a08b82f80ca00002b0d16d2a313b092a4391eb8ddc64e2c813a083837816408802cc0b400002b0cb752c6948098446c2048ed86a82fb14c88f03ce18709183280d600002b0c57e2c894d49ac4842138f286c02fc14a88b43b818608d83140b200002b0bfb12b9141c9644511f48e3465e2d3137084038215e08082a80aa00002b0b9e72b594089504471f70e7c68c2de143089c39e17008b82b40a400002b0b42d2b294109404521f58e2865c2da139085c36815908602cc0b400002b0ae312cb94cc9a447e2130f1c6e230915309183ce18109483380dc00002b0a8582c0948097245b2008e9069a2e4142887c37e17208c03000ca00002b0a2b42a593e494a4441f60e406642d513c887037415f07e828c0ae00002b09cfc2af93f49464511fc8e386562d113a083c35015607f02c80ae00002b097382b7943c9524501fc0e486682d713c887038c16b08302880a200002b091512c614b89b04722080ee86b62fb14808c43a617708782cc0b800002b08b772bf14b89b647f20d8ee86ac2fd14c88f83c817d09082d009c00002b085992bd14709844622068ebc68e2ec14608e83ae17908e82e40ae00002b07fda2b5944c96844f1ff8ea46a22fb14d88d03c818408a02e40be00002b07a002bb144496c45c1ff8e7c6722da14108a039a17408a82e80c200002b0742c2c114ac99247e20c8ee46b22f114488d03b217c090831c0d200002b06e462c294bc9a04762098ee46b02fb14a08c43b217208b82cc0ac00002b0686c2bd148097e4692018e7c69c2ef14c08e83cc18b09883280c600002b062a02bc144c97445d2010e8c6962ec14888b43a417808c03080c400002b05caf2c4149098646d2040ea069a2f314888e83c818309103180d000002b056cb2c394c09984691ff0e686782d813d087838416d08c03080c400002b050f52be94889a04772090e946a82ed14a88f03ba17908e02f40ba00002b04b182bf148498c4722090eb06a42f314988f03ca18e095032c0da00002b045582ab13e093e44c1f58e4c6762d413a085839017108b82c80b200002b03f9d2ac94209504501f68e746802e214088a039016f08b82e40ba00002b039af2c594b099c47b20b8ea06842e2141887c37216508482bc0b200002b033de2b9145896e45f2060ea06a22fa14b88cc3a218009583040b800002b02e0f2b4945096a4622038e986802e914608b83a016e08c02dc0c800002b0283e2b9141493e4431f40e2865e2e1140888c39e16e08e03080be00002b0224b2cf14e49ca4842118ef46a62f414908ac3a417508c82bc0bc00002b01c6c2c694cc9a846a2038e9468e2ef14d88d03aa17009003280de00002b0169d2ba14409544591fe8e886a22fb15088f03bc18209082dc0b800002b010c02c3943c96e44e1f20e286542cf139884436c15507d82b40a400002b00b032b3944497a4672060ed069a2ef14788c83a417b08f83040be00002b0052a2be14709764682038e986942e414a88e03a017208402dc0b200002afff5b2bb948c97645d1fc8e5466e2d514208ac39616808502d40ae00002aff9792be149c99c47520b0eac68a2f414508b839816a08982e80be00002aff39c2bb145097045e2058eb469a2ea14508d83c817e08b02d40c000002afede62ac940895e4571fa8e6c67c2d513e88a839c16f08782ac0a000002afe7dc2d615449e249021b8f446da30b15689283d418908e03000d400002afe20f2b6940c9364431f20e0864e2d1138886839616508382cc0b400002afdc532b2942097e45e2020ec06942ee14908d83aa17408a02e80ba00002afd6852b8147498a4672030ed86c430314788c83c018208f02f40ba000 else 0x2b2bae72a6139c92242b1e48da860a2b412c080834414607e82b00aa00002b2b50d2bd94589804752098ed46b82ef14c08a039016d08702b40ac00002b2af332bc947c97846c2088e9868c2e314988d43ba17f09102e80c000002b2a9522bd14709804692090e906842ed14b88b039816608782c00b600002b2a3aa2a493c09384471f68e2c66c2e414288a03ae17108c02d80c200002b29da52d295289c847e2110ef06ac2f514708bc3a017108882bc0ae00002b297fb2ac13f895a4551fd0e886742ea140888c38e16c08902e00c800002b2921a2ca14a89a24712090eb86a82f2142087438817408982fc0c400002b28c402bf94809a446b20d8ed06be2f914f88e83b417e09302f00a400002b286762bc143096445f2060eb46782ed14588c439a170087029009000002b2807f2d0151c9bc47b2088ecc6b22f314b08cc3bc16b08e03100b200002b27a822d015089ba4862130f006c82fc15509343d418909483140d600002b274b32b9944095244d1fb8e506822ec14a08d83ac17908c02e80b400002b26ee72b0942c94443c1f10e446682d213b885436816708582cc0b200002b269122be145496244f1f30e3c6782e313d087438a16e08902bc0b200002b263102ca14e49c648620b0edc6b62ed14688d03a817a08e82e00b600002b25d5b2ad93f494e44e1f30e0c6442c0134883836a16908a02e80b800002b257b929e137c90442a1e60d8461c2af12d0820352150077829c0a400002b251e22bf948498047220b0ec86b42fc15008e03c417508b02c809800002b24c292af13f89484461f60e2865e2de13f88a039c16c08382c00bc00002b2463d2c614b89aa4762090efc6b830615809383c418109603140b400002b240642bf94b499646d2058ea86882e614708cc3b417708802f00c000002b23a872bf147c9824692070ee86ae30115108ec3c018909583180d200002b2349e2c994dc9b447e2110edc6ae30015309443e2195097830c0ca00002b22ede2b494489624511fe0e786942e514808bc39a17908e82f80c600002b229042c2148c99c4742050e9c6942ea14908c83a218009182fc0c000002b2236329f139c92643d1f30e146642c713d885036c15107e02bc0b000002b21d742c6148897e46320b0ef46d02f914f89043b018009083240d600002b217a22b914789744541fc8e946902e914808b83ae17508902c80a800002b211a42d5150c9d248d2140ef86b42fd14b88dc3ae17708f032c0de00002b20bd02bc14949924622060e9068c2e414588b439e16b08782d80c600002b205f92b994549724692020e8c6902e914888e03b217f08f02f80ba00002b200452af14409624461f90e686742db138086c37816008502b80ae00002b1fa5a2cc14f09bc47220f8ec86b430215109003d417808902d00b400002b1f4822c0949c9ac46b2050e886982f214d08e83b217d092032c0ce00002b1eea62bf149098e45a2008e946822ed14c08dc3b017b08e03300c600002b1e8ba2c214909aa47820c0ee46b62fc14b88f43a4176086830c0c400002b1e2f52b5140c9464471f38e0865e2cc13d889439a16a08a82c00b400002b1dd462aa940094a45b2010e686822ef14988f43a217908f82e80be00002b1d7932a813bc93a43f1f58e4066e2de13b089038e15e083029809c00002b1d1c42b7144496a45a1fc0e7c6862ec14588ac39816f08d83200d200002b1cc052b3142c95444d1f58e4c67e2de13f88a439817408c82e40be00002b1c6292bb146496645c2008eac6962ee14f89103c817c08d83100b600002b1c0452bf14889964622060eb86a62fb14f08f43c617508e03040c400002b1ba722be945897645c2008e9068e2e414688ac38816b08c82f80be00002b1b4ac2b9146097a45d2000e786982f314e09043c017a09082fc0b800002b1aeee2ba14649624511fd0e606722dc141889839617308d03140ce00002b1a9072c694c49a44842118f3c6e031615689543f819e09703300b800002b1a3242c894bc9a84722040eb068e2ee14988c83b017608982e00ba00002b19d602b8145896e4602020e9069a2ef14a88d03ac17508782f00b600002b197cd2a013b091842f1e80e186442c3134883435215108182c40b400002b1920c2af13f494244d1f60e2464a2ba135085438816308602cc0c400002b18c362bd948898846d2078eec69e2e614708b43aa17608982e00be00002b186472ca94d89944772108f206d2308152091c3e219309603100c400002b1807b2ba945c96a45f1fa8e506862f414d88dc3a417308982c80b600002b17a9e2c0147c98c4651fc0e886882ea14908a439617208982c80a600002b174f62ab941893e4431f10e206662cf13c088c3ac16e08802d40cc00002b16ee32db957c9f44842118ef06b22fe14808b039a17008a02ec0bc00002b169062c414c899e46f2100f0c6ca300155892c3e218409383280c200002b163532a993ec9364441fc8e886922e614708a83a817708b83180d800002b15da12b4142094e4441f18e1864c2da144887039416208982c80b400002b157aa2c714b49ac46b2020ea069c2e914688c43a017208e02b409c00002b151e22b3146097045b1ff8eb46ac2fa15009083c217908c02fc0be00002b14c142b8146496e4521fb8e7068c2ec14888e03a617a08c82d00a2000))) else (if i < 454 then (if i < 452 then (if i < 451 then 0x2b42f0e2a313a890042e1ec8ddc6462d1138088437216c08882c40a400002b429342c1148898e4632078e9c6a42f514888b439c16808102900aa00002b423702b293e494243f1ef8e406802e714408d43ae17d091031c0b800002b41d5a2dc956c9e84942190f4c6f630e15189503e418b09583140ca00002b4176d2c314a49924661f98e186722d713b089437816008102ac09e00002b411a62b6945495a4541fc0e606702e514208983ac17508b82e00ca00002b40bce2bc947c9864682088ed46c02fc15189183e418909103300c000002b406072b594409644501f80e5c66e2d913e888c39c17308702d80ac00002b400302c314c89ac47020a0f046c230915589183c418009083100c000002b3fa1c2d995549da4902118ef06ae2fd14e89143ae18709103240d000002b3f43a2bf147c99446e20c8ec06c22fb14d89343e219509103100b800002b3ee7c2af94449684571fb8e606722d813e088037016108102bc0b200002b3e8bf2b2144096245c1fa0e8868a2e814288c43a417608982c80bc00002b3e2ee2bb145094e4501f68e7067c2dd142888839216c08782cc0b400002b3dd132c414b499447020d0f046ba2f714808bc39816b08c03000c000002b3d7372c194c09ae47f2128f186ce30615008e03ae17a08d02f00ac00002b3d1552c494c09a846a2098ea86942eb14788ec3b417c08d02ec0b200002b3cb942b214349564451f90e5066a2d4138088438617108b82fc0c800002b3c5c72b4943c9684571fd0e6c67a2df144888438a16d08982f00bc00002b3c0092b1940c9584521f70e4c65e2d213b887836a16a082029809c00002b3ba302bb144c95644e1fc0e586822ee14588e83bc17908e82f00ae00002b3b4662b694449704592030ea068a2e4144889c39c17809202f40c000002b3ae722c594b89a447d2108f0c6cc30715308f03ac16808782d00bc00002b3a8a32b994349564511f48e3c65a2d714088a838215e08202b40aa00002b3a2be2bf14709804592030e8c6862f614e08fc3ce18e09603000bc00002b39cdc2c294a89a04692088ee86aa2e2144888c38816e08782d80b400002b397052ba945096a45a2020ea86942e014388a039a17008a82e00c600002b3914d2b0940496c4561fe8ea869e2ec14188bc3a616c08982d40aa00002b38b712c414b49ac47c20e8ef86c62fe15209283e8199096030c0ca00002b385a72b4942c95244a1f50e546722dd14308a839817808902ac0ac00002b37fca2bc145896a4581fd8e286642d213c086038c17508782f80cc00002b37a092b093ec9444411f40e346422cb13b088039416a08482d00b400002b374182d114dc99c46e2050e906862f014708c03bc17809102e00b400002b36e792a793bc94a4501f80e486742da140888038617408e02f00c400002b368942c3149899245e2028ec86982f614b89143c417f08f032c0cc00002b362cc2b594309524511f50e406742e114388903a217d08a82dc0b800002b35cde2c894f49da48a2100f086d230815509383d218309803000b800002b357042bf14789844581fd8e8068a2db142088438817108d031c0b800002b3512b2c1148498245f2008e906782e814488b439616e08b82f40b400002b34b7a2aa93f895c4471f58e3c6662d514008c43b818109383340d200002b345e029b93688fa4211ea0e0064c2c9135084436215908702e80b400002b340062c014b499646c2060e9868a2e413f887838a16b08982e80b600002b33a312b9942c9564491f88e4c66c2e114008e83a216808802d80d200002b334842ab93c09324341ef8dfc64a2ce139085438617208882d80ae00002b32ec12b494689904652018e9868c2f014408bc3be17508982dc0ac00002b328ce2c894bc99846f2088ee46c630515409203cc189095032c0ca00002b323002b4143495644a1fa0e706962ee14a88f43b817f09383040a000002b31d462a8940094243c1ef8e146662e013d887038c16a08a82e40c400002b3177c2b6145897c4672038ebc6b22fe14d08b039416a09003100c200002b3119f2bb14749864651fe8e406662db14488b439c17809083140b800002b30bd02b1941095c44b1fa0e5866a2da13b886c3a817308d82f80ae00002b306032b4142c97246a20a0edc6b22f814e88f03bc183093830c0cc00002b300192c914cc9a04722048e786882e314488e03b417908b03080bc00002b2fa472bf145497044b1fc0e686922e6144889439016e08882d40bc00002b2f4a22a893c892a4331ec8dec63e2c2132882c37e16808902d80b600002b2eedf2b8144c96a44d1f90e4c66e2d413e888c39817008e831c0cc00002b2e8fc2bc949c98a45c1ff8e8c6722e314608c03ae17708e03000a600002b2e3262be144896445a1ff8e986982ee14a08e83b017708983000be00002b2dd6e2aa93cc9324421f98e8068a2e914888e03b417608e830809e00002b2d7972c194b09a848220e0edc69e2ef14988c83ac17708c03040ce00002b2d1dd2b0944096645f1fd8e9068c2f314888d43c617c09002ec0b600002b2cc4629e939c91243a1ed8e086682de140088838c16d08882c00a800002b2c6742bc94709784602000e746782e114288c83b617409083000c800002b2c09c2c2149098246d2028ea86a02ec14188a838a16908902dc0cc000 else 0x2b5a3dc2c114b89a84752090ecc69a2f214a08e03a017708a02cc0c400002b59e002c294d09ac47920c0ee06c230514f08f43bc18b09783100c000002b598522a793e09444481f20e186662d813a087439016e08a03040be00002b592512d515109ac47920a8f0c6dc30414c88cc39a16b08e83080be00002b58c892b094149404431f78e6067c2e714808943a217c08c82c40b400002b586bb2b9949098a45f2030ea46942f1144087839817308d02f00b600002b5810e2ad940894044b1f38e486782e114588b438c16408983100b800002b57b1c2c914b09824692090eec6b830014c08d43aa17409183140d400002b575502b7947c99247920c0ee06b42fd14e88f43ba18308d83140e000002b56f772c0148898045b2018eb46a02ef14a88d83ac17008c02f80ca00002b569b22b193f494c44d1f88e5867a2e213f08703a217608d82e00d200002b563f32ac940c9464401f28e346742ea14788d839a17008b83100b800002b55e152c1146497c4672048ec86b230214f88f83bc17909183200ba00002b558562b6144c9684561fe8e886862df14208c439215807c82b00b000002b552872b6147496645b2018ea06aa2fa14f89283ca17208882e40bc00002b54cbf2b5942c9444521fb0e3c67a2e414208a039216e08582d80b600002b546d32c714c49b047f2158f246be30015088dc3ca17e08a82e40c400002b5411c2b214009284391ef8dec62e2d213e885438e16908302e00ba00002b53b482b9144494e44c1f58e3c6602db13a887038416908802c00c200002b535572c5149898445a2018ebc6a42f614d09183cc18409202f40b600002b52f682c214a099a4702080ed86ac2ec14888f03b817a08782f40a000002b529ac2b6944c96c4521fd8e8c6a42f314c88f43ce18809303080be00002b523e42aa13c493243f1f50e4c6642d9140087837c16c08c82c80b200002b51e0b2be948497a46a2018ed06be2f914f08ec39e17209003080ae00002b518462b414409584531f98e5c6682e414488b83b417608882c40a600002b5127d2b6943895044c1f70e386782d713b884c38416208582d40b200002b50c772d315249dc48a2130f246e8313159895c3ea19309683240c400002b506992be94749824712078e9c6982eb14608a03b816f08902ec0b800002b500cd2ba947097a44f1fd0e7868c2f2147889c37e16508782e40b200002b4fada2c994d89a047d2090ed06a42db14208dc3a017b09282dc0ae00002b4f4d62c814dc99e4702050eac6982e514488b83a417d08d03100c400002b4eefe2bf946097a45f1fd8eb46942e814888ec3ca18909303240cc00002b4e90f2c814a89944672070e9468a2ec14588c83aa17608e830c0c200002b4e35a2ae13c892a4361f00df46362c8131085c37816808202d40b600002b4dd782c0149899646d20d8f0c6b430215309503d619209503280b600002b4d7b42b3142096645b2010e8868a2f3150092c3d218f09183200c000002b4d1f22b514549764571fc8e7067e2e114288b439016408982e00b400002b4cbfe2c694d89a447b20f8ee06a22f915689103d818609103040c800002b4c63c2b4145497645c1ff8e9c6902f214f89143c217a09203180cc00002b4c07d2af93f893244d1fa8e5467e2ee14608bc3b017608b82ec0b600002b4ba6d2de15649e84952168f106dc31615a09443ca18009703000c400002b4b47c2ca14d899847020d8ef06b42f914808d03a217408b02e00b800002b4ae952c894e09ba47720a8edc6b22f614e89343d817f08882dc0c600002b4a8e12a994009604551fb8e606822ec14d08cc38616d08782b80ac00002b4a3152b7946898c4672060ec469c2f614f08e43b017f09082d40b200002b49d522b3141895044f1f90e5866c2e214708d839816908782c80b000002b497922b5143095a45a1ff0e9068a2e0142089839a17108f03100c000002b491ca2ba946097245d2038ea469e2ea14608b039c17608582c00c600002b48be72c314d09a24712038ea869c2f1141087439a17308b82c40a600002b4860e2b714349684601f90e806842ea14088b43aa17808b82c009c00002b4804f2ae943c9764682058ea86a02ec14988c43ae16a08902ac0ae00002b47a762be146498c4671fe0e986bc30b15809183cc17e08d02bc0b200002b474832cd150c9c247d20e8f1c6ba2fd15389043be17c08e03180c800002b46ebb2b3141896e4581fe8e8467c2d813c886438a17208402bc0ac00002b469042ad93e893443d1ec0dd864c2c5132883c35e15808202800b000002b463462af940c9424481f68e5c6722dd14288c839a16d08b82bc0b000002b45d7d2bb947097445a2000ea068a2ee14608c03aa17908d82e00b800002b457a82b9946096e44d1f70e4066c2da14188b439c16d08f02f40b200002b451cd2bb94789704571f98e4065e2d113a086037e16608402c80aa00002b44bd82c894e89a84722088ee46ca31015809143ba17408482ec0ce00002b446342a593d09324341f08e1c65a2df13f88bc39616808302e00c400002b440612b914449524411f78e4c6782df13c088438e16108982e40be00002b43a8c2bc949c9a046d2068ebc6a82ff150890c3ac17e09283180c800002b434ad2c2148097845b1fe8e8c67e2db141088c38817408602a80b0000) else (if i < 453 then 0x2b718732b5147498245e2050eb06aa2f114b88e83a417608d03000d000002b712ab2b2142497c4632020e9c67e2e514708ec3b818509683200c200002b70cf22ab93f09384461f88e506802e613f88b039216f09303180c800002b707082c314d899e47020b0ed46c22ff14b88d83a816c08482c80be00002b7012a2bc146098045e2030ebc6902e814908f03d418809703400ce00002b6fb4d2c494dc9a447520a8ee06c02fe14f08e43b817008982c00ac00002b6f5902ad14049444371f28dfc6482c5136084037616c08802b809c00002b6efad2c214649844541f90e546702dc13f083036e15f08302b80be00002b6e9d22bb147897e4652060e946922e514d88dc3ba17c08f03000c600002b6e4052b5142495444b1f80e4864c2cc13e089838e16c08802e40a400002b6de282bd948898e45e20a0edc6aa2fb15209083ba17608602d80c000002b6d8672b0942c96444e1fb8e586622db13f887437e16608c02f00ba00002b6d2982b614389544451f40e3865e2d714608a839416508102900a000002b6ccca2b1940c94444a1f68e3c6762dd13d887837216208382b40a800002b6c6b12e11578a024a12228f5c6f631715609183c418309103240be00002b6c0d62c2948499446d20a8f046ae30315289283d218809503340cc00002b6bb262b0940c97a45a1ff0e7c67a2d914288d03b017c09303100c000002b6b5582b8946096c45f2010e906862e614188bc3b017708f82f40be00002b6af882b7145496644b1f70e8468c2ec14508b83a217508903040c400002b6a99d2c694c09a847820e8ed06962ed14b08b03ae17208b02d00b800002b6a3b42c0148097c45a1fd8e6c6782ec14708943a017f08f83040c600002b69dbb2cb95009a64742098ee86b430314908d839e17008a02e80b800002b697e52bd146898c4722058ed869c2ec14b08d43b017c08f02f00bc00002b691eb2d315009d248d2178f206d231015789143bc17c08882c80aa00002b68c492a293c89184381ef0e1064a2c813a886c38415e08402940b000002b6867f2b6943496645e2090ea86b22f114d89103c017708c82d00b000002b680ac2b9944096c4531f50e506662de14208a037e16508582d00b800002b67ad52b9948c9924782118edc6b02f614c08c83ac17708d82d00b800002b674fb2bd946c9664541fd8e5065c2d813e888836a17008802bc0ba00002b66f372b5943c9564551fe0e6c68a2e914708c03a217b08902f40bc00002b669712ae942093a4471fb8e4c66a2da14288b439017308c82b40a800002b663892c894849784622000ea06902ec14508cc3b217a08702d80bc00002b65daa2c794c09b64782098edc6c230315188d439a16e08382c00bc00002b657f22b094309664551fc8e8c68c2e7142087c37c15c08182bc0c000002b6521e2b914589764592018ebc6ae2f314a08c03a617508a02e40b800002b64c6f2a413c091e4351f20e3865a2cd13b887038c16408602a80ac00002b646d12a1139891a4301ef0e106722d113c087838a16208782d80a200002b640da2ca14f09bc47e2070ebc6a42f914908d83a617d08f82d80aa00002b63b0e2b914689804612018e886822e714a88c83b817909303240ba00002b635652ab13f093a43d1f40e3c6722dc14308bc3aa17409203100c200002b62f9e2ba94889904612000ea46902e114108b43ba17c08d03040b600002b629b92c594a09a047220b8e986962fc14e08f03c417b08f82f80c200002b623f72b3142c9704531fa0e886742df14488b43a818009183280d200002b61e342b113f09424431f18e4c68c2f113f889837015d08282b00b200002b618552c114b89a046f2080ebc69c2fd14f09283d218308e82e00a600002b612942b414489844551fb0e6c6882e714888a03ac17608802d00ba00002b60ca42ca14d09ac4692038eb06a22f1144889438415f08302a00a000002b606b72c614ec9c847d2130f006b42f714f09103b818208e82f40ba00002b600ea2b9946897a4552038e9c69c2f714688c839417808b83300ce00002b5fb332ab940094244b1fa0e646882e7142887c37c17308d03200c800002b5f5582c0149098e4632028e9c69c2f614888e43c218308d82f80ae00002b5ef8d2bb14509604552018e8468e2ea14508c43b017d08e02d80b600002b5e9b92bb147098e46e20b8ec069e2e814508b838e17308502e40cc00002b5e3f92b7142c9624481f98e5466e2d513e88a03a416508402d00b600002b5de232ba946496846420b0ed86ae30114808d03a617408a02f40aa00002b5d8712af14049404431f58e1c65c2d313c084036a15808682b80a400002b5d2aa2b794209584501f90e486702e014708c439816b08682e40bc00002b5ccc02c994e89c047f20a0eb06962ed14888a439616707f82c80ae00002b5c6d52c614ac9924692050ea06982f614c08d83a416a08902ec0c000002b5c1022b5942894443e1f38e646762e9149890c3b617708c030c0b400002b5bb362b794689704551fb0e5c66c2d3137888039417708982dc0b400002b5b5462c694b89a847d2168f446f230e15709383cc17e08e83040ca00002b5af892b2142897045a2008e9c68a2e514788f83bc17a08d02e80bc00002b5a9ba2b7143095044a1f70e486762e2141088c39617408f82f00ae000 else 0x2b88bf12ce950c9ba47b2100f006da30f15609283ba17b09002f40b400002b8861c2bd947498045a2078eb86b830b15389203c418a09283140d000002b8803e2bb94609a647320b8ed06ac2f614b88d83a217308f02e80b000002b87a602c114b49a64772110f246d230814d88f03c417108b82d00ac00002b8749b2b5942895a4591fe8e6866a2e714488ac3b416f08502c00a400002b86eaa2c994e49c247c2050eb86942e614708b43ac18008e82e80ba00002b868fe2a693c49324441f68e306542d4139085038a16d08402b00a400002b863072cb14e09c04772090ed86ac2f014988b438e16f08682e40b200002b85d2d2b7141096444c1fd0e606742dc138882835a15807f82a00b800002b8575f2bb147c98a4632060e586722d113d086c38016108582fc0d800002b851b52a893d091a42e1e78df464e2c713b884c36e15f089829c0a800002b84bf62b313f09364361f00e206522cc13c889039616908582dc0a200002b846062cd15149da4802120ef06bc2f714d08e83b817608c02a80a600002b8403f2b5944496e45b2050ea86b62f014708d43ae17408902c00b600002b83a972a513b89424491f60e3c67a2e514608d03a816f08202a409e00002b834b52c514b499e46c2050ecc6a82ed14908c43a818009283100d400002b82f002ae140495044d1fb8e7068a2e714a88e43be18508d82cc0b000002b829092cb14ec9aa47720c0ec06ac30115489003ca18308e82fc0c200002b823422b6943c94844b1f58e5067e2e914888c03aa16d08702c80ba00002b81d562c894d89ac4832130f406e231715789483ec19b09e83480e800002b817812b8944897e4571fc8eb06aa2f614c88e03a017a092030c0c400002b811a62be148c9824652068e906822e6144089c39817a09382f80bc00002b80bb42cb14ec9bc4892108ed06b02f314188943b217508d02e00b600002b805ed2b3942093c43f1f28e386562d013b086037a16208402e00b800002b800202be949897a4602038e7866e2e214708f03c218e09282f00b400002b7fa682ae941c95a4511fb0e486682d314188a43a017808c82e80c600002b7f4b02b5944c96a4582018e8068e2ee14788a439017408c02e40b800002b7eee72b814589724641fc0e706842dd144889c38016808382d40b200002b7e9452a313b092e43f1e90df46502c513a088038016608602e40b000002b7e3622c3146c98e46f20d8ed46ba30515589443ee19109283080bc00002b7dd732c0948c98e46c2080ed06b430d159893c3e619109803380c400002b7d7942c014609904642030e886802de141888438c16c08782e00c000002b7d1f629c138090c42f1ec8e246602cd13b889c38a17008282b00a800002b7cc212b9146099247420b0eb06982e7143889438616608582a80b000002b7c64f2b394449664511fe8e546762e113f088038016f08702e40c200002b7c09c2a893f09424451f50e486742db14608a03a016f08d82e80ae00002b7bade2ab13f493443f1f40e246662d213e887437a16608902e40bc00002b7b5242b2940894a4421f00e2c6582c913a884437215e07b82980a800002b7af472bd946496c45c1ff8e9c69e2f114e89143ec19409a03280c600002b7a97a2b8144898646b2040ecc6a42e714508a838c16908402a009e00002b7a3882c914bc9a64702020e946802e4142089c394169083028c09a00002b79dd12af14009504511f80e4c6782e614488bc39617808882d40be00002b797ee2c394c49ac4762078ecc6ae30015309083d418709383180cc00002b7925429c93a491a4341ef0e1c6582cf139086c39416608b82ec0aa00002b78c902b4943094844d1f68e646822dc13c888439417308b82e40bc00002b7869d2c794a499c46e20c8ee86b82fb14a08c03b417a09103180bc00002b780f02ae13e89244391ed0e1062e2be132885837e16b08a02dc0b600002b77b112be948897845e1fe8e9468e2f114488ec3c418109483240c200002b7756c2a913c493e44a1f98e606902ef14688e03c017809103100d400002b76f7a2c614c499e47a20b8e8869e2ef14c88cc39816b08a82f40c800002b7699c2bf948c98c4612038ea86a82f114708d03b617408c02e80b800002b763e22a693a091643a1f70e506782e414408dc3bc18409203240cc00002b75e222af141c95a4451f88e4067c2e6149089c39c17309003200c400002b758392c894d499246b2030ea06822e914988b43a017609103280c400002b752472c914b099046b2018ea06902f114e88f039417108302a80b400002b74c922a813c493044a1f30e2063c2b512d081436815308082900a000002b746d32ad14049444421f60e1464c2cd137883837616108582c80b400002b741092b6941093a43f1f00e2c65a2cd137084037816308982f00ae00002b73b272be94849864632038e9069a2f014888ac39016d08b83040c600002b7354c2c294809904672040ea86a42ed14988b03a417909083200d200002b72fae29d93888f842f1ea0dd46442c9136883c36c15d08482c80b600002b729db2be147097445c2028ec46ae2f315309183c218308e82dc0a800002b724122b4140c94a44c1f90e5868e2eb14508e03c617b08902e00c000002b71e3a2bc94449724672020eb86a82f914e88e83b617e09083140c8000)) else (if i < 456 then (if i < 455 then 0x2ba01932ad94289564571fe8e6466c2df14588bc39617408c02f00c200002b9fba32c614d49a847820c0ef86b22f314c88fc3d618a08a02d40a800002b9f5b62c694b09ac47620d0f146c230915108fc3d218609303240da00002b9eff62b093fc93a4391eb0df46502d013d884c38216b08a02e40c400002b9ea2c2c1948c98645c2010eac6ac2f414a08d43aa17608a02e80b800002b9e45d2b594349664561fc0e7866c2db142888c3a217908c82fc0ae00002b9de8d2b9143496644f1f48e286722d813c888437a16508482d40c800002b9d8d72af13f493043d1f10e046562d113e888838c16508a82d80ce00002b9d3062be148497e4602018e886802e013c888437216108502ac0be00002b9cd4e2ab13d493243e1f88e4c65c2dd13b887838a17009082dc0a000002b9c76a2c414d099e4712068eb06962e714688d43a617208102a80aa00002b9c16f2c694cc9b44812180f506e631015809303e2188091833c0d200002b9bbb22b0943c95a4531f40e286562d2139085439816b08a02f00c200002b9b5d12c0148497c45e1fe0e6c67c2ee14508a039816808582a80a800002b9b0052b9948c9824682070ef06b030915289143d819009403200ca00002b9aa292c194909844571fa0e5c68e2f014a08f03be18709502fc0bc00002b9a4402bd14a09924622040eac6a42fc15088fc3be17d08f82e00b400002b99e7f2b1140c9484521f78e546602cd13e889c39c16a08c02d80a400002b998b12b9144496645e1fe8e886802de143887038215b08202a00ac00002b992e82ae13f895044e1fe8e846922ee14988e03aa17c08e03080ba00002b98d262b113e49424501fa0e4c67e2e414308b838816a08b02f80b400002b987472bc945496a4541fa0e446742dd144889c38e16a08682a00a000002b981822b193f09484401ef0dfc6482ca138084836816508182b00a800002b97ba62bc94649624511fc0e9068e2e214808cc3a817508d82e40b000002b975d62b593fc96c4591fd8e906882e914908dc3c018108d031c0ce00002b970152b8142896a4521fb8eac67e2db140887839216c08b02f40b600002b96a272c2948099447020c8ed46c82fd15408e43c617808802ec0b600002b9648c29e93a891643b1ed0e006442bc134886837815a08102c00ae00002b95e7b2df15489c648d2168f146d230f15709083c417a08c82e80c000002b958c62a993d893243e1f78e4c6662d713f888038615b08582e00b600002b952e22c494c89ae4812120f346c2306157093c3d618309203040c400002b94d292ac93d492643f1f50e3c6762d0135081837616108182a00a600002b947502be948098e46c1ff8e846942e914608ac3a017909102fc0b200002b941922ab13e493643b1f08e2065a2da13f887438616008102bc0a800002b93bc92b394309624541fe0e9c68a2ea14888c439816108402dc09a00002b935eb2bb948497a4612088ec46c430415288e03ae17708d83200c800002b930282b3945c96845e2030eb46962f414f08f03b017108c02d00b400002b92a422c114b09924631fe8e9067c2dc14108c03aa17608f83100b200002b9247f2b0940893644b1f98e5466a2d813c083c36c16008302d00b800002b91e792d094f49c847d2148f3c6e830815a09544001a409983280bc00002b918ae2b3941895844a1ff8ea46842e814508cc3b017809183000c000002b912ef2b2141095c44e1fb0e606842ea14808d03b417008e82f80ca00002b90d212b6140494e4531fa8e4067a2e2142888438216208882e80c400002b907322cc14b899e46d2040eac6822e614408d03a817408c82d00a800002b901342d395489de4812118ef06ba2fe14c08e83c218609583000bc00002b8fb802a813d09364351f08e1c6562c9133885037215f08402c00a600002b8f5ae2b9945097e4632010e706882f214a88e03ae17408782bc0b200002b8ef9e2d394f09bc4792108ee46a02f014908e83ca18f09602f40ac00002b8e9ea2ab13cc9244371ef8e2463c2c3133885036e16208602c80b000002b8e3f62ca94c89a64722050e7068e2e214208b839e17908982e40c200002b8de302b0944897c4611fc0e7c67e2e213d889039e17108b82ec0c200002b8d85d2c1148098245f1fe0e706882e514208a03b017408c02d00b600002b8d2762bf946898c4642050ea06662d6137087c39016c08902e00b800002b8ccc22ae13f494e4491f50e386802ea14208b038a16608982e80b000002b8c6e92be947096445a1fd0ea869c2f114408a83ae18009083040b000002b8c0ff2c214909984652038eac6ac2f414988ac39c17508a03040c600002b8bb202c4149c9844622028eb86a42d913a886037816307e82cc0b400002b8b52a2ce950c9c248c2128f0c6ca30d159894c3f419109082d00b200002b8af4b2be945895844e1fb0e6c68a2ef14788e43d418509382f00a800002b8a98a2b3143096844f1fa0e646682db142088837617008482b40b200002b8a3932ca94e89b247920e0ef86ca30a15989303ce18109183300d000002b89dbc2be144c96845e2050e9468e2d514008d43a617809203100bc00002b897dc2c494bc99646f2098ef06be30114c88d83b618208f83000c000002b891ec2c214949aa47720f0ef46c4308152092c3da18e09783280ca000 else 0x2bb755e2c5949497c4652098ee068e2e714508a03aa17d09002e80b600002bb6f932b3142c9564571f98e6065c2cd136885037416608482940a400002bb69b52b9147c99847020f8ef06ae2f514a88ec3a4177090832c0d800002bb63eb2b814289564491f68e5466e2db13c888039c16608702a80ac00002bb5dfe2c494ac99646120a0ed06ae2fc15109103b617708f03200ce00002bb58582a213c892e43b1f08e2c6602d913a082c36a15407c82a008e00002bb52992a813b491c43e1f28e3465a2c6132083036815e08402cc0ae00002bb4cd42b414389604541fb8e606702e614908bc3ac17108802cc0b000002bb46e42c614e89a44742098ebc69e2fc14c08d43ac17c09082f40c600002bb41272b1143496e4512000e886822e414908f03c217909483080c000002bb3b442c3149498246a2038ea46ac2fe14a88dc39217608d02f00d000002bb357c2b814589684521f40e306662cb138888037c16a08a02dc0be00002bb2fb02bd14489624591fc0e8069c2e713e889c3a017f08f03140ca00002bb29bd2c214c099e4752098f1c6d630115009043b217e09183040be00002bb23fb2b2941095845b1ff8eb46a02f314908a43a017408b02e80c400002bb1e3d2b2944c97c46c2058eb868c2e814608c438e17b08f02f00b000002bb18902ae93fc97a45f1fd8e7c6862e214308943a217508c82e00b800002bb12bc2ba144c97245f1ff8e7468a2ec14c08dc3b617a08c03080c000002bb0cef2b393f495244c1fa0e7066a2dd13f089839e17508a02bc0ba00002bb07042c594c89a646d2040eb069e2fd15209443e018e09483240ca00002bb01222c794c49ac47a2070ea06a42f314788b83b617308c02d80be00002bafb602b093f09524501f50e1065e2d413d888839016008482ac0aa00002baf5812c3149c9864622040eac6982ed14808e43b4179090831c0c000002baef932cc94b09a047320e8edc69c2fb14a88d03b8175095832c0c000002bae9bf2bb144497845d2058ea869e2ee14488c03a817c08d82e80aa00002bae3e52be945c9744662048e986942ed14a88d039817208a82e40b600002bade082bc946897a45b2000ecc6a62e614908d83b617308602d40b800002bad8672a613e492e4331eb8e0864c2cf14108a439817708b82cc0ac00002bad29c2b6947098a47220b8ee868e2e313f88dc39a16d08602c40a200002baccce2b6944496c4511f70e4066e2dc13e088838616c08c82e80c000002bac74429213308d440f1de8dc06222bd133085435815207f828409200002bac1362d494fc9984692088ec06a42ea14588a838817708b82c40ae00002babb532c0947897445a2000e786722e114408a439416d08682e40c800002bab5802bc94849764581fd0e386702de13c084c37215d07f02bc0c200002baafaf2b5942895a4441f80e506662d613c886438e16608782d40c000002baa9c82c714c89a24642048ea06882ee14788a83a617008c02d40b000002baa41f2a213a491a4301e50df86382bc136886037816208782d40b600002ba9e722aa93d89284361ec0e186482d313e88a83a617908f83080c600002ba98972c014689744561f88e4065c2cf141889838816b08882ec0be00002ba92c22bb145497a4682000e8868a2de146889838a16408802c80a800002ba8ce92ba146497c4662048eb86922ec14b88c43a617608482b40b000002ba87082bf947c9864662070eb86b02f514e08e03aa18709083140b400002ba812b2c1948498c45f2078ee86b630214a89043b418208c02f80c600002ba7b602b5140c9364481fb8e6466a2df14308a039e17c08e82c00ba00002ba758e2b8145c98046e2040eb86842df143088438416908482c00a400002ba6f9e2c994d49ac47d20f8f046b630214c09203c018208e82e00c400002ba69d12bb94649764581f88e286522ce13a084437416208802e80bc00002ba642a2a913ec9504471f60e546642ca13908a839a17108682d00ae00002ba5e6b2a913dc93a43f1ef8e2066c2e3142089039015c08702cc0ae00002ba58932bb94649824632048ebc6b42f214488dc3a416608482c80b600002ba52da2b4145c96245f2018e8c6962e714808d43b217e08c02fc0be00002ba4d1d2af14089464491f58e386602de14408c83ac17608a82ec0c200002ba47472bb941894c4491f60e1065c2ce13a086c38017208882e00a400002ba41892af142095e4491f98e7067a2d914208a838616408602c00ac00002ba3bab2c194bc9c247a20e0f086a62ef14588bc3a617c08e82cc0b400002ba35da2be148899046920b0edc6ac2f114a88ec3a217c08e03100d000002ba300d2b894689624561fd8e746822e3145088c37e16208502d80a600002ba2a3d2b494249664521f60e3465e2d513c085836a16508282c40b200002ba245a2c694cc9ae4792098ecc6ba2f514a08dc3bc17d08a82c00a400002ba1e8c2bd14609724551ff8e6467a2d7138084c37a16008702dc0be00002ba18c22b4943c96a4562008e6c6902ea14588ac38616908402ac0b400002ba12ef2bd942496e4581fb0e5c65a2d1138085037416008482f40c200002ba0d382a813e495e4511f78e586802e914988ec3aa17608e03000b800002ba07602bf94949884591ff0e846822e0141087439c17708f02e80b6000) else (if i < 457 then 0x2bce9dd2c0948c9884612058ec46a22f314608983a818209202f80cc00002bce4292ab13e894e4411f10e2c65a2dc140087438c16e08a03040b400002bcde4e2b914789784551fd0e6466c2d5139085c37e15d08402cc09c00002bcd8522cf14e09aa47020f0f006cc2fd14e090c3b217c09082f80c800002bcd2512cc95009d04872148f2c6d030815609383f018a09002f00be00002bccc772be147097c4612090eb06882f014a09083a217408b82e00aa00002bcc6c02b3940894843c1ea0de06362c4134083835615008282ac0a600002bcc0ed2bb14509744561f40e146522cb13a887037615f08682b40b200002bcbb102bd147096445b1fe0e4867c2df144889839416e08982e80be00002bcb5402ba145c9684542000e586582cf13a886838c16808602ec0bc00002bcaf692c0146c9864692078eac6902e614b09083c218108f82f80c800002bca99c2b9144097045d2018e8868c2ea143888838616a08b82fc0c000002bca3cf2b914489624531fc8eb46a82f414408ec3ba18309803240d600002bc9def2be94809924681fe8e7067c2e414708a839e17708b03080ce00002bc98202bc14909884662010e886aa2ee14988e038c16d08b82d40b200002bc92612ae13f89464441f68e346762e814688a839816d08802e40a400002bc8c832be94849784602008e8c68a2ee14608b03aa17d08c02fc0d000002bc86be2ae142095a44e1f68e586862e714508c43ae17308d02e40b000002bc80ef2b7143495e4622010ea06982f114a88f83ba17208782d00b000002bc7b372a693e89424451f58e606842db13f889c39617108f02f80c800002bc756c2b914609804612028e906902ee14708d03ae17208882f00ca00002bc6fa82b113e49384491f68e146562cf139886c38216708982f40ba00002bc69c12c514bc9a847520f8ef06b22fe151090c3c618408d82cc0b600002bc63cf2cb94fc9c247e2108f046c0308154090c3b816b08482d40b000002bc5e102b113fc94e4441f60e106402c1139086c37a16d08902ac0b200002bc58362bc14349584521fa8e4c6702e314888c03a217b08e02f80c600002bc52442ca14bc98445f2088ec46ac2fc15108e03a216e08882ec0b200002bc4c892b314389744611ff0e786862e514988b03a617808f83180c200002bc46bc2bd94a89ae47720e8ee06a82f314a08c43bc17e09483140c400002bc40cf2c714c09904652068e8868a2ef14788c83ac17508882fc0be00002bc3ae42c214a899a47e2138f386e430815689443d418d096030c0c600002bc35192bb14409704501f60e5c6802e0140889c3b4176090832c0c000002bc2f572b0940093c4361ea8de064a2c613e087838016708502d40b000002bc29982b214189484411ef8df46422c713a086837816508502c80b400002bc23e12ac13ec94244b1f88e606762e714388c03b417108c82e40b000002bc1e112b7944c96c4592060ea46a82ee14808a839a17508182b80a800002bc185a2b0942496e4602030e986882e1143088838e17508c82ec0b200002bc126d2c8948c9904732070ed46be2ff14b09143ca19009283280ba00002bc0c9f2bb947898645c1fe8e846902ea14a08ac39417d09202f00ca00002bc06e72b313fc95c4511f90e6867e2eb13e884037a15807e82b00a000002bc012c2b394189584461f68e286622d613b883037216708502f00b200002bbfb2f2c7947098445e2030ecc6b42fc14b88c03b818109083180c800002bbf54e2bf94889984702050eb46ae30515409343c017f09302ec0c400002bbefa42aa94049524411ee8e246622dc14688a439a16808602cc0ba00002bbe9c52bf14509804622020e886942e514888c439217f08782c80be00002bbe3e62be149898247020a0ef86c42f914b08d83aa17e090030c0bc00002bbde0b2bf949c9984672048e7c6922f014c89103bc17a08902a40a400002bbd8402b594309604531fd0e7868a2e614488e43a417108302c80ac00002bbd2712b914609724551f80e4066e2dc1418874368156080028409c00002bbcc9b2b714489824622020eb069e2ee14488b039216b08b82e40a200002bbc6d72af142c95c4401ef0e2466e2d514108a039417008702c00aa00002bbc0f42c114a89a447820f8efc6c42fe150891c3d618e09483040ba00002bbbb222b914409584471f78e4067c2e814688e03b017b08d83280c000002bbb5392cb94d49bc4842078eb86b430115709183ce17a09002e009600002bbaf772b5944896c4612038eb069a2fa14888d83aa17e08e82f40c800002bba9a62bd145c9744581fb0e886822e814888b43aa17e09582fc0b600002bba3ee2b0942894a4421ef8e2c6602de13c086c38816a08702a00b600002bb9e192b514709784632060ebc6a42fc15289143d417f08e03140c000002bb982d2c594e09a24722130f286c230815008f43d018009683280c000002bb92632b2142093e4461f48e246702e0141889c3a416108902dc0b400002bb8ca82ad94089304481f18e4466e2da142089c3b416f08b02f00d000002bb86c82c2148497e46b2078ed86be2f914f89103d618509083180ca00002bb812e2a3940895e4571fd0e7c6862e614508ac39416808582b80b800002bb7b4d2c194b099246d20c0f186c82fe152092c3c418608d82c00be000 else 0x2be06572c0149499e4692070eac69a2ec14908c83aa18009002f80c400002be004c2d515089c84832110f146e630e152091c3be18109082f40a800002bdfa7b2b5145495c4562020eb869c2e813d088c39016d08582d40b800002bdf4bd2a993f493c4391ee0e2c64a2d313e886437615b08782cc0a200002bdeeff2b614609764682068eb869e2f1142889039e17008c03080c800002bde96e29713548ec41e1e28de06402c1137883c37816908482d40ae00002bde38c2c494909a446e2070ea06922e514808cc3be17f09202e40c600002bdddba2bc94849844632070ec06c02f614a08c03ae17108b82f00c000002bdd80a2ab13e09324391f00e0c65c2d713e086c39016f08a02dc0ac00002bdd2342bb947897a46a2068edc6b42f414f08e03be17d08902f40c400002bdcc622b514609684612098ed86962f614908e03c417d08f83200ca00002bdc6a22b114389584531f68e6067c2de143088c37816408182c40b600002bdc0d42ba944c9724642008e886a22f214d08dc3ac16c08b02f80d200002bdbb152ae140494044b1fb8e4466c2e314288d03ae186092031c0ba00002bdb51d2c994d09b447a2150f286ca30815108fc3c618109383280cc00002bdaf542bb145496c44a1f18e2467c2e614388d439c17c08e03100ba00002bda99c2ae142495244b1fb8e706822e814308d03a417008b82d40b400002bda3f32a813dc9344351ed0ddc6402c3139086c38215807c82b80a000002bd9e1d2b8940896245b2008e7067a2db140087c38416708402d80b200002bd98342c314c89904652028eb06922e914908c03ae17a08f82fc0b600002bd92682b994609784591fb8eb06842e514988c439416608782e00b200002bd8c922b9147c99c47720a8ed86a02e714908d43aa16b08502ac0a600002bd86af2c394b899446d2088ed06b42f014888c43a817208d03080cc00002bd80c92c194c49ae47a20f0f046aa2fa14d08f43b819009a833c0d000002bd7b042ba945c96a4551fe0e8c69c2ed148889839617108702e80b800002bd753e2b494549764652000e6867a2e4141088839016b08702dc0c800002bd6f692b6943096c4571fd8e806822d814408a838e17008c03000be00002bd699b2b593fc94e4561fc0e886862de14008903a015a08102b80b200002bd63b72c294909864612028e9069a2f114688d43aa16c08a82e80b600002bd5dff2a993989264391f48e506802dc13f88b03a217408982e80ce00002bd583a2b194249564451f28e2064a2d213d885438c16c08402cc0ae00002bd526f2ad94009584481fa8e606722e614588c03b417b08982e40c200002bd4c822c4948c98c4622058ec06862e114308a438415b07e82a009e00002bd46af2b6143c9564512018ea46962f814988bc3a416a08502d00bc00002bd40d42be945c9864621fd0e746962e914288b039c17a08b83140c600002bd3add2ca15009b647820b0ed46942ea14608a039216c08e82d80bc00002bd35112af940095444d1fd0e9c67a2e114688bc3a017608902d00ae00002bd2f562b2942095e4591fe8e9067a2ea14488b43c617d08e02d40b600002bd29872bd94c099846a2058ea069a2ea14788b83b017d08f02d80b800002bd23bd2b794489704531f80e586842e2141089039217008882c00b200002bd1e0e2aa13cc94a44a1f18e1c65e2cb139885837416708302b40ac00002bd184e2b314289844692050eb86aa2f514a08d838e16c08e02f80bc00002bd127f2b9144095e4592018e846922eb145088c39216f08682e80b200002bd0cad2b7142c95c44d1f40e486802e114588b039e17609003000d800002bd06e72b494409624501f60e586902f214c08d03a216708402dc0b400002bd011b2bf94589764581fd8e5465c2c913c885438e15d08682dc0b200002bcfb452bf94b49984672090ec06a22fe15509203d218b09083080ca00002bcf5902ab940095044d1f70e5866a2e314188bc3a617308682e00ac00002bcefbf2bb946c97e46d2060eb068e2e914488c83ae17a08a82dc0be000)))))))))

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



private theorem b455704 : covered 455704 455818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b455818 : covered 455818 455933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b455933 : covered 455933 456047 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456047 : covered 456047 456161 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456161 : covered 456161 456275 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456275 : covered 456275 456390 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456390 : covered 456390 456504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456504 : covered 456504 456619 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456619 : covered 456619 456733 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456733 : covered 456733 456848 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456848 : covered 456848 456962 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b456962 : covered 456962 457077 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457077 : covered 457077 457191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457191 : covered 457191 457306 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457306 : covered 457306 457420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457420 : covered 457420 457535 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457535 : covered 457535 457649 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457649 : covered 457649 457764 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457764 : covered 457764 457878 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457878 : covered 457878 457992 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b457992 : covered 457992 458106 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b458106 : covered 458106 458221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b458221 : covered 458221 458335 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b458335 : covered 458335 458450 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b458450 : covered 458450 458564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b458564 : covered 458564 458679 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b458679 : covered 458679 458793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b458793 : covered 458793 458908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b458908 : covered 458908 459022 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459022 : covered 459022 459137 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459137 : covered 459137 459251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459251 : covered 459251 459366 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459366 : covered 459366 459480 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459480 : covered 459480 459595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459595 : covered 459595 459709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459709 : covered 459709 459823 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459823 : covered 459823 459937 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b459937 : covered 459937 460052 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460052 : covered 460052 460166 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460166 : covered 460166 460281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460281 : covered 460281 460395 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460395 : covered 460395 460510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460510 : covered 460510 460624 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460624 : covered 460624 460739 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460739 : covered 460739 460853 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460853 : covered 460853 460968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b460968 : covered 460968 461082 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461082 : covered 461082 461197 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461197 : covered 461197 461311 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461311 : covered 461311 461426 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461426 : covered 461426 461540 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461540 : covered 461540 461654 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461654 : covered 461654 461768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461768 : covered 461768 461883 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461883 : covered 461883 461997 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b461997 : covered 461997 462112 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b462112 : covered 462112 462226 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b462226 : covered 462226 462341 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b462341 : covered 462341 462455 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b462455 : covered 462455 462570 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b462570 : covered 462570 462684 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b462684 : covered 462684 462799 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b462799 : covered 462799 462913 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b462913 : covered 462913 463028 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463028 : covered 463028 463142 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463142 : covered 463142 463257 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463257 : covered 463257 463371 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463371 : covered 463371 463485 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463485 : covered 463485 463599 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463599 : covered 463599 463714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463714 : covered 463714 463828 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463828 : covered 463828 463943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b463943 : covered 463943 464057 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464057 : covered 464057 464172 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464172 : covered 464172 464286 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464286 : covered 464286 464401 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464401 : covered 464401 464515 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464515 : covered 464515 464630 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464630 : covered 464630 464744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464744 : covered 464744 464859 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464859 : covered 464859 464973 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b464973 : covered 464973 465088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b465088 : covered 465088 465202 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b465202 : covered 465202 465316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b465316 : covered 465316 465430 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b465430 : covered 465430 465545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b465545 : covered 465545 465659 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b465659 : covered 465659 465774 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b465774 : covered 465774 465888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b465888 : covered 465888 466003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466003 : covered 466003 466117 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466117 : covered 466117 466232 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466232 : covered 466232 466346 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466346 : covered 466346 466461 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466461 : covered 466461 466575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466575 : covered 466575 466690 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466690 : covered 466690 466804 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466804 : covered 466804 466919 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b466919 : covered 466919 467033 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467033 : covered 467033 467148 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467148 : covered 467148 467262 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467262 : covered 467262 467377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467377 : covered 467377 467491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467491 : covered 467491 467606 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467606 : covered 467606 467720 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467720 : covered 467720 467835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467835 : covered 467835 467949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b467949 : covered 467949 468064 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b468064 : covered 468064 468178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b468178 : covered 468178 468293 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b468293 : covered 468293 468407 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b468407 : covered 468407 468522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b468522 : covered 468522 468636 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b468636 : covered 468636 468751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 455704 468751 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b455704 (joinCoverage b455818 b455933)) (joinCoverage (joinCoverage b456047 b456161) (joinCoverage b456275 b456390))) (joinCoverage (joinCoverage b456504 (joinCoverage b456619 b456733)) (joinCoverage (joinCoverage b456848 b456962) (joinCoverage b457077 b457191)))) (joinCoverage (joinCoverage (joinCoverage b457306 (joinCoverage b457420 b457535)) (joinCoverage (joinCoverage b457649 b457764) (joinCoverage b457878 b457992))) (joinCoverage (joinCoverage b458106 (joinCoverage b458221 b458335)) (joinCoverage (joinCoverage b458450 b458564) (joinCoverage b458679 b458793))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b458908 (joinCoverage b459022 b459137)) (joinCoverage (joinCoverage b459251 b459366) (joinCoverage b459480 b459595))) (joinCoverage (joinCoverage b459709 (joinCoverage b459823 b459937)) (joinCoverage (joinCoverage b460052 b460166) (joinCoverage b460281 b460395)))) (joinCoverage (joinCoverage (joinCoverage b460510 (joinCoverage b460624 b460739)) (joinCoverage (joinCoverage b460853 b460968) (joinCoverage b461082 b461197))) (joinCoverage (joinCoverage (joinCoverage b461311 b461426) (joinCoverage b461540 b461654)) (joinCoverage (joinCoverage b461768 b461883) (joinCoverage b461997 b462112)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b462226 (joinCoverage b462341 b462455)) (joinCoverage (joinCoverage b462570 b462684) (joinCoverage b462799 b462913))) (joinCoverage (joinCoverage b463028 (joinCoverage b463142 b463257)) (joinCoverage (joinCoverage b463371 b463485) (joinCoverage b463599 b463714)))) (joinCoverage (joinCoverage (joinCoverage b463828 (joinCoverage b463943 b464057)) (joinCoverage (joinCoverage b464172 b464286) (joinCoverage b464401 b464515))) (joinCoverage (joinCoverage b464630 (joinCoverage b464744 b464859)) (joinCoverage (joinCoverage b464973 b465088) (joinCoverage b465202 b465316))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b465430 (joinCoverage b465545 b465659)) (joinCoverage (joinCoverage b465774 b465888) (joinCoverage b466003 b466117))) (joinCoverage (joinCoverage b466232 (joinCoverage b466346 b466461)) (joinCoverage (joinCoverage b466575 b466690) (joinCoverage b466804 b466919)))) (joinCoverage (joinCoverage (joinCoverage b467033 (joinCoverage b467148 b467262)) (joinCoverage (joinCoverage b467377 b467491) (joinCoverage b467606 b467720))) (joinCoverage (joinCoverage (joinCoverage b467835 b467949) (joinCoverage b468064 b468178)) (joinCoverage (joinCoverage b468293 b468407) (joinCoverage b468522 b468636)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 455704 ≤ index 875000000/512 := by decide +kernel
private theorem starting_value : fast 875000000=44796869 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 875000000=44796869) (n : ℕ) (low : 875000000≤n) (bound : n≤900000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=875000000
    · rw [first,anchor]
      exact starting_value
    · have past : 875000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤900000000 by omega)
        have within : index n / 512 < 468751 := by omega
        have lower : index 875000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤900000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ875000000To900000000
