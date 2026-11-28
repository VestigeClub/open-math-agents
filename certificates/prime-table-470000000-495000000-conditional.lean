import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ470000000To495000000

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




private def radical : ℕ := 0x7b3494088241f42e9c5f1b88918dda856c7cf46870c6c5f8f72ceae66d2db328c8f86e685953b419649acdf1dcebceda9fccc428752d8dd9045bd6f3c363ef2b90d09759284ced08a688045972adf59b1e6f0c2b1702da396bf921ae146d1e6e720570e8caa699da63281c1a8bd1ee2ceeafebea31d9b3468d6c2e1fcacb6eca9d8b5e8d30a8edd95f5be3bb24f8f19bc7c1d094085f87eb4360eee2e2889c23838ec2f4f910886680fcb764d16f7b5b631b6e47d7f27c4c4b3c7f66bb099c1c25ae5321cdd52d73b32ccbe186ef9e6ea926ebbd1d597787ef6caa714ad381e9e73761e5bf32820c185a03965e33987f3a8433964a8e07c3a602eb454db088919e8591d9fb64a7a88b27485d46ace1694cc8a98f09519f88b18a711991d1954690045e96e0f37b26913b7394ecb8ed2e4259a9fe1340dc619aa5f0b917d8fa0267610962f1c1425e99bb3dd10826d833d01245cc6472517a80f058c713aa6e84c49521b71b7387178d00d29d30008e903ba4dcb9ea9a7785073e950df5f6ddb5aa85b7186fad435baa6c83733dffb913708778761f9984dff8413973c9c03d4acfed159d4479ad348c6187d6a41172b27ed39cd9b392d3e29890e6d2e10e51cb9dedac78b6cd299d01aac057e4f5758cf60ecfe475cb172666aeea85d076b79ef878b6e5740ba457acd810c82a4b2f29324e76a6f5ed10a6e25d33532f46ba781722eae0150ff19426f201d516c591cf1996cc6d924766255251141b4c257454be90b9d2f62ada5d801671d9fb52bd97c4b262840e852e522aacdb34b666259d43f7883f336903fd282c88d4c25ba99cdd253e3b9ea30b3d83ec285cbb55a200cbf1a572e8e427acc572602df92e8e3c0093ffab9dd747ff710b5c24a8510ee4b3c753cdde8eeedfb84f552c118be375de863e292b1c19972c98c1452653f4b1565703af8db3fe8d99cfd672daba436a212d2a5bc7c287dc3dfd3a17699bfe1d630af5c269880e180d44141aade4a8be2ed05eb112f4422e2c05703cea2af751d1c3427e43317ad0560d32d568a25217108c151634aa03164277a348916e0dedee37a5eeebdf2d653f800714475e243b10930b5382ede34afaa06cdf8379767b806611fd41b4b84847573406df58e968fec7dda3711d74b24640632ee2f301c6a7e97deaebec2b6fb2a946159d74c148403db40da853ac01d252a61c1f4ba6f2d196c3d617122312ea62b31275a17a68edfa1bfccfb01b069ea9a48d1bbaf38c236457ef099f3870e79da337bd8449a15eb741ee0fd94737346145bfcc3c8217cc13a84e0f7420490efe9c231297cad306d5a1e388031f89cdae6e4a1727822f27a91eb96c247690b9997671697ea629ed07e06a21e217616551e0df4b93a76c68ed5ac4f36650e32fa058c27f89b95a331695400c28ac90e6abc5f48726af9686287fada6d598183bf5d6def318b549e48690559c809fb577be261634dc1254d1affc5340eb2e432266ecc28e0650b4d76926c4458b35147a2be80b248012566f67064f31627a41c3da263b241e54c7c1d60261b2a1130f3dccb544ab3068ddf875f63e46c8775d5c62890a70e7ef26d44681958d8ebcb51120179f65bdce99ee00c1871c73b7c7aee2659a4ee84ee33d79cd81241b795925f51602ca3e0051148cf22b211eec6cee0e20bd19ba4256eedcf29f92afecdf52bcaedcb295fd70281523c2892e2974d70b0e13778a9d73708eaced570bf927b7d9d574c188637d659bf1f005c650079ac3a1307ea99ebfecc95a34584871cc6c9ea2b2583c2c72ebda93c2c4c2f950f0db6b4d2a3b6162a07ec852188674678b9fa3d6123980b55a6139a8f873e69c6069aaa056939503e2a5042900ed28b6948eba974658422acb2a606f74384394f2921fdc9c709396dddac1bb6c9d39e3e104a960010d7ab9995fcf644c5160257bfd0d090cd08416846e814817cd1f03a65f2a5f5757faaf60476e243bd064ecd2fa5bd9bd65279008dceafbd3e67109144e724d78d38bc707a77af31353f51ef6cb7050894ac4ebb5a8d54e5717e74970d447c667b399e29ba76ae9a628439d3e378c6c7612d1c7fded33fbcc736ec703ca5dfd7b245783247c78709437613f048b0891e4061aeb1c602d4bed9753be6d2e74ad17202e1d19b634e1d78e38ad57a5d3f8e492a205dfa90e0c13dcda6e525d3940d7951a947e66cd81a207426035650aa6324a73cd5bd01cd60cbaeec90a0be5f4f8fb3ee50ea5c1e381eab07788116c269de24f7195ea0d6f15d4d0f5fe2680ed734c824fdf92cf46fa21dcd6ba697ede661f8af99a7b27aeeb30b12421121eeafa55cbc41f65c82c0b902e5bf4ba0f919a591719fe461c28349c597eea171b45948a48f075fd9bb722388656f0a18a2e9082ba7b1e7d494d40f327da8bb51df5c434657e118f2a4013fd0cc11edd34ef0f0be427878d4237548fa6c6a4fb071039f11009a458ae4228c7478b6bf0fe980170437422cd36d3fbb6c466ec248650e5f258e62125690ca45fcba8eb613c7ed38c0c92fd6bdf642f1be11903cd89f0dcae3376d6e45cf25058125b2ad309a46589f22d1235be78813536b07db19105748ad28eb6e8c7269814226d4e2730609e9aa87a4f2714bc511a2bbca1a5c7b361300d9485a9b67a32fce14503bafa28406578cac10e0fc8aef9e45aff03cc35ded4a1198e2027b196987c6be13296f5b1e240595a2e4d310bfca4c410cb32350ac3f9e506f77c19da2c6e41916eb625678723d14756ca98e13467a5575323d5a0112807eaddff2876d2fc94cc7546470a480ee3ea7ce7161a89785cad56b98fc7d23c6a521af4ac18a5eb7fd4b1dd88a3036122fab90230e3285a62324316c9e7fa535a4189c9f9faa161ba2afb7c38d4a0bda4ecd256f73fac3883209dd9be33923f39e107f0d160b7b6ac99d7e384844dc4df72d170e9ddb77acf7b935ecf975a099a98d034cdebfb5ec363dbf05a1bec2792d270c009ddf18a4e1f463ef33270323779ee6d5baae1a36566b69c8e2d94107637f3ad49a1e4f260a07c84cd2738c0a1df15b7e397d20d5238ddcdecf2e5dce78628db3c98cafbd9d2bd7b6d89f1cf5639435763c9fe1b45e75b2f8cc85b7b6da8dfa6633d15302d3f5edd47a2a600541fd6d7f3d21e9e52cf1aec504b827d62423a9c82f2f948464e3c09024681ce40d441b4ea82be418977501c84cd25573df0eccd951479e662770d7824b257cea23baa00cbee780858d06135b39da53c48a71f903422147be69925b2d270b6b2798a2b81a694e49ca722bda63bfa1f704d49350e5cf4485ca7c15972db7b4c48b8f4be0a5a989b7c3e9ae629fd08bf81db0a9d5c5ac786a0d46f44ab80cca8728a52086558ca52332809d8f15775009ee5c720ee6fcedf6f519a9234b86f90861199697ec3e5616ee1c842c638162a24e4007e9d9002aa3c2403e5ea04a6ae461dce81031e45bd034d16aec09c92161510245496ce6b0ddcc82e5ccf0628ba0535b7c15e4ce495b31730074129eab3b48303efd315b909326b20a2429c365a36984bf4210c7acb2b28863ebc532f2d3b17124dd236c5138b2b279fb852d4988ba5dfb1481a6f13512ac02ea8992bb543968ac87964ca260a7237b58f858711deca96c10d38d7558af3da5c3d0ad61efedbc65938764cb38e2e6596efe041b0e364fde6af76854d6701e0ca3963d5f0a7fb4f1236e60db662243db05dc7fb8ec9c582c81327504b3d2d74edc1325c3826edef4115a7a9531c089db55d8ba1ff326034d6fe07c19ca5f96838ca64fb87e102d940bbf4af37dafd6c5e811e08ba7753ce27d30ab095234ae91a17a600b94cd1e77656752ba9cb2a79daed6949f0dbee48d615292134eca6a4ebb3a0994f2d316ce6ff8f334a1f88798802fdc152beedd9d3d79f6841aa7ffd07930a93323b9f2bab600324ed7a720917b9e332a707744604c2efb9b182896aaf368c0fa01703fc545462288d5e752cec16c09c778f48b4d89497f96aa71680c386b6b5797f9bfcf8abf1a89910d6d7cce6d30e962a988c8542bbda4658149041f85d0b73a2d959bfad7ada62020106e8021981d20ba11924246d39fd00dad5006e4c74e376e5e0b417ee23e329bffdd9d90bd0d8a0baa05f8e10089b33ccfd4e793d5bd71b2ecfb0f4d20467d0935d3b58cd89c0e174ce43c0878e435e137a829b1565db685cc35630ad4666c645e62c0622099342f6377d97f9acf98db8a68a8c3039965116bfcf2d16b8680922e609df8da138cbabd2ebdf68f1d07f817fd203486c4e5d815fdb705bc47967fcfd3c4948d6a3b2e8e93ffb87fa9f56cb918185df42816afea1a744ef165057dceb48fb967013c2bb228c79a4b264d88e5dafc41ac21195a9503f35d460ecc4519ab1ff1a046bf43461aa76ea56381ebd6f518cc9c45ad5b464b7307525fca5bd5f4a65072801b36a8c50d9175daa13eb0bc85fa257aff83c90c25d1b0f6948f20d5888bdbee0bbdb9f259df9f4f0c860274a63f5880eb1e232966d9249f16a889f50b5be7b1f9d96805b17fc100ef270f4128b05f9410c79cf2bf492b9824bd8b2e1691ac61b6e839c564dc10ff24ecdb48911c9ccd6d85350b3d9b814177b082a484e2a5614ad8cb8c2a69f0d0e0a768a0bce6a2ef2b4c03712fab12f633c4bc152ef0204cf857bfabec410df69364736c6e892b3b871e5b4b8fc71aaa4e38ad7b9d621a51ebb169a0496595e4a6d950a1ac601127d7a1aa2c5e4769ebf2e6759ef664555d5930d50b8f76aaa33ecf951eda78818ddea86b946bf84c6772b9cb61d6e4e08983907fe62203a7dd1d55ee1d1f4efe71a49cc7eba21edd83563668f15d73fe098707ddc48b832fc5204ed5e0404624a35b92cadad35e5cee5dc1d0e3bdbfe18c72915914855a29b8ea40e3643ae5baedd717ef99653712d71b0dd26044e5f8899a4ba5b954c468e13cae1c1151d3dbe278ed79d9f66ab25aa811782dd2a4b1a40ede08872caabe487d20ec6220ee18a57499f956464ee3d28923b4480e1d6cd854bdcd680a85e0af299ef86e869eb5c8ea36264e73e5b7c5312111f45cafc021e749b61f0c0b48e5d9bc63551d2e71d8935e1885b8920b6fd447601676a8f5bcd96741cc9742156909f20b3ec783cec0e0bc3cab115ec1268337f8006ed66ac130406ae0dbe83e7fb4cc84f4b351d3f1c2c919b6e003a69c2ef6e0975482a4935613965be395d9c2d8e238f7b33933cdb5771e756f4e07c33985264ed3ab38016bd8011bcd50bb629b98f408650ab993f94fd40a4dcd030447cdca8bb82a086d210a4d84200ac23002dbc87bedafd2c010e4871d60bf8b0af349cb4438112623d49a6c7d92d2818d4c870245af0624d48f5fa6f421790136931b0077c53352c4e9406f21404df59ad068ba42a452a4d51eac911125b24a774ea1294aa94783b30e17967afca29c177fbc419140f62f3a739239d62074b65a13c3892d60d41146349ac53e48b041a74793aa2eb8274133df6f3723e185f80cf9eb4e66b723c1f93dd64599c0da64778c047ef56529f5e259d18826fc46d642c43a2570cd7a629a0eb2a64b6419fd092d0d1b2fa2364e8c506

private def light (n : ℕ) : Bool :=
  if n≤149 then decide n.Prime else n.gcd 380892263763056972698595524350736933545970238573408427883655838887865527498969322620843829924502074302514052524979028027751108334657896696442372994639480443832950613971571859528835715269633083149369445271480789636247481797836800000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤22248) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 149 = 380892263763056972698595524350736933545970238573408427883655838887865527498969322620843829924502074302514052524979028027751108334657896696442372994639480443832950613971571859528835715269633083149369445271480789636247481797836800000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 149 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤22248 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 43 := by unfold smallValid; decide +kernel

private theorem sp43 : smallValid 43 43 := by unfold smallValid; decide +kernel

private theorem sp86 : smallValid 86 43 := by unfold smallValid; decide +kernel

private theorem sp129 : smallValid 129 44 := by unfold smallValid; decide +kernel

private theorem sp173 : smallValid 173 43 := by unfold smallValid; decide +kernel

private theorem sp216 : smallValid 216 44 := by unfold smallValid; decide +kernel

private theorem sp260 : smallValid 260 43 := by unfold smallValid; decide +kernel

private theorem sp303 : smallValid 303 44 := by unfold smallValid; decide +kernel

private theorem sp347 : smallValid 347 43 := by unfold smallValid; decide +kernel

private theorem sp390 : smallValid 390 44 := by unfold smallValid; decide +kernel

private theorem sp434 : smallValid 434 43 := by unfold smallValid; decide +kernel

private theorem sp477 : smallValid 477 44 := by unfold smallValid; decide +kernel

private theorem sp521 : smallValid 521 43 := by unfold smallValid; decide +kernel

private theorem sp564 : smallValid 564 44 := by unfold smallValid; decide +kernel

private theorem sp608 : smallValid 608 43 := by unfold smallValid; decide +kernel

private theorem sp651 : smallValid 651 44 := by unfold smallValid; decide +kernel

private theorem sp695 : smallValid 695 43 := by unfold smallValid; decide +kernel

private theorem sp738 : smallValid 738 43 := by unfold smallValid; decide +kernel

private theorem sp781 : smallValid 781 43 := by unfold smallValid; decide +kernel

private theorem sp824 : smallValid 824 44 := by unfold smallValid; decide +kernel

private theorem sp868 : smallValid 868 43 := by unfold smallValid; decide +kernel

private theorem sp911 : smallValid 911 44 := by unfold smallValid; decide +kernel

private theorem sp955 : smallValid 955 43 := by unfold smallValid; decide +kernel

private theorem sp998 : smallValid 998 44 := by unfold smallValid; decide +kernel

private theorem sp1042 : smallValid 1042 43 := by unfold smallValid; decide +kernel

private theorem sp1085 : smallValid 1085 44 := by unfold smallValid; decide +kernel

private theorem sp1129 : smallValid 1129 43 := by unfold smallValid; decide +kernel

private theorem sp1172 : smallValid 1172 44 := by unfold smallValid; decide +kernel

private theorem sp1216 : smallValid 1216 43 := by unfold smallValid; decide +kernel

private theorem sp1259 : smallValid 1259 44 := by unfold smallValid; decide +kernel

private theorem sp1303 : smallValid 1303 43 := by unfold smallValid; decide +kernel

private theorem sp1346 : smallValid 1346 44 := by unfold smallValid; decide +kernel

private theorem sp1390 : smallValid 1390 43 := by unfold smallValid; decide +kernel

private theorem sp1433 : smallValid 1433 43 := by unfold smallValid; decide +kernel

private theorem sp1476 : smallValid 1476 43 := by unfold smallValid; decide +kernel

private theorem sp1519 : smallValid 1519 44 := by unfold smallValid; decide +kernel

private theorem sp1563 : smallValid 1563 43 := by unfold smallValid; decide +kernel

private theorem sp1606 : smallValid 1606 44 := by unfold smallValid; decide +kernel

private theorem sp1650 : smallValid 1650 43 := by unfold smallValid; decide +kernel

private theorem sp1693 : smallValid 1693 44 := by unfold smallValid; decide +kernel

private theorem sp1737 : smallValid 1737 43 := by unfold smallValid; decide +kernel

private theorem sp1780 : smallValid 1780 44 := by unfold smallValid; decide +kernel

private theorem sp1824 : smallValid 1824 43 := by unfold smallValid; decide +kernel

private theorem sp1867 : smallValid 1867 44 := by unfold smallValid; decide +kernel

private theorem sp1911 : smallValid 1911 43 := by unfold smallValid; decide +kernel

private theorem sp1954 : smallValid 1954 44 := by unfold smallValid; decide +kernel

private theorem sp1998 : smallValid 1998 43 := by unfold smallValid; decide +kernel

private theorem sp2041 : smallValid 2041 44 := by unfold smallValid; decide +kernel

private theorem sp2085 : smallValid 2085 43 := by unfold smallValid; decide +kernel

private theorem sp2128 : smallValid 2128 44 := by unfold smallValid; decide +kernel

private theorem sp2172 : smallValid 2172 43 := by unfold smallValid; decide +kernel

private theorem sp2215 : smallValid 2215 44 := by unfold smallValid; decide +kernel

private theorem sp2259 : smallValid 2259 43 := by unfold smallValid; decide +kernel

private theorem sp2302 : smallValid 2302 44 := by unfold smallValid; decide +kernel

private theorem sp2346 : smallValid 2346 43 := by unfold smallValid; decide +kernel

private theorem sp2389 : smallValid 2389 44 := by unfold smallValid; decide +kernel

private theorem sp2433 : smallValid 2433 43 := by unfold smallValid; decide +kernel

private theorem sp2476 : smallValid 2476 44 := by unfold smallValid; decide +kernel

private theorem sp2520 : smallValid 2520 43 := by unfold smallValid; decide +kernel

private theorem sp2563 : smallValid 2563 44 := by unfold smallValid; decide +kernel

private theorem sp2607 : smallValid 2607 43 := by unfold smallValid; decide +kernel

private theorem sp2650 : smallValid 2650 44 := by unfold smallValid; decide +kernel

private theorem sp2694 : smallValid 2694 43 := by unfold smallValid; decide +kernel

private theorem sp2737 : smallValid 2737 44 := by unfold smallValid; decide +kernel

private theorem sp2781 : smallValid 2781 43 := by unfold smallValid; decide +kernel

private theorem sp2824 : smallValid 2824 43 := by unfold smallValid; decide +kernel

private theorem sp2867 : smallValid 2867 43 := by unfold smallValid; decide +kernel

private theorem sp2910 : smallValid 2910 44 := by unfold smallValid; decide +kernel

private theorem sp2954 : smallValid 2954 43 := by unfold smallValid; decide +kernel

private theorem sp2997 : smallValid 2997 44 := by unfold smallValid; decide +kernel

private theorem sp3041 : smallValid 3041 43 := by unfold smallValid; decide +kernel

private theorem sp3084 : smallValid 3084 44 := by unfold smallValid; decide +kernel

private theorem sp3128 : smallValid 3128 43 := by unfold smallValid; decide +kernel

private theorem sp3171 : smallValid 3171 44 := by unfold smallValid; decide +kernel

private theorem sp3215 : smallValid 3215 43 := by unfold smallValid; decide +kernel

private theorem sp3258 : smallValid 3258 44 := by unfold smallValid; decide +kernel

private theorem sp3302 : smallValid 3302 43 := by unfold smallValid; decide +kernel

private theorem sp3345 : smallValid 3345 44 := by unfold smallValid; decide +kernel

private theorem sp3389 : smallValid 3389 43 := by unfold smallValid; decide +kernel

private theorem sp3432 : smallValid 3432 44 := by unfold smallValid; decide +kernel

private theorem sp3476 : smallValid 3476 43 := by unfold smallValid; decide +kernel

private theorem sp3519 : smallValid 3519 43 := by unfold smallValid; decide +kernel

private theorem sp3562 : smallValid 3562 43 := by unfold smallValid; decide +kernel

private theorem sp3605 : smallValid 3605 44 := by unfold smallValid; decide +kernel

private theorem sp3649 : smallValid 3649 43 := by unfold smallValid; decide +kernel

private theorem sp3692 : smallValid 3692 44 := by unfold smallValid; decide +kernel

private theorem sp3736 : smallValid 3736 43 := by unfold smallValid; decide +kernel

private theorem sp3779 : smallValid 3779 44 := by unfold smallValid; decide +kernel

private theorem sp3823 : smallValid 3823 43 := by unfold smallValid; decide +kernel

private theorem sp3866 : smallValid 3866 44 := by unfold smallValid; decide +kernel

private theorem sp3910 : smallValid 3910 43 := by unfold smallValid; decide +kernel

private theorem sp3953 : smallValid 3953 44 := by unfold smallValid; decide +kernel

private theorem sp3997 : smallValid 3997 43 := by unfold smallValid; decide +kernel

private theorem sp4040 : smallValid 4040 44 := by unfold smallValid; decide +kernel

private theorem sp4084 : smallValid 4084 43 := by unfold smallValid; decide +kernel

private theorem sp4127 : smallValid 4127 44 := by unfold smallValid; decide +kernel

private theorem sp4171 : smallValid 4171 43 := by unfold smallValid; decide +kernel

private theorem sp4214 : smallValid 4214 43 := by unfold smallValid; decide +kernel

private theorem sp4257 : smallValid 4257 43 := by unfold smallValid; decide +kernel

private theorem sp4300 : smallValid 4300 44 := by unfold smallValid; decide +kernel

private theorem sp4344 : smallValid 4344 43 := by unfold smallValid; decide +kernel

private theorem sp4387 : smallValid 4387 44 := by unfold smallValid; decide +kernel

private theorem sp4431 : smallValid 4431 43 := by unfold smallValid; decide +kernel

private theorem sp4474 : smallValid 4474 44 := by unfold smallValid; decide +kernel

private theorem sp4518 : smallValid 4518 43 := by unfold smallValid; decide +kernel

private theorem sp4561 : smallValid 4561 44 := by unfold smallValid; decide +kernel

private theorem sp4605 : smallValid 4605 43 := by unfold smallValid; decide +kernel

private theorem sp4648 : smallValid 4648 44 := by unfold smallValid; decide +kernel

private theorem sp4692 : smallValid 4692 43 := by unfold smallValid; decide +kernel

private theorem sp4735 : smallValid 4735 44 := by unfold smallValid; decide +kernel

private theorem sp4779 : smallValid 4779 43 := by unfold smallValid; decide +kernel

private theorem sp4822 : smallValid 4822 44 := by unfold smallValid; decide +kernel

private theorem sp4866 : smallValid 4866 43 := by unfold smallValid; decide +kernel

private theorem sp4909 : smallValid 4909 44 := by unfold smallValid; decide +kernel

private theorem sp4953 : smallValid 4953 43 := by unfold smallValid; decide +kernel

private theorem sp4996 : smallValid 4996 44 := by unfold smallValid; decide +kernel

private theorem sp5040 : smallValid 5040 43 := by unfold smallValid; decide +kernel

private theorem sp5083 : smallValid 5083 44 := by unfold smallValid; decide +kernel

private theorem sp5127 : smallValid 5127 43 := by unfold smallValid; decide +kernel

private theorem sp5170 : smallValid 5170 44 := by unfold smallValid; decide +kernel

private theorem sp5214 : smallValid 5214 43 := by unfold smallValid; decide +kernel

private theorem sp5257 : smallValid 5257 44 := by unfold smallValid; decide +kernel

private theorem sp5301 : smallValid 5301 43 := by unfold smallValid; decide +kernel

private theorem sp5344 : smallValid 5344 44 := by unfold smallValid; decide +kernel

private theorem sp5388 : smallValid 5388 43 := by unfold smallValid; decide +kernel

private theorem sp5431 : smallValid 5431 44 := by unfold smallValid; decide +kernel

private theorem sp5475 : smallValid 5475 43 := by unfold smallValid; decide +kernel

private theorem sp5518 : smallValid 5518 44 := by unfold smallValid; decide +kernel

private theorem sp5562 : smallValid 5562 43 := by unfold smallValid; decide +kernel

private theorem sp5605 : smallValid 5605 43 := by unfold smallValid; decide +kernel

private theorem sp5648 : smallValid 5648 43 := by unfold smallValid; decide +kernel

private theorem sp5691 : smallValid 5691 44 := by unfold smallValid; decide +kernel

private theorem sp5735 : smallValid 5735 43 := by unfold smallValid; decide +kernel

private theorem sp5778 : smallValid 5778 44 := by unfold smallValid; decide +kernel

private theorem sp5822 : smallValid 5822 43 := by unfold smallValid; decide +kernel

private theorem sp5865 : smallValid 5865 44 := by unfold smallValid; decide +kernel

private theorem sp5909 : smallValid 5909 43 := by unfold smallValid; decide +kernel

private theorem sp5952 : smallValid 5952 44 := by unfold smallValid; decide +kernel

private theorem sp5996 : smallValid 5996 43 := by unfold smallValid; decide +kernel

private theorem sp6039 : smallValid 6039 44 := by unfold smallValid; decide +kernel

private theorem sp6083 : smallValid 6083 43 := by unfold smallValid; decide +kernel

private theorem sp6126 : smallValid 6126 44 := by unfold smallValid; decide +kernel

private theorem sp6170 : smallValid 6170 43 := by unfold smallValid; decide +kernel

private theorem sp6213 : smallValid 6213 44 := by unfold smallValid; decide +kernel

private theorem sp6257 : smallValid 6257 43 := by unfold smallValid; decide +kernel

private theorem sp6300 : smallValid 6300 43 := by unfold smallValid; decide +kernel

private theorem sp6343 : smallValid 6343 43 := by unfold smallValid; decide +kernel

private theorem sp6386 : smallValid 6386 44 := by unfold smallValid; decide +kernel

private theorem sp6430 : smallValid 6430 43 := by unfold smallValid; decide +kernel

private theorem sp6473 : smallValid 6473 44 := by unfold smallValid; decide +kernel

private theorem sp6517 : smallValid 6517 43 := by unfold smallValid; decide +kernel

private theorem sp6560 : smallValid 6560 44 := by unfold smallValid; decide +kernel

private theorem sp6604 : smallValid 6604 43 := by unfold smallValid; decide +kernel

private theorem sp6647 : smallValid 6647 44 := by unfold smallValid; decide +kernel

private theorem sp6691 : smallValid 6691 43 := by unfold smallValid; decide +kernel

private theorem sp6734 : smallValid 6734 44 := by unfold smallValid; decide +kernel

private theorem sp6778 : smallValid 6778 43 := by unfold smallValid; decide +kernel

private theorem sp6821 : smallValid 6821 44 := by unfold smallValid; decide +kernel

private theorem sp6865 : smallValid 6865 43 := by unfold smallValid; decide +kernel

private theorem sp6908 : smallValid 6908 44 := by unfold smallValid; decide +kernel

private theorem sp6952 : smallValid 6952 43 := by unfold smallValid; decide +kernel

private theorem sp6995 : smallValid 6995 43 := by unfold smallValid; decide +kernel

private theorem sp7038 : smallValid 7038 43 := by unfold smallValid; decide +kernel

private theorem sp7081 : smallValid 7081 44 := by unfold smallValid; decide +kernel

private theorem sp7125 : smallValid 7125 43 := by unfold smallValid; decide +kernel

private theorem sp7168 : smallValid 7168 44 := by unfold smallValid; decide +kernel

private theorem sp7212 : smallValid 7212 43 := by unfold smallValid; decide +kernel

private theorem sp7255 : smallValid 7255 44 := by unfold smallValid; decide +kernel

private theorem sp7299 : smallValid 7299 43 := by unfold smallValid; decide +kernel

private theorem sp7342 : smallValid 7342 44 := by unfold smallValid; decide +kernel

private theorem sp7386 : smallValid 7386 43 := by unfold smallValid; decide +kernel

private theorem sp7429 : smallValid 7429 44 := by unfold smallValid; decide +kernel

private theorem sp7473 : smallValid 7473 43 := by unfold smallValid; decide +kernel

private theorem sp7516 : smallValid 7516 44 := by unfold smallValid; decide +kernel

private theorem sp7560 : smallValid 7560 43 := by unfold smallValid; decide +kernel

private theorem sp7603 : smallValid 7603 44 := by unfold smallValid; decide +kernel

private theorem sp7647 : smallValid 7647 43 := by unfold smallValid; decide +kernel

private theorem sp7690 : smallValid 7690 44 := by unfold smallValid; decide +kernel

private theorem sp7734 : smallValid 7734 43 := by unfold smallValid; decide +kernel

private theorem sp7777 : smallValid 7777 44 := by unfold smallValid; decide +kernel

private theorem sp7821 : smallValid 7821 43 := by unfold smallValid; decide +kernel

private theorem sp7864 : smallValid 7864 44 := by unfold smallValid; decide +kernel

private theorem sp7908 : smallValid 7908 43 := by unfold smallValid; decide +kernel

private theorem sp7951 : smallValid 7951 44 := by unfold smallValid; decide +kernel

private theorem sp7995 : smallValid 7995 43 := by unfold smallValid; decide +kernel

private theorem sp8038 : smallValid 8038 44 := by unfold smallValid; decide +kernel

private theorem sp8082 : smallValid 8082 43 := by unfold smallValid; decide +kernel

private theorem sp8125 : smallValid 8125 44 := by unfold smallValid; decide +kernel

private theorem sp8169 : smallValid 8169 43 := by unfold smallValid; decide +kernel

private theorem sp8212 : smallValid 8212 44 := by unfold smallValid; decide +kernel

private theorem sp8256 : smallValid 8256 43 := by unfold smallValid; decide +kernel

private theorem sp8299 : smallValid 8299 44 := by unfold smallValid; decide +kernel

private theorem sp8343 : smallValid 8343 43 := by unfold smallValid; decide +kernel

private theorem sp8386 : smallValid 8386 43 := by unfold smallValid; decide +kernel

private theorem sp8429 : smallValid 8429 43 := by unfold smallValid; decide +kernel

private theorem sp8472 : smallValid 8472 44 := by unfold smallValid; decide +kernel

private theorem sp8516 : smallValid 8516 43 := by unfold smallValid; decide +kernel

private theorem sp8559 : smallValid 8559 44 := by unfold smallValid; decide +kernel

private theorem sp8603 : smallValid 8603 43 := by unfold smallValid; decide +kernel

private theorem sp8646 : smallValid 8646 44 := by unfold smallValid; decide +kernel

private theorem sp8690 : smallValid 8690 43 := by unfold smallValid; decide +kernel

private theorem sp8733 : smallValid 8733 44 := by unfold smallValid; decide +kernel

private theorem sp8777 : smallValid 8777 43 := by unfold smallValid; decide +kernel

private theorem sp8820 : smallValid 8820 44 := by unfold smallValid; decide +kernel

private theorem sp8864 : smallValid 8864 43 := by unfold smallValid; decide +kernel

private theorem sp8907 : smallValid 8907 44 := by unfold smallValid; decide +kernel

private theorem sp8951 : smallValid 8951 43 := by unfold smallValid; decide +kernel

private theorem sp8994 : smallValid 8994 44 := by unfold smallValid; decide +kernel

private theorem sp9038 : smallValid 9038 43 := by unfold smallValid; decide +kernel

private theorem sp9081 : smallValid 9081 43 := by unfold smallValid; decide +kernel

private theorem sp9124 : smallValid 9124 43 := by unfold smallValid; decide +kernel

private theorem sp9167 : smallValid 9167 44 := by unfold smallValid; decide +kernel

private theorem sp9211 : smallValid 9211 43 := by unfold smallValid; decide +kernel

private theorem sp9254 : smallValid 9254 44 := by unfold smallValid; decide +kernel

private theorem sp9298 : smallValid 9298 43 := by unfold smallValid; decide +kernel

private theorem sp9341 : smallValid 9341 44 := by unfold smallValid; decide +kernel

private theorem sp9385 : smallValid 9385 43 := by unfold smallValid; decide +kernel

private theorem sp9428 : smallValid 9428 44 := by unfold smallValid; decide +kernel

private theorem sp9472 : smallValid 9472 43 := by unfold smallValid; decide +kernel

private theorem sp9515 : smallValid 9515 44 := by unfold smallValid; decide +kernel

private theorem sp9559 : smallValid 9559 43 := by unfold smallValid; decide +kernel

private theorem sp9602 : smallValid 9602 44 := by unfold smallValid; decide +kernel

private theorem sp9646 : smallValid 9646 43 := by unfold smallValid; decide +kernel

private theorem sp9689 : smallValid 9689 44 := by unfold smallValid; decide +kernel

private theorem sp9733 : smallValid 9733 43 := by unfold smallValid; decide +kernel

private theorem sp9776 : smallValid 9776 43 := by unfold smallValid; decide +kernel

private theorem sp9819 : smallValid 9819 43 := by unfold smallValid; decide +kernel

private theorem sp9862 : smallValid 9862 44 := by unfold smallValid; decide +kernel

private theorem sp9906 : smallValid 9906 43 := by unfold smallValid; decide +kernel

private theorem sp9949 : smallValid 9949 44 := by unfold smallValid; decide +kernel

private theorem sp9993 : smallValid 9993 43 := by unfold smallValid; decide +kernel

private theorem sp10036 : smallValid 10036 44 := by unfold smallValid; decide +kernel

private theorem sp10080 : smallValid 10080 43 := by unfold smallValid; decide +kernel

private theorem sp10123 : smallValid 10123 44 := by unfold smallValid; decide +kernel

private theorem sp10167 : smallValid 10167 43 := by unfold smallValid; decide +kernel

private theorem sp10210 : smallValid 10210 44 := by unfold smallValid; decide +kernel

private theorem sp10254 : smallValid 10254 43 := by unfold smallValid; decide +kernel

private theorem sp10297 : smallValid 10297 44 := by unfold smallValid; decide +kernel

private theorem sp10341 : smallValid 10341 43 := by unfold smallValid; decide +kernel

private theorem sp10384 : smallValid 10384 44 := by unfold smallValid; decide +kernel

private theorem sp10428 : smallValid 10428 43 := by unfold smallValid; decide +kernel

private theorem sp10471 : smallValid 10471 44 := by unfold smallValid; decide +kernel

private theorem sp10515 : smallValid 10515 43 := by unfold smallValid; decide +kernel

private theorem sp10558 : smallValid 10558 44 := by unfold smallValid; decide +kernel

private theorem sp10602 : smallValid 10602 43 := by unfold smallValid; decide +kernel

private theorem sp10645 : smallValid 10645 44 := by unfold smallValid; decide +kernel

private theorem sp10689 : smallValid 10689 43 := by unfold smallValid; decide +kernel

private theorem sp10732 : smallValid 10732 44 := by unfold smallValid; decide +kernel

private theorem sp10776 : smallValid 10776 43 := by unfold smallValid; decide +kernel

private theorem sp10819 : smallValid 10819 44 := by unfold smallValid; decide +kernel

private theorem sp10863 : smallValid 10863 43 := by unfold smallValid; decide +kernel

private theorem sp10906 : smallValid 10906 44 := by unfold smallValid; decide +kernel

private theorem sp10950 : smallValid 10950 43 := by unfold smallValid; decide +kernel

private theorem sp10993 : smallValid 10993 44 := by unfold smallValid; decide +kernel

private theorem sp11037 : smallValid 11037 43 := by unfold smallValid; decide +kernel

private theorem sp11080 : smallValid 11080 44 := by unfold smallValid; decide +kernel

private theorem sp11124 : smallValid 11124 43 := by unfold smallValid; decide +kernel

private theorem sp11167 : smallValid 11167 43 := by unfold smallValid; decide +kernel

private theorem sp11210 : smallValid 11210 43 := by unfold smallValid; decide +kernel

private theorem sp11253 : smallValid 11253 44 := by unfold smallValid; decide +kernel

private theorem sp11297 : smallValid 11297 43 := by unfold smallValid; decide +kernel

private theorem sp11340 : smallValid 11340 44 := by unfold smallValid; decide +kernel

private theorem sp11384 : smallValid 11384 43 := by unfold smallValid; decide +kernel

private theorem sp11427 : smallValid 11427 44 := by unfold smallValid; decide +kernel

private theorem sp11471 : smallValid 11471 43 := by unfold smallValid; decide +kernel

private theorem sp11514 : smallValid 11514 44 := by unfold smallValid; decide +kernel

private theorem sp11558 : smallValid 11558 43 := by unfold smallValid; decide +kernel

private theorem sp11601 : smallValid 11601 44 := by unfold smallValid; decide +kernel

private theorem sp11645 : smallValid 11645 43 := by unfold smallValid; decide +kernel

private theorem sp11688 : smallValid 11688 44 := by unfold smallValid; decide +kernel

private theorem sp11732 : smallValid 11732 43 := by unfold smallValid; decide +kernel

private theorem sp11775 : smallValid 11775 44 := by unfold smallValid; decide +kernel

private theorem sp11819 : smallValid 11819 43 := by unfold smallValid; decide +kernel

private theorem sp11862 : smallValid 11862 43 := by unfold smallValid; decide +kernel

private theorem sp11905 : smallValid 11905 43 := by unfold smallValid; decide +kernel

private theorem sp11948 : smallValid 11948 44 := by unfold smallValid; decide +kernel

private theorem sp11992 : smallValid 11992 43 := by unfold smallValid; decide +kernel

private theorem sp12035 : smallValid 12035 44 := by unfold smallValid; decide +kernel

private theorem sp12079 : smallValid 12079 43 := by unfold smallValid; decide +kernel

private theorem sp12122 : smallValid 12122 44 := by unfold smallValid; decide +kernel

private theorem sp12166 : smallValid 12166 43 := by unfold smallValid; decide +kernel

private theorem sp12209 : smallValid 12209 44 := by unfold smallValid; decide +kernel

private theorem sp12253 : smallValid 12253 43 := by unfold smallValid; decide +kernel

private theorem sp12296 : smallValid 12296 44 := by unfold smallValid; decide +kernel

private theorem sp12340 : smallValid 12340 43 := by unfold smallValid; decide +kernel

private theorem sp12383 : smallValid 12383 44 := by unfold smallValid; decide +kernel

private theorem sp12427 : smallValid 12427 43 := by unfold smallValid; decide +kernel

private theorem sp12470 : smallValid 12470 44 := by unfold smallValid; decide +kernel

private theorem sp12514 : smallValid 12514 43 := by unfold smallValid; decide +kernel

private theorem sp12557 : smallValid 12557 43 := by unfold smallValid; decide +kernel

private theorem sp12600 : smallValid 12600 43 := by unfold smallValid; decide +kernel

private theorem sp12643 : smallValid 12643 44 := by unfold smallValid; decide +kernel

private theorem sp12687 : smallValid 12687 43 := by unfold smallValid; decide +kernel

private theorem sp12730 : smallValid 12730 44 := by unfold smallValid; decide +kernel

private theorem sp12774 : smallValid 12774 43 := by unfold smallValid; decide +kernel

private theorem sp12817 : smallValid 12817 44 := by unfold smallValid; decide +kernel

private theorem sp12861 : smallValid 12861 43 := by unfold smallValid; decide +kernel

private theorem sp12904 : smallValid 12904 44 := by unfold smallValid; decide +kernel

private theorem sp12948 : smallValid 12948 43 := by unfold smallValid; decide +kernel

private theorem sp12991 : smallValid 12991 44 := by unfold smallValid; decide +kernel

private theorem sp13035 : smallValid 13035 43 := by unfold smallValid; decide +kernel

private theorem sp13078 : smallValid 13078 44 := by unfold smallValid; decide +kernel

private theorem sp13122 : smallValid 13122 43 := by unfold smallValid; decide +kernel

private theorem sp13165 : smallValid 13165 44 := by unfold smallValid; decide +kernel

private theorem sp13209 : smallValid 13209 43 := by unfold smallValid; decide +kernel

private theorem sp13252 : smallValid 13252 44 := by unfold smallValid; decide +kernel

private theorem sp13296 : smallValid 13296 43 := by unfold smallValid; decide +kernel

private theorem sp13339 : smallValid 13339 44 := by unfold smallValid; decide +kernel

private theorem sp13383 : smallValid 13383 43 := by unfold smallValid; decide +kernel

private theorem sp13426 : smallValid 13426 44 := by unfold smallValid; decide +kernel

private theorem sp13470 : smallValid 13470 43 := by unfold smallValid; decide +kernel

private theorem sp13513 : smallValid 13513 44 := by unfold smallValid; decide +kernel

private theorem sp13557 : smallValid 13557 43 := by unfold smallValid; decide +kernel

private theorem sp13600 : smallValid 13600 44 := by unfold smallValid; decide +kernel

private theorem sp13644 : smallValid 13644 43 := by unfold smallValid; decide +kernel

private theorem sp13687 : smallValid 13687 44 := by unfold smallValid; decide +kernel

private theorem sp13731 : smallValid 13731 43 := by unfold smallValid; decide +kernel

private theorem sp13774 : smallValid 13774 44 := by unfold smallValid; decide +kernel

private theorem sp13818 : smallValid 13818 43 := by unfold smallValid; decide +kernel

private theorem sp13861 : smallValid 13861 44 := by unfold smallValid; decide +kernel

private theorem sp13905 : smallValid 13905 43 := by unfold smallValid; decide +kernel

private theorem sp13948 : smallValid 13948 43 := by unfold smallValid; decide +kernel

private theorem sp13991 : smallValid 13991 43 := by unfold smallValid; decide +kernel

private theorem sp14034 : smallValid 14034 44 := by unfold smallValid; decide +kernel

private theorem sp14078 : smallValid 14078 43 := by unfold smallValid; decide +kernel

private theorem sp14121 : smallValid 14121 44 := by unfold smallValid; decide +kernel

private theorem sp14165 : smallValid 14165 43 := by unfold smallValid; decide +kernel

private theorem sp14208 : smallValid 14208 44 := by unfold smallValid; decide +kernel

private theorem sp14252 : smallValid 14252 43 := by unfold smallValid; decide +kernel

private theorem sp14295 : smallValid 14295 44 := by unfold smallValid; decide +kernel

private theorem sp14339 : smallValid 14339 43 := by unfold smallValid; decide +kernel

private theorem sp14382 : smallValid 14382 44 := by unfold smallValid; decide +kernel

private theorem sp14426 : smallValid 14426 43 := by unfold smallValid; decide +kernel

private theorem sp14469 : smallValid 14469 44 := by unfold smallValid; decide +kernel

private theorem sp14513 : smallValid 14513 43 := by unfold smallValid; decide +kernel

private theorem sp14556 : smallValid 14556 44 := by unfold smallValid; decide +kernel

private theorem sp14600 : smallValid 14600 43 := by unfold smallValid; decide +kernel

private theorem sp14643 : smallValid 14643 43 := by unfold smallValid; decide +kernel

private theorem sp14686 : smallValid 14686 43 := by unfold smallValid; decide +kernel

private theorem sp14729 : smallValid 14729 44 := by unfold smallValid; decide +kernel

private theorem sp14773 : smallValid 14773 43 := by unfold smallValid; decide +kernel

private theorem sp14816 : smallValid 14816 44 := by unfold smallValid; decide +kernel

private theorem sp14860 : smallValid 14860 43 := by unfold smallValid; decide +kernel

private theorem sp14903 : smallValid 14903 44 := by unfold smallValid; decide +kernel

private theorem sp14947 : smallValid 14947 43 := by unfold smallValid; decide +kernel

private theorem sp14990 : smallValid 14990 44 := by unfold smallValid; decide +kernel

private theorem sp15034 : smallValid 15034 43 := by unfold smallValid; decide +kernel

private theorem sp15077 : smallValid 15077 44 := by unfold smallValid; decide +kernel

private theorem sp15121 : smallValid 15121 43 := by unfold smallValid; decide +kernel

private theorem sp15164 : smallValid 15164 44 := by unfold smallValid; decide +kernel

private theorem sp15208 : smallValid 15208 43 := by unfold smallValid; decide +kernel

private theorem sp15251 : smallValid 15251 44 := by unfold smallValid; decide +kernel

private theorem sp15295 : smallValid 15295 43 := by unfold smallValid; decide +kernel

private theorem sp15338 : smallValid 15338 43 := by unfold smallValid; decide +kernel

private theorem sp15381 : smallValid 15381 43 := by unfold smallValid; decide +kernel

private theorem sp15424 : smallValid 15424 44 := by unfold smallValid; decide +kernel

private theorem sp15468 : smallValid 15468 43 := by unfold smallValid; decide +kernel

private theorem sp15511 : smallValid 15511 44 := by unfold smallValid; decide +kernel

private theorem sp15555 : smallValid 15555 43 := by unfold smallValid; decide +kernel

private theorem sp15598 : smallValid 15598 44 := by unfold smallValid; decide +kernel

private theorem sp15642 : smallValid 15642 43 := by unfold smallValid; decide +kernel

private theorem sp15685 : smallValid 15685 44 := by unfold smallValid; decide +kernel

private theorem sp15729 : smallValid 15729 43 := by unfold smallValid; decide +kernel

private theorem sp15772 : smallValid 15772 44 := by unfold smallValid; decide +kernel

private theorem sp15816 : smallValid 15816 43 := by unfold smallValid; decide +kernel

private theorem sp15859 : smallValid 15859 44 := by unfold smallValid; decide +kernel

private theorem sp15903 : smallValid 15903 43 := by unfold smallValid; decide +kernel

private theorem sp15946 : smallValid 15946 44 := by unfold smallValid; decide +kernel

private theorem sp15990 : smallValid 15990 43 := by unfold smallValid; decide +kernel

private theorem sp16033 : smallValid 16033 44 := by unfold smallValid; decide +kernel

private theorem sp16077 : smallValid 16077 43 := by unfold smallValid; decide +kernel

private theorem sp16120 : smallValid 16120 44 := by unfold smallValid; decide +kernel

private theorem sp16164 : smallValid 16164 43 := by unfold smallValid; decide +kernel

private theorem sp16207 : smallValid 16207 44 := by unfold smallValid; decide +kernel

private theorem sp16251 : smallValid 16251 43 := by unfold smallValid; decide +kernel

private theorem sp16294 : smallValid 16294 44 := by unfold smallValid; decide +kernel

private theorem sp16338 : smallValid 16338 43 := by unfold smallValid; decide +kernel

private theorem sp16381 : smallValid 16381 44 := by unfold smallValid; decide +kernel

private theorem sp16425 : smallValid 16425 43 := by unfold smallValid; decide +kernel

private theorem sp16468 : smallValid 16468 44 := by unfold smallValid; decide +kernel

private theorem sp16512 : smallValid 16512 43 := by unfold smallValid; decide +kernel

private theorem sp16555 : smallValid 16555 44 := by unfold smallValid; decide +kernel

private theorem sp16599 : smallValid 16599 43 := by unfold smallValid; decide +kernel

private theorem sp16642 : smallValid 16642 44 := by unfold smallValid; decide +kernel

private theorem sp16686 : smallValid 16686 43 := by unfold smallValid; decide +kernel

private theorem sp16729 : smallValid 16729 43 := by unfold smallValid; decide +kernel

private theorem sp16772 : smallValid 16772 43 := by unfold smallValid; decide +kernel

private theorem sp16815 : smallValid 16815 44 := by unfold smallValid; decide +kernel

private theorem sp16859 : smallValid 16859 43 := by unfold smallValid; decide +kernel

private theorem sp16902 : smallValid 16902 44 := by unfold smallValid; decide +kernel

private theorem sp16946 : smallValid 16946 43 := by unfold smallValid; decide +kernel

private theorem sp16989 : smallValid 16989 44 := by unfold smallValid; decide +kernel

private theorem sp17033 : smallValid 17033 43 := by unfold smallValid; decide +kernel

private theorem sp17076 : smallValid 17076 44 := by unfold smallValid; decide +kernel

private theorem sp17120 : smallValid 17120 43 := by unfold smallValid; decide +kernel

private theorem sp17163 : smallValid 17163 44 := by unfold smallValid; decide +kernel

private theorem sp17207 : smallValid 17207 43 := by unfold smallValid; decide +kernel

private theorem sp17250 : smallValid 17250 44 := by unfold smallValid; decide +kernel

private theorem sp17294 : smallValid 17294 43 := by unfold smallValid; decide +kernel

private theorem sp17337 : smallValid 17337 44 := by unfold smallValid; decide +kernel

private theorem sp17381 : smallValid 17381 43 := by unfold smallValid; decide +kernel

private theorem sp17424 : smallValid 17424 43 := by unfold smallValid; decide +kernel

private theorem sp17467 : smallValid 17467 43 := by unfold smallValid; decide +kernel

private theorem sp17510 : smallValid 17510 44 := by unfold smallValid; decide +kernel

private theorem sp17554 : smallValid 17554 43 := by unfold smallValid; decide +kernel

private theorem sp17597 : smallValid 17597 44 := by unfold smallValid; decide +kernel

private theorem sp17641 : smallValid 17641 43 := by unfold smallValid; decide +kernel

private theorem sp17684 : smallValid 17684 44 := by unfold smallValid; decide +kernel

private theorem sp17728 : smallValid 17728 43 := by unfold smallValid; decide +kernel

private theorem sp17771 : smallValid 17771 44 := by unfold smallValid; decide +kernel

private theorem sp17815 : smallValid 17815 43 := by unfold smallValid; decide +kernel

private theorem sp17858 : smallValid 17858 44 := by unfold smallValid; decide +kernel

private theorem sp17902 : smallValid 17902 43 := by unfold smallValid; decide +kernel

private theorem sp17945 : smallValid 17945 44 := by unfold smallValid; decide +kernel

private theorem sp17989 : smallValid 17989 43 := by unfold smallValid; decide +kernel

private theorem sp18032 : smallValid 18032 44 := by unfold smallValid; decide +kernel

private theorem sp18076 : smallValid 18076 43 := by unfold smallValid; decide +kernel

private theorem sp18119 : smallValid 18119 43 := by unfold smallValid; decide +kernel

private theorem sp18162 : smallValid 18162 43 := by unfold smallValid; decide +kernel

private theorem sp18205 : smallValid 18205 44 := by unfold smallValid; decide +kernel

private theorem sp18249 : smallValid 18249 43 := by unfold smallValid; decide +kernel

private theorem sp18292 : smallValid 18292 44 := by unfold smallValid; decide +kernel

private theorem sp18336 : smallValid 18336 43 := by unfold smallValid; decide +kernel

private theorem sp18379 : smallValid 18379 44 := by unfold smallValid; decide +kernel

private theorem sp18423 : smallValid 18423 43 := by unfold smallValid; decide +kernel

private theorem sp18466 : smallValid 18466 44 := by unfold smallValid; decide +kernel

private theorem sp18510 : smallValid 18510 43 := by unfold smallValid; decide +kernel

private theorem sp18553 : smallValid 18553 44 := by unfold smallValid; decide +kernel

private theorem sp18597 : smallValid 18597 43 := by unfold smallValid; decide +kernel

private theorem sp18640 : smallValid 18640 44 := by unfold smallValid; decide +kernel

private theorem sp18684 : smallValid 18684 43 := by unfold smallValid; decide +kernel

private theorem sp18727 : smallValid 18727 44 := by unfold smallValid; decide +kernel

private theorem sp18771 : smallValid 18771 43 := by unfold smallValid; decide +kernel

private theorem sp18814 : smallValid 18814 44 := by unfold smallValid; decide +kernel

private theorem sp18858 : smallValid 18858 43 := by unfold smallValid; decide +kernel

private theorem sp18901 : smallValid 18901 44 := by unfold smallValid; decide +kernel

private theorem sp18945 : smallValid 18945 43 := by unfold smallValid; decide +kernel

private theorem sp18988 : smallValid 18988 44 := by unfold smallValid; decide +kernel

private theorem sp19032 : smallValid 19032 43 := by unfold smallValid; decide +kernel

private theorem sp19075 : smallValid 19075 44 := by unfold smallValid; decide +kernel

private theorem sp19119 : smallValid 19119 43 := by unfold smallValid; decide +kernel

private theorem sp19162 : smallValid 19162 44 := by unfold smallValid; decide +kernel

private theorem sp19206 : smallValid 19206 43 := by unfold smallValid; decide +kernel

private theorem sp19249 : smallValid 19249 44 := by unfold smallValid; decide +kernel

private theorem sp19293 : smallValid 19293 43 := by unfold smallValid; decide +kernel

private theorem sp19336 : smallValid 19336 44 := by unfold smallValid; decide +kernel

private theorem sp19380 : smallValid 19380 43 := by unfold smallValid; decide +kernel

private theorem sp19423 : smallValid 19423 44 := by unfold smallValid; decide +kernel

private theorem sp19467 : smallValid 19467 43 := by unfold smallValid; decide +kernel

private theorem sp19510 : smallValid 19510 43 := by unfold smallValid; decide +kernel

private theorem sp19553 : smallValid 19553 43 := by unfold smallValid; decide +kernel

private theorem sp19596 : smallValid 19596 44 := by unfold smallValid; decide +kernel

private theorem sp19640 : smallValid 19640 43 := by unfold smallValid; decide +kernel

private theorem sp19683 : smallValid 19683 44 := by unfold smallValid; decide +kernel

private theorem sp19727 : smallValid 19727 43 := by unfold smallValid; decide +kernel

private theorem sp19770 : smallValid 19770 44 := by unfold smallValid; decide +kernel

private theorem sp19814 : smallValid 19814 43 := by unfold smallValid; decide +kernel

private theorem sp19857 : smallValid 19857 44 := by unfold smallValid; decide +kernel

private theorem sp19901 : smallValid 19901 43 := by unfold smallValid; decide +kernel

private theorem sp19944 : smallValid 19944 44 := by unfold smallValid; decide +kernel

private theorem sp19988 : smallValid 19988 43 := by unfold smallValid; decide +kernel

private theorem sp20031 : smallValid 20031 44 := by unfold smallValid; decide +kernel

private theorem sp20075 : smallValid 20075 43 := by unfold smallValid; decide +kernel

private theorem sp20118 : smallValid 20118 44 := by unfold smallValid; decide +kernel

private theorem sp20162 : smallValid 20162 43 := by unfold smallValid; decide +kernel

private theorem sp20205 : smallValid 20205 44 := by unfold smallValid; decide +kernel

private theorem sp20249 : smallValid 20249 43 := by unfold smallValid; decide +kernel

private theorem sp20292 : smallValid 20292 44 := by unfold smallValid; decide +kernel

private theorem sp20336 : smallValid 20336 43 := by unfold smallValid; decide +kernel

private theorem sp20379 : smallValid 20379 44 := by unfold smallValid; decide +kernel

private theorem sp20423 : smallValid 20423 43 := by unfold smallValid; decide +kernel

private theorem sp20466 : smallValid 20466 44 := by unfold smallValid; decide +kernel

private theorem sp20510 : smallValid 20510 43 := by unfold smallValid; decide +kernel

private theorem sp20553 : smallValid 20553 44 := by unfold smallValid; decide +kernel

private theorem sp20597 : smallValid 20597 43 := by unfold smallValid; decide +kernel

private theorem sp20640 : smallValid 20640 44 := by unfold smallValid; decide +kernel

private theorem sp20684 : smallValid 20684 43 := by unfold smallValid; decide +kernel

private theorem sp20727 : smallValid 20727 44 := by unfold smallValid; decide +kernel

private theorem sp20771 : smallValid 20771 43 := by unfold smallValid; decide +kernel

private theorem sp20814 : smallValid 20814 44 := by unfold smallValid; decide +kernel

private theorem sp20858 : smallValid 20858 43 := by unfold smallValid; decide +kernel

private theorem sp20901 : smallValid 20901 43 := by unfold smallValid; decide +kernel

private theorem sp20944 : smallValid 20944 43 := by unfold smallValid; decide +kernel

private theorem sp20987 : smallValid 20987 44 := by unfold smallValid; decide +kernel

private theorem sp21031 : smallValid 21031 43 := by unfold smallValid; decide +kernel

private theorem sp21074 : smallValid 21074 44 := by unfold smallValid; decide +kernel

private theorem sp21118 : smallValid 21118 43 := by unfold smallValid; decide +kernel

private theorem sp21161 : smallValid 21161 44 := by unfold smallValid; decide +kernel

private theorem sp21205 : smallValid 21205 43 := by unfold smallValid; decide +kernel

private theorem sp21248 : smallValid 21248 44 := by unfold smallValid; decide +kernel

private theorem sp21292 : smallValid 21292 43 := by unfold smallValid; decide +kernel

private theorem sp21335 : smallValid 21335 44 := by unfold smallValid; decide +kernel

private theorem sp21379 : smallValid 21379 43 := by unfold smallValid; decide +kernel

private theorem sp21422 : smallValid 21422 44 := by unfold smallValid; decide +kernel

private theorem sp21466 : smallValid 21466 43 := by unfold smallValid; decide +kernel

private theorem sp21509 : smallValid 21509 44 := by unfold smallValid; decide +kernel

private theorem sp21553 : smallValid 21553 43 := by unfold smallValid; decide +kernel

private theorem sp21596 : smallValid 21596 44 := by unfold smallValid; decide +kernel

private theorem sp21640 : smallValid 21640 43 := by unfold smallValid; decide +kernel

private theorem sp21683 : smallValid 21683 44 := by unfold smallValid; decide +kernel

private theorem sp21727 : smallValid 21727 43 := by unfold smallValid; decide +kernel

private theorem sp21770 : smallValid 21770 44 := by unfold smallValid; decide +kernel

private theorem sp21814 : smallValid 21814 43 := by unfold smallValid; decide +kernel

private theorem sp21857 : smallValid 21857 44 := by unfold smallValid; decide +kernel

private theorem sp21901 : smallValid 21901 43 := by unfold smallValid; decide +kernel

private theorem sp21944 : smallValid 21944 44 := by unfold smallValid; decide +kernel

private theorem sp21988 : smallValid 21988 43 := by unfold smallValid; decide +kernel

private theorem sp22031 : smallValid 22031 44 := by unfold smallValid; decide +kernel

private theorem sp22075 : smallValid 22075 43 := by unfold smallValid; decide +kernel

private theorem sp22118 : smallValid 22118 44 := by unfold smallValid; decide +kernel

private theorem sp22162 : smallValid 22162 43 := by unfold smallValid; decide +kernel

private theorem sp22205 : smallValid 22205 44 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤22248) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 22249 := (joinSmall (lo:=0) (a:=11124) (b:=11125) (joinSmall (lo:=0) (a:=5562) (b:=5562) (joinSmall (lo:=0) (a:=2781) (b:=2781) (joinSmall (lo:=0) (a:=1390) (b:=1391) (joinSmall (lo:=0) (a:=695) (b:=695) (joinSmall (lo:=0) (a:=347) (b:=348) (joinSmall (lo:=0) (a:=173) (b:=174) (joinSmall (lo:=0) (a:=86) (b:=87) (joinSmall (lo:=0) (a:=43) (b:=43) sp0 sp43) (joinSmall (lo:=86) (a:=43) (b:=44) sp86 sp129)) (joinSmall (lo:=173) (a:=87) (b:=87) (joinSmall (lo:=173) (a:=43) (b:=44) sp173 sp216) (joinSmall (lo:=260) (a:=43) (b:=44) sp260 sp303))) (joinSmall (lo:=347) (a:=174) (b:=174) (joinSmall (lo:=347) (a:=87) (b:=87) (joinSmall (lo:=347) (a:=43) (b:=44) sp347 sp390) (joinSmall (lo:=434) (a:=43) (b:=44) sp434 sp477)) (joinSmall (lo:=521) (a:=87) (b:=87) (joinSmall (lo:=521) (a:=43) (b:=44) sp521 sp564) (joinSmall (lo:=608) (a:=43) (b:=44) sp608 sp651)))) (joinSmall (lo:=695) (a:=347) (b:=348) (joinSmall (lo:=695) (a:=173) (b:=174) (joinSmall (lo:=695) (a:=86) (b:=87) (joinSmall (lo:=695) (a:=43) (b:=43) sp695 sp738) (joinSmall (lo:=781) (a:=43) (b:=44) sp781 sp824)) (joinSmall (lo:=868) (a:=87) (b:=87) (joinSmall (lo:=868) (a:=43) (b:=44) sp868 sp911) (joinSmall (lo:=955) (a:=43) (b:=44) sp955 sp998))) (joinSmall (lo:=1042) (a:=174) (b:=174) (joinSmall (lo:=1042) (a:=87) (b:=87) (joinSmall (lo:=1042) (a:=43) (b:=44) sp1042 sp1085) (joinSmall (lo:=1129) (a:=43) (b:=44) sp1129 sp1172)) (joinSmall (lo:=1216) (a:=87) (b:=87) (joinSmall (lo:=1216) (a:=43) (b:=44) sp1216 sp1259) (joinSmall (lo:=1303) (a:=43) (b:=44) sp1303 sp1346))))) (joinSmall (lo:=1390) (a:=695) (b:=696) (joinSmall (lo:=1390) (a:=347) (b:=348) (joinSmall (lo:=1390) (a:=173) (b:=174) (joinSmall (lo:=1390) (a:=86) (b:=87) (joinSmall (lo:=1390) (a:=43) (b:=43) sp1390 sp1433) (joinSmall (lo:=1476) (a:=43) (b:=44) sp1476 sp1519)) (joinSmall (lo:=1563) (a:=87) (b:=87) (joinSmall (lo:=1563) (a:=43) (b:=44) sp1563 sp1606) (joinSmall (lo:=1650) (a:=43) (b:=44) sp1650 sp1693))) (joinSmall (lo:=1737) (a:=174) (b:=174) (joinSmall (lo:=1737) (a:=87) (b:=87) (joinSmall (lo:=1737) (a:=43) (b:=44) sp1737 sp1780) (joinSmall (lo:=1824) (a:=43) (b:=44) sp1824 sp1867)) (joinSmall (lo:=1911) (a:=87) (b:=87) (joinSmall (lo:=1911) (a:=43) (b:=44) sp1911 sp1954) (joinSmall (lo:=1998) (a:=43) (b:=44) sp1998 sp2041)))) (joinSmall (lo:=2085) (a:=348) (b:=348) (joinSmall (lo:=2085) (a:=174) (b:=174) (joinSmall (lo:=2085) (a:=87) (b:=87) (joinSmall (lo:=2085) (a:=43) (b:=44) sp2085 sp2128) (joinSmall (lo:=2172) (a:=43) (b:=44) sp2172 sp2215)) (joinSmall (lo:=2259) (a:=87) (b:=87) (joinSmall (lo:=2259) (a:=43) (b:=44) sp2259 sp2302) (joinSmall (lo:=2346) (a:=43) (b:=44) sp2346 sp2389))) (joinSmall (lo:=2433) (a:=174) (b:=174) (joinSmall (lo:=2433) (a:=87) (b:=87) (joinSmall (lo:=2433) (a:=43) (b:=44) sp2433 sp2476) (joinSmall (lo:=2520) (a:=43) (b:=44) sp2520 sp2563)) (joinSmall (lo:=2607) (a:=87) (b:=87) (joinSmall (lo:=2607) (a:=43) (b:=44) sp2607 sp2650) (joinSmall (lo:=2694) (a:=43) (b:=44) sp2694 sp2737)))))) (joinSmall (lo:=2781) (a:=1390) (b:=1391) (joinSmall (lo:=2781) (a:=695) (b:=695) (joinSmall (lo:=2781) (a:=347) (b:=348) (joinSmall (lo:=2781) (a:=173) (b:=174) (joinSmall (lo:=2781) (a:=86) (b:=87) (joinSmall (lo:=2781) (a:=43) (b:=43) sp2781 sp2824) (joinSmall (lo:=2867) (a:=43) (b:=44) sp2867 sp2910)) (joinSmall (lo:=2954) (a:=87) (b:=87) (joinSmall (lo:=2954) (a:=43) (b:=44) sp2954 sp2997) (joinSmall (lo:=3041) (a:=43) (b:=44) sp3041 sp3084))) (joinSmall (lo:=3128) (a:=174) (b:=174) (joinSmall (lo:=3128) (a:=87) (b:=87) (joinSmall (lo:=3128) (a:=43) (b:=44) sp3128 sp3171) (joinSmall (lo:=3215) (a:=43) (b:=44) sp3215 sp3258)) (joinSmall (lo:=3302) (a:=87) (b:=87) (joinSmall (lo:=3302) (a:=43) (b:=44) sp3302 sp3345) (joinSmall (lo:=3389) (a:=43) (b:=44) sp3389 sp3432)))) (joinSmall (lo:=3476) (a:=347) (b:=348) (joinSmall (lo:=3476) (a:=173) (b:=174) (joinSmall (lo:=3476) (a:=86) (b:=87) (joinSmall (lo:=3476) (a:=43) (b:=43) sp3476 sp3519) (joinSmall (lo:=3562) (a:=43) (b:=44) sp3562 sp3605)) (joinSmall (lo:=3649) (a:=87) (b:=87) (joinSmall (lo:=3649) (a:=43) (b:=44) sp3649 sp3692) (joinSmall (lo:=3736) (a:=43) (b:=44) sp3736 sp3779))) (joinSmall (lo:=3823) (a:=174) (b:=174) (joinSmall (lo:=3823) (a:=87) (b:=87) (joinSmall (lo:=3823) (a:=43) (b:=44) sp3823 sp3866) (joinSmall (lo:=3910) (a:=43) (b:=44) sp3910 sp3953)) (joinSmall (lo:=3997) (a:=87) (b:=87) (joinSmall (lo:=3997) (a:=43) (b:=44) sp3997 sp4040) (joinSmall (lo:=4084) (a:=43) (b:=44) sp4084 sp4127))))) (joinSmall (lo:=4171) (a:=695) (b:=696) (joinSmall (lo:=4171) (a:=347) (b:=348) (joinSmall (lo:=4171) (a:=173) (b:=174) (joinSmall (lo:=4171) (a:=86) (b:=87) (joinSmall (lo:=4171) (a:=43) (b:=43) sp4171 sp4214) (joinSmall (lo:=4257) (a:=43) (b:=44) sp4257 sp4300)) (joinSmall (lo:=4344) (a:=87) (b:=87) (joinSmall (lo:=4344) (a:=43) (b:=44) sp4344 sp4387) (joinSmall (lo:=4431) (a:=43) (b:=44) sp4431 sp4474))) (joinSmall (lo:=4518) (a:=174) (b:=174) (joinSmall (lo:=4518) (a:=87) (b:=87) (joinSmall (lo:=4518) (a:=43) (b:=44) sp4518 sp4561) (joinSmall (lo:=4605) (a:=43) (b:=44) sp4605 sp4648)) (joinSmall (lo:=4692) (a:=87) (b:=87) (joinSmall (lo:=4692) (a:=43) (b:=44) sp4692 sp4735) (joinSmall (lo:=4779) (a:=43) (b:=44) sp4779 sp4822)))) (joinSmall (lo:=4866) (a:=348) (b:=348) (joinSmall (lo:=4866) (a:=174) (b:=174) (joinSmall (lo:=4866) (a:=87) (b:=87) (joinSmall (lo:=4866) (a:=43) (b:=44) sp4866 sp4909) (joinSmall (lo:=4953) (a:=43) (b:=44) sp4953 sp4996)) (joinSmall (lo:=5040) (a:=87) (b:=87) (joinSmall (lo:=5040) (a:=43) (b:=44) sp5040 sp5083) (joinSmall (lo:=5127) (a:=43) (b:=44) sp5127 sp5170))) (joinSmall (lo:=5214) (a:=174) (b:=174) (joinSmall (lo:=5214) (a:=87) (b:=87) (joinSmall (lo:=5214) (a:=43) (b:=44) sp5214 sp5257) (joinSmall (lo:=5301) (a:=43) (b:=44) sp5301 sp5344)) (joinSmall (lo:=5388) (a:=87) (b:=87) (joinSmall (lo:=5388) (a:=43) (b:=44) sp5388 sp5431) (joinSmall (lo:=5475) (a:=43) (b:=44) sp5475 sp5518))))))) (joinSmall (lo:=5562) (a:=2781) (b:=2781) (joinSmall (lo:=5562) (a:=1390) (b:=1391) (joinSmall (lo:=5562) (a:=695) (b:=695) (joinSmall (lo:=5562) (a:=347) (b:=348) (joinSmall (lo:=5562) (a:=173) (b:=174) (joinSmall (lo:=5562) (a:=86) (b:=87) (joinSmall (lo:=5562) (a:=43) (b:=43) sp5562 sp5605) (joinSmall (lo:=5648) (a:=43) (b:=44) sp5648 sp5691)) (joinSmall (lo:=5735) (a:=87) (b:=87) (joinSmall (lo:=5735) (a:=43) (b:=44) sp5735 sp5778) (joinSmall (lo:=5822) (a:=43) (b:=44) sp5822 sp5865))) (joinSmall (lo:=5909) (a:=174) (b:=174) (joinSmall (lo:=5909) (a:=87) (b:=87) (joinSmall (lo:=5909) (a:=43) (b:=44) sp5909 sp5952) (joinSmall (lo:=5996) (a:=43) (b:=44) sp5996 sp6039)) (joinSmall (lo:=6083) (a:=87) (b:=87) (joinSmall (lo:=6083) (a:=43) (b:=44) sp6083 sp6126) (joinSmall (lo:=6170) (a:=43) (b:=44) sp6170 sp6213)))) (joinSmall (lo:=6257) (a:=347) (b:=348) (joinSmall (lo:=6257) (a:=173) (b:=174) (joinSmall (lo:=6257) (a:=86) (b:=87) (joinSmall (lo:=6257) (a:=43) (b:=43) sp6257 sp6300) (joinSmall (lo:=6343) (a:=43) (b:=44) sp6343 sp6386)) (joinSmall (lo:=6430) (a:=87) (b:=87) (joinSmall (lo:=6430) (a:=43) (b:=44) sp6430 sp6473) (joinSmall (lo:=6517) (a:=43) (b:=44) sp6517 sp6560))) (joinSmall (lo:=6604) (a:=174) (b:=174) (joinSmall (lo:=6604) (a:=87) (b:=87) (joinSmall (lo:=6604) (a:=43) (b:=44) sp6604 sp6647) (joinSmall (lo:=6691) (a:=43) (b:=44) sp6691 sp6734)) (joinSmall (lo:=6778) (a:=87) (b:=87) (joinSmall (lo:=6778) (a:=43) (b:=44) sp6778 sp6821) (joinSmall (lo:=6865) (a:=43) (b:=44) sp6865 sp6908))))) (joinSmall (lo:=6952) (a:=695) (b:=696) (joinSmall (lo:=6952) (a:=347) (b:=348) (joinSmall (lo:=6952) (a:=173) (b:=174) (joinSmall (lo:=6952) (a:=86) (b:=87) (joinSmall (lo:=6952) (a:=43) (b:=43) sp6952 sp6995) (joinSmall (lo:=7038) (a:=43) (b:=44) sp7038 sp7081)) (joinSmall (lo:=7125) (a:=87) (b:=87) (joinSmall (lo:=7125) (a:=43) (b:=44) sp7125 sp7168) (joinSmall (lo:=7212) (a:=43) (b:=44) sp7212 sp7255))) (joinSmall (lo:=7299) (a:=174) (b:=174) (joinSmall (lo:=7299) (a:=87) (b:=87) (joinSmall (lo:=7299) (a:=43) (b:=44) sp7299 sp7342) (joinSmall (lo:=7386) (a:=43) (b:=44) sp7386 sp7429)) (joinSmall (lo:=7473) (a:=87) (b:=87) (joinSmall (lo:=7473) (a:=43) (b:=44) sp7473 sp7516) (joinSmall (lo:=7560) (a:=43) (b:=44) sp7560 sp7603)))) (joinSmall (lo:=7647) (a:=348) (b:=348) (joinSmall (lo:=7647) (a:=174) (b:=174) (joinSmall (lo:=7647) (a:=87) (b:=87) (joinSmall (lo:=7647) (a:=43) (b:=44) sp7647 sp7690) (joinSmall (lo:=7734) (a:=43) (b:=44) sp7734 sp7777)) (joinSmall (lo:=7821) (a:=87) (b:=87) (joinSmall (lo:=7821) (a:=43) (b:=44) sp7821 sp7864) (joinSmall (lo:=7908) (a:=43) (b:=44) sp7908 sp7951))) (joinSmall (lo:=7995) (a:=174) (b:=174) (joinSmall (lo:=7995) (a:=87) (b:=87) (joinSmall (lo:=7995) (a:=43) (b:=44) sp7995 sp8038) (joinSmall (lo:=8082) (a:=43) (b:=44) sp8082 sp8125)) (joinSmall (lo:=8169) (a:=87) (b:=87) (joinSmall (lo:=8169) (a:=43) (b:=44) sp8169 sp8212) (joinSmall (lo:=8256) (a:=43) (b:=44) sp8256 sp8299)))))) (joinSmall (lo:=8343) (a:=1390) (b:=1391) (joinSmall (lo:=8343) (a:=695) (b:=695) (joinSmall (lo:=8343) (a:=347) (b:=348) (joinSmall (lo:=8343) (a:=173) (b:=174) (joinSmall (lo:=8343) (a:=86) (b:=87) (joinSmall (lo:=8343) (a:=43) (b:=43) sp8343 sp8386) (joinSmall (lo:=8429) (a:=43) (b:=44) sp8429 sp8472)) (joinSmall (lo:=8516) (a:=87) (b:=87) (joinSmall (lo:=8516) (a:=43) (b:=44) sp8516 sp8559) (joinSmall (lo:=8603) (a:=43) (b:=44) sp8603 sp8646))) (joinSmall (lo:=8690) (a:=174) (b:=174) (joinSmall (lo:=8690) (a:=87) (b:=87) (joinSmall (lo:=8690) (a:=43) (b:=44) sp8690 sp8733) (joinSmall (lo:=8777) (a:=43) (b:=44) sp8777 sp8820)) (joinSmall (lo:=8864) (a:=87) (b:=87) (joinSmall (lo:=8864) (a:=43) (b:=44) sp8864 sp8907) (joinSmall (lo:=8951) (a:=43) (b:=44) sp8951 sp8994)))) (joinSmall (lo:=9038) (a:=347) (b:=348) (joinSmall (lo:=9038) (a:=173) (b:=174) (joinSmall (lo:=9038) (a:=86) (b:=87) (joinSmall (lo:=9038) (a:=43) (b:=43) sp9038 sp9081) (joinSmall (lo:=9124) (a:=43) (b:=44) sp9124 sp9167)) (joinSmall (lo:=9211) (a:=87) (b:=87) (joinSmall (lo:=9211) (a:=43) (b:=44) sp9211 sp9254) (joinSmall (lo:=9298) (a:=43) (b:=44) sp9298 sp9341))) (joinSmall (lo:=9385) (a:=174) (b:=174) (joinSmall (lo:=9385) (a:=87) (b:=87) (joinSmall (lo:=9385) (a:=43) (b:=44) sp9385 sp9428) (joinSmall (lo:=9472) (a:=43) (b:=44) sp9472 sp9515)) (joinSmall (lo:=9559) (a:=87) (b:=87) (joinSmall (lo:=9559) (a:=43) (b:=44) sp9559 sp9602) (joinSmall (lo:=9646) (a:=43) (b:=44) sp9646 sp9689))))) (joinSmall (lo:=9733) (a:=695) (b:=696) (joinSmall (lo:=9733) (a:=347) (b:=348) (joinSmall (lo:=9733) (a:=173) (b:=174) (joinSmall (lo:=9733) (a:=86) (b:=87) (joinSmall (lo:=9733) (a:=43) (b:=43) sp9733 sp9776) (joinSmall (lo:=9819) (a:=43) (b:=44) sp9819 sp9862)) (joinSmall (lo:=9906) (a:=87) (b:=87) (joinSmall (lo:=9906) (a:=43) (b:=44) sp9906 sp9949) (joinSmall (lo:=9993) (a:=43) (b:=44) sp9993 sp10036))) (joinSmall (lo:=10080) (a:=174) (b:=174) (joinSmall (lo:=10080) (a:=87) (b:=87) (joinSmall (lo:=10080) (a:=43) (b:=44) sp10080 sp10123) (joinSmall (lo:=10167) (a:=43) (b:=44) sp10167 sp10210)) (joinSmall (lo:=10254) (a:=87) (b:=87) (joinSmall (lo:=10254) (a:=43) (b:=44) sp10254 sp10297) (joinSmall (lo:=10341) (a:=43) (b:=44) sp10341 sp10384)))) (joinSmall (lo:=10428) (a:=348) (b:=348) (joinSmall (lo:=10428) (a:=174) (b:=174) (joinSmall (lo:=10428) (a:=87) (b:=87) (joinSmall (lo:=10428) (a:=43) (b:=44) sp10428 sp10471) (joinSmall (lo:=10515) (a:=43) (b:=44) sp10515 sp10558)) (joinSmall (lo:=10602) (a:=87) (b:=87) (joinSmall (lo:=10602) (a:=43) (b:=44) sp10602 sp10645) (joinSmall (lo:=10689) (a:=43) (b:=44) sp10689 sp10732))) (joinSmall (lo:=10776) (a:=174) (b:=174) (joinSmall (lo:=10776) (a:=87) (b:=87) (joinSmall (lo:=10776) (a:=43) (b:=44) sp10776 sp10819) (joinSmall (lo:=10863) (a:=43) (b:=44) sp10863 sp10906)) (joinSmall (lo:=10950) (a:=87) (b:=87) (joinSmall (lo:=10950) (a:=43) (b:=44) sp10950 sp10993) (joinSmall (lo:=11037) (a:=43) (b:=44) sp11037 sp11080)))))))) (joinSmall (lo:=11124) (a:=5562) (b:=5563) (joinSmall (lo:=11124) (a:=2781) (b:=2781) (joinSmall (lo:=11124) (a:=1390) (b:=1391) (joinSmall (lo:=11124) (a:=695) (b:=695) (joinSmall (lo:=11124) (a:=347) (b:=348) (joinSmall (lo:=11124) (a:=173) (b:=174) (joinSmall (lo:=11124) (a:=86) (b:=87) (joinSmall (lo:=11124) (a:=43) (b:=43) sp11124 sp11167) (joinSmall (lo:=11210) (a:=43) (b:=44) sp11210 sp11253)) (joinSmall (lo:=11297) (a:=87) (b:=87) (joinSmall (lo:=11297) (a:=43) (b:=44) sp11297 sp11340) (joinSmall (lo:=11384) (a:=43) (b:=44) sp11384 sp11427))) (joinSmall (lo:=11471) (a:=174) (b:=174) (joinSmall (lo:=11471) (a:=87) (b:=87) (joinSmall (lo:=11471) (a:=43) (b:=44) sp11471 sp11514) (joinSmall (lo:=11558) (a:=43) (b:=44) sp11558 sp11601)) (joinSmall (lo:=11645) (a:=87) (b:=87) (joinSmall (lo:=11645) (a:=43) (b:=44) sp11645 sp11688) (joinSmall (lo:=11732) (a:=43) (b:=44) sp11732 sp11775)))) (joinSmall (lo:=11819) (a:=347) (b:=348) (joinSmall (lo:=11819) (a:=173) (b:=174) (joinSmall (lo:=11819) (a:=86) (b:=87) (joinSmall (lo:=11819) (a:=43) (b:=43) sp11819 sp11862) (joinSmall (lo:=11905) (a:=43) (b:=44) sp11905 sp11948)) (joinSmall (lo:=11992) (a:=87) (b:=87) (joinSmall (lo:=11992) (a:=43) (b:=44) sp11992 sp12035) (joinSmall (lo:=12079) (a:=43) (b:=44) sp12079 sp12122))) (joinSmall (lo:=12166) (a:=174) (b:=174) (joinSmall (lo:=12166) (a:=87) (b:=87) (joinSmall (lo:=12166) (a:=43) (b:=44) sp12166 sp12209) (joinSmall (lo:=12253) (a:=43) (b:=44) sp12253 sp12296)) (joinSmall (lo:=12340) (a:=87) (b:=87) (joinSmall (lo:=12340) (a:=43) (b:=44) sp12340 sp12383) (joinSmall (lo:=12427) (a:=43) (b:=44) sp12427 sp12470))))) (joinSmall (lo:=12514) (a:=695) (b:=696) (joinSmall (lo:=12514) (a:=347) (b:=348) (joinSmall (lo:=12514) (a:=173) (b:=174) (joinSmall (lo:=12514) (a:=86) (b:=87) (joinSmall (lo:=12514) (a:=43) (b:=43) sp12514 sp12557) (joinSmall (lo:=12600) (a:=43) (b:=44) sp12600 sp12643)) (joinSmall (lo:=12687) (a:=87) (b:=87) (joinSmall (lo:=12687) (a:=43) (b:=44) sp12687 sp12730) (joinSmall (lo:=12774) (a:=43) (b:=44) sp12774 sp12817))) (joinSmall (lo:=12861) (a:=174) (b:=174) (joinSmall (lo:=12861) (a:=87) (b:=87) (joinSmall (lo:=12861) (a:=43) (b:=44) sp12861 sp12904) (joinSmall (lo:=12948) (a:=43) (b:=44) sp12948 sp12991)) (joinSmall (lo:=13035) (a:=87) (b:=87) (joinSmall (lo:=13035) (a:=43) (b:=44) sp13035 sp13078) (joinSmall (lo:=13122) (a:=43) (b:=44) sp13122 sp13165)))) (joinSmall (lo:=13209) (a:=348) (b:=348) (joinSmall (lo:=13209) (a:=174) (b:=174) (joinSmall (lo:=13209) (a:=87) (b:=87) (joinSmall (lo:=13209) (a:=43) (b:=44) sp13209 sp13252) (joinSmall (lo:=13296) (a:=43) (b:=44) sp13296 sp13339)) (joinSmall (lo:=13383) (a:=87) (b:=87) (joinSmall (lo:=13383) (a:=43) (b:=44) sp13383 sp13426) (joinSmall (lo:=13470) (a:=43) (b:=44) sp13470 sp13513))) (joinSmall (lo:=13557) (a:=174) (b:=174) (joinSmall (lo:=13557) (a:=87) (b:=87) (joinSmall (lo:=13557) (a:=43) (b:=44) sp13557 sp13600) (joinSmall (lo:=13644) (a:=43) (b:=44) sp13644 sp13687)) (joinSmall (lo:=13731) (a:=87) (b:=87) (joinSmall (lo:=13731) (a:=43) (b:=44) sp13731 sp13774) (joinSmall (lo:=13818) (a:=43) (b:=44) sp13818 sp13861)))))) (joinSmall (lo:=13905) (a:=1390) (b:=1391) (joinSmall (lo:=13905) (a:=695) (b:=695) (joinSmall (lo:=13905) (a:=347) (b:=348) (joinSmall (lo:=13905) (a:=173) (b:=174) (joinSmall (lo:=13905) (a:=86) (b:=87) (joinSmall (lo:=13905) (a:=43) (b:=43) sp13905 sp13948) (joinSmall (lo:=13991) (a:=43) (b:=44) sp13991 sp14034)) (joinSmall (lo:=14078) (a:=87) (b:=87) (joinSmall (lo:=14078) (a:=43) (b:=44) sp14078 sp14121) (joinSmall (lo:=14165) (a:=43) (b:=44) sp14165 sp14208))) (joinSmall (lo:=14252) (a:=174) (b:=174) (joinSmall (lo:=14252) (a:=87) (b:=87) (joinSmall (lo:=14252) (a:=43) (b:=44) sp14252 sp14295) (joinSmall (lo:=14339) (a:=43) (b:=44) sp14339 sp14382)) (joinSmall (lo:=14426) (a:=87) (b:=87) (joinSmall (lo:=14426) (a:=43) (b:=44) sp14426 sp14469) (joinSmall (lo:=14513) (a:=43) (b:=44) sp14513 sp14556)))) (joinSmall (lo:=14600) (a:=347) (b:=348) (joinSmall (lo:=14600) (a:=173) (b:=174) (joinSmall (lo:=14600) (a:=86) (b:=87) (joinSmall (lo:=14600) (a:=43) (b:=43) sp14600 sp14643) (joinSmall (lo:=14686) (a:=43) (b:=44) sp14686 sp14729)) (joinSmall (lo:=14773) (a:=87) (b:=87) (joinSmall (lo:=14773) (a:=43) (b:=44) sp14773 sp14816) (joinSmall (lo:=14860) (a:=43) (b:=44) sp14860 sp14903))) (joinSmall (lo:=14947) (a:=174) (b:=174) (joinSmall (lo:=14947) (a:=87) (b:=87) (joinSmall (lo:=14947) (a:=43) (b:=44) sp14947 sp14990) (joinSmall (lo:=15034) (a:=43) (b:=44) sp15034 sp15077)) (joinSmall (lo:=15121) (a:=87) (b:=87) (joinSmall (lo:=15121) (a:=43) (b:=44) sp15121 sp15164) (joinSmall (lo:=15208) (a:=43) (b:=44) sp15208 sp15251))))) (joinSmall (lo:=15295) (a:=695) (b:=696) (joinSmall (lo:=15295) (a:=347) (b:=348) (joinSmall (lo:=15295) (a:=173) (b:=174) (joinSmall (lo:=15295) (a:=86) (b:=87) (joinSmall (lo:=15295) (a:=43) (b:=43) sp15295 sp15338) (joinSmall (lo:=15381) (a:=43) (b:=44) sp15381 sp15424)) (joinSmall (lo:=15468) (a:=87) (b:=87) (joinSmall (lo:=15468) (a:=43) (b:=44) sp15468 sp15511) (joinSmall (lo:=15555) (a:=43) (b:=44) sp15555 sp15598))) (joinSmall (lo:=15642) (a:=174) (b:=174) (joinSmall (lo:=15642) (a:=87) (b:=87) (joinSmall (lo:=15642) (a:=43) (b:=44) sp15642 sp15685) (joinSmall (lo:=15729) (a:=43) (b:=44) sp15729 sp15772)) (joinSmall (lo:=15816) (a:=87) (b:=87) (joinSmall (lo:=15816) (a:=43) (b:=44) sp15816 sp15859) (joinSmall (lo:=15903) (a:=43) (b:=44) sp15903 sp15946)))) (joinSmall (lo:=15990) (a:=348) (b:=348) (joinSmall (lo:=15990) (a:=174) (b:=174) (joinSmall (lo:=15990) (a:=87) (b:=87) (joinSmall (lo:=15990) (a:=43) (b:=44) sp15990 sp16033) (joinSmall (lo:=16077) (a:=43) (b:=44) sp16077 sp16120)) (joinSmall (lo:=16164) (a:=87) (b:=87) (joinSmall (lo:=16164) (a:=43) (b:=44) sp16164 sp16207) (joinSmall (lo:=16251) (a:=43) (b:=44) sp16251 sp16294))) (joinSmall (lo:=16338) (a:=174) (b:=174) (joinSmall (lo:=16338) (a:=87) (b:=87) (joinSmall (lo:=16338) (a:=43) (b:=44) sp16338 sp16381) (joinSmall (lo:=16425) (a:=43) (b:=44) sp16425 sp16468)) (joinSmall (lo:=16512) (a:=87) (b:=87) (joinSmall (lo:=16512) (a:=43) (b:=44) sp16512 sp16555) (joinSmall (lo:=16599) (a:=43) (b:=44) sp16599 sp16642))))))) (joinSmall (lo:=16686) (a:=2781) (b:=2782) (joinSmall (lo:=16686) (a:=1390) (b:=1391) (joinSmall (lo:=16686) (a:=695) (b:=695) (joinSmall (lo:=16686) (a:=347) (b:=348) (joinSmall (lo:=16686) (a:=173) (b:=174) (joinSmall (lo:=16686) (a:=86) (b:=87) (joinSmall (lo:=16686) (a:=43) (b:=43) sp16686 sp16729) (joinSmall (lo:=16772) (a:=43) (b:=44) sp16772 sp16815)) (joinSmall (lo:=16859) (a:=87) (b:=87) (joinSmall (lo:=16859) (a:=43) (b:=44) sp16859 sp16902) (joinSmall (lo:=16946) (a:=43) (b:=44) sp16946 sp16989))) (joinSmall (lo:=17033) (a:=174) (b:=174) (joinSmall (lo:=17033) (a:=87) (b:=87) (joinSmall (lo:=17033) (a:=43) (b:=44) sp17033 sp17076) (joinSmall (lo:=17120) (a:=43) (b:=44) sp17120 sp17163)) (joinSmall (lo:=17207) (a:=87) (b:=87) (joinSmall (lo:=17207) (a:=43) (b:=44) sp17207 sp17250) (joinSmall (lo:=17294) (a:=43) (b:=44) sp17294 sp17337)))) (joinSmall (lo:=17381) (a:=347) (b:=348) (joinSmall (lo:=17381) (a:=173) (b:=174) (joinSmall (lo:=17381) (a:=86) (b:=87) (joinSmall (lo:=17381) (a:=43) (b:=43) sp17381 sp17424) (joinSmall (lo:=17467) (a:=43) (b:=44) sp17467 sp17510)) (joinSmall (lo:=17554) (a:=87) (b:=87) (joinSmall (lo:=17554) (a:=43) (b:=44) sp17554 sp17597) (joinSmall (lo:=17641) (a:=43) (b:=44) sp17641 sp17684))) (joinSmall (lo:=17728) (a:=174) (b:=174) (joinSmall (lo:=17728) (a:=87) (b:=87) (joinSmall (lo:=17728) (a:=43) (b:=44) sp17728 sp17771) (joinSmall (lo:=17815) (a:=43) (b:=44) sp17815 sp17858)) (joinSmall (lo:=17902) (a:=87) (b:=87) (joinSmall (lo:=17902) (a:=43) (b:=44) sp17902 sp17945) (joinSmall (lo:=17989) (a:=43) (b:=44) sp17989 sp18032))))) (joinSmall (lo:=18076) (a:=695) (b:=696) (joinSmall (lo:=18076) (a:=347) (b:=348) (joinSmall (lo:=18076) (a:=173) (b:=174) (joinSmall (lo:=18076) (a:=86) (b:=87) (joinSmall (lo:=18076) (a:=43) (b:=43) sp18076 sp18119) (joinSmall (lo:=18162) (a:=43) (b:=44) sp18162 sp18205)) (joinSmall (lo:=18249) (a:=87) (b:=87) (joinSmall (lo:=18249) (a:=43) (b:=44) sp18249 sp18292) (joinSmall (lo:=18336) (a:=43) (b:=44) sp18336 sp18379))) (joinSmall (lo:=18423) (a:=174) (b:=174) (joinSmall (lo:=18423) (a:=87) (b:=87) (joinSmall (lo:=18423) (a:=43) (b:=44) sp18423 sp18466) (joinSmall (lo:=18510) (a:=43) (b:=44) sp18510 sp18553)) (joinSmall (lo:=18597) (a:=87) (b:=87) (joinSmall (lo:=18597) (a:=43) (b:=44) sp18597 sp18640) (joinSmall (lo:=18684) (a:=43) (b:=44) sp18684 sp18727)))) (joinSmall (lo:=18771) (a:=348) (b:=348) (joinSmall (lo:=18771) (a:=174) (b:=174) (joinSmall (lo:=18771) (a:=87) (b:=87) (joinSmall (lo:=18771) (a:=43) (b:=44) sp18771 sp18814) (joinSmall (lo:=18858) (a:=43) (b:=44) sp18858 sp18901)) (joinSmall (lo:=18945) (a:=87) (b:=87) (joinSmall (lo:=18945) (a:=43) (b:=44) sp18945 sp18988) (joinSmall (lo:=19032) (a:=43) (b:=44) sp19032 sp19075))) (joinSmall (lo:=19119) (a:=174) (b:=174) (joinSmall (lo:=19119) (a:=87) (b:=87) (joinSmall (lo:=19119) (a:=43) (b:=44) sp19119 sp19162) (joinSmall (lo:=19206) (a:=43) (b:=44) sp19206 sp19249)) (joinSmall (lo:=19293) (a:=87) (b:=87) (joinSmall (lo:=19293) (a:=43) (b:=44) sp19293 sp19336) (joinSmall (lo:=19380) (a:=43) (b:=44) sp19380 sp19423)))))) (joinSmall (lo:=19467) (a:=1391) (b:=1391) (joinSmall (lo:=19467) (a:=695) (b:=696) (joinSmall (lo:=19467) (a:=347) (b:=348) (joinSmall (lo:=19467) (a:=173) (b:=174) (joinSmall (lo:=19467) (a:=86) (b:=87) (joinSmall (lo:=19467) (a:=43) (b:=43) sp19467 sp19510) (joinSmall (lo:=19553) (a:=43) (b:=44) sp19553 sp19596)) (joinSmall (lo:=19640) (a:=87) (b:=87) (joinSmall (lo:=19640) (a:=43) (b:=44) sp19640 sp19683) (joinSmall (lo:=19727) (a:=43) (b:=44) sp19727 sp19770))) (joinSmall (lo:=19814) (a:=174) (b:=174) (joinSmall (lo:=19814) (a:=87) (b:=87) (joinSmall (lo:=19814) (a:=43) (b:=44) sp19814 sp19857) (joinSmall (lo:=19901) (a:=43) (b:=44) sp19901 sp19944)) (joinSmall (lo:=19988) (a:=87) (b:=87) (joinSmall (lo:=19988) (a:=43) (b:=44) sp19988 sp20031) (joinSmall (lo:=20075) (a:=43) (b:=44) sp20075 sp20118)))) (joinSmall (lo:=20162) (a:=348) (b:=348) (joinSmall (lo:=20162) (a:=174) (b:=174) (joinSmall (lo:=20162) (a:=87) (b:=87) (joinSmall (lo:=20162) (a:=43) (b:=44) sp20162 sp20205) (joinSmall (lo:=20249) (a:=43) (b:=44) sp20249 sp20292)) (joinSmall (lo:=20336) (a:=87) (b:=87) (joinSmall (lo:=20336) (a:=43) (b:=44) sp20336 sp20379) (joinSmall (lo:=20423) (a:=43) (b:=44) sp20423 sp20466))) (joinSmall (lo:=20510) (a:=174) (b:=174) (joinSmall (lo:=20510) (a:=87) (b:=87) (joinSmall (lo:=20510) (a:=43) (b:=44) sp20510 sp20553) (joinSmall (lo:=20597) (a:=43) (b:=44) sp20597 sp20640)) (joinSmall (lo:=20684) (a:=87) (b:=87) (joinSmall (lo:=20684) (a:=43) (b:=44) sp20684 sp20727) (joinSmall (lo:=20771) (a:=43) (b:=44) sp20771 sp20814))))) (joinSmall (lo:=20858) (a:=695) (b:=696) (joinSmall (lo:=20858) (a:=347) (b:=348) (joinSmall (lo:=20858) (a:=173) (b:=174) (joinSmall (lo:=20858) (a:=86) (b:=87) (joinSmall (lo:=20858) (a:=43) (b:=43) sp20858 sp20901) (joinSmall (lo:=20944) (a:=43) (b:=44) sp20944 sp20987)) (joinSmall (lo:=21031) (a:=87) (b:=87) (joinSmall (lo:=21031) (a:=43) (b:=44) sp21031 sp21074) (joinSmall (lo:=21118) (a:=43) (b:=44) sp21118 sp21161))) (joinSmall (lo:=21205) (a:=174) (b:=174) (joinSmall (lo:=21205) (a:=87) (b:=87) (joinSmall (lo:=21205) (a:=43) (b:=44) sp21205 sp21248) (joinSmall (lo:=21292) (a:=43) (b:=44) sp21292 sp21335)) (joinSmall (lo:=21379) (a:=87) (b:=87) (joinSmall (lo:=21379) (a:=43) (b:=44) sp21379 sp21422) (joinSmall (lo:=21466) (a:=43) (b:=44) sp21466 sp21509)))) (joinSmall (lo:=21553) (a:=348) (b:=348) (joinSmall (lo:=21553) (a:=174) (b:=174) (joinSmall (lo:=21553) (a:=87) (b:=87) (joinSmall (lo:=21553) (a:=43) (b:=44) sp21553 sp21596) (joinSmall (lo:=21640) (a:=43) (b:=44) sp21640 sp21683)) (joinSmall (lo:=21727) (a:=87) (b:=87) (joinSmall (lo:=21727) (a:=43) (b:=44) sp21727 sp21770) (joinSmall (lo:=21814) (a:=43) (b:=44) sp21814 sp21857))) (joinSmall (lo:=21901) (a:=174) (b:=174) (joinSmall (lo:=21901) (a:=87) (b:=87) (joinSmall (lo:=21901) (a:=43) (b:=44) sp21901 sp21944) (joinSmall (lo:=21988) (a:=43) (b:=44) sp21988 sp22031)) (joinSmall (lo:=22075) (a:=87) (b:=87) (joinSmall (lo:=22075) (a:=43) (b:=44) sp22075 sp22118) (joinSmall (lo:=22162) (a:=43) (b:=44) sp22162 sp22205)))))))))
  have good : (List.range 22249).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 495000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 22248 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 22248 := by
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


private def packet (i : ℕ) : ℕ := (if i < 126 then (if i < 63 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0 else 0) else (if i < 10 then 0 else 0)) else (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else 0)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0 else 0) else (if i < 18 then 0 else 0)) else (if i < 21 then (if i < 20 then 0 else 0) else (if i < 22 then 0 else 0))) else (if i < 27 then (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else 0)) else (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else 0))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then 0 else 0) else (if i < 34 then 0 else 0)) else (if i < 37 then (if i < 36 then 0 else 0) else (if i < 38 then 0 else 0))) else (if i < 43 then (if i < 41 then (if i < 40 then 0 else 0) else (if i < 42 then 0 else 0)) else (if i < 45 then (if i < 44 then 0 else 0) else (if i < 46 then 0 else 0)))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then 0 else 0) else (if i < 50 then 0 else 0)) else (if i < 53 then (if i < 52 then 0 else 0) else (if i < 54 then 0 else 0))) else (if i < 59 then (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else 0)) else (if i < 61 then (if i < 60 then 0 else 0) else (if i < 62 then 0 else 0)))))) else (if i < 94 then (if i < 78 then (if i < 70 then (if i < 66 then (if i < 64 then 0 else (if i < 65 then 0 else 0)) else (if i < 68 then (if i < 67 then 0 else 0) else (if i < 69 then 0 else 0))) else (if i < 74 then (if i < 72 then (if i < 71 then 0 else 0) else (if i < 73 then 0 else 0)) else (if i < 76 then (if i < 75 then 0 else 0) else (if i < 77 then 0 else 0)))) else (if i < 86 then (if i < 82 then (if i < 80 then (if i < 79 then 0 else 0) else (if i < 81 then 0 else 0)) else (if i < 84 then (if i < 83 then 0 else 0) else (if i < 85 then 0 else 0))) else (if i < 90 then (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else 0)) else (if i < 92 then (if i < 91 then 0 else 0) else (if i < 93 then 0 else 0))))) else (if i < 110 then (if i < 102 then (if i < 98 then (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else 0)) else (if i < 100 then (if i < 99 then 0 else 0) else (if i < 101 then 0 else 0))) else (if i < 106 then (if i < 104 then (if i < 103 then 0 else 0) else (if i < 105 then 0 else 0)) else (if i < 108 then (if i < 107 then 0 else 0) else (if i < 109 then 0 else 0)))) else (if i < 118 then (if i < 114 then (if i < 112 then (if i < 111 then 0 else 0) else (if i < 113 then 0 else 0)) else (if i < 116 then (if i < 115 then 0 else 0) else (if i < 117 then 0 else 0))) else (if i < 122 then (if i < 120 then (if i < 119 then 0 else 0) else (if i < 121 then 0 else 0)) else (if i < 124 then (if i < 123 then 0 else 0) else (if i < 125 then 0 else 0))))))) else (if i < 189 then (if i < 157 then (if i < 141 then (if i < 133 then (if i < 129 then (if i < 127 then 0 else (if i < 128 then 0 else 0)) else (if i < 131 then (if i < 130 then 0 else 0) else (if i < 132 then 0 else 0))) else (if i < 137 then (if i < 135 then (if i < 134 then 0 else 0) else (if i < 136 then 0 else 0)) else (if i < 139 then (if i < 138 then 0 else 0) else (if i < 140 then 0 else 0)))) else (if i < 149 then (if i < 145 then (if i < 143 then (if i < 142 then 0 else 0) else (if i < 144 then 0 else 0)) else (if i < 147 then (if i < 146 then 0 else 0) else (if i < 148 then 0 else 0))) else (if i < 153 then (if i < 151 then (if i < 150 then 0 else 0) else (if i < 152 then 0 else 0)) else (if i < 155 then (if i < 154 then 0 else 0) else (if i < 156 then 0 else 0))))) else (if i < 173 then (if i < 165 then (if i < 161 then (if i < 159 then (if i < 158 then 0 else 0) else (if i < 160 then 0 else 0)) else (if i < 163 then (if i < 162 then 0 else 0) else (if i < 164 then 0 else 0))) else (if i < 169 then (if i < 167 then (if i < 166 then 0 else 0) else (if i < 168 then 0 else 0)) else (if i < 171 then (if i < 170 then 0 else 0) else (if i < 172 then 0 else 0)))) else (if i < 181 then (if i < 177 then (if i < 175 then (if i < 174 then 0 else 0) else (if i < 176 then 0 else 0)) else (if i < 179 then (if i < 178 then 0 else 0) else (if i < 180 then 0 else 0))) else (if i < 185 then (if i < 183 then (if i < 182 then 0 else 0) else (if i < 184 then 0 else 0)) else (if i < 187 then (if i < 186 then 0 else 0) else (if i < 188 then 0 else 0)))))) else (if i < 220 then (if i < 204 then (if i < 196 then (if i < 192 then (if i < 190 then 0 else (if i < 191 then 0 else 0)) else (if i < 194 then (if i < 193 then 0 else 0) else (if i < 195 then 0 else 0))) else (if i < 200 then (if i < 198 then (if i < 197 then 0 else 0) else (if i < 199 then 0 else 0)) else (if i < 202 then (if i < 201 then 0 else 0) else (if i < 203 then 0 else 0)))) else (if i < 212 then (if i < 208 then (if i < 206 then (if i < 205 then 0 else 0) else (if i < 207 then 0 else 0)) else (if i < 210 then (if i < 209 then 0 else 0) else (if i < 211 then 0 else 0))) else (if i < 216 then (if i < 214 then (if i < 213 then 0 else 0) else (if i < 215 then 0 else 0)) else (if i < 218 then (if i < 217 then 0 else 0) else (if i < 219 then 0 else 0))))) else (if i < 236 then (if i < 228 then (if i < 224 then (if i < 222 then (if i < 221 then 0 else 0) else (if i < 223 then 0 else 0)) else (if i < 226 then (if i < 225 then 0 else 0) else (if i < 227 then 0 else 0))) else (if i < 232 then (if i < 230 then (if i < 229 then 0 else 0) else (if i < 231 then 0 else 0)) else (if i < 234 then (if i < 233 then 0 else 0) else (if i < 235 then 0 else 0)))) else (if i < 244 then (if i < 240 then (if i < 238 then (if i < 237 then 0 else 0) else (if i < 239 then 0x17b29992cd14fc9b04722100ee06be2fb14d88dc3aa175090030c0c8000017b23952d795289da48520e0ee86b22fb14e88f43c0180090030c0d2000017b1db62bb145095a4511f70e306782de14288a439817c09083180d4000017b17b62c894bc9ac47720d0eec6b630115088dc3ba17008602f80be000017b11cf2c3148497c4642070efc6c230214f89003c817608982e40a8000017b0ba42da15549e449721d0f5c6cc30215889503d418609603340d4000017b059e2d215049c247a20e8ef46c230815108f83c418109103040ce000017affc82bb946896c4652038eac6982f514908c438c17208802f00b0000017af9e72c3149898c4642040eb06a82ec14508bc3b617c08982ec0b4000017af4052c0947898c46b2090ea86882f414b08fc3bc18109303040c4000017aee022d695409d84842128f186c630115088f43c016f08b82f00b0000017ae7f22d5151c9c247820c0f106c630014f88dc3a217508b82c80c0000017ae1dc2d7953c9d648d2170f506d030b14f89143ce18309403100c4000017adbe52cf94fc9be47720a0ed46a22f614e88f43b618409202f80c8000017ad5e82d095089cc4792138f306cc30e15b09503ec19209703240c8000017acfd52d715549e848c2190f446d030415008e83c018108b830c0ae000017ac9b02e19598a0c4a721b0f606ec30e15909403d618209403180ba000017ac3bd2ca14d49a446c2030e906922f114708c83c4181091030c0c4000017abdd12ca14c89a44732068eb06982f314d88f83b217d08b83040ba000017ab7c62d795249b847820b8f006ce30215308d43a017708602cc0c8000017ab1e52c614b098e4642000ea069e2f114f88e43b217508a03040ba000017aabcd2da15109aa4732048e9c6942eb14808c439417108a02dc0ba000017aa5f22c394b499c4752098edc6ac2ec14188943a217609203040b4000017a9fe92da95489ea4932180f106ce30f15a89483e818609803300d4000017a99f32cb14e09a847920a0ecc6ae2fc14d88f43b417108582b40ae000017a93d32de955c9dc48e2178f306e431116189683e418909383140ba000017a8df22c014c09a847c2180f386ce30a14f89083d418809483180ba000017a881d2bc14549764652018ea068c2e714708c03ac17608982e40b2000017a82142cc94c098c45d2068eb86a02f814c08e83b217109102e80c0000017a7c0d2cf94ec9bc47620a8efc6ac2fc14e08e03a617c08f03100d0000017a761a2cc14dc9904772090eac6902f414f891c3c417e08a02dc0b0000017a6fff2dd15409e449521e0f1c6b0304155093c3d818809083200c2000017a69eb2d395189d04872130f046bc2fd14c88f03be17f09003040c6000017a63d62dd15389ba47a20f0f086c030114e88ec3b417f09102ec0c2000017a5de02cf94bc99647020a0ef06b42f614888d43b217108802e80c8000017a57e12cf95049c44812148f0c6da31215789143ae17208802e00b4000017a51f42c614a898a47320b8f006c430b15509403e818f09703340d4000017a4be92da94fc9dc4882130efc6c430e15809383d818809103100c6000017a45e62d7150c9ca48a2138f046e630e15308f43bc17a08d82ec0b2000017a3fe22d795589ec4992140ef86d22f714f88f83ac17a09083080ae000017a39d92d4954c9ec4902188f186bc30515209043b818008f82d40aa000017a33e52c494b49ba48620d8ec86bc2fc15088d03c0182092030c0ec000017a2dc32de95709e648e2190f646dc30215189103b818709283240c8000017a27af2d995149d04902170f046c6304153890c3c218b08e82cc0c2000017a21c02c714b49a24822160f286d631215689383e218808f83100ce000017a1bca2cc14a49924692068ea86962e614608b839a17808902e80b2000017a15b02da958ca0048f2188f486de31b15709543f018e09603240a8000017a0f9c2d8150c9b848a20c8ee06a02f914c88fc3c8189093031c0d6000017a09982cf15209cc4812170f3c6e0304155093c3ea18c09283140ca000017a036d2e19580a164ac2248fc47483521748a0841a1a80a283780d40000179fd762d1150c9c24852138f146ca30814f89243ba17908c82e00ae0000179f7752ce94fc9bc47a2068edc6a82f315108e83ac17408c02bc0be0000179f1832ca94d099e48020a8ef46b430214c88b83be17d09002fc0c60000179eb892cb94d49b847c20e0f046aa2f414e090c3c018409283200da0000179e5a52c714b899e47620b8ef86ca30115188fc3d218609302f00bc0000179dfc62c094b498e46e2060eac6a42eb144889837e16708902e00a60000179d9c52c894b898e46920b0ebc68e2e314608dc3ae17709002e40b40000179d3be2cc14d49b84802098ec46a42f315089083c417f08e83100ca0000179cdbf2ce15049c64822108ebc6b030015309143d217b08e82e80b60000179c7ae2d594fc9de4872138f0c6c830915208f43b017d09183440c60000179c1d12b6944c9704571fe8ea86942f915088f83b817f08782d80ac0000179bbbd2d515289d448b2150f4c6e231415689043c018709083080c60000179b5b72d5951c9ca4892178f4c6ea30b15289143c818108c82e00c40000179afd12c614a49884612060ee46942ed14708c039e17608a82e80b2000 else 0x17caa8a2dd95989fe49b21b8f646fa31a15d09503c617e09103200d0000017ca4792da150c9cc48e21c0f506f831215c09143d217e08a02cc0b0000017c9e832c914d09a24702078ecc6b62fe15388d83b617708a02dc0ba000017c98792cd14fc9ac4872130f206bc2f414988d83b817f08d83100bc000017c926f2d515749e249721d8f606d831015c896c3dc18609983140d6000017c8c682cf15009bc4802160f146b22ff153890c3b217408d82d00c2000017c86802c614c49ae47320b0f046b22ff15009343d818409183200b6000017c80ca2a694009564501fd0e686802e1137086c36815008002ac0ae000017c7a942e29588a0249921e8f846fc31515989343dc18b09203000c8000017c74812dc95609dc4892138f546ec316159092c3e418a08f83080c6000017c6e7d2d315309d44872168f1c6dc31215b09583d8193096030c0be000017c686c2d695589d048720e0ee06a62f514b09003c418008f02fc0be000017c62912bc94549844692050e7866c2dc14288ac39e17708702b80b6000017c5c7b2de15509de48f21b8f806f631d15f09603f618d09803280c2000017c56472eb15b8a204ac2280fd870c32b16489683ee19009583280ce000017c50742bd94649804682020ea068e2f214b88e03b817c08c02f40b8000017c4a892c094809724521fb0e606542d013a885837616108482dc0bc000017c44982cc94f49ac4792090ed46a42f514808cc39816b08502dc0b6000017c3e7f2d695309c847f20f8ef46b22fe15509343d618809082e40bc000017c387a2d795489d848e2180f1c6ca30c155892c3e018d094831c0ca000017c325f2d715409d448520c8f086dc307151091c3c018209203180b4000017c2c752ca94bc9984622060ec46a42f814d08f43ba17608b02ec0be000017c26512dc95609e64902138f206d02fe15088e83b617a08c82f40bc000017c207f2b8144496e45f1fe0e9068c2f414788bc3ba18008e82fc0ce000017c1a382ef95e0a184ac2210f606f631215909503d619509903240c8000017c142a2d815409e04922180f2c6d62ff14e89083ac17b08a02f40c2000017c0e642b514509804652070ed86b22f314d89103d017a08802b0092000017c083e2e4956c9fe49321b0f1c6c830315509283c818408f83000bc000017c02242e395a4a0e4a12230f6c6f6312161099040819f09e03600cc000017bfc3e2be94a096e4612018e986982e4143088837616b08502d40ba000017bf6492ca14f49ba47d2108f206ae302150891c3dc19409803180c2000017bf04e2d115049ce4862110f286e431015189143d218809082d40ae000017bea502cf95209b847720f8f086c230414c88cc3b017608982dc0aa000017be4622c714e09c047920c0f0c6c02fe15309283d618909803000b4000017bde622ce14bc99446b2040e946862e514208b83a817408f82e00b6000017bd8572d315009b847b20c0ee069e2fc14788e03aa17e08d82e00c0000017bd26d2c994d89c448220c8ee46ae2fd14d88fc3ba17f08b82f40b0000017bcc3f2e695cca2a4b02288fcc73433a16389983fc18d09283300da000017bc6272d915589e64822138f046b42f514f08d83b017a08a82e40ac000017bc0312d114e49be47620a8ee46a82f714908c039216b08b82cc0be000017bba382cc14c49b647c20f8ee46c4301150090c3aa17a08c02f00ba000017bb4312d4152c9e44962198f606f631215589143c617d08d83100be000017bae452c194c899e4692030eac6b02fb14c89083ca18309183040ba000017ba8182e295a8a0c4a72218fa470431f15709403f619909e03440d0000017ba20d2d715549f249a2258fac6f631315a09483f819309903080ba000017b9c072d395249e248620f8f1c6ca30614f08fc3cc17f09083180c4000017b95f62d895389e849121d0f386d830815d89703fe1a509703540da000017b900a2ca95009c04822108ee06b42f414e88d43a217708c82ec0c4000017b89e22ea15aca144972190f506e030b15b09243d218709783380c4000017b84122b5943495e45c1fe0e7467a2de13d086c39616008402a00ac000017b7e252c1948897e4652070ed86a82f615589403ce190096032c0d6000017b782d2ca94cc9a047820b8ec86a82ec14b08b438a16e08702a40aa000017b72222d595189d84902148f486e630415389243c818308f83040be000017b6c262d014c89ae48420f8ed06a82f214888bc3a416d08a82d80be000017b660e2db95489e649521d8f6c6ea31715588fc3b618208f82f80be000017b5fdf2e09594a0849a21f8f6c70432015f09943f218a093832c0ce000017b59f02c714b498e4742098ec869c2f814d08c039217b08e03000c4000017b54052ca94c099046720e0f0c6ce30114f89183c818409083200ce000017b4e002ce14fc9c648020e8ef06b22ff15209183da19109983200ca000017b47ca2e51594a0c4a52220fa470e31c15d095c3dc19009903100cc000017b41932ed15e0a2e4b02290f7c70a331169099c4121a40a503740ea000017b3bb22c614e09ac4742078eac6ac2f214608a83b018108f82e80d0000017b35ae2cf95189d24852110f186d2310153091c3da19209403000ce000017b2f892e5959ca144b02258fb4716320160898040019b09a830c0c8000)) else (if i < 242 then (if i < 241 then 0x17e2a6b2ba948c97045e1fd0e5c66e2d313f88ac39e17508b82e80bc000017e246e2cd14d49a64702110f206c82fe15509503e2189097832c0e2000017e1e682d215009e04912160f286ca30415b092c3d218508f03080c4000017e18812c594bc9a44652040ea06a02f114888e43bc17b08782dc0b2000017e12812d014b499246f20e0ed86a82f614e090c3c617e08f02f40bc000017e0c772cd950c9ce4912150f346e230a15208ec3b817708d830c0ac000017e067d2c914a09984782080eb86942fc152090c3c217f09303040bc000017e007f2d115089bc4832168f286d4314157093c3d418d09883540e0000017dfa7d2d5151c9c047320c0eec6b62fc14f09103c8183093831c0ce000017df4912c414709864632020ea06842e1141889039e17308a82fc0b0000017deea82c514b499447e20c8ee86b02fc14e08fc3be17d09303040c4000017de8a42d495209da4852120ef86c230214f091c3bc18408f03100d8000017de2a42cd94ec9ca47a2120f2c6c62fe154891c3da18c09603240c4000017ddc7c2e3158c9fe49b2198f586e430a15989303e418409003140c6000017dd6602db95209e84992210f606e631915b09243cc18809683200ca000017dd0782c594c09a04612010e846922eb14208a838816b08882d00b4000017dca522df95609e44902160f106d2313156891c3c618909102e00c6000017dc48a2b814549764622000e786822e4141086837e16708902bc0ac000017dbe8c2d294dc9ac47820f8eec6a22f514888c03b817408a82c40a2000017db88a2ce94e89ce48d2138ef46b62f714f88e43b4180094031c0ba000017db28a2d1950c9c84852198f6070631b15989343c618209082f80aa000017dacbf2b9141494c4571ff8ea067c2d713c085437216607f02b40be000017da6972df95709ea4912170f486d830d15989583f2194099032c0d2000017da0812d615489de4892190f3c6e830715089303c018109283440d2000017d9a762d9954c9ee48f2198f206c62fd15589403ce18508f02e40c6000017d94642d315049bc47b2120f286e8318157093c3fa19b09a83300ce000017d8e582d2150c9cc4862100f146d031015289143c018308d82f00cc000017d885f2cd14f09ac47b20a8ee86ae2f815108d03aa17a08e03040ca000017d827b2c394a499c46820a8ec06a42f114f09183ce18809182f80be000017d7c762cc94c89984722068eac6b22fb15009043be18209603600e4000017d767b2d014e09ac4762128f246ba30215308f83b818009103040b0000017d70722d395589e84a321b0f546d430415089183c618709303000b4000017d6a842c294cc9b847d20f8f0c6cc31715809383e019209683180b6000017d648b2ca94a899a47420e0ee06b830114e88f03a017109182dc0be000017d5ea92cc14d09a647b2118ee86c6307159093c3d017d091830c0c0000017d58a92d015009c447f20c8efc6b22f1145089039817308902bc0bc000017d52ca2c2149c99e4681fe0e986982ed14608b43aa17908d02fc0c6000017d4cb22dc95389ee49f2228f786ec31415c895c3d618609283140b0000017d46a52d315209cc47b2068ed06b62f514a08e83ba17f08e82fc0ba000017d40812e11590a0c4a32258f8c71832815d89603f019c09a83640ee000017d3a832d014ec9a04772058e986942f715288f03c417a09002fc0c8000017d34992cb14e89a64612038ec869a2f614908c439a17208602d80aa000017d2ea62c814c09be47e2128f4c6e430915889443ca18008f82c80ba000017d28992d995549de48320d0ee46aa307153090c3b417e08e03000c2000017d22b42c714a49a84732058e9c6902e714508bc3a617908b02dc0b6000017d1ca92d595549ec49c21f0f74700320154893c3fc18d09783300ba000017d16b02ca14ec9a446c2088ef46b62fc14d08ec3be18108f82f00b6000017d10b02c994b89984611fd8e5c67e2e9142888037a15a08382ec0b8000017d0ab82cb94dc9a84742080eac6962e814a89043c617b08c02d00b8000017d04c02c814f09b84732080eb46a62e714608d83a417008d03080c0000017cfedd2c0147898c46d2090ec86a82f414a08b43a817a08d03080b6000017cf8e92cc14e89bc4862120efc6c230214b08b439817e08a82f00bc000017cf2c82dd15789f449621f8f406e031615709543ec18f09a830c0c6000017ced062b4143496c45f2038ebc69a2e914c89143c617808e82e00a6000017ce6e42e195c4a204a021c8f446ca30815989503fa19409303340cc000017ce0f52c614a49a447a20f0f0c6be2fc15108f83bc18808f02f00c6000017cdaf32d295449e44952200f606f431715b09303ce18709603400da000017cd4df2db95449fa49821d0f686ee30d15c89243e618c09303180c6000017ccedf2d115289ca48a21a0f3c6f231415a09503e419209382ec0a6000017cc8f42c3947897e4632078edc6be2fb15008fc3c017b09183000b2000017cc2d52da152c9ca47d2118f146dc30214c89083c8179094830c0d2000017cbccb2dd1598a0c4a121e8f846f031515b89283c818209402f80ba000017cb6c82cf94f499c46b20d8efc6b42fe15389383d619309402e80c4000017cb0a72e095b4a124aa2218f5c6ec31a15d893c3ee18d09182ec0b8000 else 0x17faa0a2dc95149aa47420a8ee86b62fc15008e03a417408602b00b4000017fa4172cd14c49ae4772090ee86b02f514c08d03a616e08b82c40bc000017f9e2b2c594f09b447d20a8eec6c2307156893c3e418c09483580c2000017f97fc2ea95b8a2a4b32208f7070031515689383dc18509203000b4000017f91fc2cf95249c24802150f346dc305154891c3e019d09c03540c8000017f8c0b2cb94e09a646d20d0ee869a2fe14a08e43bc17408c02fc0be000017f860d2cd14ec9b647c20b0e986a02ed14b09043b817408c030c0cc000017f7fd62e695d8a184a82270f8870e32d166899c40218c09683140d8000017f79c02db95709e84882168f246b82ff14e89043ae17208d82f80c8000017f73c12d195289c64912100ee46aa2f314808f43c217a094032c0c2000017f6dc22d6953c9e248a2150f486e831015109143be19009583240ca000017f67c92d014fc9c848c2100ef46b42f714d88d83b817308f82f40bc000017f61bc2dd955c9f64a221e8f4c6cc30515108f03bc17708a82e80bc000017f5ba62de958ca0648d2138ee06c430c15408e83be17e08e02dc0ca000017f55c92bb94389624501fc0e806822ee14788c039416e08782a409e000017f4fe82c294989a847920a8ee46ae2fc14e89083c418209483280cc000017f49ed2cc95149ac4682050ec46a62fd15488e43b218909303300d2000017f43fe2c914f89ca48220f8f046c230114b88ec3ba17708c02f40b6000017f3e0a2c894c49b44862180f506de31715909503ce19009683100c2000017f380e2ce94fc9be48a2158f1c6da30d15589383d818d09803080c0000017f320e2d295209d648e2150f246dc31615909543fa19209783000d2000017f2c082cd94e49ac47c2098ed86ac2fd15008f43ac17b08e03180c6000017f26192cd14c899e47620e0f0c6d231415388ec3b418808f02e00a4000017f20252cb94ec9b647720c0ec468c2ec14488e83ba17c09182f80ba000017f1a2a2d114e09cc47d20a0f006c030415389103cc18709483540ca000017f141d2d495089be47420f8efc6c231115c898840219b09282f00bc000017f0e2a2c914f09c44722050ec06a82fd14c88f83c217c09183440d6000017f08302cd94d89ac47c2120f1c6d230815809183d818409383300dc000017f021e2d695449e24812128edc6b22f614908e43ac18109203180cc000017efc3a2c3147496845b1fa8e5866a2d913e88983a017808602d80ca000017ef6062e795c0a344b622b8fbc72832916409b43ee196091030c0c4000017eefff2d295409cc48e2120ef46c4307154092c3da18d09983140a8000017eea062c714d499246d2040e986a42eb145087c37216408082b80b2000017ee3ec2d915509e84942158efc6b62f814d88e43c418a091830c0b8000017ede202b314189444441f38e106562d513e889438416d08983140d8000017ed83b2c2149099846d20c0ef06c230114e88e43b617e09403580b6000017ed24f2c594bc9aa4712068ee069c2ec14888c43b016f08602e80b8000017ecc4c2ce94cc9ba4882128f046ba2fb15008e83b817908f03040c6000017ec62e2de15409d04852180efc6c62fe14c08d03ba17f08b03080be000017ec03a2ca14cc9c24802128ee86b42f614908c038e16c08d82d40aa000017eba312d414fc9be47c20e0f086c030115089203f019609903400d0000017eb44f2bc144496045f2000e946762d8140889038e16f08982b40a6000017eae4a2cf95089ce4862140f586f230e15089143ce17d08d832c0ca000017ea8622c894d89b047a20e8ec069c2f514808cc3b217a08f82f40b6000017ea27b2c2147c9884551fe0e7468a2dd14308a83a817208982ec0b4000017e9c8b2bf949097c4602018e946982e614a88b43b617c08d82fc0cc000017e96762de95789ee49b2198f306e031715c09603de18e09703340ce000017e90742d294ec9cc48220a0ed86bc2ee14688cc39617908f02f80b2000017e8a732ca94fc9b04872128f006c82f114988dc3b217608d83000ca000017e84932c6948497e4692070e9c6842ed14b88d43a017b08c82ec0b2000017e7e912d195309ca4872138f206ba30014d88c438a17b08c83040bc000017e78a22c614b49a04762088ee06ae2f014c88d83aa17908882dc0b2000017e72ae2cb14cc9a04712070ea069c2f014688b43ae18108f82ec0ba000017e6c8d2dc15409f049b2200f786f431715c892c3ee19509a03240c4000017e66872d194f49b448320e8ed46b02f714f08d03aa16808982dc0b8000017e606e2db15789f249b21d8f9870e32616289643ce195097032c0ca000017e5a8b2bf146c9a647c20c8ed46a62f714b88c439817008b82ec0b8000017e54882d8956c9fc49f21f8f806e231c16109443ea18809783280c0000017e4e7f2da954c9da4962180f406ce30315108e83b817c08f82fc0c4000017e48532e01558a0249c2178f186b82f914688b83ba17808b02f40b0000017e42132ef15e0a364c0230900073833c16d09b84241af0a183600d0000017e3c462bd146096645d1fd8eb46902e914708983a817608882e80ca000017e364b2cc150c9ac4832110f406e230b15809603e818d09603400ce000017e30432d515289e048d2170f346d830c154892c3da18e09102f80aa000) else (if i < 243 then 0x1812b602bf14809924672030ea86ac2f914a08a038816a084029c0a80000181251c2f11604a3e4b72290fb072232c169896c3fe19d09983300d600001811f062d895109c447f20e8f006cc30015288f83a417a08f832c0c6000018119122c294bc9b247920c0efc6bc2f915108e83a016f09283040b8000018112fa2d6150c9ba47920b0ee06c030015089203be17d094030c0ca00001810cf92d395009d048e2168f3c6ec31c157894c3e819109403280da000018106f22d2954c9de4842150f446e631215289183cc18508d82f00be000018100f32cc14e09a24692018ea86902ea14788b03b217b08b02d40ac0000180fae62d715409d648c2158f386e4305158091c3ac17d08b02d80b20000180f4d72d3951c9c44802118eec69c2fa14c88bc3a417508b02e00ae0000180eec62dd95449e848d2138f446f432316189983e018909503080c20000180e8b62d895509f649a2178f386f231115a09183d6183095030c0b20000180e29b2d815589de48b2100f146b62f714e08c839817208902ec0b20000180dca52cc14fc9c04802108f2c6c430915409083c618408f03240c80000180d6bc2c4149c99e46e2048ea06a82ef148089839417108a82d40a00000180d0a42da95389ec4912160f206de30c15409083ac16d08882e40b40000180caaa2cf15049ac47a20c8f006cc30114b08d03aa17208982b40c00000180c4a02d3950c9c84732098ecc6a42f414b08cc3a617608d82f80c00000180beaf2cb95149cc4892100f006cc30014e09003ba18308d82dc0bc0000180b89c2d995689f249b2240f9c6fc31d16109503e818f09603280d20000180b2c32c214909964602060ea06a22f314a88c439e17608d02fc0b80000180ac9f2e595b4a184aa2228f7070c31c15a09403dc18008b02d80ce0000180a6b22c594989884612040ea46a22ed14808e03ba17f08f82e40b40000180a0c12cb14bc9a04601fe8ea86942ea14508c839e17008202c00aa00001809a962e615a8a124a421e8f6070831615b095c3d2186090830c0ca000018094992cd95009c64872130f0c6c6307157092c3d218d09c03540de00001808ecd2b914549744652048e946942e1141087838616308602cc0b8000018088c82d194fc9d84892150f006d231615a09583ce18908e03080c2000018082aa2dd15589ee49221b0f3c6e631215489183d018e09082f40a800001807c9b2da95409e64902120ef46be2fc151891c3d018109002f00b0000018076882da15389e249b21e0f786fa32c167898841819909703180c6000018070822d395349de4892198f6470031a16309ac40e192098831c0b800001806aa32c1949898a4632050ed86aa2f414908d83a416a08a02e40be000018064af2c3949899046d20c8ef06a630315088ec3dc17e09202f00c600001805e8b2e095709f24952180f6070232f161092c3d0187092831c0bc0000180586d2dd155c9fc49e21d0f6870832c15e09783ee18809002e809e0000180528e2c6149499c47120c8efc6c82f314e08f83a617508c02dc0bc00001804c8e2d615349e84962178f506e230e15889583f619109103340ce0000180466e2e715b4a1e4af2230f7c6f8313155890c3b8189095031c0c6000018040742cd14ac98445f2048ea069c2ef14388a83a417308c02d80da00001803a8e2c694c099246d2098eb06902ed14788ec3b417e09002fc0be0000180347c2d495189cc4842150ee06a02ea145888439016d08c82d80be00001802e6e2d795389d048020f0edc6ba30314e08f43b416e08b82d00b6000018028632d4951c9da4872148f246cc2fe14f890c3be188090031c0c6000018022622cc94f89ce4962188f0c6b630115609283d418509002f80c000001801c6a2d115049a247d20c0ec06aa2f614988b839817608a82ac0a6000018016802cd14b09b446f2080eb068a2e014488d039a17608e03200dc0000180104e2e595c0a1a4a721e8f346dc31115789643e219509a031c0c200001800a392d595089d648720f0ef46c230315389343ca18709103200de000018004252d9954c9e448d2100f0c6be30414e09283dc19309a03280ca000017ffe1f2d315189da48220f8ef86ba2fa15389043ae17209103000b2000017ff8142d415149c847c20d8f1c6ec31d15789443de18808d02f00ce000017ff2602af13ec93e43f1ed8e006502cf13c088c38016d08602c00b4000017fec452d915509e04932138f146b830414d08d83ae17c08b02e80c2000017fe66d2c1148898246c2058ea467c2e0146889039616d08582ac0a8000017fe05a2d495109ce4882130f286ca30115109283ec18f09903500e0000017fda5d2d595409d24902140f306d430e15689083be17c08e02e80b6000017fd4862be94789984752078ea86a62f514788e03ae17a09083100bc000017fce972cc14e09b648d2110f246e631515989603e618908f02e00b8000017fc8922d615509ea4902100ef069a2fa14688b83a417408e83340c4000017fc2842d8153c9c848220f8ee469e2f114908dc3b617d08f03240da000017fbc682d595189c64802128f206d0306150891c3ae16608e02d80b4000017fb62b2ed95cca224ad2200f846f431115408fc3bc18209003180c8000017fb01e2d595009b447b20b8ee86ba309157092c3ea19309402ec0b8000 else 0x182ac6e2d515089ca4862110f086c630815008d83a417609102f40b80000182a6492e09588a064a82210f686e630c15489043ca18309082dc0ca0000182a0682c114bc99046d2080eec6b22f7150091c3c018e09682fc0b600001829a5f2d395109e248a2150f0c6ca300156091c3c218309303040c0000018294542d915209d448b2160f446e830d154091c3c017908e02d409e00001828e4a2d214fc9c04802130eec6c630415209343d218509783540c6000018288572c6148498646f20c0edc6b82fc14d08f43c017d09083000ca000018282622cb15149cc49121b8f306da30b15409243d618708f02e80b600001827c532d715149ce48720c8ee46a42f714888ec3a217008782e40b8000018276352e515bca0a4a521c0f686ee31c15a094c3de19309583400d4000018270592c0149099c4702080e906882ec14a08d03c217c09203240d600001826a4e2d695109ce4872110efc6ac2f314a89083be17708c82c80bc000018264562cb14c499a46b2040eb868c2e914c08e83ba17e09603140c000001825e342e215509f048e2140f106d430d150091c3c6186096030c0c00000182581a2db15449d848a2148f146c830214e88d03ac17a08c02f40bc000018252142d295349d04812118f2c6c630014f89103d017e08d03000da00001824c022dc1578a0c4ad21f0f6c706324160893c3c2181087829c0a6000018246092cb94b499046e2098f006ac2f714808b83ba18409202fc0ba00001823fe62e115749e24852150efc6ce30014e88ec3b417408d82f80c4000018239ba2e51590a0249921f0f7c6fa31315589403e2189090832c0d2000018233952db957c9f849a2210f886f830415589143b217908d02d80b000001822d842d595049ba47e20d0f146ca30714e89183c418409283080be000018227b32b614489704561fd8e786762e414808c03a817408a82e00bc000018221b02d215209d248c2148f0c6c22fc14e09383da189091030c0ac00001821bdb2bd14789864622008e9c6922f914d08f83c018108a82f80b0000018215d62cd94dc9ac46c2010ea067c2df145088837c16f08982e40a600001820fb62dc95309de48620f0ef46962ef14d08dc3c4186095830c0ba000018209912e295789de49e21c8f806ee30915689203c617408a02cc0bc000018203ae2c014989b047320d0ee46a82ef14788a43a017509082ec0b40000181fdc62c694b49b046a2040eb06ae2fc14808c83aa17508b02f40ba0000181f7db2c594ac99c47020b8ed06a62f314c88f039a17c096031c0b60000181f1d12d395249ce47b20e0eec6c630c15209043c618409303000c00000181eba42e5155ca084a52210f606f431215e09643e418f09083140c80000181e5822df15889f649e21c8f606fc31615a097c3f619209703140d20000181df812cf94fc9d447c20e8f106b42f914b08cc3b618609082d00a60000181d9a42c714bc99a4782078ed06ac2f014788e83be17408382f80980000181d3a52ce94dc9a447520b8ee46b22fb14f88fc3be18a09182fc0b60000181cdb92c814b89944742050ed46a62ef144889c38016f08b82c40b80000181c79d2d895289cc47920e0edc6ae30415289243d818e09582ec0b40000181c1b62c194b499c46f20c0ef86b82e614888a83b217c08e83240e40000181bbec2ba145498647220c8eec6be2ff14908e43a418109602f40be0000181b5aa2e915b0a024a221e8f606f631015d893c3d618309082e40a80000181afaa2cd94e09ac4822150efc6a22f2143888c38c17108502b00ac0000181a9f22ad143896644e1f90e4867e2e814988f43aa18009483140d40000181a3f42d6955c9f64972170f486d431115489303d418009383100b400001819de62de9578a064a121e8fa070231515d09303cc18209002f80d2000018197cf2dd15409ec4912138f286d230715209283e018d09583500dc000018191c52d395189e24852118ef06b230815709403c8188090830c0c000001818bcb2ca94c09a847a20b0eb46942e5144088439016908502b40b2000018185b62d7151c9d04852158f306f231615509143d618d09583300c600001817faf2d49554a064992150f386ce30215789243d218609502f40b2000018179a12d3950c9ce47f21a0f586cc2fd14d08e03bc18a09103140c4000018173b62c414a89a24752108f346d630215409183d2186093832c0c400001816d9d2d495309d248520f0ed86c230414d88f03a817b09103180b4000018167a72d0951c9d247c20f0f046ba30114c88ec3ac16e08502c00b00000181618d2db15509ea4972140f286e030514a88f83a217b09282d80d000001815b872d214f49b047b20a0ec86b830615288fc3c618408802e00ba000018155402f61620a4c4bd2308fe072232f16389ac4021a7097031c0c800001814f252da15709fe4a421d0f8c70031715909543ea18b09403240ca000018149172d795489f449921f8f586ee31f16009683d818e09683240ce0000181433a2c414b49a44732078ec86ba304152892c3ce18a08d82d009e00001813d7f2ad140493a43a1f18e2864e2ce136882036c16208702f40b80000181373d2ed95f8a404c222d8ff873633c16909c040619e09e03380cc000018131422cb14d49a04641fc8e7867e2e1140888839616b08902d40be000))) else (if i < 248 then (if i < 246 then (if i < 245 then 0x1842c842da15649ca47f20e8ef06c630215209103b417908702b40b2000018426ac2ba14489644552060ea86a22f514908ec3ac17b08982e80be000018420c72c594e09a647d2060e7c6702d914208c03aa17308a82d40be00001841ac92cb94dc99447520a0ed46a02ec14608b039016b08b02f00c8000018414cd2cc14f89cc48a2188f546ea31315789103d819109583300ca00001840ead2dd95309ee4922190f446f230e15689243b617e09002fc0b6000018408852ea15c4a124aa2268fe073633b16209944021a209b83340ce000018402512e3159ca064a22250fa46fa31916109803fc19409803200e20000183fc702c5149098645e2020e9869c2ee14708c03a617008c82e40ba0000183f68b2c614a898646920b0ef86c42ee14888d439817108d02f00c60000183f0892d214f49b647920d8f046ca2fa14d08f83c618208b82c40ac0000183ea962c794c899446d2070ec06b830f15388f03c217f09282e00b40000183e4982ca14e89b64872130f406d230815309083cc18909283000c20000183de862d6153c9ea49b21c0f586e030a15489343e618f09202f40b20000183d8722d5151c9d84872158f606d22f914c88ec3a817f08d03040c00000183d2512e195689ea4982160f306d231215d09303c217a08f02b00ac0000183cc6d2c114649824621fd8e606842e814488b03b417509102f00be0000183c68b2c094889904742080ec86962ec145088c39617d09003140c60000183c09d2c994d09a847520a8eb86a42f414788e039e17e09083280c80000183ba8a2d615509ce4872108eec6c02fe14f89043ae18109183100c40000183b4792d515609f449d2200f846f031615709443de18d09703280c80000183ae9c2bd94749744552000e7c6762dc140888039016708b82f40b20000183a8862e0157ca0a4a42198f1c6ce309153891c3c818209102f80be0000183a28c2d0151c9d048720e8f146b62ff14f091c3c818309282f00b400001839c912c914d09ae48320c8f046c22f915209103bc17a08c02d80bc000018396aa2c1145c95e44e1fd0e6c6562d413b087c37016908482a409a000018390952d715249da48e2170f346dc30215008d83ba17e09283040b800001838a642e915ac9f64a42238f946f431115c89403fc18f09803440cc000018384522da150c9d04892170ee46ca2ff14e88f43a817c08d82f80b400001837e6a2c2147897645f1fc0e946962e614b88dc3b017b08b02c40a20000183784d2dd15549f64932190f2c6c82ff14b08a03a817908d03080bc000018372622c694b499846f2058ec86ac2f514f88cc39817809083200c600001836c722c694f49b04672048e946a42f014608ac39e17308502bc0b4000018366882c694ac98a46d2058ea468a2e5142088c39e16e08902e80bc000018360822c994bc99e4752070ec86aa2f414a88ec3cc18409303080bc00001835a9b2c1147097c45d2008e806802e814408a039816e08782f40c0000018354a02ca94d099246b2030ea46a62fd15489083d418e09403340cc00001834ea22c994bc9a447720a8ed06982f314c88fc3ca18309603040c40000183488c2de1578a044922130f206ce30515008fc3c217e08702c00b40000183429d2cb14a49b847c2088ee86bc30414e89103d017e08f03000b200001833c862d895149c847f20c8f0c6c830a15589483dc190094835c0c8000018336ac2c1149c99e47c20e0edc6a42e814808a439217308702d00c20000183308f2e41560a124a02150f406d630815189243d018909083100be00001832ab52c514b49a447620f8f006b22fa14e88e43ae16f08302b40a8000018324c12c314a49a246b2060e9c6a62e814588bc39617e08f03000c400001831eed2bb14749644632038e8867a2e2142889838c17308f82e80b6000018318d02df9570a004a42210f5c6f431315608f83c218109283180bc000018312c02d795389c24832088ee86b82fa14688cc3b817909182f40d800001830cb52d695209c64882150f4c6f632115f099040e19909403140ae000018306d72c5148099647520c0f146d430315509043bc17608c02d40b6000018300af2e1157c9fe4a321c8f8470831a15c897c40419309783280d20000182fac32c594fc9b847d20d8f146d230815289083b817108c82d40be0000182f4b02db95789fe49e2190f2c6e431a158895c3ec19209683280c40000182eea02d7154c9e64802170f2c6c42ff15309143c8185092030c0c20000182e8852da95609f04942170f186c430214f08f03c017908d02e00bc0000182e2922d294f89b247f2108f146bc2fa14d08f83b418008c82ec0ba0000182dc802d595049ba4852178f106ba30615489743ea19609403100ca0000182d69c2c3149499046d20a8ec46902f814d08f83b217c09082e80a60000182d0a22d1952c9ea4942190f5c6da30a15a89803e218409303240ba0000182caa02cd15189de4812180f586e230c15209183c618508d02e80cc0000182c4a62c814cc9b64862140f1c6d030215208e43b017a09383180b00000182bee12ac940c94444b1f70e6c6862ef14b08b43a016e08982d00bc0000182b8ba2df156c9fc4942180f606f231c15e095c3d818b09202e80c00000182b2782f215bca124a62250f6c6f031d15c896840219609f83480dc000 else 0x185ac9a2bd148098a45c1ff8e906842e714508b038a16408602dc0c40000185a6a22ca94dc9ac47920a0ed46a22ef14788c438617408a83000be0000185a0ab2d195089aa47a20b0ecc6a230015088e83b617408c82d409e00001859aa92d115409c64832128ee46b02f414988b039c16a08702c80ca000018594a62d395189cc48120e8f086c630b15709303ce18b09302e00c200001858e782e2157ca0049421d0f346e831615c09603e618809503200c6000018588922c514b09844642038eac6ac2f514e89183d218908f83100ba0000185826d2e3958ca1a4aa2238fa071a32515f89643fe1a20a1835c0e400001857c6f2d014f89b247b20e0ecc6b830615309183be18509282f80b2000018576852c4949c99c47020d0ecc6b030615489083c217a08d82f80c20000185708a2d094e49ae4752110f306d830615088e83c618009102f00c400001856a8c2cf94fc9b04762178f2c6cc30b15208f43c418f09703300d4000018564a92be948c9844682048ea869c2f714908cc3a617e08f03040ca00001855e962d395109c44822118f346d230614e08cc3a617408902d00c0000018558982cb949498e46e2060ed46bc30214d89043b218609082ec0b00000185526e2e0955c9fe49321e0f906f031315d89343da18e08e82fc0c800001854c6c2cf950c9b647820a0ee86b62f315008e43a417408a82e40ac0000185466d2d315189ce48220d0ec06a02fc14f09003c218108a82d80a80000185406e2cc15049c84862100f0c6b830515008e03b217908b83040b600001853a6e2cf950c9c64782088ec06a22ed146088837016508782e40ba0000185343b2e41590a1049a21a8f506e430e154892c3d217a08d83080bc00001852e432c694ac9be4752038e946982f2147091c3ce19009e83540de000018528782b0143096445d1fc8e986802e514388c03b417e09303140de000018522712d215289d848c2158f0c6de31215a89303d618b096831c0b800001851c3d2e815a8a0e4a02210fa46ee31e15a092c3c018309083040be000018516412d094fc9b248620d0ee86aa2f514e89183d618b08e82f40aa000018510612bc947498845a1fd8eac6a22eb14a09043ba17f096030c0bc00001850a4b2d895309ce47c2140f446e831915d09583e619109403240c60000185043e2d695349c647f20f8ef86ba2f914d09083dc195098032c0d00000184fe4e2ce94cc9b647520e8ee06b62fa14d88fc3bc17408982e00bc0000184f8492cf15149ce48a2188f3c6d630e15389183c818409103280cc0000184f2552c714ac99447020f0ef46c02f714788d83b216f08682d00a40000184ec712c5149098846a2080f086d630d15589403d619609a033c0be0000184e68a2c594d09a647a20a8edc6a22f814c09043b417508c82f00c80000184e0772d715489e649721d8f486f231115309103c017608902d00ae0000184da702cd14d49a04722040ec46862de13f888c3a617308b02c40a80000184d45b2d595209d649121b0f506e8321162099c4101a90a7035c0da0000184ce5c2d195089ce48e2150f246d030714e08d83ac17809303100bc0000184c8442dc15489d24932178f50704327166098840419a09c03500ce0000184c2412cf15209c247f2128f406e431a15809403d618608d82dc0ae0000184bc522c4949c9844661ff8eb06962f914d08c03a816e08382b00b20000184b6552cc14e09ac48520e8f006b230314c88f03bc18108d03000c60000184b0732c694b49964752118f2c6cc30414d88c83a817108182dc0b40000184aa792d495049d84872170f106c030815289283e218b09703100c20000184a46e2d394f49ae47920c8ee06cc30715308fc3ec18708f83280be00001849e7e2c614e09b246e2098ec86b830215189083c817f08d03040b6000018498682dd15409e248a2180f386f431e15d09543de19509c83680da0000184927e2c514ac9ae47e2118ef86982f914f89183e4186099830c0c800001848c6e2d815589ec49c21d8f746fc31615b89603ee18e09683100ca0000184866a2d115209ee48f21a0f286ba2fc15008fc3b617708c82ec0be0000184805a2dd95a4a0a4ac2220f6870c32815e89903ee19709e03400c200001847a6c2c994b49b247720f8ef46b22f414d08e43a617708b82f80aa000018474532dc955c9d848220d8ed06b62fd14f89343da17b08e02cc0ac00001846e582ca94c89aa4752100edc6b42fc15609243d018109002e80bc000018468252ec15dca1e49e2170f606f031e15288ec3c418508d82f40bc0000184624d2be14849a247020d8f106ce300154091c3ce18c09403100c800001845c6a2c0947c9804691ff0e746862e114188d03b017108982d80b4000018456552dd15609de4862140f5c6fe31a15d09543d018908f02f00be000018450872bb146097a4611fe8e686762e014308c839e16e08802e40a800001844a942c894d09a047020a0ecc6b830514f08d439c16908702d80b2000018444b82bf14949884682030eac6a22f214908c439a16d08f02ec0be00001843ec92c494889884652050ecc6ac2fe14e090c3bc17c08d02e80be000018438ae2dc1598a104ab2288f9070431b15f896c3e219109903500e8000018432982dd955c9e64992200f546f231715489303d217e08b82b00bc000) else (if i < 247 then 0x1872c802da955c9fa49521c8f6c6d230b15809403fa19d09e03340e6000018726742d6151c9d84882120f206d831315a89243e419009683340ce000018720752d214ec9be48b2160f786e430c14d89043c818109402d40b200001871a952c0949898445d2018e786842dd14008c439817508a82fc0c40000187147c2dc95509f448c2148f006d430d15c09543f218809403080c800001870e952c5148098046a2060e9c6902ee14688cc3b617f08902d00b80000187089b2ce14bc98c4652058ec06a22fc14d08d439217008602cc0ac000018702852db951c9dc48d2140f086bc30a15409283ca17f08d030c0d20000186fc812d795709e64892118f186e0311159093c3e818b096832c0cc0000186f65c2e49570a1a49c21c0f6c6e631215609243ca17d08b82cc0ac0000186f0812bd94909984752080ef46b830214d08e43a417208b02dc0b80000186ea6d2d895509e649e21c8f4c6d230d15489403ea1a109d033c0dc0000186e4582d8155c9f049d21d0f5c6f231215689103b418208e82f40be0000186de2c2de1578a064a22198f486e431015589303b017f08d83080c60000186d80d2df9584a0e4a72218f7c6f030d15609283d618b09502fc0b40000186d2032d715349d64812130f086cc30d15889283d017b08f03000c00000186cc212c494b49a447220a0ec86a62f614d88d43a017908e03080c20000186c6242d195349d248c2180f0c6d231215f89743ea193091031c0c40000186c05a2b8142494e44e1fc0e6c6822dd144889839e17008302d80b00000186ba802c2949c9964672018e746822da14208b839417308c82b40b40000186b4782d5156c9ea4a021e0f686e231215288f83ac17808f02f80b00000186ae892c7949098e46f2050e9c68c2ec14908c83ae17c095032c0d00000186a8712dc95889fa49721f0f846f032015b093c3d418e09a03680cc0000186a2a82ba147098e4712080eb86a22fc14b88cc3b818209082d40c400001869cba2c114a49a44832118f286d831115b09283cc18f09703100be000018696c62cc94f89aa47220d0ed06b030415409383f0195095831c0c6000018690c22d4950c9d24832138f346cc30e15409343d217f08e82ec0d000001868a972e995dca244a72238f846fc31715b09383e018c09602f40be000018684922d594fc9ac47e20f8ed46ae2f415089003c817f09083000c600001867e932cc950c9c648d2128f006b82fe15209003c018008e831c0c4000018678b02c094b89a646a20a0ed46ac2f4148089c3b017f09082cc0a2000018672d82b9946c97c45b2010e8c68c2e714c08c43ac17208d02e80ba00001866cd52cc15009b047920a8ef06ac2f514b88e83ac17a08802e00c4000018666c42da95549f249a21e0f586e830914e89103c018609902f00c2000018660ae2dc9594a0049a21a8f846fe31c15789303ce18308e82ec0b400001865ac52cb14ec9b647720b8ec06ae2f515008d43ba18309202f80c0000018654942ea95cca084982148f406e431b158092c3da18b09303000c600001864e972ce94e89a84882140f0c6ce2fd15008cc3ae17a08b02e80ae000018648bd2be949097a4672010ea86b22fb14c08dc3d017808482d80c2000018642c02ca14fc9b04822120f3c6d430915509303e018e09983180c600001863cb72d795289d048c2140ef86c82fe15189203ce180090831c0d8000018636b92ce95049c847c2108ee46bc30615509343cc18409002f00ba000018630c02d115189dc48c21a0f386d230015188fc3c018109282ec0b200001862a9c2e095849ea4812128f246cc30c159093c3e619109503240c20000186249c2d695409de48f2140ef06b42f914608d039c16d08982b00b000001861e9d2d095089b047b20a8ef86e430c15489203d218808d02d40b4000018618c82c0147497e45c1fc8e8c6a22f014789043b617f08d82c80b0000018612a72df95449ea49521e0f646e630815509103ca18309603440d600001860c732e71590a1a4ab2228fb46fa31515a09503e819809b03280d4000018606822cc14dc9b647320f8f106ce2f214808a839216208082900ac000018600742d395149c648e2150f186bc30014e890c3b218509203000c00000185fa562dd155c9ec48d2158f406da308155892c3d018908f83040d00000185f44c2d595409e44972190f5c6e030715109183ce17808b03080c00000185ee452ce94c099e46a2060ea468a2e114408e03c218208c02fc0b60000185e83a2d5951c9bc4862120ed06ae2f2147088839416608702cc0b60000185e2512c914c499a46f20c8ecc6ae2f514a88ec3b017c08f03080c00000185dc4f2d5154c9d848d2158f2c6cc31615e09643e818c09a831c0c60000185d6862b0940c95244f1fe8e446762d3137086c39a17508f03100c20000185d0a22c6148c98a4622050ea46b42fd15289183ba17f08d82bc0aa0000185ca9d2d2151c9d248320b8ec86a62ff14a09003d018008e02f80b60000185c4b32cb94ac9984712048eb06a22f514c88ec3d018508d82f80c00000185bea62d315109ea48f2148f286cc2f814b08d83ac17708a830c0be0000185b8982d81540a024a02190f506ee31615609043bc17808c82c40b20000185b27e2e19580a1249921e8f446d030715489683ee19009a83240c4000 else 0x188ac4c2d095309c447720d0ed86be30414d08c439c17208b82c80ac0000188a6642c714e89a447920a0f046b22f814d88c43a617908d02d40bc0000188a0652cf94dc9a646b2070eb06a82f515209303de18f09203240c800001889a552d495089b648121a0f6c6fe32615b89403e219209603240ca000018894582cd94d89b447820f0efc6c230915689303d818e09403200ca00001888e572d0150c9ac4722080ed86ba2f814a08e83b018309403080d00000188883f2d815609e04952198f1c6c0301157891c3b417908c02b00a4000018882412d114fc9ba4802080ed06ac30615289783fa19509583400d800001887c3c2ce95249d44932208f546de30615088e43b618009182fc0b6000018876402d395249c44882120f346d630a15689403cc17e09183180dc0000188703f2cd94c89a24722070eb46a22f814e892c3e619309983200b600001886a192d5952c9cc4872118f0c6be306157891c3cc18d08f03040b8000018864252cb14e09c647f20e0f106d030a15709683d618b09083040c600001885e192dc155c9fe49421c0f486e631515589243ca18609182d40ba0000188581d2cd95089c44812060eb86962eb14308b039216d08a02e80b80000188521e2d214e89b047420c0efc6b830615509043b617909203180c400001884c402c0949c97c4622048ec469e2f314588b83ac17308882d80b6000018846562c4149498845f2030e9c6962e6146889c39e172092033c0be000018840762c294d09b64762080ec86ba2fa15309143c817b09002e40b600001883a9d2c1147097c45d2050eb86be2f714988f03a816f08c02f40b8000018834a62ce14f49ae47420c0ecc6ac2f814508943a616908882ec0b000001882ea42d014d099645e2010ea869a2fa14b08d03b617809083040d2000018828ac2c994f89ac4792090ed86aa2fd15088dc3ba186095032c0ca000018822af2d114f49b647920c8ecc6a62f4145089039216f08a82f40bc00001881cc42c2149c99c4652050ec86a62f314988bc3b017408a03000be000018816de2c114b499246c2030eb46862f214908b03b017108c82dc0b0000018810e42d015049c048720e0ee86b22f214b88dc3ce18009302f80bc00001880ac62db956c9f24982188f606ee31a15789103c417d09083180ce000018804a32e495aca1a4ac2260f6c6f431215489383de188094833c0ca0000187fe9e2cd94f89c64832120efc6b42ee14a88b83ae17d08e02e00b40000187f8972d415149d048e2158f8872232516389883f419a09703540ea0000187f2a92c814d89c047f2160f486d831215e89683e218f09783140c60000187ec912dd15589e649821f0f6c6ec31115789383e619409103080c40000187e6ac2c214c49924642028eb06982fc15089183d218409a033c0c60000187e0982d795409d048c2128f346d42fd15389143ba179091830c0c20000187da982cf15209d448120e8ed46ba30814c08bc3a817908902e40ac0000187d4792dd956ca0e4aa2230f7470631d16189503d017b09103300de0000187ce872c894c89bc48320e0ef46ca30d15589343d818708b02d40b40000187c87f2d014f09b647520d0ecc6ba30815309243bc17e08b82e80b40000187c2752d115209bc48920e0efc6b830414e08f43aa17508f82e80b60000187bc872c594c09c44882120ef06ac30214e08d439c16f08302d80ac0000187b67d2d294fc9c447b20e8f046ca2fc15489243c6184090030c0c60000187b08b2c714a89a24792110ef86b230314c88d03ba17e09082fc0c80000187aab22bb146097a46d2060ea86a62f114a88ec3aa17208a82e00b60000187a4b62cf94e89c247c2100f2c6e630a156892c3c6189095033c0b600001879ea22d815509ea4952178f146e230c15a09443e017e08882f40cc000018798c12c214cc9a046f2078ea469a2f014d88f43c417508c02f40ac000018792952e1956c9fc4a52200f606ce30a15a89603e218509603280ce00001878c972d295289ce48e21a8f206be2fe14d88f83d017e08982fc0c0000018786b02bd147499646f20b0edc6c62fb14c08fc3c217e08f03000c4000018780b52d0153c9d848f2158f2c6ee30d15489483e219209603040b200001877a972de9564a064b02230f9071832415a89503e418809083000c80000187748e2d1950c9d64862138ef86ba2fb15108c83a417408b82fc0ba00001876e9d2c894d89b647e20c8f206e430e15408fc3b817309103100d2000018768a02d215089bc47f2108f206d030214f88d03b417f094030c0c0000018762962d015409d24882148f446da30e15789583d818c09403200c400001875c822d815549ee4a52258f9470c31e15d89603d8192096030c0c20000187565f2e2959ca204b12258f8470631915c89703d818909383100c6000018750812c094709944792078f006b62ec14908c03a017a08902c00a800001874a662dd154c9fc4982198f786f4314154890c3cc17c08f831c0c00000187448f2c014b099846f2088ebc6a02fd14708cc3a017508c82fc0c400001873e7e2d694ec9a647420c8ebc6b430915088fc3b217908882f80be000018738842cc95189e048e2118f006b02fb14888e43ba17c08c83100d0000018732982c414a497445d1fa8e706822e313f888438817608c02f40b2000)) else (if i < 250 then (if i < 249 then 0x18a2c2d2d295489ee4a22240fb470c31b15b89483f619b09f83540cc000018a26462c3948498a4652018e846ac2e914588d839a17408602c40ae000018a204f2cb94e09a447d20d0ed86982f614808a43a417608f02f80bc000018a1a112f095dca2a4a92280fb872432c16189643f018409203180c8000018a14092d3151c9cc4822130f146de30815389003d018709583100e4000018a0df92d895109de48a21a0f486d230515208f43c417e08d82f80c6000018a07fb2d715189ec48f2160f406d42fe14708b03b217b08b02f00c2000018a01e02df15309d248e2160f2c6ca30615009103d218808e03040c00000189fbc42da95489da48d2150f406d830815009103c618309202e00aa0000189f5a92e015749f649b21e0f7c6fa31815d09803ea19609583140da0000189efb22c994e89c44822158f586d030f15209183ce18f092832c0bc0000189e9b62cf95009ba4852100eec6aa2fd14f09283d618e09403040c00000189e3cf2c714d49b648020f0ef86ce30b157090c3c818c096033c0dc0000189ddb82de95649de4842150f386e230515889603f4189095034c0cc0000189d79e2df958ca0a49d21e8f686e0310159093c3e819509e034c0cc0000189d1ad2c814d49c847d20d8f346dc31416009783f819809903100b20000189cba62d214f49cc47f2118ef86b62fc14b88c039417308702dc0ae0000189c5c72c094749664551fa0e646882e614508a039c16d08982ec0bc0000189bfc42d094bc9a847920c0ed46be300150890c3a617108a02e00bc0000189b9d32c514a49764531fd0e786902eb14708d83a016f08e030c0ba0000189b3e02c694b49964692050e9868c2e014108dc3b217d08c02fc0b40000189addb2d3951c9d047f20c0ef86e030d15288f43be17c08d02e80c20000189a7b42e215c0a1049e21c0f8471a32516409643f219109883240c00000189a1c42c514a49884611fc8e286742d613f887838a17108b82dc0bc00001899bdf2be948499c47520e8ee46aa2ec14908c43a417b09402f40ce0000189960d2be944096645b1f90e446542cf13d085c38416f08902d00aa000018990092ce94ec9b247420b0ea069c2f314c08e03be17608f02e40aa000018989e32dd9570a0a4a921e8f746f831915989403f419009203000c0000018983f72c594e09b44862118ed469c2f5146889039a17308e03000c800001897e0c2c614c49b04732108f146cc30715209083c417d08c82e00be000018977f82d495189cc48f2148f106da2ff14f89103ac16f08c82f40ac0000189721a2c3149498a4621fd0e6c6662df13d08a039416e08c82e00aa00001896c222cb94d89a847720a0eec6ac2f214d88e83a017b092830c0a4000018966272ca94c899645d2028ea06ba30015289443ec18f095031c0d2000018960132d915649f049f21d0f686f231515d092c3c818909703140c200001895a382ba94449564541fb8e8867e2ee14988c43a817908f02ec0d2000018954362d9951c9ce4862160f386c62fd14f091c3da18b08f82d40c600001894e2f2cc94f09a446a2000e9c6962e914308a039c18009002f00b0000018948412c714b099e46f20c8ecc6b62f514908a439617908d83200c2000018942742bd945c9684591fa8e6c67c2df14488d03ba18b09203000b800001893c752d815549e64902178f306c22fd15008c83b017008d82f80c4000018936662d695109de48a20b8ef06b830814f09003cc19509483140c2000018930422e295949f649b21a0f346e2313156093c3d618e09783280b600001892a362d8954c9e049c21c8f646e831215989283e618509183000cc000018924502c294809ae47720e0f046bc2ff156091c3de18909503040b600001891e462d3150c9c84832108f046b42ff15488c839a16c08702c40a4000018918562c194a499646f2088ea468e2e8141887037815e07f82b80aa000018912652ce950c9e24892170f1c6b02f715389183d418509002f00ba00001890c6d2ca94e89be4882118f146c02f714e89103ca18509683340c4000018906772c914bc97c45b1fe0e7467c2e314408b839416f08a83000ca000018900a22c0948898446a2008e746842de143088839016708782ac0a80000188fab82c614b499846e2080ec86b430415189003c218508d83040c60000188f4af2d395209da48f2128f3c6d430915109043aa16e08202a40aa0000188eeb72cc94c09bc47a20d8ef46a22f714988d43ae16a08282c40980000188e8b72cf14d89a647120a0ec46862e714488c839815e08282b40a20000188e2ba2cc94ec9a047520a8f0c6b82fc14988cc3aa17308b02c80bc0000188dc952df95949fc4a72230f886f231215689343de18b09903040e40000188d6612e6159c9f44a42210fa06fa31c15d09583de18b08f02f00b40000188d0522dc15809f44a321f8f386c0303155894c3e219309503240cc0000188ca5b2cb94fc9c64812130f2c6d230715209143b618a08f02f80c20000188c4772c0147498646c20d0ea469c2ec14388a039216708a82d80b80000188be6f2d595349d44842128f286cc31115709343de18008b82f00bc0000188b85c2d615209e048f2170f406e030514f893c3d018108f82fc0ba0000188b2502d515289ca4812150f246c630415089083c618609a03300d4000 else 0x18bac452c5148c99046f20e8eec6c22f814e08c43aa17e09082e40bc000018ba6542c814c49ac47b20e0edc6be2fb14808d03a416d08602f80c6000018ba03a2dc15749e248620f8f186c030515088f839e16808e02e00c0000018b9a402c994b89ba47b2108efc6ba30414a88b43b217308f82f00aa000018b93f82f29614a404b422b8fbc71031d16089803ea18c099034c0da000018b8e262be949898e4602050ed86b22f414d88f83b817a08f82e80c2000018b88282ca14d89be48520f8ee06a02ec14c88c439817908c82e00ba000018b823b2c294a49924651ff0e346702d813b886438016908482b80c8000018b7c2c2d395189c04832100ee46c02fe15189203c418b09402e80b0000018b765a2bb945896845f2010e946962e714708a03a417508e82f80c2000018b70662c914d099a4792080ec86ac2f714c88dc3c818108d82e40cc000018b6a402e3156c9de49521d0f6c6f632015a89343e418d09402fc0c4000018b64352d595149c647b20b0f386b6305151891c3e018108e02e40b8000018b5dfb2ee95dca244a22218f9c6fc31515a09583e218b09583340d0000018b58062cc94e89a84752118ef86c830f15a89003ba19009a834c0d8000018b52192c694c09a247520f8eec6b02ed14a08d43ac17408902e00c6000018b4c0d2cd94e89a04752090eb867a2e414608b03a217208e03280be000018b460d2cf94e89a447520a8edc6ba2fb15108f03c418b09603400ce000018b40112ca14c09944651fe0e746822ec14908e43b618209383300d4000018b3a0e2d195349c448c2168f4c6d830a15409143ce18a09583240ca000018b34362c494a49a24662028e986842d513e887838a16b08102a8098000018b2e2b2da95209bc4802118f106bc301155092c3f418709b03340de000018b28272d5952c9d04822080ed06ae2fa14b08f83b817d094830c0c0000018b22372c794ac99847a20e8f046d030314d09143d418509583480e0000018b1c2c2d895189cc48520c8ee468c2e4142089c39016808802ec0a6000018b16092e71590a024a52210f8c6fa31515b09403ea18f095030c0c0000018b0fec2dc15689f448e2150f4c6e630c15288fc3b217508c82e00c0000018b09fe2c294ac99a4712070ea067e2e314588d03bc17708f830c0d0000018b041e2c294c899847d20d8f206c830615209003c417d08f02dc0b4000018afdf02e615c4a304ae2210f2c6d030014b89243b818e09783300c2000018af7ee2ce95009b247820b8ef06ba2fd14f89183ca18609483000d0000018af1f82cd14c49b047b20e0ee06b02ff15389183d617c08d02d00cc000018aec1a2bd142c96445c2028ec869a2ec145089038816f08882c40ba000018ae60d2d915549ee49921c8f4c6ce30915488f03bc18209283200d2000018ae0232c3948c98e4682020ec46942f214788b83ae17e08b02e00b8000018ada2c2d015089d04912168f586be30615288fc3b418509083040be000018ad4682b2941c94c43f1ef0e1c6622db141886c38016808d02f00be000018ace702c894e09a047a2050ebc69c2e714908b438616508702b80a8000018ac8802c894c89a646d2058e9c6a62fc14e08e83bc17908e82f00c4000018ac2902c214ac99c47720a8ed46a02f214a88e83d0188094032c0d0000018abc762d995389d648c2140f306d430615289283ce18109502f80b4000018ab6642d695009c647f20e0f0c6d630a15a89443d018709603240cc000018ab0752c814d89a446a2050ee86b82f714888bc3a617e08902d40ca000018aaa4e2df15aca004af2268fc072633316b89c040e1a009d83200d8000018aa45e2c6949c9964692038e986942ec14808b03a617809303000ca000018a9e3a2e195809f04a021f0f9470632c162897c40419309583040b8000018a98602bf146498846a2088ea86a02f515209043d219309a03300c6000018a925d2cf14e89b247e20f8ee06be2fd15408f43d818d094830c0c8000018a8c632d195309be4842118f1c6c430215189143c017f09602fc0be000018a864d2d395209be4782108ed46c830615289043d218009283380c6000018a802a2e5959ca124ad2268f7c6fe31515609303ca18309383280ce000018a7a282d515209c84882138f086c42f614e08d83b017308e02fc0be000018a74192d995409e04852140f186ba2f914b88c43aa17d091831c0c8000018a6e222d095249c648a2138f0c6c631015689443dc18a09502fc0c8000018a67ec2ef1610a304b422b8fcc71a32916309a03f419d099833c0d4000018a61de2d695289e848c2130f146d030b154090c3c817d09102f80aa000018a5bd52d894f09ba47d20d8ee06b030115309283da18b09283080d2000018a55e32c494a89984712080ec46aa2f514c88c03aa17e08b82c40b4000018a50002c6948c97845a2020ea06982f114608d83b817d08d83240d0000018a49d82db15889fc4a321d8f786fa31d15909483e818909803180b8000018a43ed2c2148499646e2048e7c6a22f214908cc39c16d08b82fc0ba000018a3de72ca14c89b247b2138ef86c62ff15488f83d418e09783180c4000018a38092c0145896e4562008e6867c2e414088a839c16b08d02f80b4000018a32382b794509604541f98e506782e8143088838216a08802f40b2000) else (if i < 251 then 0x18d2b692b9944496a45d1ff8e7067e2e1143088c3aa17608802b80aa000018d25602ca94cc9a847f20c0eb46b42f614608bc3a217408c02b40b6000018d1f412df15a8a184a521d8f786fe315159091c3bc18409283380bc000018d196d2ba147498c46d2058e9068e2e314308c83a817308b82ec0ca000018d13752c994f89b848120f8f086da30c157894c3d018008f02f00b6000018d0d4b2e195949f849621d0f6c6f831615689243d818808e02c80b0000018d076a2c394c499a4702080ebc6902df13d086838416308b82dc0ba000018d01672ca94bc9964692088ee86b82f514c09143c618709582f80c6000018cfb502db15609f249621f8f746fe32115e89643d6187091831c0d0000018cf5492d115009c04862100edc6ac2f914a88b43a817d09102f80c4000018cef4b2ca14f09c247f2158f206dc30c15789183c217e09103040d0000018ce9832b594249704662020ea06922f0141889438e16b08802d80ba000018ce3a42c194b498a4692038ed46b42f314e89103c417d08e82e80b6000018cdd8f2db15549d649a2198f2c6d630815709383d618a09402e40aa000018cd7a92bf14b89a04672070f006ce30314f88fc3c017e09203080d4000018cd1b02d515349c247c20e8eb06a22f314f09143ce18509082fc0be000018ccba02d91550a024a12238f9c71e32f16789b440a1a309a03040ca000018cc5ad2cc95009c04862138f1c6c82fc15009143de18b09683100c2000018cbf962db95689d648c2170f1c6b82fb15209043d018008c82d00b6000018cb96a2e895bca0e4a92210f8470631a15c096c3fc19909a032c0d6000018cb3982b6947496e45c1fd0e7867a2f114188a439c17208d02e00ae000018cadd62b5141c9524551ff8e8067e2e514908c03b217008882dc0bc000018ca7b72df1588a0049a21b0f486be2f8144088039c16e08982f80c4000018ca1cb2ca94e49b647e2170f1c6d82fd14888c43a417908e03000ce000018c9bac2e215649dc49721a8f0c6c830415008c03a416708402a80a6000018c95a02d295349c84812128f146c430714f08d03ba17808b03000be000018c8f792e615b4a004ac2250f746de30f15b89383d8185095831c0be000018c89842cb14c09b04842100f106da30e158898c3fa1a709983280c2000018c839b2c514a89a047820f0f186ae2f314708c83a818008e830c0d2000018c7d8f2d715289d44882148f206f231615a89343c618508e82f00c2000018c776e2de953c9e649221f0f606fe322160093c3e618f09702f80c6000018c717b2cc95009c648020f8f146e2314158092c3d018d09283100b6000018c6ba22c0949c9844661fc8e5866e2d814588f43ca18908f02f80b8000018c65802e3157c9ea49121b8f8c71431615e09403e21a409b83080cc000018c5fa82bf147499446e2080ed06a42e514188a439016808a02e80ba000018c59c32bf148497445a1ff8e9c68c2e614908bc3a817e08e02dc0be000018c53f52ba94649744571fc0e786922e914408a439616908782b409c000018c4e172be945c96a4591f98e586782d614208b838c16608582c40a6000018c482a2c794d89ae47620b8ec46ae2ea146089c3a417b09003000b2000018c41f02ef15dca1c4aa21c8f6c6ee30a14f08e83ae17f094830c0b8000018c3bdf2d995509c248120d8ed86b02fa15289243cc186094830c0ca000018c35cb2d6151c9d24902148f186c42ff15609143b817b08f82e40ba000018c2fb52db9570a0a4a52238f9c70e31c15d89683e019009202f80b8000018c29cb2c1947c96e4591fe0e446642dd141886437a15f08082940aa000018c23b52db95649f049d2180f506ec30e15889443e618c09683480e4000018c1dbf2d115149b246f2080ed46a22f314608e83ac18209583140be000018c17b22d595189e64902198f446ea31015989303ba17708c02f80b4000018c119c2da151c9c848e2110f306dc307153093c3e819b09f836c0da000018c0b9a2d815309c84852160f306d030c154892c3e018e09203100ba000018c05992cb14c899846f2068ec46b4301154091c3d2187096033c0d0000018bffab2cd94cc9ae48c2128f0c6cc30215509143b817908e82fc0b6000018bf9cf2c014789884661fb0e7c6822f314b88d03c417d08f83040c4000018bf3e72c514b499e46f2050ea86a42e514608e43c218408f02f40bc000018bedd12d395349d04812130f306d230d15389143ca18408b02c40b8000018be7e72c5948c98e46c20a8eb86902f014708e03c217d09202e80b4000018be1fb2cb14f09a446c2080ec46a22ec14a08a039a17408f02f40ae000018bdbe42d9953c9d848a2150f446d430215189383da18809183000c0000018bd5fd2c914dc9b447b2120ed46ae2fc154894c3c618209483300c4000018bcfe32dc95549f04932158f3c6d430614e891c3b2181096032c0c8000018bc9ef2ca94b899246e20d0ec46a22fe15108d83b818208f82e00b4000018bc3dc2da15349d248e2110ef86c02fe15209103c218509583240c6000018bbdf52c694dc9c447d2128ee86b62fc15189243e018809203280da000018bb8222ba945097445e1fd8e9869a2fb14e88c439817e08f83080c2000018bb2342c514bc99e46f20a8eac6922e6142088c37e16808682ac0c0000 else 0x18e57410000000000000000000000000000000003d218608c02fc0ca000018e51262db95389d648420f8f146c22f614f891c3d618308e82f80b6000018e4b3b2c914f89ba48720e0f346de31115309303da17f08e83180c0000018e45462cd95209d64862130f1c6d4307155891c3ce18009183100d2000018e3f572cd14c099e46820a8ea86ac2fd14b08c43ac17208c82fc0ae000018e39422d615649ec4872108f146cc30415109083c218209183040c8000018e335a2c8948c97a4561fc0e486822ef14e08d03a217308982cc0aa000018e2d4a2dc15889fa4a421c8f606e830e154893c3e618e09083140be000018e274f2cf95189c047d2158f1c6c22fd14d88f83bc17608d82f00c4000018e21662c494a497a45a2030e746782e114188883a017708e02f40b4000018e1b612d395389d848a20f8ec46942f414b88e439c17408c02e00ba000018e15652ce950c9a247020d0f046b230815188e83b617908f02f40c4000018e0f6c2cc94f49d24852108ee86c42fa15008d43b417b09003000b4000018e096b2cc14dc9be4882148f306ca307151890c3c418609383300ca000018e03602d995509e24932210f5c6de30d15989283e218f09783340d6000018dfd772c394b498e4642020e906602d513a087c38216c08602d80b6000018df7542df95789fc49e21b8f5c70431715889543fc19009883280ce000018df17b2c194889864662010e8069a30515289043cc18408f82e80be000018deb642db9578a0049e2210f946f231215509183da18709183000ba000018de56e2c714a898a45c1fe0e746762d013e08b03ae16d08982e40b4000018ddf712cf14dc9c048d2178f346ca30415289283d617f09002d00b8000018dd96c2d015109de49421c0f406e431315809083b818108f030c0c2000018dd3732d095049d447c2110eec6aa2ee14808f03d018809603400d0000018dcd4f2e315889fe4992188f286d230c15e89443e018809282dc0a0000018dc7322e0958c9fc49e2208f646f031715c098040019409603100ce000018dc1812ad94189604551f90e3065a2c8135089438216f08a82f00b2000018dbb862c6948498e4612008e886aa2ef147889439c17608c031c0ca000018db57a2d295349c44762020eac67a2ea14588d83a617508f82fc0aa000018daf922c694a89b84822108f006be2fe14f09203cc18309003100cc000018da9ad2c194b098a4692098ee069c2f014908d43aa17108882d40be000018da39e2d515289f048a2170f346d430d156093c3f619009c031c0ce000018d9dd62b694289684682010e5467c2ec14c891c3ce18108f82f80ce000018d97ce2d895449e649521c0f0c6c62fe15189243ce17508c02f80b8000018d91e22ca15109d847920b8eec6a42ed14888ec3cc18a08f02fc0c4000018d8bb12e395789ec4902150f306d830c156091c3e418108a82d00b8000018d858e2db958ca0e49f2220f906f2313155092c3d619009303180c8000018d7f9e2ce951c9e248a2160f0c6d030a14f08f83c417a09683340c6000018d799a2ce14d09ae47120b0eb469a2f214708f43a417309103040b0000018d737b2d795109b647b20f0ef86c82ff15009203c417d08a02e00b4000018d6d382f61648a524c622c0fc072031f16109783f819109903200ba000018d67462c594f49ae47d2120f286c430815b89443e418d09583280cc000018d613f2d0951c9c84872160f1c6d830315509103c618d08f02e80a8000018d5b4b2cc94909884702068e9c6842eb14888d03a217008a82dc0bc000018d55462d095289d048a2120f0469e2e914c08f43be18309003240c2000018d4f282e31598a084a321b8f606e632216089803ea18909a032c0cc000018d49502c014889824612020eb069c2ef14688e03c8182094030c0d2000018d43382da15609e04902180f586e2307153090c3d018709102e40b6000018d3d262d815149e04852130f086b430115309303d618d09983140be000018d37352c6149c98e45b1ff0eac6a62f814e09183aa17c08d83040ca000018d31402c914b898046c2048e8c67a2e5142089c39217408d82dc0ac000))))))))

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



private theorem b244720 : covered 244720 244845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b244845 : covered 244845 244971 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b244971 : covered 244971 245097 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b245097 : covered 245097 245223 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b245223 : covered 245223 245349 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b245349 : covered 245349 245475 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b245475 : covered 245475 245601 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b245601 : covered 245601 245727 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b245727 : covered 245727 245852 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b245852 : covered 245852 245978 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b245978 : covered 245978 246104 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b246104 : covered 246104 246230 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b246230 : covered 246230 246356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b246356 : covered 246356 246482 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b246482 : covered 246482 246608 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b246608 : covered 246608 246734 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b246734 : covered 246734 246859 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b246859 : covered 246859 246985 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b246985 : covered 246985 247111 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b247111 : covered 247111 247237 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b247237 : covered 247237 247363 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b247363 : covered 247363 247489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b247489 : covered 247489 247615 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b247615 : covered 247615 247741 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b247741 : covered 247741 247866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b247866 : covered 247866 247992 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b247992 : covered 247992 248118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b248118 : covered 248118 248244 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b248244 : covered 248244 248370 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b248370 : covered 248370 248496 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b248496 : covered 248496 248622 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b248622 : covered 248622 248748 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b248748 : covered 248748 248874 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b248874 : covered 248874 249000 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b249000 : covered 249000 249126 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b249126 : covered 249126 249252 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b249252 : covered 249252 249378 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b249378 : covered 249378 249504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b249504 : covered 249504 249630 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b249630 : covered 249630 249756 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b249756 : covered 249756 249881 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b249881 : covered 249881 250007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b250007 : covered 250007 250133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b250133 : covered 250133 250259 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b250259 : covered 250259 250385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b250385 : covered 250385 250511 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b250511 : covered 250511 250637 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b250637 : covered 250637 250763 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b250763 : covered 250763 250888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b250888 : covered 250888 251014 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b251014 : covered 251014 251140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b251140 : covered 251140 251266 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b251266 : covered 251266 251392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b251392 : covered 251392 251518 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b251518 : covered 251518 251644 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b251644 : covered 251644 251770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b251770 : covered 251770 251895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b251895 : covered 251895 252021 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b252021 : covered 252021 252147 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b252147 : covered 252147 252273 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b252273 : covered 252273 252399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b252399 : covered 252399 252525 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b252525 : covered 252525 252651 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b252651 : covered 252651 252777 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b252777 : covered 252777 252902 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b252902 : covered 252902 253028 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b253028 : covered 253028 253154 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b253154 : covered 253154 253280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b253280 : covered 253280 253406 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b253406 : covered 253406 253532 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b253532 : covered 253532 253658 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b253658 : covered 253658 253784 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b253784 : covered 253784 253909 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b253909 : covered 253909 254035 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b254035 : covered 254035 254161 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b254161 : covered 254161 254287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b254287 : covered 254287 254413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b254413 : covered 254413 254539 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b254539 : covered 254539 254665 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b254665 : covered 254665 254791 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b254791 : covered 254791 254916 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b254916 : covered 254916 255042 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b255042 : covered 255042 255168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b255168 : covered 255168 255294 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b255294 : covered 255294 255420 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b255420 : covered 255420 255546 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b255546 : covered 255546 255672 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b255672 : covered 255672 255798 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b255798 : covered 255798 255923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b255923 : covered 255923 256049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b256049 : covered 256049 256175 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b256175 : covered 256175 256301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b256301 : covered 256301 256427 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b256427 : covered 256427 256553 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b256553 : covered 256553 256679 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b256679 : covered 256679 256805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b256805 : covered 256805 256931 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b256931 : covered 256931 257057 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b257057 : covered 257057 257183 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b257183 : covered 257183 257309 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b257309 : covered 257309 257435 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b257435 : covered 257435 257561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b257561 : covered 257561 257687 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b257687 : covered 257687 257813 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 244720 257813 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b244720 (joinCoverage b244845 b244971)) (joinCoverage b245097 (joinCoverage b245223 b245349))) (joinCoverage (joinCoverage b245475 (joinCoverage b245601 b245727)) (joinCoverage (joinCoverage b245852 b245978) (joinCoverage b246104 b246230)))) (joinCoverage (joinCoverage (joinCoverage b246356 (joinCoverage b246482 b246608)) (joinCoverage b246734 (joinCoverage b246859 b246985))) (joinCoverage (joinCoverage b247111 (joinCoverage b247237 b247363)) (joinCoverage (joinCoverage b247489 b247615) (joinCoverage b247741 b247866))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b247992 (joinCoverage b248118 b248244)) (joinCoverage b248370 (joinCoverage b248496 b248622))) (joinCoverage (joinCoverage b248748 (joinCoverage b248874 b249000)) (joinCoverage (joinCoverage b249126 b249252) (joinCoverage b249378 b249504)))) (joinCoverage (joinCoverage (joinCoverage b249630 (joinCoverage b249756 b249881)) (joinCoverage b250007 (joinCoverage b250133 b250259))) (joinCoverage (joinCoverage b250385 (joinCoverage b250511 b250637)) (joinCoverage (joinCoverage b250763 b250888) (joinCoverage b251014 b251140)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b251266 (joinCoverage b251392 b251518)) (joinCoverage b251644 (joinCoverage b251770 b251895))) (joinCoverage (joinCoverage b252021 (joinCoverage b252147 b252273)) (joinCoverage (joinCoverage b252399 b252525) (joinCoverage b252651 b252777)))) (joinCoverage (joinCoverage (joinCoverage b252902 (joinCoverage b253028 b253154)) (joinCoverage b253280 (joinCoverage b253406 b253532))) (joinCoverage (joinCoverage b253658 (joinCoverage b253784 b253909)) (joinCoverage (joinCoverage b254035 b254161) (joinCoverage b254287 b254413))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b254539 (joinCoverage b254665 b254791)) (joinCoverage b254916 (joinCoverage b255042 b255168))) (joinCoverage (joinCoverage b255294 (joinCoverage b255420 b255546)) (joinCoverage (joinCoverage b255672 b255798) (joinCoverage b255923 b256049)))) (joinCoverage (joinCoverage (joinCoverage b256175 (joinCoverage b256301 b256427)) (joinCoverage b256553 (joinCoverage b256679 b256805))) (joinCoverage (joinCoverage b256931 (joinCoverage b257057 b257183)) (joinCoverage (joinCoverage b257309 b257435) (joinCoverage b257561 b257687)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 244720 ≤ index 470000000/512 := by decide +kernel
private theorem starting_value : fast 470000000=24855718 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 470000000=24855718) (n : ℕ) (low : 470000000≤n) (bound : n≤495000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=470000000
    · rw [first,anchor]
      exact starting_value
    · have past : 470000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤495000000 by omega)
        have within : index n / 512 < 257813 := by omega
        have lower : index 470000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤495000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ470000000To495000000
