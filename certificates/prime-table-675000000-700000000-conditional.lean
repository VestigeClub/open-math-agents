import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ675000000To700000000

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




private def radical : ℕ := 0x25a4755bd7e543abaeea0d77548a61a21af15752e7137a205a5aa66be5b5162b73b2d3d85cf7a3448985dbfe3b3ab61635ba8b50d6c89b68dc80f12771f531cf96d993d41ab06bc80ceb78f07ae1f88bb428c328e641d1b327102ad0e46e26fead07c3fcd8fee30fabcca6740ac707c2df6acc8506c06a84f65830e3b2b101c58ee21cc1f00928911271cc8b20f47800786c6aa2e85a489eee76775b868aeb8ba47629acc9bcd696a15aa6f0260729a98c652f071391c843c45ef293539df0674d8415bfbd84e601a668a900c2ef712f76fcf4e03db1bbda6217dd8adf9c102fe7d46bcf530562b70d261643f5e278fbbaed43dcb73f3e3ad924da5746b8499d023f9b161b6d939798853706f64b28609d85c044d4e776b0cfc80f95323f80f3a688ae992e8ddfae19a9182bef6d8c52f013e41cacbbdfbfae533c7d3359afe6123f602aaff3b3d9e33edac9bd2a2e795d72cc02f9688f7dad65fbf3fc445cb55e306b0c5d98ce41cbcc09c0d22612300e45dca25c821cff91b7756f2045e64b4054d8b180cd4cd35d703b9a7a13d4b3b14a42fe29a5b7d0180cce7adedb74c0bf00dd2f8eac461f53f20667dccff8edfec0d23a26ebfabf3034a15a49c5a0d1d8ec239ccc3a2b766e2f17b74a3c01f72375051d333b9903803181abc745b93ec1807e5d43db1e49795f768abdb1142eae2d72b910d8b88c458df2163b8d63c21c26711bf1d451166d715406c382f72187c3160858278daa79df9054e2878c47c1e52650ed5a69d9ce02cc95810d9ad61f33b91086b5d490132cf376faf2ef1d65ab33feef51bf4ecdcb6eb4af537be4f182ff472a49cb2015c2bea5864ffc31934f4696347829e8d310761e3df44b668e59d2f9ca3c9e27e9647a86dd99711378231d6b7fab4a1b79d0cd0291fef7db75f13bbee30bf37be0189f7d8a4960cdc8c6b30fce45d07fe4f54cf65d9d8d26a7c130f8de1e5770eb56a61a3b5093f95072757158407d0f260d20be62afc0267b68dcc271e90bac86e7851b4e27add88ba685ad7c54adbecf48f630c0547b1e0690a104251df65f88d9b3b4a67d3a42891efa8852aa21ab7a03c675d41f167e42f7e0a1f376f9b051dc924523556bd53537f2f79818f7124b6a8d5ee45921ca8ac5e0ed54084e565b4fed0d118c9c80be935a21604e26fce93edd6ee0e1e6403d3320a833e997e7b403aec80255dd87d28eefceaf8475683e92b9bfc00563f8755f18648424fa2c021fbf5128b731cfb0de1cdf792850191605ce98ef891df1143437f0eb3d685c0c905bceb7bf3bbfe072a85fb7b30a5855c91c59ddde9ba87c3bd5b23a6b68599eaa70e0ac061ec7dafcbd6a2e5bc93e7958cedf4462913894dd819a3b3645b94178efe5596a6e1ca22b307ba42415ac0d53db76cf0f0c88bbfd95d3a9dbb83b500c8cf03662cb9a11ae6cb8d12780e95007de86f030b9d0597af4a7912b99e332b6f604715bcb3aa7b94fcef49246ca7b1333dd946b084ed4210600392f6bb2571bcf3ec251fca1c966517f772bac724f724292abb34fe8ae60a1b08e861dacbdc3639461b59ad974e485016e6e8034f3c9198f3155a45dc55074189337acb9e866e360b239fd82d6a3363fa4546ba4e010f87b1203e36b02aab2f4013de3bf488a346c63cb7df06b5707cb058380397b699de196bf4f7c6fc21cd2aa709084ec7a9f0f8e94d022ec04bef1b5b8d2fa8b935748048deea5e906eee6be7d6409b9c578115e8dea3a1e2347d4bfbca201c38f31a916ba3163ed8d7b35926ca5e9a4387e2276ed1b2bf0e9a53816dda4287228a50abb131cea87ea9f31b6fe385879cd9013563ea16bef73ca43718fc246bfe8a2c0b4a6bf86459525c4382059fc6631925570b38a78a7bb9a818ae3104968fd5a93bbb92d3bcb21ccb9340605313ed6b8f9b864b99e16200450585f9f7e699d8e1d2ce47731f8dfaf7c0a4594a2e743f58c0d17ee3a1e707064f5596951d1f3c2fdca17f5398ab21435586dd7d57922810a9029a09892b12c839463f7cea16ba234d979751a384be9442843fa47380e7a7761e61a606dc21a2fd965af5d7b88f6cf1ccdc493132621a872a72e29f31986fee6ed113dace12e66bb65f9a37a9a24dc61839133b4607970a27c5aa6d6eee9e03f9fe9c2ae95deda5bc167bff4a47ba7f150bd77d4f8b2142e871fdc07a0d1e62867d7fd34b3fd2ae06fc26ea5a6750495736075b75ec38bb46434c5b5359f70ed05e62f7cf05b51359db740e89410b0a8176c341fa6eb16dd9b52ed82ebe148ad967b3c939e83369dc276b42e3984f0056e9c3575f061304eb48ddba0f2ff07e411f335f346e3f73911578a80b684f1b8b0a9b3c77d5c1b6d28569edaeb09082764c34fe414eb1ffe9004814da8b9e621e44eab3a881a421fd496016f6dfdd09e0c65775ce506ec6d7a827c0484d61264ef58588f9587efdcc2a4ffb449294d0c76855ff01129a273de4f4e0b9775c645108fbe56433177641b981e6f30c17017a85eef4390ad1a70842ee5783b065975f023382eb17ea52e474cdba070ba67da8c55a5f76b7c7acd0d355c25a7ed9b419700b6e1ff9b5a3a6e73c8455c11d016e422c6eb7a9c81a2e8d31923246a02a72df155208f279b9d879dd8c80761188d2be62df2c0f05d13bb91d6e70591c074b40de5c53bd9c546cae014ac9ac21b379ff67c604862bc19170a1b32712f4c04496af31e5f3cfbaec46982590b768bd3d3c3c1f17c3123079a895ace4f29f6de500e9d067f8633203bc6f7717d71d57e849dbedc00ed865f343981ec4b73ecb3e9788a3c97f86ba9ebcb185448ae20371477d1a53d0f9645c8cf1c8185ef3d2936f6c554a673de8f6565351672e6080a5f208f7f4e0251f72bb79c3011e2751b172304b7bf3f2edece3a165efc4831eb7921643168810f64ed36fd2d1233742e18a62cb5cfba9cecdeeda9bf9e7db0c6f92dd219b09dcf6493cc9618cd43d861ce838ad128f7c9581a80d0526572efeda0e1c06d6fd5bbb69c08c05333457e8e9513d31bfe13ad126f0cc0a085a895bb9c4d83e769d35b539310ad320d06533f09b962d869541c9f1f935439f5cdcb4ee1e84970b1f3433b39d16d130db783ee66d29ac5420673868c8ac7c8f32dec75363db59739b1d181b75ac7b08e42eb28b88e44c3f68749fb377a32c2d4d1f2bf91e0028b4a451318d34f0fd102dc1dc8e0aae8645bdebc087a29814cdefb6dc60ca9c54faf77fab8c611c4633da8a5bdeea6ea63b5c6bed1dbaa678f8d6d75fe360de8d6c836405fad2e67f327ba932ddd9f48df0a89dd5adb76d96c4f2da6f08029c45e1514dfea158a48c79e91f82f845e1c6ab83691bfd877ce3283cc9878d2f9f3110e290cf616acae60f49a7d57ae2ffd439bd1945f91b97aadd6d90946e4db85c0f909ac05d4f56e9b49d87781226f4e02489a52eb3d73c86580cfe426430e60045f2f6844eab541238554161781efa612686ef8e46c0330b1f63346ef485697e4e06f22f556a3fd4673baa8e2a41f28fb2749768a330d87c47895c2a9e7fd99d684873a5dd0ba9e31e8e4a35e30b70a0c3b05e3f2b79f8dca16e72b913a3024b7aa0323e7f2730925c6d9858d3f33b46c5c0de1be6e0d1b003b5f5939d710df8540e035169105c1a1bef7c04a9b1821e02a363e488d7a8bd51543c71dcabd15d0b7e9f8ac1054bf1132e564111221bc71327fcdbc16b3a9244de11dd3dc4613095bc2351454ba51fb379ca9c87d34c3463dac75a9e2b7fcd6b59b51025997d25380fac259a635bbac9537172bedcce5e53a649c437c156b7fe70d4e785bfd8f207fc3e445b6ca94fdeee03fbc96e4152f4619b34f80a921a30795ea5716b5f2156d6b26693d30623b894dbe069eae055f7ab27d5ccef2d86061ce4d76e8378eeb698d4e8859b2b76dee9a6dcb42ba98d0619c0243a801ee23cef7ef1c50f0c161cfa116af3edb4ffec15b32d71429d26153d5bd8b77acfab825c8e84090a56f9571037e66f152313653cea44975bace2d0ceff36e7e1f76ed987ede1b6b108efbc381dff514a9eb3eddce9f47f407c784cb4391a7a7d84891f4d63ec7b7b9986c87b2a4d9bf0ebd5411066c77ba0980f950c446f78b38f78fb6a5990db9c676a4e6f12c03bbc3f01f103b757e0aa2e1dc7a040b36502d4f732024fb410281f10fb2dc902c4992e419ff47a7b7cb2c42df4bafa261742c4c74a5a7182381d4f62a5d5458e14f60ec7b8eff9160c25180ce22b6402493c151f89cd111355713eac0a899ad7941dbd7abf3f7c508336068eb55519c3ff54b82a958518b5c79665d5e9f91f5f8984ca3e9a4411e2f5f57d752e7ecb4441d7bbef5653b62407cb5f4bad9ca1c9880f64a81821104bcbe9c894c38a3de612400ac00c6c111da43b11b531ea54d7c4facb44e37e12fc7afb1070310fbcca1fbf9e59c7261198f25f63d96ef6d9fca26ca2c2225879d696c85ea2709d50158ad9dc2c962c078b3322509731a2f5026ddfea6fb6cf510962533fa32607529e41b4a9ea2a51cc1819f1eac9f2780ddc725eee6d9ce99fad44c5666f563aa51e76bab528576bfc058848cddf960b3726c1aca79a68e7abac6da36a1a0bbdb6e4e01b8fc186f5f7cceda452adc55438c36dc5836175e2cdd11ed0f44bb74dddaf8ea05393e2c0180fa084e86a5c983046f80cb4cb5ef1242e8a031b8e16214ba8c19ec4f1a1a77590da44de199ca731f38dbbe7d04e9b33b2a23689d15ea000e7f5cdc5a48b38304885189f76786df4c6d58d5b9e56afbbab2d0c289db947325cae06f6ba449b9aa55f5a8b2ce9e358c74b3f14641ba90d2695b0b771f0b8fc030c4abd42d07c2f715504ea2e069c7e5c7edf40069573efc866aa5c4f5c529263934282dca5a29934fa4409904040818925f4dfc3131ea3c467db281145e31b05f55f1f02feec6f8336ad74dc9e82dc9d71ca618dcbfaa01352032e0b980d71b5bcf730ae1a6b9f3773f7aeef3b527ee892df2d161083f5929d9473f19b713a5466073c5d3194803cfa732a4287ccc81097a8be201e1ba50b47acb2c7ea2855af17a0c7171c6bb6c4469f0de4f2fc9e2e37331ff77802aa23b19c631152e0c8b529fafb07813ebb8783bd64c5bfc9cf2a55434587f447486bfb58a0879f8ad9b5bdbd73673bb1eed66cea3f1f2db7ae84f8a55d65278eddd5e370d13736c39075985922556f44f34bed2d83f5134a3ce80dd897d94c1a1b5942d8d75fc6be9fec3efcbac14bb50d1faf9b7d90d9abf16d1cef8edaa28e902703bbd91de4d9985d15dcc6efa261d2bfb6f904134f0900a87ad00eb62f3247c751143bcfe6ab0f67a5591cb8467387dd368241882b8a4cbbb008e9131f1ca8466b6d88f55655591833336cba4ae9e6f9ce0165ddf12d1d64944f686d09a508857ffbf831275eaf88c1b8bdbaaef5e0bd358d01abe9224100f485b87417b33d107d09193a5c85b6a42115ff7d3f0d15923257600425b2865545788d3f628b5c890fa6d956bb4877b8409fb89a761d6f1b7d8a9dc603c11857a636dd3888b6c19ebfc1e0f684a1dbf87fdb6e03c2d2af8a04224349d92a55ccd18c47d70c42061f301ce8c9a3af84325082acd808cd879230f6c19eb4417baaf8bb9cec86e62ad7f1d50baf5b1d74ddb850f97388f80e4b973ae899100bc2f5e026c149bb1c11a81bf7b093d40ef0a7439e6f028c6c2c9e7080e0a5b234abfe2c6b1dc6f6e8448e7560aa016179c11c6ffc9562f750788efbe9f10894846b5514238ee0420fd55f4b951341151772caf78f2c67650df2cd65114a8e00139d53593767fa510afd88e42b3e39ee09329deffc2a0f6e82928ecdbe26553a84911f49e7a16b81b001a2d6f188ba413aeb090b82fe7fb89eb7537a626267abd34570f59d4ea7ea58ae0cfe49aec7bb1938bd7b516475c704536fe7c979bd5ffe0b928ad7b5337b11be6e87c1dd3c250abf55b8d1dd854712b0dbcfa5817730820e74149f18985b475b3f1f5f3c608dd7f6f97671d89423683e8c7a5e211ff47cc1f9d75ce9459d26f7ceafbf196652ea4044fe8a848bb608983375fd1beb6d2f0334005a89b8c2818cd213e322ed32b6434d2973a311c508cd8371dc90544ff0af8fbb49fb1ab1ef1b1448c397fda746cca1b984cdc0640c235aca1ec7e208eafad7d60b5a3895ef238e38529f7f430cf9c3e68f2cae25a1c6ca235d486c01598eac3baebee3857569e5ca51a7fdf7b734cab7de860077d89cd548e06a54857ff8c889084117b44653a26d2b843b5ccee916703d6ea6dc82e310914a00d682cbd4ed9ae4393d395d4ce4ad8349437b11d6694cf58c373000413587f8ee8807ddbdb16d6c2d2db579525c3feaa57c47ca0baeccd6758c7db8f3dc63cb112ed5b601ec73879a7271b00700b654ec16b9c4cccf1920b3bbf95920c51861f4584d699b7e2932990b68d6cbaf2a3ffce21918e8ae30d8db1420aa20501932f1b99e27773bf01e011d2dc29e7d980d13733fe4a4efa9638d0b283de0a454f2a2a981808d68ef42d4768432200ea051914c4fb953138868326edfa4bd9a492d654224a66837e03e7f940965db70b745fbb39027eca6c6a1ec2ec4b7e3549e51c0800d11c7754c6537a939bb578c031d4ab2eeed71cd2f6b339849f77fb274fac8de16826

private def light (n : ℕ) : Bool :=
  if n≤162 then decide n.Prime else n.gcd 12296942187394494341101789284917501765723005994271693066207625211678145401177289658609880984670515317835995074429904709708273401807824365415928975695099566042246320538220924308010459938381430588227927174194100982189204709615293198326390773410925903872000000000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤26457) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 162 = 12296942187394494341101789284917501765723005994271693066207625211678145401177289658609880984670515317835995074429904709708273401807824365415928975695099566042246320538220924308010459938381430588227927174194100982189204709615293198326390773410925903872000000000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 162 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤26457 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 51 := by unfold smallValid; decide +kernel

private theorem sp51 : smallValid 51 52 := by unfold smallValid; decide +kernel

private theorem sp103 : smallValid 103 51 := by unfold smallValid; decide +kernel

private theorem sp154 : smallValid 154 52 := by unfold smallValid; decide +kernel

private theorem sp206 : smallValid 206 51 := by unfold smallValid; decide +kernel

private theorem sp257 : smallValid 257 52 := by unfold smallValid; decide +kernel

private theorem sp309 : smallValid 309 52 := by unfold smallValid; decide +kernel

private theorem sp361 : smallValid 361 52 := by unfold smallValid; decide +kernel

private theorem sp413 : smallValid 413 51 := by unfold smallValid; decide +kernel

private theorem sp464 : smallValid 464 52 := by unfold smallValid; decide +kernel

private theorem sp516 : smallValid 516 51 := by unfold smallValid; decide +kernel

private theorem sp567 : smallValid 567 52 := by unfold smallValid; decide +kernel

private theorem sp619 : smallValid 619 51 := by unfold smallValid; decide +kernel

private theorem sp670 : smallValid 670 52 := by unfold smallValid; decide +kernel

private theorem sp722 : smallValid 722 52 := by unfold smallValid; decide +kernel

private theorem sp774 : smallValid 774 52 := by unfold smallValid; decide +kernel

private theorem sp826 : smallValid 826 51 := by unfold smallValid; decide +kernel

private theorem sp877 : smallValid 877 52 := by unfold smallValid; decide +kernel

private theorem sp929 : smallValid 929 51 := by unfold smallValid; decide +kernel

private theorem sp980 : smallValid 980 52 := by unfold smallValid; decide +kernel

private theorem sp1032 : smallValid 1032 51 := by unfold smallValid; decide +kernel

private theorem sp1083 : smallValid 1083 52 := by unfold smallValid; decide +kernel

private theorem sp1135 : smallValid 1135 52 := by unfold smallValid; decide +kernel

private theorem sp1187 : smallValid 1187 52 := by unfold smallValid; decide +kernel

private theorem sp1239 : smallValid 1239 51 := by unfold smallValid; decide +kernel

private theorem sp1290 : smallValid 1290 52 := by unfold smallValid; decide +kernel

private theorem sp1342 : smallValid 1342 52 := by unfold smallValid; decide +kernel

private theorem sp1394 : smallValid 1394 52 := by unfold smallValid; decide +kernel

private theorem sp1446 : smallValid 1446 51 := by unfold smallValid; decide +kernel

private theorem sp1497 : smallValid 1497 52 := by unfold smallValid; decide +kernel

private theorem sp1549 : smallValid 1549 52 := by unfold smallValid; decide +kernel

private theorem sp1601 : smallValid 1601 52 := by unfold smallValid; decide +kernel

private theorem sp1653 : smallValid 1653 51 := by unfold smallValid; decide +kernel

private theorem sp1704 : smallValid 1704 52 := by unfold smallValid; decide +kernel

private theorem sp1756 : smallValid 1756 51 := by unfold smallValid; decide +kernel

private theorem sp1807 : smallValid 1807 52 := by unfold smallValid; decide +kernel

private theorem sp1859 : smallValid 1859 51 := by unfold smallValid; decide +kernel

private theorem sp1910 : smallValid 1910 52 := by unfold smallValid; decide +kernel

private theorem sp1962 : smallValid 1962 52 := by unfold smallValid; decide +kernel

private theorem sp2014 : smallValid 2014 52 := by unfold smallValid; decide +kernel

private theorem sp2066 : smallValid 2066 51 := by unfold smallValid; decide +kernel

private theorem sp2117 : smallValid 2117 52 := by unfold smallValid; decide +kernel

private theorem sp2169 : smallValid 2169 52 := by unfold smallValid; decide +kernel

private theorem sp2221 : smallValid 2221 52 := by unfold smallValid; decide +kernel

private theorem sp2273 : smallValid 2273 51 := by unfold smallValid; decide +kernel

private theorem sp2324 : smallValid 2324 52 := by unfold smallValid; decide +kernel

private theorem sp2376 : smallValid 2376 52 := by unfold smallValid; decide +kernel

private theorem sp2428 : smallValid 2428 52 := by unfold smallValid; decide +kernel

private theorem sp2480 : smallValid 2480 51 := by unfold smallValid; decide +kernel

private theorem sp2531 : smallValid 2531 52 := by unfold smallValid; decide +kernel

private theorem sp2583 : smallValid 2583 51 := by unfold smallValid; decide +kernel

private theorem sp2634 : smallValid 2634 52 := by unfold smallValid; decide +kernel

private theorem sp2686 : smallValid 2686 51 := by unfold smallValid; decide +kernel

private theorem sp2737 : smallValid 2737 52 := by unfold smallValid; decide +kernel

private theorem sp2789 : smallValid 2789 52 := by unfold smallValid; decide +kernel

private theorem sp2841 : smallValid 2841 52 := by unfold smallValid; decide +kernel

private theorem sp2893 : smallValid 2893 51 := by unfold smallValid; decide +kernel

private theorem sp2944 : smallValid 2944 52 := by unfold smallValid; decide +kernel

private theorem sp2996 : smallValid 2996 52 := by unfold smallValid; decide +kernel

private theorem sp3048 : smallValid 3048 52 := by unfold smallValid; decide +kernel

private theorem sp3100 : smallValid 3100 51 := by unfold smallValid; decide +kernel

private theorem sp3151 : smallValid 3151 52 := by unfold smallValid; decide +kernel

private theorem sp3203 : smallValid 3203 52 := by unfold smallValid; decide +kernel

private theorem sp3255 : smallValid 3255 52 := by unfold smallValid; decide +kernel

private theorem sp3307 : smallValid 3307 51 := by unfold smallValid; decide +kernel

private theorem sp3358 : smallValid 3358 52 := by unfold smallValid; decide +kernel

private theorem sp3410 : smallValid 3410 51 := by unfold smallValid; decide +kernel

private theorem sp3461 : smallValid 3461 52 := by unfold smallValid; decide +kernel

private theorem sp3513 : smallValid 3513 51 := by unfold smallValid; decide +kernel

private theorem sp3564 : smallValid 3564 52 := by unfold smallValid; decide +kernel

private theorem sp3616 : smallValid 3616 52 := by unfold smallValid; decide +kernel

private theorem sp3668 : smallValid 3668 52 := by unfold smallValid; decide +kernel

private theorem sp3720 : smallValid 3720 51 := by unfold smallValid; decide +kernel

private theorem sp3771 : smallValid 3771 52 := by unfold smallValid; decide +kernel

private theorem sp3823 : smallValid 3823 51 := by unfold smallValid; decide +kernel

private theorem sp3874 : smallValid 3874 52 := by unfold smallValid; decide +kernel

private theorem sp3926 : smallValid 3926 51 := by unfold smallValid; decide +kernel

private theorem sp3977 : smallValid 3977 52 := by unfold smallValid; decide +kernel

private theorem sp4029 : smallValid 4029 52 := by unfold smallValid; decide +kernel

private theorem sp4081 : smallValid 4081 52 := by unfold smallValid; decide +kernel

private theorem sp4133 : smallValid 4133 51 := by unfold smallValid; decide +kernel

private theorem sp4184 : smallValid 4184 52 := by unfold smallValid; decide +kernel

private theorem sp4236 : smallValid 4236 51 := by unfold smallValid; decide +kernel

private theorem sp4287 : smallValid 4287 52 := by unfold smallValid; decide +kernel

private theorem sp4339 : smallValid 4339 51 := by unfold smallValid; decide +kernel

private theorem sp4390 : smallValid 4390 52 := by unfold smallValid; decide +kernel

private theorem sp4442 : smallValid 4442 52 := by unfold smallValid; decide +kernel

private theorem sp4494 : smallValid 4494 52 := by unfold smallValid; decide +kernel

private theorem sp4546 : smallValid 4546 51 := by unfold smallValid; decide +kernel

private theorem sp4597 : smallValid 4597 52 := by unfold smallValid; decide +kernel

private theorem sp4649 : smallValid 4649 52 := by unfold smallValid; decide +kernel

private theorem sp4701 : smallValid 4701 52 := by unfold smallValid; decide +kernel

private theorem sp4753 : smallValid 4753 51 := by unfold smallValid; decide +kernel

private theorem sp4804 : smallValid 4804 52 := by unfold smallValid; decide +kernel

private theorem sp4856 : smallValid 4856 52 := by unfold smallValid; decide +kernel

private theorem sp4908 : smallValid 4908 52 := by unfold smallValid; decide +kernel

private theorem sp4960 : smallValid 4960 51 := by unfold smallValid; decide +kernel

private theorem sp5011 : smallValid 5011 52 := by unfold smallValid; decide +kernel

private theorem sp5063 : smallValid 5063 51 := by unfold smallValid; decide +kernel

private theorem sp5114 : smallValid 5114 52 := by unfold smallValid; decide +kernel

private theorem sp5166 : smallValid 5166 51 := by unfold smallValid; decide +kernel

private theorem sp5217 : smallValid 5217 52 := by unfold smallValid; decide +kernel

private theorem sp5269 : smallValid 5269 52 := by unfold smallValid; decide +kernel

private theorem sp5321 : smallValid 5321 52 := by unfold smallValid; decide +kernel

private theorem sp5373 : smallValid 5373 51 := by unfold smallValid; decide +kernel

private theorem sp5424 : smallValid 5424 52 := by unfold smallValid; decide +kernel

private theorem sp5476 : smallValid 5476 52 := by unfold smallValid; decide +kernel

private theorem sp5528 : smallValid 5528 52 := by unfold smallValid; decide +kernel

private theorem sp5580 : smallValid 5580 51 := by unfold smallValid; decide +kernel

private theorem sp5631 : smallValid 5631 52 := by unfold smallValid; decide +kernel

private theorem sp5683 : smallValid 5683 52 := by unfold smallValid; decide +kernel

private theorem sp5735 : smallValid 5735 52 := by unfold smallValid; decide +kernel

private theorem sp5787 : smallValid 5787 51 := by unfold smallValid; decide +kernel

private theorem sp5838 : smallValid 5838 52 := by unfold smallValid; decide +kernel

private theorem sp5890 : smallValid 5890 51 := by unfold smallValid; decide +kernel

private theorem sp5941 : smallValid 5941 52 := by unfold smallValid; decide +kernel

private theorem sp5993 : smallValid 5993 51 := by unfold smallValid; decide +kernel

private theorem sp6044 : smallValid 6044 52 := by unfold smallValid; decide +kernel

private theorem sp6096 : smallValid 6096 52 := by unfold smallValid; decide +kernel

private theorem sp6148 : smallValid 6148 52 := by unfold smallValid; decide +kernel

private theorem sp6200 : smallValid 6200 51 := by unfold smallValid; decide +kernel

private theorem sp6251 : smallValid 6251 52 := by unfold smallValid; decide +kernel

private theorem sp6303 : smallValid 6303 52 := by unfold smallValid; decide +kernel

private theorem sp6355 : smallValid 6355 52 := by unfold smallValid; decide +kernel

private theorem sp6407 : smallValid 6407 51 := by unfold smallValid; decide +kernel

private theorem sp6458 : smallValid 6458 52 := by unfold smallValid; decide +kernel

private theorem sp6510 : smallValid 6510 52 := by unfold smallValid; decide +kernel

private theorem sp6562 : smallValid 6562 52 := by unfold smallValid; decide +kernel

private theorem sp6614 : smallValid 6614 51 := by unfold smallValid; decide +kernel

private theorem sp6665 : smallValid 6665 52 := by unfold smallValid; decide +kernel

private theorem sp6717 : smallValid 6717 51 := by unfold smallValid; decide +kernel

private theorem sp6768 : smallValid 6768 52 := by unfold smallValid; decide +kernel

private theorem sp6820 : smallValid 6820 51 := by unfold smallValid; decide +kernel

private theorem sp6871 : smallValid 6871 52 := by unfold smallValid; decide +kernel

private theorem sp6923 : smallValid 6923 52 := by unfold smallValid; decide +kernel

private theorem sp6975 : smallValid 6975 52 := by unfold smallValid; decide +kernel

private theorem sp7027 : smallValid 7027 51 := by unfold smallValid; decide +kernel

private theorem sp7078 : smallValid 7078 52 := by unfold smallValid; decide +kernel

private theorem sp7130 : smallValid 7130 51 := by unfold smallValid; decide +kernel

private theorem sp7181 : smallValid 7181 52 := by unfold smallValid; decide +kernel

private theorem sp7233 : smallValid 7233 51 := by unfold smallValid; decide +kernel

private theorem sp7284 : smallValid 7284 52 := by unfold smallValid; decide +kernel

private theorem sp7336 : smallValid 7336 52 := by unfold smallValid; decide +kernel

private theorem sp7388 : smallValid 7388 52 := by unfold smallValid; decide +kernel

private theorem sp7440 : smallValid 7440 51 := by unfold smallValid; decide +kernel

private theorem sp7491 : smallValid 7491 52 := by unfold smallValid; decide +kernel

private theorem sp7543 : smallValid 7543 51 := by unfold smallValid; decide +kernel

private theorem sp7594 : smallValid 7594 52 := by unfold smallValid; decide +kernel

private theorem sp7646 : smallValid 7646 51 := by unfold smallValid; decide +kernel

private theorem sp7697 : smallValid 7697 52 := by unfold smallValid; decide +kernel

private theorem sp7749 : smallValid 7749 52 := by unfold smallValid; decide +kernel

private theorem sp7801 : smallValid 7801 52 := by unfold smallValid; decide +kernel

private theorem sp7853 : smallValid 7853 51 := by unfold smallValid; decide +kernel

private theorem sp7904 : smallValid 7904 52 := by unfold smallValid; decide +kernel

private theorem sp7956 : smallValid 7956 52 := by unfold smallValid; decide +kernel

private theorem sp8008 : smallValid 8008 52 := by unfold smallValid; decide +kernel

private theorem sp8060 : smallValid 8060 51 := by unfold smallValid; decide +kernel

private theorem sp8111 : smallValid 8111 52 := by unfold smallValid; decide +kernel

private theorem sp8163 : smallValid 8163 52 := by unfold smallValid; decide +kernel

private theorem sp8215 : smallValid 8215 52 := by unfold smallValid; decide +kernel

private theorem sp8267 : smallValid 8267 51 := by unfold smallValid; decide +kernel

private theorem sp8318 : smallValid 8318 52 := by unfold smallValid; decide +kernel

private theorem sp8370 : smallValid 8370 51 := by unfold smallValid; decide +kernel

private theorem sp8421 : smallValid 8421 52 := by unfold smallValid; decide +kernel

private theorem sp8473 : smallValid 8473 51 := by unfold smallValid; decide +kernel

private theorem sp8524 : smallValid 8524 52 := by unfold smallValid; decide +kernel

private theorem sp8576 : smallValid 8576 52 := by unfold smallValid; decide +kernel

private theorem sp8628 : smallValid 8628 52 := by unfold smallValid; decide +kernel

private theorem sp8680 : smallValid 8680 51 := by unfold smallValid; decide +kernel

private theorem sp8731 : smallValid 8731 52 := by unfold smallValid; decide +kernel

private theorem sp8783 : smallValid 8783 52 := by unfold smallValid; decide +kernel

private theorem sp8835 : smallValid 8835 52 := by unfold smallValid; decide +kernel

private theorem sp8887 : smallValid 8887 51 := by unfold smallValid; decide +kernel

private theorem sp8938 : smallValid 8938 52 := by unfold smallValid; decide +kernel

private theorem sp8990 : smallValid 8990 52 := by unfold smallValid; decide +kernel

private theorem sp9042 : smallValid 9042 52 := by unfold smallValid; decide +kernel

private theorem sp9094 : smallValid 9094 51 := by unfold smallValid; decide +kernel

private theorem sp9145 : smallValid 9145 52 := by unfold smallValid; decide +kernel

private theorem sp9197 : smallValid 9197 51 := by unfold smallValid; decide +kernel

private theorem sp9248 : smallValid 9248 52 := by unfold smallValid; decide +kernel

private theorem sp9300 : smallValid 9300 51 := by unfold smallValid; decide +kernel

private theorem sp9351 : smallValid 9351 52 := by unfold smallValid; decide +kernel

private theorem sp9403 : smallValid 9403 52 := by unfold smallValid; decide +kernel

private theorem sp9455 : smallValid 9455 52 := by unfold smallValid; decide +kernel

private theorem sp9507 : smallValid 9507 51 := by unfold smallValid; decide +kernel

private theorem sp9558 : smallValid 9558 52 := by unfold smallValid; decide +kernel

private theorem sp9610 : smallValid 9610 52 := by unfold smallValid; decide +kernel

private theorem sp9662 : smallValid 9662 52 := by unfold smallValid; decide +kernel

private theorem sp9714 : smallValid 9714 51 := by unfold smallValid; decide +kernel

private theorem sp9765 : smallValid 9765 52 := by unfold smallValid; decide +kernel

private theorem sp9817 : smallValid 9817 52 := by unfold smallValid; decide +kernel

private theorem sp9869 : smallValid 9869 52 := by unfold smallValid; decide +kernel

private theorem sp9921 : smallValid 9921 51 := by unfold smallValid; decide +kernel

private theorem sp9972 : smallValid 9972 52 := by unfold smallValid; decide +kernel

private theorem sp10024 : smallValid 10024 51 := by unfold smallValid; decide +kernel

private theorem sp10075 : smallValid 10075 52 := by unfold smallValid; decide +kernel

private theorem sp10127 : smallValid 10127 51 := by unfold smallValid; decide +kernel

private theorem sp10178 : smallValid 10178 52 := by unfold smallValid; decide +kernel

private theorem sp10230 : smallValid 10230 52 := by unfold smallValid; decide +kernel

private theorem sp10282 : smallValid 10282 52 := by unfold smallValid; decide +kernel

private theorem sp10334 : smallValid 10334 51 := by unfold smallValid; decide +kernel

private theorem sp10385 : smallValid 10385 52 := by unfold smallValid; decide +kernel

private theorem sp10437 : smallValid 10437 52 := by unfold smallValid; decide +kernel

private theorem sp10489 : smallValid 10489 52 := by unfold smallValid; decide +kernel

private theorem sp10541 : smallValid 10541 51 := by unfold smallValid; decide +kernel

private theorem sp10592 : smallValid 10592 52 := by unfold smallValid; decide +kernel

private theorem sp10644 : smallValid 10644 52 := by unfold smallValid; decide +kernel

private theorem sp10696 : smallValid 10696 52 := by unfold smallValid; decide +kernel

private theorem sp10748 : smallValid 10748 51 := by unfold smallValid; decide +kernel

private theorem sp10799 : smallValid 10799 52 := by unfold smallValid; decide +kernel

private theorem sp10851 : smallValid 10851 51 := by unfold smallValid; decide +kernel

private theorem sp10902 : smallValid 10902 52 := by unfold smallValid; decide +kernel

private theorem sp10954 : smallValid 10954 51 := by unfold smallValid; decide +kernel

private theorem sp11005 : smallValid 11005 52 := by unfold smallValid; decide +kernel

private theorem sp11057 : smallValid 11057 52 := by unfold smallValid; decide +kernel

private theorem sp11109 : smallValid 11109 52 := by unfold smallValid; decide +kernel

private theorem sp11161 : smallValid 11161 51 := by unfold smallValid; decide +kernel

private theorem sp11212 : smallValid 11212 52 := by unfold smallValid; decide +kernel

private theorem sp11264 : smallValid 11264 52 := by unfold smallValid; decide +kernel

private theorem sp11316 : smallValid 11316 52 := by unfold smallValid; decide +kernel

private theorem sp11368 : smallValid 11368 51 := by unfold smallValid; decide +kernel

private theorem sp11419 : smallValid 11419 52 := by unfold smallValid; decide +kernel

private theorem sp11471 : smallValid 11471 52 := by unfold smallValid; decide +kernel

private theorem sp11523 : smallValid 11523 52 := by unfold smallValid; decide +kernel

private theorem sp11575 : smallValid 11575 51 := by unfold smallValid; decide +kernel

private theorem sp11626 : smallValid 11626 52 := by unfold smallValid; decide +kernel

private theorem sp11678 : smallValid 11678 51 := by unfold smallValid; decide +kernel

private theorem sp11729 : smallValid 11729 52 := by unfold smallValid; decide +kernel

private theorem sp11781 : smallValid 11781 51 := by unfold smallValid; decide +kernel

private theorem sp11832 : smallValid 11832 52 := by unfold smallValid; decide +kernel

private theorem sp11884 : smallValid 11884 52 := by unfold smallValid; decide +kernel

private theorem sp11936 : smallValid 11936 52 := by unfold smallValid; decide +kernel

private theorem sp11988 : smallValid 11988 51 := by unfold smallValid; decide +kernel

private theorem sp12039 : smallValid 12039 52 := by unfold smallValid; decide +kernel

private theorem sp12091 : smallValid 12091 52 := by unfold smallValid; decide +kernel

private theorem sp12143 : smallValid 12143 52 := by unfold smallValid; decide +kernel

private theorem sp12195 : smallValid 12195 51 := by unfold smallValid; decide +kernel

private theorem sp12246 : smallValid 12246 52 := by unfold smallValid; decide +kernel

private theorem sp12298 : smallValid 12298 52 := by unfold smallValid; decide +kernel

private theorem sp12350 : smallValid 12350 52 := by unfold smallValid; decide +kernel

private theorem sp12402 : smallValid 12402 51 := by unfold smallValid; decide +kernel

private theorem sp12453 : smallValid 12453 52 := by unfold smallValid; decide +kernel

private theorem sp12505 : smallValid 12505 51 := by unfold smallValid; decide +kernel

private theorem sp12556 : smallValid 12556 52 := by unfold smallValid; decide +kernel

private theorem sp12608 : smallValid 12608 51 := by unfold smallValid; decide +kernel

private theorem sp12659 : smallValid 12659 52 := by unfold smallValid; decide +kernel

private theorem sp12711 : smallValid 12711 52 := by unfold smallValid; decide +kernel

private theorem sp12763 : smallValid 12763 52 := by unfold smallValid; decide +kernel

private theorem sp12815 : smallValid 12815 51 := by unfold smallValid; decide +kernel

private theorem sp12866 : smallValid 12866 52 := by unfold smallValid; decide +kernel

private theorem sp12918 : smallValid 12918 52 := by unfold smallValid; decide +kernel

private theorem sp12970 : smallValid 12970 52 := by unfold smallValid; decide +kernel

private theorem sp13022 : smallValid 13022 51 := by unfold smallValid; decide +kernel

private theorem sp13073 : smallValid 13073 52 := by unfold smallValid; decide +kernel

private theorem sp13125 : smallValid 13125 52 := by unfold smallValid; decide +kernel

private theorem sp13177 : smallValid 13177 52 := by unfold smallValid; decide +kernel

private theorem sp13229 : smallValid 13229 51 := by unfold smallValid; decide +kernel

private theorem sp13280 : smallValid 13280 52 := by unfold smallValid; decide +kernel

private theorem sp13332 : smallValid 13332 51 := by unfold smallValid; decide +kernel

private theorem sp13383 : smallValid 13383 52 := by unfold smallValid; decide +kernel

private theorem sp13435 : smallValid 13435 51 := by unfold smallValid; decide +kernel

private theorem sp13486 : smallValid 13486 52 := by unfold smallValid; decide +kernel

private theorem sp13538 : smallValid 13538 52 := by unfold smallValid; decide +kernel

private theorem sp13590 : smallValid 13590 52 := by unfold smallValid; decide +kernel

private theorem sp13642 : smallValid 13642 51 := by unfold smallValid; decide +kernel

private theorem sp13693 : smallValid 13693 52 := by unfold smallValid; decide +kernel

private theorem sp13745 : smallValid 13745 51 := by unfold smallValid; decide +kernel

private theorem sp13796 : smallValid 13796 52 := by unfold smallValid; decide +kernel

private theorem sp13848 : smallValid 13848 51 := by unfold smallValid; decide +kernel

private theorem sp13899 : smallValid 13899 52 := by unfold smallValid; decide +kernel

private theorem sp13951 : smallValid 13951 52 := by unfold smallValid; decide +kernel

private theorem sp14003 : smallValid 14003 52 := by unfold smallValid; decide +kernel

private theorem sp14055 : smallValid 14055 51 := by unfold smallValid; decide +kernel

private theorem sp14106 : smallValid 14106 52 := by unfold smallValid; decide +kernel

private theorem sp14158 : smallValid 14158 51 := by unfold smallValid; decide +kernel

private theorem sp14209 : smallValid 14209 52 := by unfold smallValid; decide +kernel

private theorem sp14261 : smallValid 14261 51 := by unfold smallValid; decide +kernel

private theorem sp14312 : smallValid 14312 52 := by unfold smallValid; decide +kernel

private theorem sp14364 : smallValid 14364 52 := by unfold smallValid; decide +kernel

private theorem sp14416 : smallValid 14416 52 := by unfold smallValid; decide +kernel

private theorem sp14468 : smallValid 14468 51 := by unfold smallValid; decide +kernel

private theorem sp14519 : smallValid 14519 52 := by unfold smallValid; decide +kernel

private theorem sp14571 : smallValid 14571 52 := by unfold smallValid; decide +kernel

private theorem sp14623 : smallValid 14623 52 := by unfold smallValid; decide +kernel

private theorem sp14675 : smallValid 14675 51 := by unfold smallValid; decide +kernel

private theorem sp14726 : smallValid 14726 52 := by unfold smallValid; decide +kernel

private theorem sp14778 : smallValid 14778 52 := by unfold smallValid; decide +kernel

private theorem sp14830 : smallValid 14830 52 := by unfold smallValid; decide +kernel

private theorem sp14882 : smallValid 14882 51 := by unfold smallValid; decide +kernel

private theorem sp14933 : smallValid 14933 52 := by unfold smallValid; decide +kernel

private theorem sp14985 : smallValid 14985 51 := by unfold smallValid; decide +kernel

private theorem sp15036 : smallValid 15036 52 := by unfold smallValid; decide +kernel

private theorem sp15088 : smallValid 15088 51 := by unfold smallValid; decide +kernel

private theorem sp15139 : smallValid 15139 52 := by unfold smallValid; decide +kernel

private theorem sp15191 : smallValid 15191 52 := by unfold smallValid; decide +kernel

private theorem sp15243 : smallValid 15243 52 := by unfold smallValid; decide +kernel

private theorem sp15295 : smallValid 15295 51 := by unfold smallValid; decide +kernel

private theorem sp15346 : smallValid 15346 52 := by unfold smallValid; decide +kernel

private theorem sp15398 : smallValid 15398 52 := by unfold smallValid; decide +kernel

private theorem sp15450 : smallValid 15450 52 := by unfold smallValid; decide +kernel

private theorem sp15502 : smallValid 15502 51 := by unfold smallValid; decide +kernel

private theorem sp15553 : smallValid 15553 52 := by unfold smallValid; decide +kernel

private theorem sp15605 : smallValid 15605 52 := by unfold smallValid; decide +kernel

private theorem sp15657 : smallValid 15657 52 := by unfold smallValid; decide +kernel

private theorem sp15709 : smallValid 15709 51 := by unfold smallValid; decide +kernel

private theorem sp15760 : smallValid 15760 52 := by unfold smallValid; decide +kernel

private theorem sp15812 : smallValid 15812 51 := by unfold smallValid; decide +kernel

private theorem sp15863 : smallValid 15863 52 := by unfold smallValid; decide +kernel

private theorem sp15915 : smallValid 15915 51 := by unfold smallValid; decide +kernel

private theorem sp15966 : smallValid 15966 52 := by unfold smallValid; decide +kernel

private theorem sp16018 : smallValid 16018 52 := by unfold smallValid; decide +kernel

private theorem sp16070 : smallValid 16070 52 := by unfold smallValid; decide +kernel

private theorem sp16122 : smallValid 16122 51 := by unfold smallValid; decide +kernel

private theorem sp16173 : smallValid 16173 52 := by unfold smallValid; decide +kernel

private theorem sp16225 : smallValid 16225 52 := by unfold smallValid; decide +kernel

private theorem sp16277 : smallValid 16277 52 := by unfold smallValid; decide +kernel

private theorem sp16329 : smallValid 16329 51 := by unfold smallValid; decide +kernel

private theorem sp16380 : smallValid 16380 52 := by unfold smallValid; decide +kernel

private theorem sp16432 : smallValid 16432 52 := by unfold smallValid; decide +kernel

private theorem sp16484 : smallValid 16484 52 := by unfold smallValid; decide +kernel

private theorem sp16536 : smallValid 16536 51 := by unfold smallValid; decide +kernel

private theorem sp16587 : smallValid 16587 52 := by unfold smallValid; decide +kernel

private theorem sp16639 : smallValid 16639 51 := by unfold smallValid; decide +kernel

private theorem sp16690 : smallValid 16690 52 := by unfold smallValid; decide +kernel

private theorem sp16742 : smallValid 16742 51 := by unfold smallValid; decide +kernel

private theorem sp16793 : smallValid 16793 52 := by unfold smallValid; decide +kernel

private theorem sp16845 : smallValid 16845 52 := by unfold smallValid; decide +kernel

private theorem sp16897 : smallValid 16897 52 := by unfold smallValid; decide +kernel

private theorem sp16949 : smallValid 16949 51 := by unfold smallValid; decide +kernel

private theorem sp17000 : smallValid 17000 52 := by unfold smallValid; decide +kernel

private theorem sp17052 : smallValid 17052 51 := by unfold smallValid; decide +kernel

private theorem sp17103 : smallValid 17103 52 := by unfold smallValid; decide +kernel

private theorem sp17155 : smallValid 17155 51 := by unfold smallValid; decide +kernel

private theorem sp17206 : smallValid 17206 52 := by unfold smallValid; decide +kernel

private theorem sp17258 : smallValid 17258 52 := by unfold smallValid; decide +kernel

private theorem sp17310 : smallValid 17310 52 := by unfold smallValid; decide +kernel

private theorem sp17362 : smallValid 17362 51 := by unfold smallValid; decide +kernel

private theorem sp17413 : smallValid 17413 52 := by unfold smallValid; decide +kernel

private theorem sp17465 : smallValid 17465 51 := by unfold smallValid; decide +kernel

private theorem sp17516 : smallValid 17516 52 := by unfold smallValid; decide +kernel

private theorem sp17568 : smallValid 17568 51 := by unfold smallValid; decide +kernel

private theorem sp17619 : smallValid 17619 52 := by unfold smallValid; decide +kernel

private theorem sp17671 : smallValid 17671 52 := by unfold smallValid; decide +kernel

private theorem sp17723 : smallValid 17723 52 := by unfold smallValid; decide +kernel

private theorem sp17775 : smallValid 17775 51 := by unfold smallValid; decide +kernel

private theorem sp17826 : smallValid 17826 52 := by unfold smallValid; decide +kernel

private theorem sp17878 : smallValid 17878 52 := by unfold smallValid; decide +kernel

private theorem sp17930 : smallValid 17930 52 := by unfold smallValid; decide +kernel

private theorem sp17982 : smallValid 17982 51 := by unfold smallValid; decide +kernel

private theorem sp18033 : smallValid 18033 52 := by unfold smallValid; decide +kernel

private theorem sp18085 : smallValid 18085 52 := by unfold smallValid; decide +kernel

private theorem sp18137 : smallValid 18137 52 := by unfold smallValid; decide +kernel

private theorem sp18189 : smallValid 18189 51 := by unfold smallValid; decide +kernel

private theorem sp18240 : smallValid 18240 52 := by unfold smallValid; decide +kernel

private theorem sp18292 : smallValid 18292 51 := by unfold smallValid; decide +kernel

private theorem sp18343 : smallValid 18343 52 := by unfold smallValid; decide +kernel

private theorem sp18395 : smallValid 18395 51 := by unfold smallValid; decide +kernel

private theorem sp18446 : smallValid 18446 52 := by unfold smallValid; decide +kernel

private theorem sp18498 : smallValid 18498 52 := by unfold smallValid; decide +kernel

private theorem sp18550 : smallValid 18550 52 := by unfold smallValid; decide +kernel

private theorem sp18602 : smallValid 18602 51 := by unfold smallValid; decide +kernel

private theorem sp18653 : smallValid 18653 52 := by unfold smallValid; decide +kernel

private theorem sp18705 : smallValid 18705 52 := by unfold smallValid; decide +kernel

private theorem sp18757 : smallValid 18757 52 := by unfold smallValid; decide +kernel

private theorem sp18809 : smallValid 18809 51 := by unfold smallValid; decide +kernel

private theorem sp18860 : smallValid 18860 52 := by unfold smallValid; decide +kernel

private theorem sp18912 : smallValid 18912 52 := by unfold smallValid; decide +kernel

private theorem sp18964 : smallValid 18964 52 := by unfold smallValid; decide +kernel

private theorem sp19016 : smallValid 19016 51 := by unfold smallValid; decide +kernel

private theorem sp19067 : smallValid 19067 52 := by unfold smallValid; decide +kernel

private theorem sp19119 : smallValid 19119 51 := by unfold smallValid; decide +kernel

private theorem sp19170 : smallValid 19170 52 := by unfold smallValid; decide +kernel

private theorem sp19222 : smallValid 19222 51 := by unfold smallValid; decide +kernel

private theorem sp19273 : smallValid 19273 52 := by unfold smallValid; decide +kernel

private theorem sp19325 : smallValid 19325 52 := by unfold smallValid; decide +kernel

private theorem sp19377 : smallValid 19377 52 := by unfold smallValid; decide +kernel

private theorem sp19429 : smallValid 19429 51 := by unfold smallValid; decide +kernel

private theorem sp19480 : smallValid 19480 52 := by unfold smallValid; decide +kernel

private theorem sp19532 : smallValid 19532 52 := by unfold smallValid; decide +kernel

private theorem sp19584 : smallValid 19584 52 := by unfold smallValid; decide +kernel

private theorem sp19636 : smallValid 19636 51 := by unfold smallValid; decide +kernel

private theorem sp19687 : smallValid 19687 52 := by unfold smallValid; decide +kernel

private theorem sp19739 : smallValid 19739 52 := by unfold smallValid; decide +kernel

private theorem sp19791 : smallValid 19791 52 := by unfold smallValid; decide +kernel

private theorem sp19843 : smallValid 19843 51 := by unfold smallValid; decide +kernel

private theorem sp19894 : smallValid 19894 52 := by unfold smallValid; decide +kernel

private theorem sp19946 : smallValid 19946 51 := by unfold smallValid; decide +kernel

private theorem sp19997 : smallValid 19997 52 := by unfold smallValid; decide +kernel

private theorem sp20049 : smallValid 20049 51 := by unfold smallValid; decide +kernel

private theorem sp20100 : smallValid 20100 52 := by unfold smallValid; decide +kernel

private theorem sp20152 : smallValid 20152 52 := by unfold smallValid; decide +kernel

private theorem sp20204 : smallValid 20204 52 := by unfold smallValid; decide +kernel

private theorem sp20256 : smallValid 20256 51 := by unfold smallValid; decide +kernel

private theorem sp20307 : smallValid 20307 52 := by unfold smallValid; decide +kernel

private theorem sp20359 : smallValid 20359 51 := by unfold smallValid; decide +kernel

private theorem sp20410 : smallValid 20410 52 := by unfold smallValid; decide +kernel

private theorem sp20462 : smallValid 20462 51 := by unfold smallValid; decide +kernel

private theorem sp20513 : smallValid 20513 52 := by unfold smallValid; decide +kernel

private theorem sp20565 : smallValid 20565 52 := by unfold smallValid; decide +kernel

private theorem sp20617 : smallValid 20617 52 := by unfold smallValid; decide +kernel

private theorem sp20669 : smallValid 20669 51 := by unfold smallValid; decide +kernel

private theorem sp20720 : smallValid 20720 52 := by unfold smallValid; decide +kernel

private theorem sp20772 : smallValid 20772 51 := by unfold smallValid; decide +kernel

private theorem sp20823 : smallValid 20823 52 := by unfold smallValid; decide +kernel

private theorem sp20875 : smallValid 20875 51 := by unfold smallValid; decide +kernel

private theorem sp20926 : smallValid 20926 52 := by unfold smallValid; decide +kernel

private theorem sp20978 : smallValid 20978 52 := by unfold smallValid; decide +kernel

private theorem sp21030 : smallValid 21030 52 := by unfold smallValid; decide +kernel

private theorem sp21082 : smallValid 21082 51 := by unfold smallValid; decide +kernel

private theorem sp21133 : smallValid 21133 52 := by unfold smallValid; decide +kernel

private theorem sp21185 : smallValid 21185 52 := by unfold smallValid; decide +kernel

private theorem sp21237 : smallValid 21237 52 := by unfold smallValid; decide +kernel

private theorem sp21289 : smallValid 21289 51 := by unfold smallValid; decide +kernel

private theorem sp21340 : smallValid 21340 52 := by unfold smallValid; decide +kernel

private theorem sp21392 : smallValid 21392 52 := by unfold smallValid; decide +kernel

private theorem sp21444 : smallValid 21444 52 := by unfold smallValid; decide +kernel

private theorem sp21496 : smallValid 21496 51 := by unfold smallValid; decide +kernel

private theorem sp21547 : smallValid 21547 52 := by unfold smallValid; decide +kernel

private theorem sp21599 : smallValid 21599 51 := by unfold smallValid; decide +kernel

private theorem sp21650 : smallValid 21650 52 := by unfold smallValid; decide +kernel

private theorem sp21702 : smallValid 21702 51 := by unfold smallValid; decide +kernel

private theorem sp21753 : smallValid 21753 52 := by unfold smallValid; decide +kernel

private theorem sp21805 : smallValid 21805 52 := by unfold smallValid; decide +kernel

private theorem sp21857 : smallValid 21857 52 := by unfold smallValid; decide +kernel

private theorem sp21909 : smallValid 21909 51 := by unfold smallValid; decide +kernel

private theorem sp21960 : smallValid 21960 52 := by unfold smallValid; decide +kernel

private theorem sp22012 : smallValid 22012 52 := by unfold smallValid; decide +kernel

private theorem sp22064 : smallValid 22064 52 := by unfold smallValid; decide +kernel

private theorem sp22116 : smallValid 22116 51 := by unfold smallValid; decide +kernel

private theorem sp22167 : smallValid 22167 52 := by unfold smallValid; decide +kernel

private theorem sp22219 : smallValid 22219 52 := by unfold smallValid; decide +kernel

private theorem sp22271 : smallValid 22271 52 := by unfold smallValid; decide +kernel

private theorem sp22323 : smallValid 22323 51 := by unfold smallValid; decide +kernel

private theorem sp22374 : smallValid 22374 52 := by unfold smallValid; decide +kernel

private theorem sp22426 : smallValid 22426 51 := by unfold smallValid; decide +kernel

private theorem sp22477 : smallValid 22477 52 := by unfold smallValid; decide +kernel

private theorem sp22529 : smallValid 22529 51 := by unfold smallValid; decide +kernel

private theorem sp22580 : smallValid 22580 52 := by unfold smallValid; decide +kernel

private theorem sp22632 : smallValid 22632 52 := by unfold smallValid; decide +kernel

private theorem sp22684 : smallValid 22684 52 := by unfold smallValid; decide +kernel

private theorem sp22736 : smallValid 22736 51 := by unfold smallValid; decide +kernel

private theorem sp22787 : smallValid 22787 52 := by unfold smallValid; decide +kernel

private theorem sp22839 : smallValid 22839 52 := by unfold smallValid; decide +kernel

private theorem sp22891 : smallValid 22891 52 := by unfold smallValid; decide +kernel

private theorem sp22943 : smallValid 22943 51 := by unfold smallValid; decide +kernel

private theorem sp22994 : smallValid 22994 52 := by unfold smallValid; decide +kernel

private theorem sp23046 : smallValid 23046 52 := by unfold smallValid; decide +kernel

private theorem sp23098 : smallValid 23098 52 := by unfold smallValid; decide +kernel

private theorem sp23150 : smallValid 23150 51 := by unfold smallValid; decide +kernel

private theorem sp23201 : smallValid 23201 52 := by unfold smallValid; decide +kernel

private theorem sp23253 : smallValid 23253 51 := by unfold smallValid; decide +kernel

private theorem sp23304 : smallValid 23304 52 := by unfold smallValid; decide +kernel

private theorem sp23356 : smallValid 23356 51 := by unfold smallValid; decide +kernel

private theorem sp23407 : smallValid 23407 52 := by unfold smallValid; decide +kernel

private theorem sp23459 : smallValid 23459 52 := by unfold smallValid; decide +kernel

private theorem sp23511 : smallValid 23511 52 := by unfold smallValid; decide +kernel

private theorem sp23563 : smallValid 23563 51 := by unfold smallValid; decide +kernel

private theorem sp23614 : smallValid 23614 52 := by unfold smallValid; decide +kernel

private theorem sp23666 : smallValid 23666 52 := by unfold smallValid; decide +kernel

private theorem sp23718 : smallValid 23718 52 := by unfold smallValid; decide +kernel

private theorem sp23770 : smallValid 23770 51 := by unfold smallValid; decide +kernel

private theorem sp23821 : smallValid 23821 52 := by unfold smallValid; decide +kernel

private theorem sp23873 : smallValid 23873 52 := by unfold smallValid; decide +kernel

private theorem sp23925 : smallValid 23925 52 := by unfold smallValid; decide +kernel

private theorem sp23977 : smallValid 23977 51 := by unfold smallValid; decide +kernel

private theorem sp24028 : smallValid 24028 52 := by unfold smallValid; decide +kernel

private theorem sp24080 : smallValid 24080 51 := by unfold smallValid; decide +kernel

private theorem sp24131 : smallValid 24131 52 := by unfold smallValid; decide +kernel

private theorem sp24183 : smallValid 24183 51 := by unfold smallValid; decide +kernel

private theorem sp24234 : smallValid 24234 52 := by unfold smallValid; decide +kernel

private theorem sp24286 : smallValid 24286 52 := by unfold smallValid; decide +kernel

private theorem sp24338 : smallValid 24338 52 := by unfold smallValid; decide +kernel

private theorem sp24390 : smallValid 24390 51 := by unfold smallValid; decide +kernel

private theorem sp24441 : smallValid 24441 52 := by unfold smallValid; decide +kernel

private theorem sp24493 : smallValid 24493 52 := by unfold smallValid; decide +kernel

private theorem sp24545 : smallValid 24545 52 := by unfold smallValid; decide +kernel

private theorem sp24597 : smallValid 24597 51 := by unfold smallValid; decide +kernel

private theorem sp24648 : smallValid 24648 52 := by unfold smallValid; decide +kernel

private theorem sp24700 : smallValid 24700 52 := by unfold smallValid; decide +kernel

private theorem sp24752 : smallValid 24752 52 := by unfold smallValid; decide +kernel

private theorem sp24804 : smallValid 24804 51 := by unfold smallValid; decide +kernel

private theorem sp24855 : smallValid 24855 52 := by unfold smallValid; decide +kernel

private theorem sp24907 : smallValid 24907 51 := by unfold smallValid; decide +kernel

private theorem sp24958 : smallValid 24958 52 := by unfold smallValid; decide +kernel

private theorem sp25010 : smallValid 25010 51 := by unfold smallValid; decide +kernel

private theorem sp25061 : smallValid 25061 52 := by unfold smallValid; decide +kernel

private theorem sp25113 : smallValid 25113 52 := by unfold smallValid; decide +kernel

private theorem sp25165 : smallValid 25165 52 := by unfold smallValid; decide +kernel

private theorem sp25217 : smallValid 25217 51 := by unfold smallValid; decide +kernel

private theorem sp25268 : smallValid 25268 52 := by unfold smallValid; decide +kernel

private theorem sp25320 : smallValid 25320 52 := by unfold smallValid; decide +kernel

private theorem sp25372 : smallValid 25372 52 := by unfold smallValid; decide +kernel

private theorem sp25424 : smallValid 25424 51 := by unfold smallValid; decide +kernel

private theorem sp25475 : smallValid 25475 52 := by unfold smallValid; decide +kernel

private theorem sp25527 : smallValid 25527 52 := by unfold smallValid; decide +kernel

private theorem sp25579 : smallValid 25579 52 := by unfold smallValid; decide +kernel

private theorem sp25631 : smallValid 25631 51 := by unfold smallValid; decide +kernel

private theorem sp25682 : smallValid 25682 52 := by unfold smallValid; decide +kernel

private theorem sp25734 : smallValid 25734 51 := by unfold smallValid; decide +kernel

private theorem sp25785 : smallValid 25785 52 := by unfold smallValid; decide +kernel

private theorem sp25837 : smallValid 25837 51 := by unfold smallValid; decide +kernel

private theorem sp25888 : smallValid 25888 52 := by unfold smallValid; decide +kernel

private theorem sp25940 : smallValid 25940 52 := by unfold smallValid; decide +kernel

private theorem sp25992 : smallValid 25992 52 := by unfold smallValid; decide +kernel

private theorem sp26044 : smallValid 26044 51 := by unfold smallValid; decide +kernel

private theorem sp26095 : smallValid 26095 52 := by unfold smallValid; decide +kernel

private theorem sp26147 : smallValid 26147 52 := by unfold smallValid; decide +kernel

private theorem sp26199 : smallValid 26199 52 := by unfold smallValid; decide +kernel

private theorem sp26251 : smallValid 26251 51 := by unfold smallValid; decide +kernel

private theorem sp26302 : smallValid 26302 52 := by unfold smallValid; decide +kernel

private theorem sp26354 : smallValid 26354 52 := by unfold smallValid; decide +kernel

private theorem sp26406 : smallValid 26406 52 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤26457) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 26458 := (joinSmall (lo:=0) (a:=13229) (b:=13229) (joinSmall (lo:=0) (a:=6614) (b:=6615) (joinSmall (lo:=0) (a:=3307) (b:=3307) (joinSmall (lo:=0) (a:=1653) (b:=1654) (joinSmall (lo:=0) (a:=826) (b:=827) (joinSmall (lo:=0) (a:=413) (b:=413) (joinSmall (lo:=0) (a:=206) (b:=207) (joinSmall (lo:=0) (a:=103) (b:=103) (joinSmall (lo:=0) (a:=51) (b:=52) sp0 sp51) (joinSmall (lo:=103) (a:=51) (b:=52) sp103 sp154)) (joinSmall (lo:=206) (a:=103) (b:=104) (joinSmall (lo:=206) (a:=51) (b:=52) sp206 sp257) (joinSmall (lo:=309) (a:=52) (b:=52) sp309 sp361))) (joinSmall (lo:=413) (a:=206) (b:=207) (joinSmall (lo:=413) (a:=103) (b:=103) (joinSmall (lo:=413) (a:=51) (b:=52) sp413 sp464) (joinSmall (lo:=516) (a:=51) (b:=52) sp516 sp567)) (joinSmall (lo:=619) (a:=103) (b:=104) (joinSmall (lo:=619) (a:=51) (b:=52) sp619 sp670) (joinSmall (lo:=722) (a:=52) (b:=52) sp722 sp774)))) (joinSmall (lo:=826) (a:=413) (b:=414) (joinSmall (lo:=826) (a:=206) (b:=207) (joinSmall (lo:=826) (a:=103) (b:=103) (joinSmall (lo:=826) (a:=51) (b:=52) sp826 sp877) (joinSmall (lo:=929) (a:=51) (b:=52) sp929 sp980)) (joinSmall (lo:=1032) (a:=103) (b:=104) (joinSmall (lo:=1032) (a:=51) (b:=52) sp1032 sp1083) (joinSmall (lo:=1135) (a:=52) (b:=52) sp1135 sp1187))) (joinSmall (lo:=1239) (a:=207) (b:=207) (joinSmall (lo:=1239) (a:=103) (b:=104) (joinSmall (lo:=1239) (a:=51) (b:=52) sp1239 sp1290) (joinSmall (lo:=1342) (a:=52) (b:=52) sp1342 sp1394)) (joinSmall (lo:=1446) (a:=103) (b:=104) (joinSmall (lo:=1446) (a:=51) (b:=52) sp1446 sp1497) (joinSmall (lo:=1549) (a:=52) (b:=52) sp1549 sp1601))))) (joinSmall (lo:=1653) (a:=827) (b:=827) (joinSmall (lo:=1653) (a:=413) (b:=414) (joinSmall (lo:=1653) (a:=206) (b:=207) (joinSmall (lo:=1653) (a:=103) (b:=103) (joinSmall (lo:=1653) (a:=51) (b:=52) sp1653 sp1704) (joinSmall (lo:=1756) (a:=51) (b:=52) sp1756 sp1807)) (joinSmall (lo:=1859) (a:=103) (b:=104) (joinSmall (lo:=1859) (a:=51) (b:=52) sp1859 sp1910) (joinSmall (lo:=1962) (a:=52) (b:=52) sp1962 sp2014))) (joinSmall (lo:=2066) (a:=207) (b:=207) (joinSmall (lo:=2066) (a:=103) (b:=104) (joinSmall (lo:=2066) (a:=51) (b:=52) sp2066 sp2117) (joinSmall (lo:=2169) (a:=52) (b:=52) sp2169 sp2221)) (joinSmall (lo:=2273) (a:=103) (b:=104) (joinSmall (lo:=2273) (a:=51) (b:=52) sp2273 sp2324) (joinSmall (lo:=2376) (a:=52) (b:=52) sp2376 sp2428)))) (joinSmall (lo:=2480) (a:=413) (b:=414) (joinSmall (lo:=2480) (a:=206) (b:=207) (joinSmall (lo:=2480) (a:=103) (b:=103) (joinSmall (lo:=2480) (a:=51) (b:=52) sp2480 sp2531) (joinSmall (lo:=2583) (a:=51) (b:=52) sp2583 sp2634)) (joinSmall (lo:=2686) (a:=103) (b:=104) (joinSmall (lo:=2686) (a:=51) (b:=52) sp2686 sp2737) (joinSmall (lo:=2789) (a:=52) (b:=52) sp2789 sp2841))) (joinSmall (lo:=2893) (a:=207) (b:=207) (joinSmall (lo:=2893) (a:=103) (b:=104) (joinSmall (lo:=2893) (a:=51) (b:=52) sp2893 sp2944) (joinSmall (lo:=2996) (a:=52) (b:=52) sp2996 sp3048)) (joinSmall (lo:=3100) (a:=103) (b:=104) (joinSmall (lo:=3100) (a:=51) (b:=52) sp3100 sp3151) (joinSmall (lo:=3203) (a:=52) (b:=52) sp3203 sp3255)))))) (joinSmall (lo:=3307) (a:=1653) (b:=1654) (joinSmall (lo:=3307) (a:=826) (b:=827) (joinSmall (lo:=3307) (a:=413) (b:=413) (joinSmall (lo:=3307) (a:=206) (b:=207) (joinSmall (lo:=3307) (a:=103) (b:=103) (joinSmall (lo:=3307) (a:=51) (b:=52) sp3307 sp3358) (joinSmall (lo:=3410) (a:=51) (b:=52) sp3410 sp3461)) (joinSmall (lo:=3513) (a:=103) (b:=104) (joinSmall (lo:=3513) (a:=51) (b:=52) sp3513 sp3564) (joinSmall (lo:=3616) (a:=52) (b:=52) sp3616 sp3668))) (joinSmall (lo:=3720) (a:=206) (b:=207) (joinSmall (lo:=3720) (a:=103) (b:=103) (joinSmall (lo:=3720) (a:=51) (b:=52) sp3720 sp3771) (joinSmall (lo:=3823) (a:=51) (b:=52) sp3823 sp3874)) (joinSmall (lo:=3926) (a:=103) (b:=104) (joinSmall (lo:=3926) (a:=51) (b:=52) sp3926 sp3977) (joinSmall (lo:=4029) (a:=52) (b:=52) sp4029 sp4081)))) (joinSmall (lo:=4133) (a:=413) (b:=414) (joinSmall (lo:=4133) (a:=206) (b:=207) (joinSmall (lo:=4133) (a:=103) (b:=103) (joinSmall (lo:=4133) (a:=51) (b:=52) sp4133 sp4184) (joinSmall (lo:=4236) (a:=51) (b:=52) sp4236 sp4287)) (joinSmall (lo:=4339) (a:=103) (b:=104) (joinSmall (lo:=4339) (a:=51) (b:=52) sp4339 sp4390) (joinSmall (lo:=4442) (a:=52) (b:=52) sp4442 sp4494))) (joinSmall (lo:=4546) (a:=207) (b:=207) (joinSmall (lo:=4546) (a:=103) (b:=104) (joinSmall (lo:=4546) (a:=51) (b:=52) sp4546 sp4597) (joinSmall (lo:=4649) (a:=52) (b:=52) sp4649 sp4701)) (joinSmall (lo:=4753) (a:=103) (b:=104) (joinSmall (lo:=4753) (a:=51) (b:=52) sp4753 sp4804) (joinSmall (lo:=4856) (a:=52) (b:=52) sp4856 sp4908))))) (joinSmall (lo:=4960) (a:=827) (b:=827) (joinSmall (lo:=4960) (a:=413) (b:=414) (joinSmall (lo:=4960) (a:=206) (b:=207) (joinSmall (lo:=4960) (a:=103) (b:=103) (joinSmall (lo:=4960) (a:=51) (b:=52) sp4960 sp5011) (joinSmall (lo:=5063) (a:=51) (b:=52) sp5063 sp5114)) (joinSmall (lo:=5166) (a:=103) (b:=104) (joinSmall (lo:=5166) (a:=51) (b:=52) sp5166 sp5217) (joinSmall (lo:=5269) (a:=52) (b:=52) sp5269 sp5321))) (joinSmall (lo:=5373) (a:=207) (b:=207) (joinSmall (lo:=5373) (a:=103) (b:=104) (joinSmall (lo:=5373) (a:=51) (b:=52) sp5373 sp5424) (joinSmall (lo:=5476) (a:=52) (b:=52) sp5476 sp5528)) (joinSmall (lo:=5580) (a:=103) (b:=104) (joinSmall (lo:=5580) (a:=51) (b:=52) sp5580 sp5631) (joinSmall (lo:=5683) (a:=52) (b:=52) sp5683 sp5735)))) (joinSmall (lo:=5787) (a:=413) (b:=414) (joinSmall (lo:=5787) (a:=206) (b:=207) (joinSmall (lo:=5787) (a:=103) (b:=103) (joinSmall (lo:=5787) (a:=51) (b:=52) sp5787 sp5838) (joinSmall (lo:=5890) (a:=51) (b:=52) sp5890 sp5941)) (joinSmall (lo:=5993) (a:=103) (b:=104) (joinSmall (lo:=5993) (a:=51) (b:=52) sp5993 sp6044) (joinSmall (lo:=6096) (a:=52) (b:=52) sp6096 sp6148))) (joinSmall (lo:=6200) (a:=207) (b:=207) (joinSmall (lo:=6200) (a:=103) (b:=104) (joinSmall (lo:=6200) (a:=51) (b:=52) sp6200 sp6251) (joinSmall (lo:=6303) (a:=52) (b:=52) sp6303 sp6355)) (joinSmall (lo:=6407) (a:=103) (b:=104) (joinSmall (lo:=6407) (a:=51) (b:=52) sp6407 sp6458) (joinSmall (lo:=6510) (a:=52) (b:=52) sp6510 sp6562))))))) (joinSmall (lo:=6614) (a:=3307) (b:=3308) (joinSmall (lo:=6614) (a:=1653) (b:=1654) (joinSmall (lo:=6614) (a:=826) (b:=827) (joinSmall (lo:=6614) (a:=413) (b:=413) (joinSmall (lo:=6614) (a:=206) (b:=207) (joinSmall (lo:=6614) (a:=103) (b:=103) (joinSmall (lo:=6614) (a:=51) (b:=52) sp6614 sp6665) (joinSmall (lo:=6717) (a:=51) (b:=52) sp6717 sp6768)) (joinSmall (lo:=6820) (a:=103) (b:=104) (joinSmall (lo:=6820) (a:=51) (b:=52) sp6820 sp6871) (joinSmall (lo:=6923) (a:=52) (b:=52) sp6923 sp6975))) (joinSmall (lo:=7027) (a:=206) (b:=207) (joinSmall (lo:=7027) (a:=103) (b:=103) (joinSmall (lo:=7027) (a:=51) (b:=52) sp7027 sp7078) (joinSmall (lo:=7130) (a:=51) (b:=52) sp7130 sp7181)) (joinSmall (lo:=7233) (a:=103) (b:=104) (joinSmall (lo:=7233) (a:=51) (b:=52) sp7233 sp7284) (joinSmall (lo:=7336) (a:=52) (b:=52) sp7336 sp7388)))) (joinSmall (lo:=7440) (a:=413) (b:=414) (joinSmall (lo:=7440) (a:=206) (b:=207) (joinSmall (lo:=7440) (a:=103) (b:=103) (joinSmall (lo:=7440) (a:=51) (b:=52) sp7440 sp7491) (joinSmall (lo:=7543) (a:=51) (b:=52) sp7543 sp7594)) (joinSmall (lo:=7646) (a:=103) (b:=104) (joinSmall (lo:=7646) (a:=51) (b:=52) sp7646 sp7697) (joinSmall (lo:=7749) (a:=52) (b:=52) sp7749 sp7801))) (joinSmall (lo:=7853) (a:=207) (b:=207) (joinSmall (lo:=7853) (a:=103) (b:=104) (joinSmall (lo:=7853) (a:=51) (b:=52) sp7853 sp7904) (joinSmall (lo:=7956) (a:=52) (b:=52) sp7956 sp8008)) (joinSmall (lo:=8060) (a:=103) (b:=104) (joinSmall (lo:=8060) (a:=51) (b:=52) sp8060 sp8111) (joinSmall (lo:=8163) (a:=52) (b:=52) sp8163 sp8215))))) (joinSmall (lo:=8267) (a:=827) (b:=827) (joinSmall (lo:=8267) (a:=413) (b:=414) (joinSmall (lo:=8267) (a:=206) (b:=207) (joinSmall (lo:=8267) (a:=103) (b:=103) (joinSmall (lo:=8267) (a:=51) (b:=52) sp8267 sp8318) (joinSmall (lo:=8370) (a:=51) (b:=52) sp8370 sp8421)) (joinSmall (lo:=8473) (a:=103) (b:=104) (joinSmall (lo:=8473) (a:=51) (b:=52) sp8473 sp8524) (joinSmall (lo:=8576) (a:=52) (b:=52) sp8576 sp8628))) (joinSmall (lo:=8680) (a:=207) (b:=207) (joinSmall (lo:=8680) (a:=103) (b:=104) (joinSmall (lo:=8680) (a:=51) (b:=52) sp8680 sp8731) (joinSmall (lo:=8783) (a:=52) (b:=52) sp8783 sp8835)) (joinSmall (lo:=8887) (a:=103) (b:=104) (joinSmall (lo:=8887) (a:=51) (b:=52) sp8887 sp8938) (joinSmall (lo:=8990) (a:=52) (b:=52) sp8990 sp9042)))) (joinSmall (lo:=9094) (a:=413) (b:=414) (joinSmall (lo:=9094) (a:=206) (b:=207) (joinSmall (lo:=9094) (a:=103) (b:=103) (joinSmall (lo:=9094) (a:=51) (b:=52) sp9094 sp9145) (joinSmall (lo:=9197) (a:=51) (b:=52) sp9197 sp9248)) (joinSmall (lo:=9300) (a:=103) (b:=104) (joinSmall (lo:=9300) (a:=51) (b:=52) sp9300 sp9351) (joinSmall (lo:=9403) (a:=52) (b:=52) sp9403 sp9455))) (joinSmall (lo:=9507) (a:=207) (b:=207) (joinSmall (lo:=9507) (a:=103) (b:=104) (joinSmall (lo:=9507) (a:=51) (b:=52) sp9507 sp9558) (joinSmall (lo:=9610) (a:=52) (b:=52) sp9610 sp9662)) (joinSmall (lo:=9714) (a:=103) (b:=104) (joinSmall (lo:=9714) (a:=51) (b:=52) sp9714 sp9765) (joinSmall (lo:=9817) (a:=52) (b:=52) sp9817 sp9869)))))) (joinSmall (lo:=9921) (a:=1654) (b:=1654) (joinSmall (lo:=9921) (a:=827) (b:=827) (joinSmall (lo:=9921) (a:=413) (b:=414) (joinSmall (lo:=9921) (a:=206) (b:=207) (joinSmall (lo:=9921) (a:=103) (b:=103) (joinSmall (lo:=9921) (a:=51) (b:=52) sp9921 sp9972) (joinSmall (lo:=10024) (a:=51) (b:=52) sp10024 sp10075)) (joinSmall (lo:=10127) (a:=103) (b:=104) (joinSmall (lo:=10127) (a:=51) (b:=52) sp10127 sp10178) (joinSmall (lo:=10230) (a:=52) (b:=52) sp10230 sp10282))) (joinSmall (lo:=10334) (a:=207) (b:=207) (joinSmall (lo:=10334) (a:=103) (b:=104) (joinSmall (lo:=10334) (a:=51) (b:=52) sp10334 sp10385) (joinSmall (lo:=10437) (a:=52) (b:=52) sp10437 sp10489)) (joinSmall (lo:=10541) (a:=103) (b:=104) (joinSmall (lo:=10541) (a:=51) (b:=52) sp10541 sp10592) (joinSmall (lo:=10644) (a:=52) (b:=52) sp10644 sp10696)))) (joinSmall (lo:=10748) (a:=413) (b:=414) (joinSmall (lo:=10748) (a:=206) (b:=207) (joinSmall (lo:=10748) (a:=103) (b:=103) (joinSmall (lo:=10748) (a:=51) (b:=52) sp10748 sp10799) (joinSmall (lo:=10851) (a:=51) (b:=52) sp10851 sp10902)) (joinSmall (lo:=10954) (a:=103) (b:=104) (joinSmall (lo:=10954) (a:=51) (b:=52) sp10954 sp11005) (joinSmall (lo:=11057) (a:=52) (b:=52) sp11057 sp11109))) (joinSmall (lo:=11161) (a:=207) (b:=207) (joinSmall (lo:=11161) (a:=103) (b:=104) (joinSmall (lo:=11161) (a:=51) (b:=52) sp11161 sp11212) (joinSmall (lo:=11264) (a:=52) (b:=52) sp11264 sp11316)) (joinSmall (lo:=11368) (a:=103) (b:=104) (joinSmall (lo:=11368) (a:=51) (b:=52) sp11368 sp11419) (joinSmall (lo:=11471) (a:=52) (b:=52) sp11471 sp11523))))) (joinSmall (lo:=11575) (a:=827) (b:=827) (joinSmall (lo:=11575) (a:=413) (b:=414) (joinSmall (lo:=11575) (a:=206) (b:=207) (joinSmall (lo:=11575) (a:=103) (b:=103) (joinSmall (lo:=11575) (a:=51) (b:=52) sp11575 sp11626) (joinSmall (lo:=11678) (a:=51) (b:=52) sp11678 sp11729)) (joinSmall (lo:=11781) (a:=103) (b:=104) (joinSmall (lo:=11781) (a:=51) (b:=52) sp11781 sp11832) (joinSmall (lo:=11884) (a:=52) (b:=52) sp11884 sp11936))) (joinSmall (lo:=11988) (a:=207) (b:=207) (joinSmall (lo:=11988) (a:=103) (b:=104) (joinSmall (lo:=11988) (a:=51) (b:=52) sp11988 sp12039) (joinSmall (lo:=12091) (a:=52) (b:=52) sp12091 sp12143)) (joinSmall (lo:=12195) (a:=103) (b:=104) (joinSmall (lo:=12195) (a:=51) (b:=52) sp12195 sp12246) (joinSmall (lo:=12298) (a:=52) (b:=52) sp12298 sp12350)))) (joinSmall (lo:=12402) (a:=413) (b:=414) (joinSmall (lo:=12402) (a:=206) (b:=207) (joinSmall (lo:=12402) (a:=103) (b:=103) (joinSmall (lo:=12402) (a:=51) (b:=52) sp12402 sp12453) (joinSmall (lo:=12505) (a:=51) (b:=52) sp12505 sp12556)) (joinSmall (lo:=12608) (a:=103) (b:=104) (joinSmall (lo:=12608) (a:=51) (b:=52) sp12608 sp12659) (joinSmall (lo:=12711) (a:=52) (b:=52) sp12711 sp12763))) (joinSmall (lo:=12815) (a:=207) (b:=207) (joinSmall (lo:=12815) (a:=103) (b:=104) (joinSmall (lo:=12815) (a:=51) (b:=52) sp12815 sp12866) (joinSmall (lo:=12918) (a:=52) (b:=52) sp12918 sp12970)) (joinSmall (lo:=13022) (a:=103) (b:=104) (joinSmall (lo:=13022) (a:=51) (b:=52) sp13022 sp13073) (joinSmall (lo:=13125) (a:=52) (b:=52) sp13125 sp13177)))))))) (joinSmall (lo:=13229) (a:=6614) (b:=6615) (joinSmall (lo:=13229) (a:=3307) (b:=3307) (joinSmall (lo:=13229) (a:=1653) (b:=1654) (joinSmall (lo:=13229) (a:=826) (b:=827) (joinSmall (lo:=13229) (a:=413) (b:=413) (joinSmall (lo:=13229) (a:=206) (b:=207) (joinSmall (lo:=13229) (a:=103) (b:=103) (joinSmall (lo:=13229) (a:=51) (b:=52) sp13229 sp13280) (joinSmall (lo:=13332) (a:=51) (b:=52) sp13332 sp13383)) (joinSmall (lo:=13435) (a:=103) (b:=104) (joinSmall (lo:=13435) (a:=51) (b:=52) sp13435 sp13486) (joinSmall (lo:=13538) (a:=52) (b:=52) sp13538 sp13590))) (joinSmall (lo:=13642) (a:=206) (b:=207) (joinSmall (lo:=13642) (a:=103) (b:=103) (joinSmall (lo:=13642) (a:=51) (b:=52) sp13642 sp13693) (joinSmall (lo:=13745) (a:=51) (b:=52) sp13745 sp13796)) (joinSmall (lo:=13848) (a:=103) (b:=104) (joinSmall (lo:=13848) (a:=51) (b:=52) sp13848 sp13899) (joinSmall (lo:=13951) (a:=52) (b:=52) sp13951 sp14003)))) (joinSmall (lo:=14055) (a:=413) (b:=414) (joinSmall (lo:=14055) (a:=206) (b:=207) (joinSmall (lo:=14055) (a:=103) (b:=103) (joinSmall (lo:=14055) (a:=51) (b:=52) sp14055 sp14106) (joinSmall (lo:=14158) (a:=51) (b:=52) sp14158 sp14209)) (joinSmall (lo:=14261) (a:=103) (b:=104) (joinSmall (lo:=14261) (a:=51) (b:=52) sp14261 sp14312) (joinSmall (lo:=14364) (a:=52) (b:=52) sp14364 sp14416))) (joinSmall (lo:=14468) (a:=207) (b:=207) (joinSmall (lo:=14468) (a:=103) (b:=104) (joinSmall (lo:=14468) (a:=51) (b:=52) sp14468 sp14519) (joinSmall (lo:=14571) (a:=52) (b:=52) sp14571 sp14623)) (joinSmall (lo:=14675) (a:=103) (b:=104) (joinSmall (lo:=14675) (a:=51) (b:=52) sp14675 sp14726) (joinSmall (lo:=14778) (a:=52) (b:=52) sp14778 sp14830))))) (joinSmall (lo:=14882) (a:=827) (b:=827) (joinSmall (lo:=14882) (a:=413) (b:=414) (joinSmall (lo:=14882) (a:=206) (b:=207) (joinSmall (lo:=14882) (a:=103) (b:=103) (joinSmall (lo:=14882) (a:=51) (b:=52) sp14882 sp14933) (joinSmall (lo:=14985) (a:=51) (b:=52) sp14985 sp15036)) (joinSmall (lo:=15088) (a:=103) (b:=104) (joinSmall (lo:=15088) (a:=51) (b:=52) sp15088 sp15139) (joinSmall (lo:=15191) (a:=52) (b:=52) sp15191 sp15243))) (joinSmall (lo:=15295) (a:=207) (b:=207) (joinSmall (lo:=15295) (a:=103) (b:=104) (joinSmall (lo:=15295) (a:=51) (b:=52) sp15295 sp15346) (joinSmall (lo:=15398) (a:=52) (b:=52) sp15398 sp15450)) (joinSmall (lo:=15502) (a:=103) (b:=104) (joinSmall (lo:=15502) (a:=51) (b:=52) sp15502 sp15553) (joinSmall (lo:=15605) (a:=52) (b:=52) sp15605 sp15657)))) (joinSmall (lo:=15709) (a:=413) (b:=414) (joinSmall (lo:=15709) (a:=206) (b:=207) (joinSmall (lo:=15709) (a:=103) (b:=103) (joinSmall (lo:=15709) (a:=51) (b:=52) sp15709 sp15760) (joinSmall (lo:=15812) (a:=51) (b:=52) sp15812 sp15863)) (joinSmall (lo:=15915) (a:=103) (b:=104) (joinSmall (lo:=15915) (a:=51) (b:=52) sp15915 sp15966) (joinSmall (lo:=16018) (a:=52) (b:=52) sp16018 sp16070))) (joinSmall (lo:=16122) (a:=207) (b:=207) (joinSmall (lo:=16122) (a:=103) (b:=104) (joinSmall (lo:=16122) (a:=51) (b:=52) sp16122 sp16173) (joinSmall (lo:=16225) (a:=52) (b:=52) sp16225 sp16277)) (joinSmall (lo:=16329) (a:=103) (b:=104) (joinSmall (lo:=16329) (a:=51) (b:=52) sp16329 sp16380) (joinSmall (lo:=16432) (a:=52) (b:=52) sp16432 sp16484)))))) (joinSmall (lo:=16536) (a:=1653) (b:=1654) (joinSmall (lo:=16536) (a:=826) (b:=827) (joinSmall (lo:=16536) (a:=413) (b:=413) (joinSmall (lo:=16536) (a:=206) (b:=207) (joinSmall (lo:=16536) (a:=103) (b:=103) (joinSmall (lo:=16536) (a:=51) (b:=52) sp16536 sp16587) (joinSmall (lo:=16639) (a:=51) (b:=52) sp16639 sp16690)) (joinSmall (lo:=16742) (a:=103) (b:=104) (joinSmall (lo:=16742) (a:=51) (b:=52) sp16742 sp16793) (joinSmall (lo:=16845) (a:=52) (b:=52) sp16845 sp16897))) (joinSmall (lo:=16949) (a:=206) (b:=207) (joinSmall (lo:=16949) (a:=103) (b:=103) (joinSmall (lo:=16949) (a:=51) (b:=52) sp16949 sp17000) (joinSmall (lo:=17052) (a:=51) (b:=52) sp17052 sp17103)) (joinSmall (lo:=17155) (a:=103) (b:=104) (joinSmall (lo:=17155) (a:=51) (b:=52) sp17155 sp17206) (joinSmall (lo:=17258) (a:=52) (b:=52) sp17258 sp17310)))) (joinSmall (lo:=17362) (a:=413) (b:=414) (joinSmall (lo:=17362) (a:=206) (b:=207) (joinSmall (lo:=17362) (a:=103) (b:=103) (joinSmall (lo:=17362) (a:=51) (b:=52) sp17362 sp17413) (joinSmall (lo:=17465) (a:=51) (b:=52) sp17465 sp17516)) (joinSmall (lo:=17568) (a:=103) (b:=104) (joinSmall (lo:=17568) (a:=51) (b:=52) sp17568 sp17619) (joinSmall (lo:=17671) (a:=52) (b:=52) sp17671 sp17723))) (joinSmall (lo:=17775) (a:=207) (b:=207) (joinSmall (lo:=17775) (a:=103) (b:=104) (joinSmall (lo:=17775) (a:=51) (b:=52) sp17775 sp17826) (joinSmall (lo:=17878) (a:=52) (b:=52) sp17878 sp17930)) (joinSmall (lo:=17982) (a:=103) (b:=104) (joinSmall (lo:=17982) (a:=51) (b:=52) sp17982 sp18033) (joinSmall (lo:=18085) (a:=52) (b:=52) sp18085 sp18137))))) (joinSmall (lo:=18189) (a:=827) (b:=827) (joinSmall (lo:=18189) (a:=413) (b:=414) (joinSmall (lo:=18189) (a:=206) (b:=207) (joinSmall (lo:=18189) (a:=103) (b:=103) (joinSmall (lo:=18189) (a:=51) (b:=52) sp18189 sp18240) (joinSmall (lo:=18292) (a:=51) (b:=52) sp18292 sp18343)) (joinSmall (lo:=18395) (a:=103) (b:=104) (joinSmall (lo:=18395) (a:=51) (b:=52) sp18395 sp18446) (joinSmall (lo:=18498) (a:=52) (b:=52) sp18498 sp18550))) (joinSmall (lo:=18602) (a:=207) (b:=207) (joinSmall (lo:=18602) (a:=103) (b:=104) (joinSmall (lo:=18602) (a:=51) (b:=52) sp18602 sp18653) (joinSmall (lo:=18705) (a:=52) (b:=52) sp18705 sp18757)) (joinSmall (lo:=18809) (a:=103) (b:=104) (joinSmall (lo:=18809) (a:=51) (b:=52) sp18809 sp18860) (joinSmall (lo:=18912) (a:=52) (b:=52) sp18912 sp18964)))) (joinSmall (lo:=19016) (a:=413) (b:=414) (joinSmall (lo:=19016) (a:=206) (b:=207) (joinSmall (lo:=19016) (a:=103) (b:=103) (joinSmall (lo:=19016) (a:=51) (b:=52) sp19016 sp19067) (joinSmall (lo:=19119) (a:=51) (b:=52) sp19119 sp19170)) (joinSmall (lo:=19222) (a:=103) (b:=104) (joinSmall (lo:=19222) (a:=51) (b:=52) sp19222 sp19273) (joinSmall (lo:=19325) (a:=52) (b:=52) sp19325 sp19377))) (joinSmall (lo:=19429) (a:=207) (b:=207) (joinSmall (lo:=19429) (a:=103) (b:=104) (joinSmall (lo:=19429) (a:=51) (b:=52) sp19429 sp19480) (joinSmall (lo:=19532) (a:=52) (b:=52) sp19532 sp19584)) (joinSmall (lo:=19636) (a:=103) (b:=104) (joinSmall (lo:=19636) (a:=51) (b:=52) sp19636 sp19687) (joinSmall (lo:=19739) (a:=52) (b:=52) sp19739 sp19791))))))) (joinSmall (lo:=19843) (a:=3307) (b:=3308) (joinSmall (lo:=19843) (a:=1653) (b:=1654) (joinSmall (lo:=19843) (a:=826) (b:=827) (joinSmall (lo:=19843) (a:=413) (b:=413) (joinSmall (lo:=19843) (a:=206) (b:=207) (joinSmall (lo:=19843) (a:=103) (b:=103) (joinSmall (lo:=19843) (a:=51) (b:=52) sp19843 sp19894) (joinSmall (lo:=19946) (a:=51) (b:=52) sp19946 sp19997)) (joinSmall (lo:=20049) (a:=103) (b:=104) (joinSmall (lo:=20049) (a:=51) (b:=52) sp20049 sp20100) (joinSmall (lo:=20152) (a:=52) (b:=52) sp20152 sp20204))) (joinSmall (lo:=20256) (a:=206) (b:=207) (joinSmall (lo:=20256) (a:=103) (b:=103) (joinSmall (lo:=20256) (a:=51) (b:=52) sp20256 sp20307) (joinSmall (lo:=20359) (a:=51) (b:=52) sp20359 sp20410)) (joinSmall (lo:=20462) (a:=103) (b:=104) (joinSmall (lo:=20462) (a:=51) (b:=52) sp20462 sp20513) (joinSmall (lo:=20565) (a:=52) (b:=52) sp20565 sp20617)))) (joinSmall (lo:=20669) (a:=413) (b:=414) (joinSmall (lo:=20669) (a:=206) (b:=207) (joinSmall (lo:=20669) (a:=103) (b:=103) (joinSmall (lo:=20669) (a:=51) (b:=52) sp20669 sp20720) (joinSmall (lo:=20772) (a:=51) (b:=52) sp20772 sp20823)) (joinSmall (lo:=20875) (a:=103) (b:=104) (joinSmall (lo:=20875) (a:=51) (b:=52) sp20875 sp20926) (joinSmall (lo:=20978) (a:=52) (b:=52) sp20978 sp21030))) (joinSmall (lo:=21082) (a:=207) (b:=207) (joinSmall (lo:=21082) (a:=103) (b:=104) (joinSmall (lo:=21082) (a:=51) (b:=52) sp21082 sp21133) (joinSmall (lo:=21185) (a:=52) (b:=52) sp21185 sp21237)) (joinSmall (lo:=21289) (a:=103) (b:=104) (joinSmall (lo:=21289) (a:=51) (b:=52) sp21289 sp21340) (joinSmall (lo:=21392) (a:=52) (b:=52) sp21392 sp21444))))) (joinSmall (lo:=21496) (a:=827) (b:=827) (joinSmall (lo:=21496) (a:=413) (b:=414) (joinSmall (lo:=21496) (a:=206) (b:=207) (joinSmall (lo:=21496) (a:=103) (b:=103) (joinSmall (lo:=21496) (a:=51) (b:=52) sp21496 sp21547) (joinSmall (lo:=21599) (a:=51) (b:=52) sp21599 sp21650)) (joinSmall (lo:=21702) (a:=103) (b:=104) (joinSmall (lo:=21702) (a:=51) (b:=52) sp21702 sp21753) (joinSmall (lo:=21805) (a:=52) (b:=52) sp21805 sp21857))) (joinSmall (lo:=21909) (a:=207) (b:=207) (joinSmall (lo:=21909) (a:=103) (b:=104) (joinSmall (lo:=21909) (a:=51) (b:=52) sp21909 sp21960) (joinSmall (lo:=22012) (a:=52) (b:=52) sp22012 sp22064)) (joinSmall (lo:=22116) (a:=103) (b:=104) (joinSmall (lo:=22116) (a:=51) (b:=52) sp22116 sp22167) (joinSmall (lo:=22219) (a:=52) (b:=52) sp22219 sp22271)))) (joinSmall (lo:=22323) (a:=413) (b:=414) (joinSmall (lo:=22323) (a:=206) (b:=207) (joinSmall (lo:=22323) (a:=103) (b:=103) (joinSmall (lo:=22323) (a:=51) (b:=52) sp22323 sp22374) (joinSmall (lo:=22426) (a:=51) (b:=52) sp22426 sp22477)) (joinSmall (lo:=22529) (a:=103) (b:=104) (joinSmall (lo:=22529) (a:=51) (b:=52) sp22529 sp22580) (joinSmall (lo:=22632) (a:=52) (b:=52) sp22632 sp22684))) (joinSmall (lo:=22736) (a:=207) (b:=207) (joinSmall (lo:=22736) (a:=103) (b:=104) (joinSmall (lo:=22736) (a:=51) (b:=52) sp22736 sp22787) (joinSmall (lo:=22839) (a:=52) (b:=52) sp22839 sp22891)) (joinSmall (lo:=22943) (a:=103) (b:=104) (joinSmall (lo:=22943) (a:=51) (b:=52) sp22943 sp22994) (joinSmall (lo:=23046) (a:=52) (b:=52) sp23046 sp23098)))))) (joinSmall (lo:=23150) (a:=1654) (b:=1654) (joinSmall (lo:=23150) (a:=827) (b:=827) (joinSmall (lo:=23150) (a:=413) (b:=414) (joinSmall (lo:=23150) (a:=206) (b:=207) (joinSmall (lo:=23150) (a:=103) (b:=103) (joinSmall (lo:=23150) (a:=51) (b:=52) sp23150 sp23201) (joinSmall (lo:=23253) (a:=51) (b:=52) sp23253 sp23304)) (joinSmall (lo:=23356) (a:=103) (b:=104) (joinSmall (lo:=23356) (a:=51) (b:=52) sp23356 sp23407) (joinSmall (lo:=23459) (a:=52) (b:=52) sp23459 sp23511))) (joinSmall (lo:=23563) (a:=207) (b:=207) (joinSmall (lo:=23563) (a:=103) (b:=104) (joinSmall (lo:=23563) (a:=51) (b:=52) sp23563 sp23614) (joinSmall (lo:=23666) (a:=52) (b:=52) sp23666 sp23718)) (joinSmall (lo:=23770) (a:=103) (b:=104) (joinSmall (lo:=23770) (a:=51) (b:=52) sp23770 sp23821) (joinSmall (lo:=23873) (a:=52) (b:=52) sp23873 sp23925)))) (joinSmall (lo:=23977) (a:=413) (b:=414) (joinSmall (lo:=23977) (a:=206) (b:=207) (joinSmall (lo:=23977) (a:=103) (b:=103) (joinSmall (lo:=23977) (a:=51) (b:=52) sp23977 sp24028) (joinSmall (lo:=24080) (a:=51) (b:=52) sp24080 sp24131)) (joinSmall (lo:=24183) (a:=103) (b:=104) (joinSmall (lo:=24183) (a:=51) (b:=52) sp24183 sp24234) (joinSmall (lo:=24286) (a:=52) (b:=52) sp24286 sp24338))) (joinSmall (lo:=24390) (a:=207) (b:=207) (joinSmall (lo:=24390) (a:=103) (b:=104) (joinSmall (lo:=24390) (a:=51) (b:=52) sp24390 sp24441) (joinSmall (lo:=24493) (a:=52) (b:=52) sp24493 sp24545)) (joinSmall (lo:=24597) (a:=103) (b:=104) (joinSmall (lo:=24597) (a:=51) (b:=52) sp24597 sp24648) (joinSmall (lo:=24700) (a:=52) (b:=52) sp24700 sp24752))))) (joinSmall (lo:=24804) (a:=827) (b:=827) (joinSmall (lo:=24804) (a:=413) (b:=414) (joinSmall (lo:=24804) (a:=206) (b:=207) (joinSmall (lo:=24804) (a:=103) (b:=103) (joinSmall (lo:=24804) (a:=51) (b:=52) sp24804 sp24855) (joinSmall (lo:=24907) (a:=51) (b:=52) sp24907 sp24958)) (joinSmall (lo:=25010) (a:=103) (b:=104) (joinSmall (lo:=25010) (a:=51) (b:=52) sp25010 sp25061) (joinSmall (lo:=25113) (a:=52) (b:=52) sp25113 sp25165))) (joinSmall (lo:=25217) (a:=207) (b:=207) (joinSmall (lo:=25217) (a:=103) (b:=104) (joinSmall (lo:=25217) (a:=51) (b:=52) sp25217 sp25268) (joinSmall (lo:=25320) (a:=52) (b:=52) sp25320 sp25372)) (joinSmall (lo:=25424) (a:=103) (b:=104) (joinSmall (lo:=25424) (a:=51) (b:=52) sp25424 sp25475) (joinSmall (lo:=25527) (a:=52) (b:=52) sp25527 sp25579)))) (joinSmall (lo:=25631) (a:=413) (b:=414) (joinSmall (lo:=25631) (a:=206) (b:=207) (joinSmall (lo:=25631) (a:=103) (b:=103) (joinSmall (lo:=25631) (a:=51) (b:=52) sp25631 sp25682) (joinSmall (lo:=25734) (a:=51) (b:=52) sp25734 sp25785)) (joinSmall (lo:=25837) (a:=103) (b:=104) (joinSmall (lo:=25837) (a:=51) (b:=52) sp25837 sp25888) (joinSmall (lo:=25940) (a:=52) (b:=52) sp25940 sp25992))) (joinSmall (lo:=26044) (a:=207) (b:=207) (joinSmall (lo:=26044) (a:=103) (b:=104) (joinSmall (lo:=26044) (a:=51) (b:=52) sp26044 sp26095) (joinSmall (lo:=26147) (a:=52) (b:=52) sp26147 sp26199)) (joinSmall (lo:=26251) (a:=103) (b:=104) (joinSmall (lo:=26251) (a:=51) (b:=52) sp26251 sp26302) (joinSmall (lo:=26354) (a:=52) (b:=52) sp26354 sp26406)))))))))
  have good : (List.range 26458).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 700000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 26457 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 26457 := by
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


private def packet (i : ℕ) : ℕ := (if i < 178 then (if i < 89 then (if i < 44 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 8 then (if i < 6 then 0 else (if i < 7 then 0 else 0)) else (if i < 9 then 0 else (if i < 10 then 0 else 0)))) else (if i < 16 then (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else (if i < 15 then 0 else 0))) else (if i < 19 then (if i < 17 then 0 else (if i < 18 then 0 else 0)) else (if i < 20 then 0 else (if i < 21 then 0 else 0))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else (if i < 26 then 0 else 0))) else (if i < 30 then (if i < 28 then 0 else (if i < 29 then 0 else 0)) else (if i < 31 then 0 else (if i < 32 then 0 else 0)))) else (if i < 38 then (if i < 35 then (if i < 34 then 0 else 0) else (if i < 36 then 0 else (if i < 37 then 0 else 0))) else (if i < 41 then (if i < 39 then 0 else (if i < 40 then 0 else 0)) else (if i < 42 then 0 else (if i < 43 then 0 else 0)))))) else (if i < 66 then (if i < 55 then (if i < 49 then (if i < 46 then (if i < 45 then 0 else 0) else (if i < 47 then 0 else (if i < 48 then 0 else 0))) else (if i < 52 then (if i < 50 then 0 else (if i < 51 then 0 else 0)) else (if i < 53 then 0 else (if i < 54 then 0 else 0)))) else (if i < 60 then (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else (if i < 59 then 0 else 0))) else (if i < 63 then (if i < 61 then 0 else (if i < 62 then 0 else 0)) else (if i < 64 then 0 else (if i < 65 then 0 else 0))))) else (if i < 77 then (if i < 71 then (if i < 68 then (if i < 67 then 0 else 0) else (if i < 69 then 0 else (if i < 70 then 0 else 0))) else (if i < 74 then (if i < 72 then 0 else (if i < 73 then 0 else 0)) else (if i < 75 then 0 else (if i < 76 then 0 else 0)))) else (if i < 83 then (if i < 80 then (if i < 78 then 0 else (if i < 79 then 0 else 0)) else (if i < 81 then 0 else (if i < 82 then 0 else 0))) else (if i < 86 then (if i < 84 then 0 else (if i < 85 then 0 else 0)) else (if i < 87 then 0 else (if i < 88 then 0 else 0))))))) else (if i < 133 then (if i < 111 then (if i < 100 then (if i < 94 then (if i < 91 then (if i < 90 then 0 else 0) else (if i < 92 then 0 else (if i < 93 then 0 else 0))) else (if i < 97 then (if i < 95 then 0 else (if i < 96 then 0 else 0)) else (if i < 98 then 0 else (if i < 99 then 0 else 0)))) else (if i < 105 then (if i < 102 then (if i < 101 then 0 else 0) else (if i < 103 then 0 else (if i < 104 then 0 else 0))) else (if i < 108 then (if i < 106 then 0 else (if i < 107 then 0 else 0)) else (if i < 109 then 0 else (if i < 110 then 0 else 0))))) else (if i < 122 then (if i < 116 then (if i < 113 then (if i < 112 then 0 else 0) else (if i < 114 then 0 else (if i < 115 then 0 else 0))) else (if i < 119 then (if i < 117 then 0 else (if i < 118 then 0 else 0)) else (if i < 120 then 0 else (if i < 121 then 0 else 0)))) else (if i < 127 then (if i < 124 then (if i < 123 then 0 else 0) else (if i < 125 then 0 else (if i < 126 then 0 else 0))) else (if i < 130 then (if i < 128 then 0 else (if i < 129 then 0 else 0)) else (if i < 131 then 0 else (if i < 132 then 0 else 0)))))) else (if i < 155 then (if i < 144 then (if i < 138 then (if i < 135 then (if i < 134 then 0 else 0) else (if i < 136 then 0 else (if i < 137 then 0 else 0))) else (if i < 141 then (if i < 139 then 0 else (if i < 140 then 0 else 0)) else (if i < 142 then 0 else (if i < 143 then 0 else 0)))) else (if i < 149 then (if i < 146 then (if i < 145 then 0 else 0) else (if i < 147 then 0 else (if i < 148 then 0 else 0))) else (if i < 152 then (if i < 150 then 0 else (if i < 151 then 0 else 0)) else (if i < 153 then 0 else (if i < 154 then 0 else 0))))) else (if i < 166 then (if i < 160 then (if i < 157 then (if i < 156 then 0 else 0) else (if i < 158 then 0 else (if i < 159 then 0 else 0))) else (if i < 163 then (if i < 161 then 0 else (if i < 162 then 0 else 0)) else (if i < 164 then 0 else (if i < 165 then 0 else 0)))) else (if i < 172 then (if i < 169 then (if i < 167 then 0 else (if i < 168 then 0 else 0)) else (if i < 170 then 0 else (if i < 171 then 0 else 0))) else (if i < 175 then (if i < 173 then 0 else (if i < 174 then 0 else 0)) else (if i < 176 then 0 else (if i < 177 then 0 else 0)))))))) else (if i < 267 then (if i < 222 then (if i < 200 then (if i < 189 then (if i < 183 then (if i < 180 then (if i < 179 then 0 else 0) else (if i < 181 then 0 else (if i < 182 then 0 else 0))) else (if i < 186 then (if i < 184 then 0 else (if i < 185 then 0 else 0)) else (if i < 187 then 0 else (if i < 188 then 0 else 0)))) else (if i < 194 then (if i < 191 then (if i < 190 then 0 else 0) else (if i < 192 then 0 else (if i < 193 then 0 else 0))) else (if i < 197 then (if i < 195 then 0 else (if i < 196 then 0 else 0)) else (if i < 198 then 0 else (if i < 199 then 0 else 0))))) else (if i < 211 then (if i < 205 then (if i < 202 then (if i < 201 then 0 else 0) else (if i < 203 then 0 else (if i < 204 then 0 else 0))) else (if i < 208 then (if i < 206 then 0 else (if i < 207 then 0 else 0)) else (if i < 209 then 0 else (if i < 210 then 0 else 0)))) else (if i < 216 then (if i < 213 then (if i < 212 then 0 else 0) else (if i < 214 then 0 else (if i < 215 then 0 else 0))) else (if i < 219 then (if i < 217 then 0 else (if i < 218 then 0 else 0)) else (if i < 220 then 0 else (if i < 221 then 0 else 0)))))) else (if i < 244 then (if i < 233 then (if i < 227 then (if i < 224 then (if i < 223 then 0 else 0) else (if i < 225 then 0 else (if i < 226 then 0 else 0))) else (if i < 230 then (if i < 228 then 0 else (if i < 229 then 0 else 0)) else (if i < 231 then 0 else (if i < 232 then 0 else 0)))) else (if i < 238 then (if i < 235 then (if i < 234 then 0 else 0) else (if i < 236 then 0 else (if i < 237 then 0 else 0))) else (if i < 241 then (if i < 239 then 0 else (if i < 240 then 0 else 0)) else (if i < 242 then 0 else (if i < 243 then 0 else 0))))) else (if i < 255 then (if i < 249 then (if i < 246 then (if i < 245 then 0 else 0) else (if i < 247 then 0 else (if i < 248 then 0 else 0))) else (if i < 252 then (if i < 250 then 0 else (if i < 251 then 0 else 0)) else (if i < 253 then 0 else (if i < 254 then 0 else 0)))) else (if i < 261 then (if i < 258 then (if i < 256 then 0 else (if i < 257 then 0 else 0)) else (if i < 259 then 0 else (if i < 260 then 0 else 0))) else (if i < 264 then (if i < 262 then 0 else (if i < 263 then 0 else 0)) else (if i < 265 then 0 else (if i < 266 then 0 else 0))))))) else (if i < 312 then (if i < 289 then (if i < 278 then (if i < 272 then (if i < 269 then (if i < 268 then 0 else 0) else (if i < 270 then 0 else (if i < 271 then 0 else 0))) else (if i < 275 then (if i < 273 then 0 else (if i < 274 then 0 else 0)) else (if i < 276 then 0 else (if i < 277 then 0 else 0)))) else (if i < 283 then (if i < 280 then (if i < 279 then 0 else 0) else (if i < 281 then 0 else (if i < 282 then 0 else 0))) else (if i < 286 then (if i < 284 then 0 else (if i < 285 then 0 else 0)) else (if i < 287 then 0 else (if i < 288 then 0 else 0))))) else (if i < 300 then (if i < 294 then (if i < 291 then (if i < 290 then 0 else 0) else (if i < 292 then 0 else (if i < 293 then 0 else 0))) else (if i < 297 then (if i < 295 then 0 else (if i < 296 then 0 else 0)) else (if i < 298 then 0 else (if i < 299 then 0 else 0)))) else (if i < 306 then (if i < 303 then (if i < 301 then 0 else (if i < 302 then 0 else 0)) else (if i < 304 then 0 else (if i < 305 then 0 else 0))) else (if i < 309 then (if i < 307 then 0 else (if i < 308 then 0 else 0)) else (if i < 310 then 0 else (if i < 311 then 0 else 0)))))) else (if i < 334 then (if i < 323 then (if i < 317 then (if i < 314 then (if i < 313 then 0 else 0) else (if i < 315 then 0 else (if i < 316 then 0 else 0))) else (if i < 320 then (if i < 318 then 0 else (if i < 319 then 0 else 0)) else (if i < 321 then 0 else (if i < 322 then 0 else 0)))) else (if i < 328 then (if i < 325 then (if i < 324 then 0 else 0) else (if i < 326 then 0 else (if i < 327 then 0 else 0))) else (if i < 331 then (if i < 329 then 0 else (if i < 330 then 0 else 0)) else (if i < 332 then 0 else (if i < 333 then 0 else 0))))) else (if i < 345 then (if i < 339 then (if i < 336 then (if i < 335 then 0 else 0) else (if i < 337 then 0 else (if i < 338 then 0 else 0))) else (if i < 342 then (if i < 340 then 0 else (if i < 341 then 0 else 0)) else (if i < 343 then 0 else (if i < 344 then 0x217671f2c414889ac47320c8f046c6304154890c3b017608c83000b40000217613d2c714f09ae47c20b0ee86942ec14b09043b818909483000b800002175b782bc949c9844591fb8e8068c2ec14a889838616708a02d40b6000021755882c994e49ac47620c0f106d030a15708f43ba17f094832c0d200002174fac2c4149899646e20e8eec6b82f114c08fc3d018708f82f80c60000217499f2d89568a024a121e0f946fc31815689643f019309a83280be000021743d82bc14689704571fd0e6c6742db13e88a03a016d08602bc0a400002173de72c394a097445c1ff0e7467e2e114288c83c618709183240c4000021738072b6941c95c4582008e6c67a2e314788c43a217d08c82ec0ba000021732212c394bc9b047a20d8f346fc31515a89343cc18309202e40be00002172c5a2b614249544501fc8ea06902da14188c03a417b08d02d80c0000021726462d715409ea49321a8f5c6f630a14f88f03c818708c02d80ac0000217205f2c614b099445d1fc0e6867e2e014608a839617409003180cc00002171a682cb14b49b847320f8f206d42fc14988ec3a817808d82cc0aa000021714802c594b89a046f2090ebc6bc30d15409303ce17c08a02ec0c600002170e982c594949864682088ebc6982fb14d08d43bc18309183100b6000021708c42b5943095a4521f88e7867c2e013e888c3a016f08c02f40b8000021703062b0941494644a1f58e306642cd138884c38016108102b40aa0000216fd302bd14909864652070eec6b22ee149889439416d08482bc0b00000216f74e2bc145896e4581f98e6069c2f914d88d03a617c08d02d80bc0000216f16c2c494b097e45b1fa8e386722d7141888038817008b82cc0bc0000216eb842c614c49aa4652020e8c69e2f014608b43b817a08d82e40d40000216e59f2c414c09b64832130f146ba2fb14c88e03ac17108b02cc0a60000216dfae2cb14e09b84812140efc6ca30715009003b817408b82c00b60000216d9c52c1949898846d2078eac6ac2f914c08e43b017609402f80bc0000216d3d52c994cc9b247b2150efc6b02f914888e03be18709282f00be0000216cdca2d315149c647f20f0efc6b82fd14e08dc39816108302bc0bc0000216c7ed2be946c9724572070e906802e414b88dc3bc18608f83040b00000216c2142c0147098e4582000e546642d813f088c38a17108882c40c20000216bc212c994f09ae47b2118efc6b030014d88f83b017608c83040c40000216b6582b714209524431f20e1c6542c7135888039016f08b82c80a60000216b0842b814349684612078ed86a82f814f89083be18209103100d40000216aa7d2d0150c9c447b20d8eb46c430b15409103ae17508602dc0bc0000216a4b02b814349604602008e8868e2e514688bc3a817c08d02ec0b600002169eee2b1940c9484491f30df06462cd13c885c38e16c08902f40b2000021698fc2cf15149ce47920d8f006aa2eb141088438216508602d00ac000021693062c5148899045f1fc8e7467c2e414288a839217708e83080be00002168d182c514c89b647b20e0f046b830215009183d017f09003080d2000021687632ae13fc9544411f20e1865c2c4138886c38816808382b40b0000021681942b8945496845e2038ec06a22f515309043ac17208c02e80aa00002167bb32c194bc98e45b1fc8e6068a2e013d887438016d08f02e80c2000021675bd2c714a899c46e20d8f1c6f231615809503e819609182f80b000002166fcc2c614a49a247d20c0ee46b230014e89083ca18509303240d600002166a042b914689804672048ea06942e414388b439216808b02dc0ae000021664172ca14ec9be4782060ecc6a22eb14808d43aa17908b82f40b400002165e0e2d315189b64802148f246b230215509303d819409683400c4000021658432ba146c9664581ff8eac6942f514a88e03b818309282e80c4000021652572c214989924702078ea86982e814308b43ac17808e82fc0c200002164c642cc14d49ac47e20d8ed06b42fd14f89083b617c09603200d8000021646892c1949498e46e20a8ec46aa2e814088c439217208f02e40c40000216408e2cd14f09b448a20d8ee46b62fd14b88e43b017c08d02d80c000002163a9d2c4148098a4602010e8c6942e814c08b83a416b08c82d40be000021634cb2ba946496c45d2030e786862e614088c43aa17008482d80ca00002162f032b7946094c44c1f30e3465a2d313b887c38215507d82900aa000021629322bb94889924622058ebc6962ed14d88e83be17f08882e00ba000021623372cd94a49824682068ea868e2dc14408a43b617808d03080d800002161d402cc14f09c046f2070ec069e2fe14b08cc3b817a08e02dc0b8000021617502c894d89b647420d8ef46c4308156093c3c218109203140c2000021611582cc94c899446f2030e9469c2f414708c43ac17d094831c0a400002160b452d815209d44862108f286b22f814f08d039e17808d03000c0000021605482ce15009ca48120f8f0c6dc31215909383d618909783280c00000215ff782b8145097845c1fa0e7467e2e513b884437616108782a40ac0000215f9a42ba945896c4572010e846802e5142087838e16f08982c00b60000215f3c72c294b097e45f2000e9868c2e2143088038c16a08482b409c000 else 0x218e0c32b1140895c44d1fa8e646762e014308a43b018408e82e00bc0000218dac62d214fc9b24732010ed46ba2f914f89283c618309383180d80000218d4d72c814d09ae46f2080ec86ca303157093c3ea18f09703300c40000218cedc2cd14cc9b647a2090ec069a2ea14908d83a617508c02e00be0000218c8dd2d014f89ce4852130ee46c030214f08e43c817108b82ec0ba0000218c3022c1148899445c1fe8e906902f314d88f03c2188094030c0ba0000218bd082c594bc9b247b20d8f046c230815009083c018709202ec0b20000218b7052cb94bc9a046e2058ebc6ac2f915189043a818308f83240d60000218b1032cb94e49b048420d8f106b22f214708a439617a08a02d40b20000218ab192c514bc9904612070ea468c2de140889038616308a02d80ba0000218a5402c094789904612058ee469c2f0147889838e16c08602a40b600002189f5f2c3148497845d2040eb06a62fd14808e43c218309883480c8000021899962b1944096644f1fb0e446762e014488d03a416c08402bc0b2000021893bf2b8947c9824672040e9c69e2fc14a09143d0187091031c0c400002188dcd2c914c49aa4682030eb06b82fd15389003ca18808c82d40a2000021887be2db15709f64a52210f9071232015d09683de18d09302e40bc000021881d02c0947499046b2070ecc69e2e8143889c3a016f08b82ec0c000002187bb62da95549e048b2170f60706322164899440019009483240be000021875f32b394209604591fd8e886902ec14a08d43a617808982cc0bc0000218700d2c194449764672040e886942f414a08cc39e17008702c80ae00002186a352bd947898645d1ff0ea46962e714308bc3a617508b82f00c0000021864432ca94e89a84722058ebc6a82f114c09043c217e09203100bc00002185e452cc94c89a647120a8efc6bc2fc14f09083b217c09403180b8000021858782b7142896e45b2000e706822e013f08a439a17008b031c0c8000021852802c3148499847120a0ee06c62fe14d08e83bc17d090830c0cc00002184c9b2c394b899047a2090ecc6a62f714e88e43ba17408b82e00b4000021846c62bc147c9804682038e7867e2ea143088839c17708d02ec0c0000021840ef2c1149499446e20c0f146ca30a15709543d618208c02d40ae00002183b102c214ac99e47f20e8ee46b42fe14c88dc3c217f08a83000c80000218354b2b3943c9644501fd8e7c6782e113f88903a617708802bc0c000002182f642c994c099e4822118f246d631015789283d618209583300c2000021829532d615409e44912158f286d430415089183de18409203040be0000218238a2b1142c9604461f78e686862e1145088c38415e08102b00bc00002181dba2b8143897244a1f60e3c6642d8141889038a17508782b40aa000021817e02bf948497e4652050ec06b02fb15008e43a617908f833c0d0000021812032bc945896045e1fd8e6867c2de14288ac38a16a08682e40b600002180c012d215289d649021a0f546e030615509543dc18c09583340d80000218062f2bc146499e46b2040ebc69a2f214988d439616d08d02fc0ca0000218003d2cb94bc99a4732070ed06a22ea145089c3b617808c82dc0aa0000217fa482ca14f49b247020c8ee06b82f815088fc3d018509883240b60000217f48a2b1941c96045b2048e7066e2e3146088838816708482a40a00000217ee8f2cc14dc9b44862158f006b02ec14688f43ca18308e02ec0be0000217e8bb2bf148098c46b2080eb869e2f514e090c3c417d08e02f00cc0000217e2ed2b3140494a4461f50e4067a2e1143088c39416f08c82e00be0000217dd102bf946897e46920a0ec86a42f815309183ca185094831c0c80000217d7382bf145c9804521f70e6c6662d8139883835a15708202a00b00000217d14c2c114b099c46f20b0ed469a2ec14888e03c618a090832c0d60000217cb5a2cc94a099e4652028ea06942e314588b439e17408b82c80be0000217c5782c294a099647020c8ef46ae2fe150091c3c818609403000b60000217bf932c0945496c45e1ff0e7867c2e914908d43a217008602f40b20000217b9a22c894cc9a847f20a0eac68c2e214788a439016608782c00c40000217b3c42c114889864642078eec6be30515189183be17b08d82a80b00000217add82c1947897c4611fc8e6c6802ed14788a039017208702d40b80000217a8052b894609744531fd8e8068c2ed14c88e83c2180090030c0c80000217a21d2c5149098045e2008ea06962f014788c43aa17608d83040bc00002179c472c214909924652050e886922e213e88a439e16b08882b409c000021796552ca14cc9b04802148f0c6b030315489143b618209203100bc0000217907b2c114a49824662058e9c6882e714508ac39617308482bc0ba00002178a982c1948c9884621ff8e986a82f814b08ec3c018609383300c0000021784912d715449da48e21a0f7c70232616089543ee18d09402f80b200002177eb42bc145c9784521fd0e8868e2ee144889838616608802fc0b2000021778b72ce95109d648d21d0f2c6be2fc14d08dc3b618009002e80be000021772fa2b113e093c44a1f20e286542c6134884435e15708182a00a200002176d042c814bc9aa47f2088ed06a82fb14e88ac38216808d82d80ae000)))) else (if i < 351 then (if i < 348 then (if i < 346 then 0x21a5a352ca14f89d04852110f206ba2f614a88e03a617b094830c0c0000021a545a2bd947095a4491fa0e586662d2138887437e16408c83140c4000021a4e732cc94dc99e4712080ee46b82fa14f08f03b218509483180c2000021a48aa2b2940c94a44c1fb0e8067e2ec14208c03be17808b82b80a6000021a42d32bc147497c4571fc0e646882e213f08cc3c018809203040c0000021a3cec2c3148c99446d2088ed06ae30315109003c017b08f02d40ae000021a37272b3142096644f1f58e686862de13f08b839a17008c02f40bc000021a316c2aa13cc93443a1f60e686722d5136887c38416c08982e40c6000021a2b772ca94ec9c04882188f486be31315e09503da18a09383400c2000021a258c2c5149498a4591fd0eac6862f314b08dc3ac18208c02c80ac000021a1fa22c594a899645b1fb0e806782dc139089439217608b02e00b4000021a19912d715409dc4862120ef06be30f155892c3c818c09b83300da000021a13c02bf146c9744672020ea86b02ed14908d83b216a08582d00ac000021a0df62b8945497045f1ff8e686702e8149889c39e17a08f82f80ba000021a08132c014b899a46c2080e806982ef14808bc3ac18008d03000c0000021a020d2cf94f49ae47720e8ec06b630414f89183c217308602b80a00000219fc0c2d095549f249721b8f546de30a15789103c818309182d40b40000219f6192cd14fc9be4832198f206e831615889603dc18c095833c0ce0000219f0192d495289d848a2138f306e0317153891c3c4182093830c0c60000219ea1e2cd94b49a047320e0ef06bc30115289243ca181093032c0d40000219e4452c0148c9864612000e886802e214688d83a817708c82b00b80000219de812b4144c9504521f70e446822e414288a83b617108983100d00000219d8872ce94e89ac46f20d0ef06b22ef14908b83b017d08b82ec0ae0000219d2d42ae141c9444521f60e3865c2ca136886439816b08982ec0b00000219ccd22d595309cc48220d0eac6a22ef14a88e03b017909003040b00000219c6ec2c714d49c048f2198f486e431115b09943f818609582f80a80000219c0de2d194fc9a84822080ed46ca2ff14c08dc3a417208702c80b80000219bafa2bd145896645a1fb0e586782d813b888c38e15e07d82b809c0000219b5582a5939c8f842c1e68dcc6062b4131081036215a08182d40aa0000219af572d315189d448c2178f046be301157893c3da18609303140d40000219a9562d415309cc48220f8ef06ae2f114608bc3b017808d03000cc0000219a3702be94889844651ff0e586642dc142088039417508c03080c000002199d682d495209ce4832130f346d230e15689303e219809983480d8000021997c42a713e49384301ea0dec6442cd13f088436c17008e030c0ce000021991c62d195389cc48a2168f546e031515809243c018108e03080b200002198bd52ca14dc9b44722080ec469e2f014608ac39c17108f82f40c6000021985f12ba141c9724672030e9468a2e614308b83b017d090833c0e800002197ff22d4152c9c848720e8ef46ac2f714608ac3a418409202fc0b800002197a022c5949c99c47520a8ec86c02fd14d08d03ba18a09182f80ba000021974232c394cc9944702090ec86b42fb14b88e03c818509203100b200002196e262d715589d84892128f0469e2ed14608c43c617e09102ec0ba000021968492c214ac9a846f2070e9c6902ef14a88d03aa17b08b02c80aa000021962632c414a899246a2098e6c6702e4142889039016d08883140c600002195c7d2c294bc9a04722058ed46c02f914608b83a417a08c02f40c4000021956a12bc147898e47020b8f0c6c630515309203dc18509203140c8000021950992d115189d648b2108f006a42f814788d43aa17808b82f00b400002194aaf2c794a499445a1fb8e6c68c2ec14c08f039617308a83080c8000021944c12cc14d09b04862138f0c6d831215508ec3b417008703000b000002193ed62ca149c9924712140f1c6be30214e89243d817808c83000c2000021938fc2bd94809724541fd0e6c68e2ef14c08e43aa17408e02d40b4000021933232be94749704602050edc6ac2f114b08d43ac17608e02ec0b000002192d822a593ac91c43c1f18e2c6482d313b08903a217708d82ec0ca0000219278c2c714889864601ff0e9c68e2ea14a08b03a617208802cc0b00000219219e2c614c49ac47b2108eec6d030a15709283c417908c830c0b200002191b912dc156c9ec4952200f606fa31d162096c40619a09c03380d2000021915a52c494a899846c2098edc6c230c15188fc3ae17708d02d80b200002190fb32c814a899046d2038ea46862de13d088c39a16608702e00bc000021909db2bc946c9664592010e9867e2da141087838416208602d00b2000021903f82c414c499c46c2080ea869a2f614d88e83c018009082f00b60000218fdfc2d215209d449821b8f646ea31b15b09603d618809083000be0000218f8152c514b09a446920a8f006c62fa145889439616b08b82f00c60000218f23d2bd146096e4632068eac6962ec14488a83a416e08882f80d20000218ec552c694b899c47a2080ee06ac2fa152093c3c417d09002f40ae0000218e6802be149098a46a2070eb06a82f214f08c43b417108a02c40be000 else (if i < 347 then 0x21bd3362b6945897645e2040e986982f114b08dc3b418709403180c6000021bcd8b2aa13d89404461ff0e706822e414508dc3bc17f08e03000c0000021bc7a22c614b499847220c0ef86b22f714c88e83bc17b08c82fc0c6000021bc1a92ce150c9c84812100ef46bc2f814b88a83ac18608f82e80b6000021bbbaf2cb14c89aa46d2060ed46aa2eb14408c039217608e82e40be000021bb5dd2c2945895e4562028ec06ac30115309043b417208a82e00b0000021baffa2c114b49be47a20a0ee468a2eb14808d03ca18509103240ca000021baa2e2b614449784642048eb06982f614c08bc37e16108282980ac000021ba43d2cb14e499e47220b8ef46c230115109043ae18008f03000a8000021b9e6d2b9944896445a1fd8e846a22ec14988ec3c418308582d40b6000021b98882c694ec9b447b2108ef06a22f914e09003d618809383400da000021b929a2c014c098e4631ff8e5066a2d313d887839616d08382a80aa000021b8cc32bd14309544501fb0e6c67e2dd142087037615f08e82ec0be000021b86a82df15809f649c21a0f3c6ce303154090c3c418a09603200d2000021b80b62cc14c499a4662058ec86b22f314908d039c17308f82f40c4000021b7ae22bb946898646520e0f006be304153090c3c017a09183000b6000021b75142ba14349544511f68e6c66e2da143889439c17208882bc0b2000021b6f502b113fc94a4471fc0e386682e0141889039617108d82fc0c0000021b69602cf15049bc47720e0ef06ae30614f08e83a417008882e00b8000021b63a12ad13e494c44b1fa0e706602e714508983ba18109203200c8000021b5daf2cd94fc9c847920a0ee46c430614f090c3ca18609302f40b2000021b57c12c514b098e47320f0ee86c62f714b08ec3ac17708b02e80b8000021b51ae2d015049c04842120f046ba30515009103be18009203080cc000021b4ba62cf94ec9b046b2090eb46a42f714b088839e17809183140b0000021b45a12d495109c247b2158f106d030715408f43ba17a08c02f80b2000021b3fd42b794749764622060ee06b02f515208f43b018709203080be000021b39de2c894ac9a646f2028e7869a2f514988d83c418209302fc0c2000021b34202af141493c44a1f30e2c6702db14108a43aa16d08b83040b2000021b2e252d115049c247c2130f206ca30515609243d418809703000ca000021b28632b994649844501f30e406742db13d887838416608782b40b0000021b228b2bf94709824652068ebc6902e413a884837c16208182a40ac000021b1ca92c414b899a4752090ed06a22f614a88f43ba17208e83200c8000021b16de2ba145097645f2038e9c6862ee14588dc38a16b08982e40ae000021b10f22cc14d49b64802100efc6d830f15809403e618a09603280c4000021b0b0b2c794a89a046f2078ebc6a22fb14c08d03ac17f09102fc0ba000021b05272c3148499446f2088eb069a2f314888c43b017708d82fc0c8000021aff1f2d595149c848d2110f246cc2f714c08dc3be17308802d80be000021af9152d615349da4902180f406ea31615f896c3e218609803180ca000021af30c2d215149d64862158f486f231e15e896c40019309583140c8000021aed202ce94d099847b20d8f086ac2fa15589403e218508f83200b8000021ae7772a693ac91a4471f48e3c6562c6135882c35e15808602d40a4000021ae1822cb94dc9b647c2118f006ae2ee15409183b217b09082e40c8000021adbae2c214a498445f2058eb86aa2f514a88e439e17308702cc0a2000021ad5ae2cf94e49b247f2130f186ca30815208f83be187095030c0cc000021acfec2b5942896844c1f70e6c69a2f214d08e03a417308502b00b8000021aca162c114949964652018ec86ba2f614788c839c17308c82ec0aa000021ac4102d495149e048f2128f506e631115c89983f819809603340c4000021abe242c894cc9c04702030ea06922e714608c439a17108d02d00aa000021ab8442bf947c98c4642038ea06882e314808d43a617708a82e80b2000021ab24c2cb94f09b24782100f0c6de31215809403d819209783100c0000021aac882ba142c95a4521f88e6066a2d9142888c38416008a02d40be000021aa6bc2ba144497645e2090ec86a82f714e88ec3c018708d82ec0bc000021aa0e62b814689784662060ee86b62f414a08dc3ac17a08882c40b2000021a9b1b2b594549664591fc8e8c6962f314508d43b618d09302f80ca000021a95652a993d893e43e1f10e2066e2da14108a43b618008d82f40ac000021a8f8f2bb14709744601ff8e8c6962f614908f43b217e08f02d80bc000021a89c22b914649804602008ea46762dd13b887038616e08302b40aa000021a83bd2d69538a004a021c0f806f431516389903f018d092831c0c6000021a7dcd2c514b09984632018ec06a22fc14c89083ba17f08c82f40ba000021a77ed2c3149c9a84742068ed46aa2fb150092c3da18d096830c0bc000021a72192bc14709784621fb0e786942ef14708b839616a08a02b40b4000021a6c302c694a898a4632060e8c6a22f614988c83ac18109002f80c8000021a661a2db95609f249d2158f4c6e230915409383d618509403240c8000021a60202cf950c9ce48020e0efc6bc30915389183dc18a09583140ca000 else 0x21d4ca52c714a099a46a20c0edc6b42ff14708e03a817808a02e40b2000021d46ae2c6149c99847020b8ed469c2f414788c83b417509082f80ba000021d40fe2a493e49504431f68e2c65a2d313b087c38615e08982ec0b8000021d3af32d3952c9d04952148f1c6ca30a14e08f83b817808b831c0be000021d350e2c394b49ac4732078ee86b62f915009383ca18509202e40b6000021d2f262c994e49ba4862138f146b42fe15288f03be18009382f80c0000021d29232cd14d49aa47b20c8ef46c230614f09043a217709082f00ba000021d231b2d6151c9d248f2148f3c6e4306154090c3be17b09003240c8000021d1d252c714b499446f20a0ef06be30014e09103bc17508b82fc0b6000021d17432be14949844642020ea86862ee14908c839c16f08882e40a2000021d112b2d895309d248820e0f006ae30415108e83b417c09283180c2000021d0b5b2bc94949924682058ec06a62f614d08d03a216408983140c4000021d057d2c0947c9864652040ea069c2fb14b08e43c0186095030c0d0000021cffb72b5143095c4521fd8e646782e613e888838c17a08e03000c6000021cf9bc2cf94dc9b247c20c8ecc6a42ee14c08dc3ac18108d03140be000021cf3e52bd946096a4531fd8e5067e2e614708e43ac17608982d40ae000021cee072bc94549684531fd0e7067c2db13c089038216608982e40c8000021ce8152cc14bc9a447320c0ed06ca30415109203c618308d82f40ce000021ce20f2d115189d84882150f246e231415089043ca17c08c02dc0ac000021cdc232c5949099e4782098ebc6b02f814e09143c418508e83100c2000021cd66c2ae13fc9464501fc0e8468c2e5142087038015d08382c00a6000021cd05a2dc9564a004a52220f7c6f631115509183c217f09283040b2000021cca702c2149098845e2058ed86bc2fd15309383de18008f02fc0bc000021cc47a2c994f89cc47d20d0f006ce305154090c3d218609283040d6000021cbec42ad13ec94243a1f28e3465e2d113c087c37816108402a00b4000021cb8a82e095a0a044a021d0f886f631415989103b017908b03140b8000021cb2c42c394b097e4541f88e806862e6142088038816b08102c00b8000021cacd42ca149499e47120b0ed06a82f614b08c03aa16e08e031c0c0000021ca71d2a813d892843a1ef8e1c6642e413f085837817008f02d00b2000021ca10c2d5950c9b04772078ee06b42f714c08e03b018108f02c80a0000021c9b2d2c194ac9884692028eb06b02f114c09183b818009383140ca000021c953e2c5949498c46b2088ec06962ec14908c03a817409003200da000021c8f502cc94d89b647c2120f006bc30814f88fc3c818408b03000d2000021c89922b094349524571fe0e786802db139887437e15c08782f00ba000021c839b2c994cc9a047a20d8ed86ac2fa15209203be17608b02f80cc000021c7dd82b9945496e4672028eb06b42f815108e839e16a08a82f40b4000021c78112af941c9524501f08dfc6642d513b08a03a017308d83000d2000021c71e92e19578a1e4b022b0fd4716323163898c3e418d09683440c2000021c6bff2c894b89a847820b0eec6922f114e08a438616f08c02ec0c8000021c66372b314089444421f70e3864a2ba136882836a16308582ec0be000021c602a2da95589f64992158f0c6b22ef14b88f83c218509183140bc000021c5a732af143c94a4511fa0e906882da13b087838816c08882d80b6000021c54872c494ac9b447a20c8ec46ae2f614c88fc3c618408d02cc0bc000021c4ec42b8947498c4622010e6866c2e213e88d43a617408b82d40b4000021c48ea2bf14a49ae46a2038e846942ec14788b839216e08c02fc0c0000021c43112bf147097a4652010e7867e2de14508a83a016d08702d80b8000021c3d552aa13f493843c1f28e4c6682d6138886c36415b08682a80ae000021c377e2bb949497e4602068ed46a62ea14708e43c217b08e031c0ca000021c318a2cc14e098c4651ff0e5c6702dc140888839c17208882cc0bc000021c2b972cd94e899c46d2038eb86a82f714b89103b217d08d02ec0d2000021c25ac2c414889904692040ea468e2ed14588d039a17608b82e0094000021c1fc42c414b499e4692080eb86a82f7151891c3d618608f02ec0c2000021c19ed2c014809804672030e986862e114308d43ba17c09302e40be000021c14182be14549684521fa8e586642e314788ac3b417b09203200c8000021c0e2d2c914e89b447220c0ef86cc30115009003cc18508e82e00ba000021c081d2db15449d048f21a0f206da30d15088e039617208d82f80b8000021c02242ca14d499e4742030ec06a02f114c88a839017008882d00b0000021bfc4f2bb147096a4692060ed86a02e914188883a617008a82b40a2000021bf64e2d5152c9d047920c8ec86ba2fa14f89043ba18409583140d4000021bf05a2cc95089b646f2090ef06c030114b08dc3c617c08f83040b4000021bea812bb94649764601ff8e6867c2e914708c03a017908903000ba000021be4952cc94d89aa4782050eec6ae2eb14d08c43b017b08e831c0c6000021bdedc2b2143896645a1ff8e5c68a2e514988b839c17108c02f00be000021bd8f82c394ac99c47620e8eb468c2f114c89043a017d08b82e00b0000)) else (if i < 349 then 0x21ec6cd2b894749864622058eb069e2f714f892c3d018208e82d00b4000021ec0f42b994409604621fc8e8c6862ef14e08e83b417708a03040c4000021ebb032cb14b098e4672098ed06ae2f914808a039416f08e03000c6000021eb5232c294889844672098ecc6962f914d89083b617c09082ec0be000021eaf1f2d295049d648f21b8f486d42ff14d88dc3c217408c02ec0ac000021ea95c2b5144c9724632030e7c6842db14508a839017308d82e40ba000021ea3872c194a499246a20b0ed46ba2f4151090c3e619209783280bc000021e9d762e0956c9e248d21a0f586f031915c09543ea199098032c0c2000021e979c2ba146497c4582020eac6b02fb14e88d039216c08782cc0b2000021e91b32ca94bc9aa47c20b8edc6c62fb14f08ec3b418009382fc0c6000021e8bbf2cc94fc9cc48c2150f246d430915089383d219009182f40c6000021e85c92c694b499a4671fc8e6867e2dc142088439416a08982cc0bc000021e7fe72b894609784612008e8468c2f514c091c3d018109102ec0ba000021e7a082bf947898245d1fb8e6c6722d9140887839217008702a80a4000021e74162c714f49b24702050e9c6982e314a89103c4188095832c0be000021e6e242c994b89b44822150f206c02fb14f88f83b818008b82e40cc000021e68432c4148097245d1fe8e906842eb14788c43a818409283080ae000021e624f2ca94e49b247d20c0ed86ca2f8148089c38216a08902e00b2000021e5c422d8955c9f049d2228f6c70032415a09403e819809c035c0e0000021e567e2b494149564411f08e146542cc13c087436e16308682e80b6000021e509c2bb946c98c46d2048e7c68a2e914488903a817408b02c80c4000021e4ab72c714d49b84702068ec86aa2fe15188f83b417e08f83040cc000021e44bc2cb94dc99c46a2070ec86942f214588c438016d08882b00b2000021e3ed12c194b49a447720b0ed86ae2ff14b88f43be17e08d830c0ce000021e38ce2d5153c9d84932180f3c6e431115709583ec19e09683400d6000021e32e72c5946499046e2158f0c6d430715009203be18408c02f80c6000021e2d092bd148096044e1f78e586702d9140887c38016c08a02ec0c0000021e27322bb14889804642058ec46c62fd14b88d43c218a093831c0be000021e214d2c4149099247520f0f0c6ca31115589303de19509483440d2000021e1b6e2c294a09a046a2078ebc6a62f414f090c3c018709383140c0000021e159d2c4949098e4621fd8e9468a2e414588c439e182096032c0c4000021e0fe92af93fc95645a1fd0e6065a2d614208c439e17408a03100b2000021e0a0e2bd949899447020a8eb46aa2e814108c83b417708e83000ca000021e04072d695109ba47e20e0edc6b230514f89083ae18108e02f40c0000021dfe122cf14f49b047920d8ee46b230615389043cc17508a02d80b0000021df8212ca949099e4682070eb06a82ef145089439a17608d82dc0ba000021df2412be14389804612088ec06a22e0141089439a17308b82d40b6000021dec4f2c094709804732050eac6a42fa14d08f83aa17b08e831c0d8000021de63c2db95689e84942178f346da309150890c3c018909102e40b4000021de02e2d895309e047a2098ee06b82f614a88dc3b216a08582d80bc000021dda362cd14e49ba4852130f286bc2ff15209183d818f09382e80b2000021dd4862aa13ec93c4491f98e586722db144887437c16608882e00b8000021dce722d715549e048d2190f2c6ca30415188ec3bc17708502d40ba000021dc8802c514a89b848420d0ef46cc30915508fc3d218809503500c2000021dc2c02af940895e4551fe8e986862df13e889c38416408102e40b8000021dbcaf2de15689d24852100f3c6c82f214a08dc3a616b08a82c40b4000021db6e52b4143897a4622018ea86822ec14588d03b417308a82e80b2000021db10d2c214b499a4702058ed86b22f414b090c3ba18609083180d4000021dab272c094689844611fb0e6868e2e414588bc3b0177090830c0ce000021da5382c894c09924682010e986802f014e08f03b817808982f80b8000021d9f4d2c994d899e46f2038ea869a2e814488d83c218009202f40c2000021d995e2c714d899846320a0ea46882e214488a43a816e08582cc0b2000021d935d2cd14d49a04732088ec46c22fd14d88b83a418008c02e40cc000021d8d682cd94c499e47720c8ee06c02fb15008f83c617f09082e40c6000021d87812c614b89ac48220e0ed06b8300153092c3e218e09683240d2000021d81962c894b09944762090eec6a02ea143888c39016c08682b00c4000021d7baf2c6948898646b2070ed06b62fa15008f43ca17f09603240bc000021d75e92b4144895643a1f68e786922ef14808d83a217b08b82dc0a4000021d6fd62d3952c9ea49521b0f186d030915089243d019809503140c8000021d69f82bf949497045b1fe8eb86b22fa14f08f83c417f09302dc0ae000021d64352b0940c93a43f1ef8e306542de142089c39617608b82e40bc000021d5e6a2b494749724671ff8e9c6862e714608b83a017808c030c0b8000021d586f2d114e49aa47520c0eec6b82f914e09083c218e090030c0ce000021d528c2c2148c97045c1ff0e6067a2e313e087c38c16408582e80c6000 else (if i < 350 then 0x22040b72b0141495a4591f90e7c6882dd14188a838816d08c82d80c800002203ab22d595449cc47c20e8eb06a82ef14a08d43b417908d02e40c00000220349f2d8155c9f44a021c8f686ea31715f098840419b09803180b800002202ebb2c694a49a248220e8ef86c02f714d088439216908b82d00b4000022028c22c794c89a64772098eb869c2e314908d83aa17f09002f40b8000022023022b493f89424421f38e0865c2d713e08a039216e08b82c80ba00002201d3e2b0947097c4561f68e6066a2cb137883838016608882dc0ba000022017662ba944896845e1fa8e6467a2df13f888438e17008702bc0b8000022011872c014b49a44702060eb468c2e914488bc3a817308b82f00ce00002200b932cb94b89aa4782098efc6c02fc14f88ec3a017408902d40c2000022005d32b5140c95e45c2060ecc6aa2f314888d83a417e08d83140c0000021fffd22d195209ce47620d0ed46ac30215189243d818b09582fc0c4000021ffa122b2941c94a4381f18e3c67a2d913d887c37816b08702ec0b0000021ff4392c014889804692030ea86962f714988ec3ae16c09403140c8000021fee4c2c394ac9a046e2078ec46b430015389083b6177090831c0ce000021fe8772bb146097846a2068e946982e914788d03bc17a08d82dc0b0000021fe2692d695389d248a2120f106da30e156091c3d017808b82cc0aa000021fdc8e2bf14589824602038ec469a2fa14e09203ee192099034c0d8000021fd6b02ba947c97445b1ff8e886882e7144889839e17e08b02dc09e000021fd0c12cc94f89b84882140ee06b430315309043b417908b03040c8000021fcadb2c594cc99647320c8ecc68e2e714708d03a417608a03040d2000021fc4f72c714b09be4882100f186b830114f892c3dc17d08482b4094000021fbeff2cf95189be47a20c8ed46aa2fa14f08fc3cc18709103240d0000021fb9362b614249604561f70e4868e2eb14388c83ae17208d83040aa000021fb33f2c714b499646b2028e7c6982f314c88c03ac17d08c03100b6000021fad742bd14609804672050ea068e2e513b887c38816b08782d40b4000021fa78e2c6948499046b1fe0e946642cd13c086837216808602a00b2000021fa1a72c194a098a4642010eb468c2ee146889c3a216b08d82e80bc000021f9b932dc95649ec4912198f306da31215009083b217d08e83380da000021f95822d314f89d04872108f186ce30814b89083d218b09282e40bc000021f8fab2be14709784521fd0ea068a2f214d08c839e17508a02cc0b4000021f89e82b7944096e4612008e9468c2e1144889838a17008c02c80a6000021f84202b514349764632080ecc69c2e414988d03b417108c82ec0c6000021f7e352c4147499046b20e8ef46ca30c15509503e018e08f82f00c8000021f78312d115089ca48820e8eec6b830315209103c818308d82fc0d0000021f725f2b414349724531fc8e6867a2e3142889c38416a08c82e40c8000021f6c952b594409704551fe0e8067e2df14308cc39c17108e02ec0c6000021f66812d9955c9e849020f8f206b22fc14a09103be17c09203200c8000021f60792d315149d048820b0f006bc2fa14f88f43be17c09182f80c2000021f5aa52bb146498c4702040e9c6962ea14488ac3a017208102d00b8000021f54d12ba14149524471ed8e206542d2136083438616408502cc0c0000021f4ecf2cb14d89c248120c8ec469c2ef14b88e83be18709683540d4000021f48e02cc14f89ac46c20c8eec6c02ff14808f83be17d08902a00b0000021f430f2b4140c94c4511f80e5865c2c812d880c36215807f82bc0a8000021f3cfd2dd1564a024a52250f8470031c15e096c3de18d09583180e2000021f36f42d315349cc48d2128f306cc30715389083bc18208e02f00b0000021f31242bb948c9864662070ebc6a82fa14a08ec3c418609303100c8000021f2b522b8145c97e45f1fd0e6c6682d513e088c38216008282a80bc000021f25592cb14c499846c2060e8c67c2e014388b439c17108f03240d2000021f1f962b493e09524471f98e406822e714708c43ba18609182e80ba000021f198e2d495249ac47320e0ee46c430014f88f03a017508f83080c8000021f139a2ca14b899646d20d8ed46882e214288c43a017708c82fc0cc000021f0d982d115009ae46f2048ecc6982ec14308b43a617309303040d0000021f07d12bb145897e45d1fe0e686a42f214a88cc3b417708402b40aa000021f01cc2ca94bc97c45f2068ec86b22f314a88ac3b617d09503300be000021efc0b2b394249444421ef0df86422c913b089038e16608983040c0000021ef6302b7141094e43d1ef0e406582d1138085036e16008402bc0b6000021ef06d2b794109424451f70e4c67c2e214388b03a216e08a02e00b8000021eea6d2d115409ce47e2100f346ce30c15609343d818a09203080c0000021ee4892c394949a647e2100efc6c62fb14e08d43b817c092031c0bc000021edea92c4948c99246c20a8edc6b22ff14b88f83be17f092030c0cc000021ed89b2ce953c9c648520f8f106ce30b15409483e418809783240c2000021ed28a2d7952c9c849721a0f506ea31715e096c3f418a091833c0c2000021ecc9a2ca94c89ae47a2118eec6982e914a08e03b817c09202fc0c0000 else 0x221ba9b2d295189e64922190f546ea31615d098c3f619509483100c60000221b49e2d015009c04862130f186c42fd14a88dc39e17508e83140c40000221aeb52c894cc99a46e20a0ee06bc30015088dc3ca17b08b02e40aa0000221a8bc2ca14bc9ac47620a8ed86aa2f214c88ec3bc18008f83200c00000221a2f12b314089604561f88e7c6902e714408b839416d08982cc0ba00002219d1c2bb945c9764642048ec06ba30515389103b217408a82e00bc0000221973f2c0147898245d2018ebc6ac2f715308e03ae17509382f80ca000022191572c994ac99647120a0ecc6962ed14908fc3a617d09083240ce00002218b6d2c4148c99c47520d8f206ac2f814f08fc3bc17608702c00a0000022185862c414b498a45a2058ea06902ec14488ac3a417908f02f00cc00002217f642e315709fa4a82248f8c6fc31815989543e619509a03100bc000022179872c294b89a04682020e9c6902ec14888d43b417908c82e80ba000022173812d294f89c248e2160f246da30d15108f83b218009283200b800002216d9c2c494889864692080ea86882e8143088037816308182980a2000022167b52c2149098e46f2030eb46b42f914a88e03c417a08e02cc0aa000022161e52b7141494044d1fa0e6067e2e814888d43b418009102f80c200002215c262b194349684521fc0e5466a2d313c087437c16e08902d80a8000022156242d3951c9c847a20c0ee86ac2fc14d08d83c018109202f80d8000022150302ca14fc9e048d2178f306d630415589103ca17c09503080be00002214a652b694509764582018e686642d413988b038a16b08802e40b00000221447c2c614b49a646b2050ec86b02f014988b43b217e08d82d80b600002213e9b2c2148498a46f2048ed06c631015509343da183097034c0c0000022138a52d195089b84842188f286dc2f414908d03a816f08a82f00be000022132ed2b113f894a4511fc8e646902ea143088838c17308582a80ae00002212cf02d215249e448b2138f046b82ed14b88f83b817808882e40c2000022126fc2c814dc9a246f2048ecc6ae2f214608ec3c217f08c03000ba0000221211c2c1948097e4662090eac6962f014c88e839c167083029c09200002211b172d014c09a247020b0ef86ca30514e09083ce18b09783200d8000022115152d5952c9da4892168f646f631a15889483d218809583140b400002210f382c1947c97a46b2078ef06ae30215188fc3ac17b08e82d80b80000221094a2c614a09a446b2080e986882f0145888439c17808702bc0ae000022103682be946495a4571fe0e8c6762e114088a43a417408a02c80b00000220fd752ca94ec9b846f2058e9067c2e014508cc3a617a08c02e80be0000220f7a22ba145097c45e2018ea469c2f414508a039e17508e02fc0be0000220f1a92c894e89ba47720d8ee86c6308153891c3d018209303300ce0000220ebcf2c094a49a047220a0ed86b42fb14f08f43c618509103000b40000220e5ba2d595649e649321c0f206be300154091c3e619009483080ba0000220dfb12d695409cc48c2138f306d030a15408fc3b218709482e40ca0000220d9dc2be14809864672078eec6b830315109103b017408982e40b60000220d3fa2c394989a247b2088efc6c230015089243c618808b82c80ac0000220ce312b2143095644c1f10e246622d613d08cc3b217d08d82f80be0000220c8522c114a098c46e20b8edc6a42f2144889c38c16c08b82ec0c20000220c27c2bf94a098c4702070ed46902ee14b88f839c17008602c40b20000220bc9e2ba14549644561fc0e506982dd13d88c43ae17908d03100c40000220b6b92c594ac99c4702078ed86b42fa14d89103c618208a82e00bc0000220b0ec2b914649784541fa8e5c67e2e1140887038416608a02e40b60000220aaf02d015309e84982168f246ce30714888cc3b017308802e80c80000220a51e2b3944896845f1fe0e706842eb14708ac3ac16a08782cc0b200002209f3f2c194c49c646e20a8ee86b82f414888a43aa17808f03000bc000022099502c894ec9c048a2170f006b430815008f83bc17e08d02e40ae000022093502cc14e09c84872128f486e6315158094c3dc17b08a82e40bc00002208d4c2d195209cc48720c0f046c030315609203d418009583000bc000022087792b6945c97e4642030eb86902ea14c08ec3b017908d830c0b8000022081a22ba147c9864672050e906982fa15188e038e181093830c0ce00002207bee2ab140094e4501fe0e846882ea13f08bc38c17608a02d80c2000022076002c7148497e46e20f8f086c430615589103b217708d02d80ba000022070492a893e494a4431ef0e146582c0133081434c14b074827408e00002206a532cf14c89ae46c2058ec06ac2f014f09103d218c09503200da000022064612cb14d89ba4802118f286b62f714d89043ca18409383140ce00002205e662ce15289de4952180f2c6de30315409043ce192096831c0d4000022058882bd947c9904642050ed46ac2f514988e43a217008b02d00b40000220527c2cd94e89c64882150f286c6307158892c3d817e08c83000c000002204c772d915389da48e2158f446de30e14f08ec3a417408e83100be000022046742ce95049c64852128f286cc2fe14f08e43b017b092830c0b6000))) else (if i < 354 then (if i < 352 then 0x22334222be14d49ae46f20d8eec6c630414d89003c618109202fc0a800002232e4a2c0947096e4642050ea86a82f014688903a017b08a82e80b60000223285f2c994c89ac4722078eb06962e914708a839e17308b832c0d00000223227c2bf149c99e4642040ecc6962ef14808c039616908902e40be00002231ca32c0949c98e4702050eb06a82fa14a89083d818508f02ec0c6000022316f72aa140494643a1f78e2c6622d614488d839e17208882e80be000022311152c2145c97c4531fa8e6067c2e113b887c37c16908582ec0b600002230b412b4944897645c2010e6466e2d813d08a039617408e03180bc000022305682c314ac99e4682068efc6b02f214988d03b617c08a02f80c20000222ffa72b3143896c45c1f90e106482c9138084c37416908782ec0b40000222f9c42c294a499c46c2060ea86aa30014c08a43aa17908e82d00ba0000222f4042b3941c94c43c1f20e206502c9135084037015f08502b40ac0000222ee302b4143c94c4491f78e3466e2db14088ac39417108882e40be0000222e8202d915409de4862170f146d230715089103d818109383140be0000222e2392c314a099446d20b0ecc6942e614488c039a16f08782c40b00000222dc552bd947496444f1fc8e546762e113f887438816e08d02f00aa0000222d6742c214909804682030e5c6882e714108983a217408a02e40b80000222d0882c514ac9ae47720d0ef86b42f714c09003c418909583100c40000222ca9e2ca14c49a246d2068f086ca30e15489203e018c09502f00c20000222c4a12ce94f49dc4832158f146be2fb14e08c439416e08282cc0ba0000222beb92c094849924682080edc6ac2fa15409003ca18609103300d60000222b8dc2c294989a047220a0ec46b62fd14b08e43b617108a830c0b40000222b2e52ca14b89a847220d0ef06c030c15189143a216e08902b80940000222ad0b2bd146c97a45e1fe8e546822e614a08c03aa16e08a82c80c00000222a7092d495489d448d2180f3c6dc30315188fc3d218209103040ca0000222a1342b8947898c46d20b0eec6b22fa14b08c03aa17e08c82e80b400002229b5b2bf94b099a46d2098ed86ba2f814808cc3a416b08682d40b80000222954b2d495249d648c2148f1c6bc2fc14d08cc3aa17508883100d600002228f4c2d295109d048320d0ef86d4309153092c3c417708c829c0aa000022289722be947c98e46b2080ec86ae2f114c08f83bc17b08c030c0b0000022283aa2b4944895c4491fc0e706902e213b088c3a018309403100be00002227dbf2c594d89b847b2118f046c4303153890c3e018d09683180b6000022277d32c414c89b047a20d8ee469c2f814b08bc38a16d08b82f40d2000022271eb2bc140c94043a1ec8de463c2be134883835a15d08082900a600002226bfc2c614ac99446c2030ea469a2ef14c08e83b817c09103080b4000022266182c2949c9a84692028e846982ef14508ac3a017608e03180be0000222603a2c494bc9924602070e7467a2d4141086c38416e08782ec0bc00002225a3c2cc94ec9c84812120f0c6cc30515509243ce17d09403180b60000222543b2d414fc9b447820d8ed86b02f814b88e43bc18609683140ce00002224e592c1148c98c4601fd8e8869a2f214c88ec3be18308b82f40ce0000222488a2c2149c9964682020e9868a2e714208a439e16f08a82f80c8000022242942cd94d899847120a0f206ca308153891c3d018409303200ce00002223cb92ba947096e4672078ee46b82f114b88f43ba17f08e82e80c8000022236d02c594ac9864652038e8467e2e214888d439c17108782e80a4000022230bd2d71560a0049321f0f9070632715e09583f618b09582fc0c200002222b002ab940c92c4401f70e6467a2e5141889839616608502c00a8000022225182c614d09904672010e8467e2e314088d439817208902d40c200002221f292c394ac99046b20b8ef86bc30314c88f83c217408a02c40be000022219522be143c9584521fd0e746942ed14d08f83c018208d82e40b8000022213682c6147c99446c20b0f106be30a15508f83bc189092831c0cc00002220d822c814d899845e1fe8e6c6782e514288a438615e08502980ae0000222079e2c614b099046f20a8ed86aa2ea144089c38816908602cc0b4000022201b32c594a899a47220a8edc6b82f214708b43a618309403140c00000221fbab2d414d89a64772098ec86b82fb14d08c83b017d08c02f80b60000221f5a82d615489f649d21b8f606e8317158890c3ce18d09183340d40000221efc42c714d49b047920c8ecc69c2ee14b08f03c617e08e03080b80000221e9b22d715209d448d2140f2c6d430615409383d2187094830c0d00000221e3c32cd94d09ae4782088ed869c2ec14708f43ba17e091830c0c80000221de0a2af94189664441f10e0064a2d0139887838617108a82e40b80000221d8442bc94689884632030eb46a02eb14608b43a416f08682d40b20000221d2602be947098046b2050ec46ac2fc14c88e03c218608b82dc0ce0000221cc702c794d499c47920b0ee06c630414b08c83aa17408682cc0c40000221c6882c014a89ac47d20b8ef86bc2fd15088fc3ac17808c82f00ae0000221c09f2c714c49a247d2130ef86c02fe14c08c03b617608c02e80ac000 else (if i < 353 then 0x224acb92ca94c898a46e2078ea86a02f514a88c83a818108d82d80ac0000224a6cc2c894b89c84882128f206b42f414a08c439e17208682d00bc0000224a0c62d0951c9dc48c21a0f386da31415609203d018e09583140c200002249ae32c014c49924692058edc6ac2f815288cc39416c08702e40c2000022494f42c494e09b64842190f3c6da309151091c3c617c08f830c0c600002248f182be147497c4612000e846862df13f089039017008702fc0ae000022489492b4143496e4632020eb069e2eb14d891c3ce18008e83000c4000022483842b314589764591fc0e5066e2d013c085038015f08482a80b200002247da72c3148099c4692050ea06c030115108f83ae17708a02ec0ba000022477b72cf151c9da49621f0f7470231015789403d618709502f40c2000022471c72ca94a89924682070eec6aa2f714888d839e16c08582dc0b600002246bb52d315489de49521c0f6c6f232415f09443e018908f02e40be000022465f92b4944898246c2030e8868e2f214588c43ba18409483140b600002245ff32d115089da48a2158f306e030b14f090c3c017d09103080c4000022459e92d494fc9c248320c8ef06ac2f814a88fc3c618109382f00be0000224541a2ba948498e4692028e906982f014808b03aa17e09182f40b600002244e2b2c494a89a847020a8ee069e2f014a08dc3a017408882e80c40000224484b2be946897445c2048ecc6c22f314989103b018a09503480d2000022442652c4949c9a047020e0ec069c2f715189043c418609003000be00002243c752cc14cc9a44722078ecc6b82f314588b43be17f09202cc0b2000022436892ca94bc99c47a2080edc6ae2fd14c88d03a616e08482a00ac000022430c82b0140c96644e1fe0e6c69c2e5146089439817008582c80a400002242ae62c414989924652008e8c6962ef14b08c43a017a08e82d00a80000224251c2af94109544451fb0e806942ec14e08dc3b417c08c02e00c400002241f432bb949099a4732070ebc6a22f414a88f83ce18608d02c80ac0000224195a2c494e09ac4772090ee06ac2fe14c88bc3a816f08682d80d00000224137d2bf949099046c2070ea86bc302150891c3c818009082fc0ce00002240da02c394ac99846c2060ea46942eb14608c03a818108e02f80bc000022407c12c4949898246920a8ee46c02f914e88fc3b018008f83000b4000022401f92bb146497e45b2058eb469a2fb14e89143c217a08e03140c80000223fbfc2d595049e049c21e8f5c70031c15889183be18209583300b20000223f62d2bb946c9804672040e8c6822d814308a839e16c08702b00bc0000223f0442c514bc98e46e2078ef06ae2f914b88d03b017908f03240cc0000223eaab29f136890a4251e28df06622c9134884837816908282a009e0000223e4cd2be145c96e44a1f48e146582d013b887037e16808282b80aa0000223df0a2b0141495a44e1f30e1864a2c3135885838215a07d829809a0000223d91e2c294d49c447a20d8ed86902e414408ac3a616a08402a80ac0000223d32b2c994c499046b2078edc6ae2f814c88e43b418208a02f40b60000223cd6c2af93f092e4421f08e146522d0139087c37a16d08602e40b00000223c7a32b4941094c4551fd8e4c6602d913e087439617008482bc0c40000223c1b32cb94c49aa47a2090ee46ae2ff14e88f83a216c08802d40bc0000223bbe72b593fc9424421ef8df46622d513a086438815708482d80b40000223b6002c894c09aa47420a8efc6be30214f89003dc19809f03640e60000223aff82d6152c9b848020e0f086b82ff14c890c3b818508f02d80ba0000223aa072c794ec9bc47720b8ee46ce30d15709303e818e08e82f80b00000223a4142c914e09c44832150f5c70631915309083c218208d83080b400002239e612ac93f093a4421fa0e686742dd13c889438c15708102cc0b4000022398722ce14d09c048120b8ef86bc2ff15208c83a216908a02f80ae000022392942bf148899846f2088f146c430215289083c618f09503140d200002238cb12c194909864602040e9c68a2e514508d43c617b08a02dc0c4000022386ea2b914509784621fe0e8c68c2df14088b439816e08802dc0a4000022381022c894c89ac47120a8ed46a830014988c43a017808c02ec0b400002237b0b2cf94f89ba47d2128f346d831615a09743da18609603180c8000022375332be14a89924632000eb069e2ff15288b039c17f08c82e80ac00002236f5e2ba145897c4612060ed469c2f114108c03ba17008a02f00b20000223698b2bd14709804672060ea06be30315309483d618f09983540e2000022363892c914dc9b04772058ecc6b230415088f43b617808b83000be00002235da02c694ac9aa47b2118f186b430115108f83ca18108e02d80aa000022357c42c0946497e45c2040ed46aa2fe14f89083da18808e82e80ba000022351ce2ce94e09a44822110ee46d230615889283d618508e83000ca00002234c0b2b214209584471f30e2c66c2dc13b886837e16408182c009a000022346072cf94c09ac47320b0eb46982e914388b43a617b08f83040be000022340072d195189cc4822120f2c6b02fb14c08dc3a217308802cc0bc000022339f82d614fc9b447a20e0edc6a22ef14788bc3b817108b02d40b4000 else 0x22627222c594e49a847220e8f006b82f815089343c218409103100ce000022621712b0941095c44c1f38e306682d713e086c37015207b028409200002261b922bd94509624581f98e706702e5142887c38616108702cc0aa000022615aa2be947498c4642058eb46b82f214a88ac39016d08e02e40b200002260faf2cd14d099046a2060ebc6aa2f714d89283d818a08e831c0d0000022609c22c714a89a04712080ed068c2ee14c88c03aa17608b82e40c0000022603bc2d195109d648320e0f186d22fd14e08f03b217608c82f80cc0000225fdeb2be94a099446e2048ed06b82fd14c88e03ac17408a82d00bc0000225f7ea2cf951c9d04902170f506ea31415809303c618108d82e80c00000225f1fd2c414d099847520d0eec6b030815489103c618109002fc0c20000225ebf22d995349e24922160efc6c42fa15309083bc18809403000c00000225e6272b414289704642020eb06862f414e09143bc17a08d82f00b40000225e05c2b614149644652010e9868e2ee14a08e43a817708d02d00a20000225da762c394b89a646d2040eb46a22fc14c08c839e17208902a80b40000225d4702d915309e049221b0f4c6f631215189083ba18009102ec0b60000225ce7a2cb94e89c64952170f8c6f6311155890c3ba17008c02e40c60000225c8a22be948096e4531fe0e4c66c2dd14688cc3bc17908782e00c20000225c2cf2bc146097c4632068ec86922f815209203bc17708e83000ae0000225bce12c514d09b247f2128f186aa2f614888ac3a617608c83000b60000225b6eb2ce94e099e47820f0f3c6ca31415309043c017f09202ec0bc0000225b0f92c994fc9ae4762070ec069a2f6145089438616c08a02b40b60000225aaff2c814cc9984762090f146be2f914688c03a817b08e82f80bc0000225a5182ca14a899446d2050e886902ea14b88fc3ce18709683440c800002259ef72dc15749fa49a21a0f646ee31615d89303d8184091031c0c2000022599222ba947c98c4622040e946a02ec14a88c03a017908f82d80b4000022593332c614849884622020ed46ac2f314c08cc3aa17b08902e40aa00002258d6a2b494149524491fc0e806862e414208b039e17c09183140da0000225879e2b9946896a4561fc0e346602d313e086436e16608182c00ae000022581a62cb14d49b447d20a8eec6b62fe14488d03c018409583180d000002257bbe2c1948096a45d1fa0e7c6922eb14088b03a017408982dc0c2000022575c72d114e49a04722090ebc6982ec14608d43a016908a02d80b600002256fe72c2147c9784651fd0e8c6782e814488b03ac17308682c80ac00002256a212b5142895e45b1fc8e7c68c2ff14e89283d418709c83340e0000022564232d214ec9a84712080ee86b02f714a08b839c17c09003100bc00002255e512bf94889984722068eb86a22fa14a88ac3a217b08c82ec0b40000225588d2b7942c9624651ff8e7c6842f414f89183c218308d03080c4000022552972ce15089aa47c20f8f086c430c15389143c817d08d82c80b600002254c922d115049ba4822100f186ce30114b09003c818409303240d4000022546a22c714c89984682018e806722d413b088037e16508302f00be000022540a62cf14e89b847e2098e9c6942ec14c88f43d219109703100d400002253aad2ce14fc9aa4852110eec6a02f414d08fc3b818109083340ce000022534b92cc15209d448a2170f286d430a15488f43d218309103380d600002252ebf2c514a89a046d2088ee46c4303153891c3c218a09583340ca000022528d42c794d89ac47720e0f046d030915589203d818009202f00c2000022522f52c094889804641fe8e7468c2e614288983a817d08f02f80b600002251d132c1149c99a4682058eb86a42f014688b439217308a02b00a6000022517102d094cc9a246f2080edc69e2e814208ac3a617408702cc0a20000225112f2c314a099e4682068ea46982fa14908c03a417808c030c0e000002250b2b2d7951c9cc4882118ee46d030114f08e03aa180092830c0be0000225053c2c914ac99a46a2048eac69a2f714e89043b817f08f82f80be0000224ff2e2d99580a0a49f21c0f586e632016109803fc19b0a203680e40000224f9682b6146897445b2010e8468c2f1145888c39c16908982cc0aa0000224f39d2b494609464441f70e4066e2e6141086437416608682b80bc0000224ed782e09588a0e49e2190f4c6e031715e89683e618d09182fc0c00000224e7a22b8947c99246a2058eb46942f314a89143be18909103100b60000224e1c92bb945497a4672018eb867c2db139086838a16508382d40b80000224dc092b3144495a44e1fa0e5067e2ef14808bc3ae17308a82f00b00000224d6562af13ec95244b1fc0ea469c2f815009283c818108e83000ac0000224d0522d415089c848220c0ee46c630d158094c3f619f097031c0d60000224ca862b5946c9804641ff0e7468c2dd144889439c17908c82c40ba0000224c4912cf95009c44722090ed46bc30015589283e218608d02ec0b40000224beac2ba145097e4611fc0e6c6722e814708c43aa17f08d82f00b80000224b8a22d495109ca48920f8ef86ae2ff14d88e43bc18208f02f80ac0000224b2a42c814c49b447e20f8f246c82fc15288f43b417b08b02ec0b8000)) else (if i < 355 then 0x2279fd52bc945c9944652060ed06ba2f914508e03b417c08d03040d4000022799bd2df15589e248c2168f506d430e15689183c818909403340d4000022793cf2c694c49ac47d2098ed86ae2fc15188ec3bc17c08d83000b400002278deb2c694bc9b046c2030eac68c2e8145889839016a08a82c00b2000022788102bd14809864712090ed86b22fc14f08f83b6175087829c0ac000022782422ba947098846720a0ef86b430515409243cc18609303240c600002277c352d715409e048f2178f406e231215789483d8190099033c0d40000227767c2a993e49444471fa0e4466e2db14708b439417208882ac0b8000022770962c514a499a46820a0eb06a02e614208bc3a417408c82c80ae00002276ae42aa93f894a4421ef8df46442cb134886c38016608702d40ac000022764e12d214fc9b848520a8ed46be2f314888a83a417808e03380ca00002275f0a2ba94649784621fd8ea069e2f814a88e83aa17108982f40b8000022759152d015009aa47820a0ed06c4301152091c3d6185098834c0d20000227530e2d214dc9c44872148ef86b82f815209083c818309383080b800002274d4e2b314349664571ff0e906822e213d089c3a417808b02d40b60000227475f2c314b89964642028e906862e614308e43b617608902c80b4000022741b32a694109524441f20e346522d013f889038816608502d40b800002273bb42cc14c89a24732120ee86ae2f114a08c43a618109082e00c8000022735de2bc147497c4612060ef86ba2fb14d88cc3ae16f08882cc0aa000022730362a013789184341eb0e086322b512f883436e15b08602b40b400002272a5d2bd947497845a1fc0e546722e113e88ac39616608302b80a80000227246c2cf15109d448220e8ecc6ae2f914c89043b017a08b83000c000002271e9a2c094a497e4612008e4c6682cd135884837416308382b40ac000022718bd2b914609784642070ea86942ef14c88ec39e17508982fc0c2000022712e02c094b09944742080eb86942f814908e03a818008b82f80cc00002270ce42cb94dc9a04652020e9c6942fa14a08dc39a17408a02e40b4000022707132b594349644501f98e506802e414208cc3a617108c02f00be000022701432ba945897a45d2018e6c6862e113d888c37816708502c00aa0000226fb4e2cd150c9cc47b2090f046b42f514d89003d418808c82f40ae0000226f58d2af940894a44c1fc8e846762da14288b039616e08802bc0a60000226ef962c794ec9ac4752080ec068e2f1146089c39216f08e03280d40000226e9ba2bb948c9764611f80e606742da13c08b03ac17808a02dc0be0000226e3d22c594b498c45e2028e7466c2d914108a039216e08882c00b00000226ddc42d815289d649321b8f606f030e157892c3d618d097833c0ce0000226d7da2c4149899a45e1fd8ea46862f014488b039816f08b82e40ba0000226d2102b3941895a4511f58e486642db14088a039416a08282d40b60000226cc472b4941c9704501fc0e5866a2dc140089c39417608882ec0ba0000226c65b2c694b89a647e20d8f146c230915209343cc18c09082d80bc0000226c0582d315409f049321a0f486e831715689683f219109b03380d60000226ba7b2c314b49904612030eb068a2ea14b88cc3b618008d82f80ba0000226b46d2d9153c9ea49921a8f306da30f156892c3d2180094032c0ca0000226ae722d295309ee4a121b8f406e830815588fc3c817708d02f00c00000226a8a72bc945c9884602018ebc6a02ed14688bc3a617108903000c00000226a2a62cf95209c64702078eac6922ed14908c43a017d08c830c0ca00002269cd62b314389644491f38e0c6582d214108d03aa17708a83040bc0000226970f2b5946896445e2028e786802e713f887837c16708182bc0ae0000226914f2b394249644541f88e5c68a2e914788cc3a017d08a82c00aa00002268b6b2c5149899a4712098ee86ac2fc14608b03a417208a02d40b2000022685702cf95009b248120c0ee86b82fe14e08e83ba17409002fc0b400002267faf2b9145c9644632000e6c6682e314708b439817008582d80ac000022679cd2bd94b09a447420e8f186d02f914b88b839e17508a82e00b6000022673eb2c214749624541fa8e2465c2d5142889c37e16d08702d80ba00002266e1f2b8144096c4481f98e3066a2d813c086837e16e08a02d80ba000022668572b6940494244e1f10e086502c5134886c37016108482980b00000226626b2c894d49b64892178f1c6c830514d88d039e17308782a80b600002265c792cc14ec9cc47c2100f046b030014f89243c417909083140ce0000226569a2bf147c98445a1ff8e646702dd14388b43aa18408f82e40ae000022650c02bd146898c46f2090ea46a22e814788b039417408e82f00ba00002264ada2c094849804661ff0e9469a2ec14a88ec3b617908d02e00b0000022644e62c894e09a447520c0ec86ae2f314f08e439e17008782d00b000002263ed42d695589e248d2180f606dc32216089743f219a09603040cc0000226390d2b2142496a4531f78e9c69c2eb144889c39616608802ec0c2000022633262c0947c9884611fe0e9068c2eb14508d83c8184097832c0c800002262d122d995009b447b20f8ef86b030715389343de18409182f40bc000 else (if i < 356 then 0x22918992c0147498a4601fd0e6466a2df14308b038816a08583000b8000022912c92b514589624531fb0e686862d313e88a83ae17808902c40bc00002290cde2c294709784652048ed46b22fc14e09083c418508d83040c6000022907132bb94449764501fb8e6067c2de13d885037416408482e00b8000022900f62dc1558a0649c21c0f5c6f231115489003be18209283100be0000228faf32d415249bc4802128eec6b02f214c08f039c17408a02e40ac0000228f5452a813e09384401f50e0c6522c8133083035814a07d82a40b00000228ef562cd94bc99c4631ff0e806942e314408ac39a16e08902ec0b80000228e9682ca14ec99046a2068eac67a2e113d089c3a017408f02e80ba0000228e3702d214fc9b847920d0eec6b630015388f03ac17a092030c0b40000228dd902c514c09804621fd8e6867e2de13f887c37a15808902d00aa0000228d7c52b914749704621ff8e9068c2ea14388983aa17708e02dc0c20000228d1942e995b0a044a221b0f546e030b151091c3aa17909083000d00000228cbe22ad14109464421fb0e6467a2df13b886439016908482d80920000228c61e2b8943c95a4581ff0e7c6802d7140888439e16c08202d00b80000228c0692ab93ec9204381ef8dfc6522c213e887839417508c83240ba0000228ba7b2c594d89964652088ee86b62f814d89103d018109102e00b20000228b4962c0948c99c4702088ee46a42f214788e03b818008d03000ca0000228aea42c994c09b247b20c0edc6ae2fc14d89143ce18209302f00b80000228a8c22c114c499846d2040ebc6aa2f715208f03aa17208c02e00c20000228a2e72bf949c9864692030e8c69c2f114488c43a617808e03100cc00002289cf62cb14ac98a4722060e806962f114b88e83ba18408d83040ba0000228971a2c394b898846b2088ed86c02f114888b83a417608a02d80a40000228912d2c014b89ac4732088eb86942fa14788c438c16708a82dc0be00002288b552ba943096a45a2018e9c6a22ea14a08ec3b417d08a82e80b60000228856c2c514a09a647d20c0ec06b82ff14f88f43b617a08e03180ce00002287f772ce14ec9bc47720a8efc6b430815609103da18f09503100c8000022879872c294949a647420a0ee06bc2f614b88e03c218b094030c0be000022873ad2c0947c98a46b1fe8e886902ed14908a43a217c09203080ca00002286d9d2d715149cc4812110f106ca302154092c3ca18409103080b8000022867a42c794d49c44812120f146d230515609603ec19109583440d8000022861b42c894d899e4622088eb069c2ef14608dc39a17708b82d40b400002285bf42ac13fc93444f1ff8ea06a22fb15009303d418809603200b8000022856122bd949c99046c20c0f006b82f514b08c43b617308c02c00c0000022850592ad941c94044a1f80e446742dc14088bc3b017e08e02dc0aa00002284a9c2b0140895244b1fd8e5c66c2d5139086035e16308782e00a2000022844c22be14789844612000e606922e3146889c39017708482dc0c000002283ecd2cd14e89b64742120f446ea31515989483d818609403140b0000022838df2c694e89b647a20d0ed46962f314d08cc3ba17f09202f40ca000022833102b8946495a44f1f48e306562c713a889038e16a084829c0b600002282d032d615349ce4862148f546d830015609103ca18b09483180b8000022826ef2db95349d849121b0f486de30315389143c017d08b02e00b00000228210a2c594c89a64742088ecc6a82fa15708fc3cc18308e83140d000002281afe2d495309ec48f2198f3c6e631c15b09583e818f09103200d0000022815272be946896a4531fb8e5c67c2e913f087c38216408182a00b800002280f422be948899a4692050ed06a62f8152891c3bc17e08a82c40b2000022809682b8143897a4571fc8e3c6622d913c884837216c08482c80b0000022803822c294889844662088eec6b62f915008fc3a816d09083040b80000227fd992cc14cc9ac47c20d0ed86b22f014a089c38216a08482c00ba0000227f7b42c594b899c46b2080ee06b830215089143b417f08882d80bc0000227f1d92c3949c98045e1f80e4c68c2ea14808c03b017f08f82f40c20000227ec012bb94889964631fe0e8c67a2e714688a839217809382e80b40000227e6372b6142095a45b2018e5c6822e714608a439a17108a82e00a20000227e06e2b894709724592050ea069a2ef14588ac3a617808e02e00ac0000227da862ca94f09c04842158f3c6dc31315a899440c19e09d835c0d40000227d4b32c014709804682010e9c6942ef150890c3c017308b82c00a20000227ceb52ce94d09a246f2088eb06a62ee14788c03a217308e03080be0000227c91a29a93749084281e88dd863c2ce136886438215c08082b40b00000227c31c2ce150c9c84892170f286e230c157093c3d618208f83100ba0000227bd422c814f09ac46f2098ed068c2f614d88f03b218409283640d80000227b7732b9146c9724561f90e386602d2135883037015d08182c00b00000227b1912b9943c97645c1fe0eb46922f114788c038616c08202a00bc0000227ab982cc95049e04902138f306ca30014b89003c019409803380e00000227a5b72c2948c97c46b2098ebc6902f114888d43b818708d82f80ce000 else 0x2292a310000000000000000000000030f15689583dc18a08e82d00b6000022924662bb94549584511f50e346662d613c087c38c16c08702f40c200002291e712c914d09aa4782130f106cc2fe14c88dc3ba18309182ec0d0000)))))))))

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



private theorem b351498 : covered 351498 351587 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351587 : covered 351587 351676 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351676 : covered 351676 351765 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351765 : covered 351765 351854 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351854 : covered 351854 351943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b351943 : covered 351943 352032 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352032 : covered 352032 352121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352121 : covered 352121 352210 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352210 : covered 352210 352299 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352299 : covered 352299 352388 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352388 : covered 352388 352477 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352477 : covered 352477 352566 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352566 : covered 352566 352655 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352655 : covered 352655 352744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352744 : covered 352744 352833 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352833 : covered 352833 352922 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352922 : covered 352922 353011 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353011 : covered 353011 353100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353100 : covered 353100 353190 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353190 : covered 353190 353279 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353279 : covered 353279 353368 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353368 : covered 353368 353457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353457 : covered 353457 353546 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353546 : covered 353546 353635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353635 : covered 353635 353724 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353724 : covered 353724 353813 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353813 : covered 353813 353902 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353902 : covered 353902 353991 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b353991 : covered 353991 354080 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354080 : covered 354080 354169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354169 : covered 354169 354258 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354258 : covered 354258 354347 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354347 : covered 354347 354436 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354436 : covered 354436 354525 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354525 : covered 354525 354614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354614 : covered 354614 354703 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354703 : covered 354703 354792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354792 : covered 354792 354881 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354881 : covered 354881 354970 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b354970 : covered 354970 355059 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355059 : covered 355059 355148 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355148 : covered 355148 355237 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355237 : covered 355237 355326 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355326 : covered 355326 355415 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355415 : covered 355415 355504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355504 : covered 355504 355593 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355593 : covered 355593 355682 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355682 : covered 355682 355771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355771 : covered 355771 355860 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355860 : covered 355860 355949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b355949 : covered 355949 356038 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356038 : covered 356038 356127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356127 : covered 356127 356216 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356216 : covered 356216 356305 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356305 : covered 356305 356394 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356394 : covered 356394 356483 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356483 : covered 356483 356572 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356572 : covered 356572 356661 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356661 : covered 356661 356750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356750 : covered 356750 356839 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356839 : covered 356839 356928 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b356928 : covered 356928 357017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357017 : covered 357017 357106 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357106 : covered 357106 357195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357195 : covered 357195 357284 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357284 : covered 357284 357373 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357373 : covered 357373 357462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357462 : covered 357462 357551 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357551 : covered 357551 357640 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357640 : covered 357640 357729 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357729 : covered 357729 357818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357818 : covered 357818 357907 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357907 : covered 357907 357996 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b357996 : covered 357996 358085 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358085 : covered 358085 358174 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358174 : covered 358174 358263 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358263 : covered 358263 358352 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358352 : covered 358352 358441 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358441 : covered 358441 358530 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358530 : covered 358530 358619 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358619 : covered 358619 358708 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358708 : covered 358708 358797 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358797 : covered 358797 358887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358887 : covered 358887 358976 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b358976 : covered 358976 359065 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359065 : covered 359065 359154 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359154 : covered 359154 359243 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359243 : covered 359243 359332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359332 : covered 359332 359421 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359421 : covered 359421 359510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359510 : covered 359510 359599 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359599 : covered 359599 359688 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359688 : covered 359688 359777 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359777 : covered 359777 359866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359866 : covered 359866 359955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b359955 : covered 359955 360044 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360044 : covered 360044 360133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360133 : covered 360133 360222 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360222 : covered 360222 360311 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360311 : covered 360311 360400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360400 : covered 360400 360489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360489 : covered 360489 360578 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360578 : covered 360578 360667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360667 : covered 360667 360756 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360756 : covered 360756 360845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360845 : covered 360845 360934 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b360934 : covered 360934 361023 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361023 : covered 361023 361112 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361112 : covered 361112 361201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361201 : covered 361201 361290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361290 : covered 361290 361379 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361379 : covered 361379 361468 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361468 : covered 361468 361557 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361557 : covered 361557 361646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361646 : covered 361646 361735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361735 : covered 361735 361824 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361824 : covered 361824 361913 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b361913 : covered 361913 362002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362002 : covered 362002 362091 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362091 : covered 362091 362180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362180 : covered 362180 362269 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362269 : covered 362269 362358 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362358 : covered 362358 362447 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362447 : covered 362447 362536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362536 : covered 362536 362625 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362625 : covered 362625 362714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362714 : covered 362714 362803 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362803 : covered 362803 362892 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362892 : covered 362892 362981 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b362981 : covered 362981 363070 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363070 : covered 363070 363159 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363159 : covered 363159 363248 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363248 : covered 363248 363337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363337 : covered 363337 363426 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363426 : covered 363426 363515 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363515 : covered 363515 363604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363604 : covered 363604 363693 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363693 : covered 363693 363782 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363782 : covered 363782 363871 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363871 : covered 363871 363960 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b363960 : covered 363960 364049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364049 : covered 364049 364138 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364138 : covered 364138 364227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364227 : covered 364227 364316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364316 : covered 364316 364405 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364405 : covered 364405 364494 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b364494 : covered 364494 364584 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 351498 364584 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b351498 b351587) (joinCoverage b351676 b351765)) (joinCoverage (joinCoverage b351854 b351943) (joinCoverage b352032 (joinCoverage b352121 b352210)))) (joinCoverage (joinCoverage (joinCoverage b352299 b352388) (joinCoverage b352477 b352566)) (joinCoverage (joinCoverage b352655 b352744) (joinCoverage b352833 (joinCoverage b352922 b353011))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b353100 b353190) (joinCoverage b353279 b353368)) (joinCoverage (joinCoverage b353457 b353546) (joinCoverage b353635 (joinCoverage b353724 b353813)))) (joinCoverage (joinCoverage (joinCoverage b353902 b353991) (joinCoverage b354080 b354169)) (joinCoverage (joinCoverage b354258 b354347) (joinCoverage b354436 (joinCoverage b354525 b354614)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b354703 b354792) (joinCoverage b354881 b354970)) (joinCoverage (joinCoverage b355059 b355148) (joinCoverage b355237 (joinCoverage b355326 b355415)))) (joinCoverage (joinCoverage (joinCoverage b355504 b355593) (joinCoverage b355682 b355771)) (joinCoverage (joinCoverage b355860 b355949) (joinCoverage b356038 (joinCoverage b356127 b356216))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b356305 b356394) (joinCoverage b356483 b356572)) (joinCoverage (joinCoverage b356661 b356750) (joinCoverage b356839 (joinCoverage b356928 b357017)))) (joinCoverage (joinCoverage (joinCoverage b357106 b357195) (joinCoverage b357284 (joinCoverage b357373 b357462))) (joinCoverage (joinCoverage b357551 b357640) (joinCoverage b357729 (joinCoverage b357818 b357907))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b357996 b358085) (joinCoverage b358174 b358263)) (joinCoverage (joinCoverage b358352 b358441) (joinCoverage b358530 (joinCoverage b358619 b358708)))) (joinCoverage (joinCoverage (joinCoverage b358797 b358887) (joinCoverage b358976 b359065)) (joinCoverage (joinCoverage b359154 b359243) (joinCoverage b359332 (joinCoverage b359421 b359510))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b359599 b359688) (joinCoverage b359777 b359866)) (joinCoverage (joinCoverage b359955 b360044) (joinCoverage b360133 (joinCoverage b360222 b360311)))) (joinCoverage (joinCoverage (joinCoverage b360400 b360489) (joinCoverage b360578 (joinCoverage b360667 b360756))) (joinCoverage (joinCoverage b360845 b360934) (joinCoverage b361023 (joinCoverage b361112 b361201)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b361290 b361379) (joinCoverage b361468 b361557)) (joinCoverage (joinCoverage b361646 b361735) (joinCoverage b361824 (joinCoverage b361913 b362002)))) (joinCoverage (joinCoverage (joinCoverage b362091 b362180) (joinCoverage b362269 b362358)) (joinCoverage (joinCoverage b362447 b362536) (joinCoverage b362625 (joinCoverage b362714 b362803))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b362892 b362981) (joinCoverage b363070 b363159)) (joinCoverage (joinCoverage b363248 b363337) (joinCoverage b363426 (joinCoverage b363515 b363604)))) (joinCoverage (joinCoverage (joinCoverage b363693 b363782) (joinCoverage b363871 (joinCoverage b363960 b364049))) (joinCoverage (joinCoverage b364138 b364227) (joinCoverage b364316 (joinCoverage b364405 b364494))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 351498 ≤ index 675000000/512 := by decide +kernel
private theorem starting_value : fast 675000000=35024348 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 675000000=35024348) (n : ℕ) (low : 675000000≤n) (bound : n≤700000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=675000000
    · rw [first,anchor]
      exact starting_value
    · have past : 675000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤700000000 by omega)
        have within : index n / 512 < 364584 := by omega
        have lower : index 675000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤700000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ675000000To700000000
