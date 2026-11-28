import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ170000000To195000000

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




private def radical : ℕ := 0x1f18099ec342fe792e7862b96107485b61c2f70221da93998b92d3f1b3c20da2d766a6aa963b6dfbd67d45d0c71ad58755090c700f2ce13a53e865132a0c22c61769744343995a76857ec254037d48c7a54e3fa2a0fcb0540adac9dde8e82ad8e8c9e47a877705ef4c3edbe116910a89e2356df15b08cbeda53c8ef5b7c25fc936ab0ccbd4f93bc904c0c555151f8aa6116d22c357b872ef9dcc1f0f7774b25334f7f3ce4f24eba8ff4b1c275dba8166e84b4ddc09872e6118a02a99a0edc96b70d6472c8790e25e06fa5dae0a45073a4bb504d3fc00286a572ae1b43f28221ed49fad555acbabad62a153bc38bc80586d45e51d90bf360aebd0a4544a56f7ab5c466770126444f9f97747c2133b276dd625bb9a8c645668fb1dd73480ef22e910dd8cac42b10a6334ab08e5397ccb5da68c6bbbf5db08116d395fcf9671f837e88a10ec55726aea84cc76be633e239f65323fde0ac43cfa41abe055ca62c009ecce364cb4747ed0d301269aca46d9179bd573d52233101a171ec13fbcd13f6b1b92fba61a5e901baec99c2826b8a073b4707ac7d16dd6b846ff5cc418c413fbc1736aafcccd20df06666991d1e255ec9f8b79ab6d60631f79db340ec79d5948acb57f4629852068064aab32c5dd62c2fea38b6a22dd6d5141972c2cbc5fba47b547cc18b9d6b5bb04186e618fad0895e028046869e0ceedd0dd6e3c1c4845a3c193ce1551a38b6f8b93b3cc25440de2572c8a247c29049d6ea2fd92a89d52bfa2772ad9c2532154285374b6ac63589201b1aed132927bcf85f2f0b033c18451ce441562b99a28165a09d365845cdad4e773bbd6b7743c1f2ca9e7b5dfbe772a86d09b0fb77b297ee36b29f4f53e0af5949a9da97845398e24e3f116934cd5e454477c87cee6ee8f66369f433fcc2597670712c53df94f7f048f6f1498f30cb8c404114d242b92f1dc16ae58047305191d74df8bca4955f72b2c0804f148ac5a68c34e7da338e2eb326c3e1893b6996731dd44075c05d14e28add30cdfb999f0052db596f2f1bb147d4cd3b25dc172d9c97bb77cb4f7eca87efcb3d51c9f762d37159e3a350b639b30fba2e347e0414108affebe40e406f16f0baf75151da215df34dbba07c51904b5f78e2f878dbb3a3aadc96dbd62545eca2e33cfce09e59d8b8ec7967296ac0e0a1c7a6aadc532310361f23edff93cf32225a6ca88ea25aebb48e09eccd42c167a4789f20df29b39859785d8fcd3ac891366da451fc252f2de4dd8fc418c903c2eabb70d54248603621da4addee461d0c62db23bf712464fb8fab3f356d97348942d402decbfe92a8b715f97b923b545c29ea618b1531ec95118215360f7ef5b82f7d5c9ae5be5cd4890c9610d0122be1a370c41280c3164176d0b3f0202fff706a9e23ef90e3f29aeedae15a8fba2ba0425cdf1db5dee477b15e01d88a5e29b25926365bb05d2ceb0e055203685429c94298edb11f5b3833fdf23802ed4c7d782b2d6b22980796bb3ebeb1621159c22ca0e4777ebfa37873c6730e7b251117f3bb347b47ec7dc0767e26332059cda58814ecd793ee0672321d9d69cea77526b6fe31d70a23a49b31c3d83feb56b28185fe2a797b6d3a073f0eab6ee55f4e10853f7d71a5faf81aa903a3d58fae1789e150e63f4fe2468500e4a7b0ab4e18516c1e3edfcd3287b83a0da87da5155f37e1231c58aaa9d89a21b30b9dedaf5fc79673ff827fd3a795f66cba0b7c2a7ee4b289bc1ce65e049fbb550557636e67d18bbb81648a99a18e4bee7251faf876998ceda8c10301cc179adce68639d7bf8a922dae8c9f548363e07adec08070bc90adf8908109c57f93ee26216f4ba135b0df2f0dc9f9355d4e240bff0f7b59ab29181a83c5e08c09425a367e25ff723d99e849cac5c7f3823324029797aaf0030d231da59692693bd41cd595c283c72bfece03c046ee0293991e93490c9012766a98a7c30c7d63e3131781485e378614e1bf1f3466b10f70aa6bb19eb969430f51ec67f21222654c79adda2412d0b4a59aed1451d274bd6ed4087856b1e7562a7d92701e8f369042496e49dddcda1556f14a6fc36caef6445b9f24617c2e062403ef44c19b648c205390f252ae0f6aff0c058a94bd6c9bc829964f77df0a739cbde3842fa7933aff36b532ef951b9ea0068ff8ee0af34bd74305e4d27f363cf6464a0fa39ea823571b73459fc4b70ae483f15c136314f53de6b841919f019b83648e4f0fbd4138ba4325f0988c1a6733fc3b13ee5d8c1b02bda0d03bc4719dd3c9fb6fb39570f1c54f9b73570af43887f37777de981db797dea5abfb4211a3fbea3cb1962de7a688896e1c81a22588073c938ca97e172f8cb8988d6bf0e6482696f04d1ff7795f5f2a7791f509905b89f43ad1ba19778fbbab60f586fa4f3f89968aa1d07510387919bf26dac26a6624ab8dc545111f29b53cae2ad2654b8da126e481f13f85213b5707fdbf2bfed7d631f5f37b300a201576dc2e26d0a32dde28c5ea74330058a4f3a2dcbec5796aae172b7c9cf1ea155ec4cfa67c16c254111a7dfe4a5b8879ad7971619f887582ebae47bd531ebc04b8db82dc85ef3229b8bd0afa6fc9feaf38dbf7de0939d3fc49c38a925a304d77bf3125a0eda6acddf7b34bc63dbcbf6dabf67e4d8a3343ec502c18ae61628fdc44668c337b9cd53685f20c33f8fb262cfba90794c3ce35ae5a1873fdff7ac531660bd4e17e046172b4c94e95e5816386591d0f3e58bd0167f819ce4ba9b3204e1f2fa9f3235861a0c7887c65829f944a23c4dda25d038223bdd4dc2f8f1f9dcc6a6a9c790dbf0d8567c352bbb65dc6e60c30ca6e31438256d53a505f4088b30b1f371f5a1e599ae34020b9e11caf0f6f88a2d6b472bccebacf0c1c374c51d37f8a507fe041cdb39a23d52c07a06a024c60b8f51fede3ca47b9b17de98fb17f6e0c9d493ac509f9f9ef01dd07b2b85f2d012eb356ce42e02ba1d7dd546112add2e3cc22bcfb321f801a156813e4418933f55e1a8d3b06f7c80c12a29d9e25a4516ef777c3586cdd646337d2edfac6695c262157ca7bb927b62710854ed76af70ca757b69811e93c19277d0bc6fca704b21db98475e8b9be08bcaef49362ba811dd5321713ad5c6d3813f7dd1f4de2026f86bb600fb5a5035f59d188b9cd1e1733cc74e844fd0b29ba60f31e676c32cac952ce595201d5996eafb7270055b5f3dc5aab0c93577aaa85465b5bfee48e1333767c2e2464b5984fa00af99ef46fb77b07174e55c44e1a2b2ca2168bae83fe8f9765c7a769672c079f6d861319e8fb32baef7a96b33d6170fb16e81f893d89a55728ca07fd873b6112282e6ef68b2b6a5b8c7456c2eb24b982949af802d7f29f491a3f48db549b79f49a1eef65a9a969053da34db179d63fc731eeabe3d4354e1aed6b93254ff47fa44a31d3956d1fa727c90ab86ba7ed578334006051e09be756c7d690aa924b3c649f2346b3f6b66f9288d829a5a41415108f49b9214c92241328e

private def light (n : ℕ) : Bool :=
  if n≤118 then decide n.Prime else n.gcd 468452584975429065657431236280838416439267950499862031533310318788629800927518416622330123618486343228862579684398745837012213486653229822121742374957258403779058860032000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤13964) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 118 = 468452584975429065657431236280838416439267950499862031533310318788629800927518416622330123618486343228862579684398745837012213486653229822121742374957258403779058860032000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 118 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤13964 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 54 := by unfold smallValid; decide +kernel

private theorem sp54 : smallValid 54 55 := by unfold smallValid; decide +kernel

private theorem sp109 : smallValid 109 54 := by unfold smallValid; decide +kernel

private theorem sp163 : smallValid 163 55 := by unfold smallValid; decide +kernel

private theorem sp218 : smallValid 218 54 := by unfold smallValid; decide +kernel

private theorem sp272 : smallValid 272 55 := by unfold smallValid; decide +kernel

private theorem sp327 : smallValid 327 54 := by unfold smallValid; decide +kernel

private theorem sp381 : smallValid 381 55 := by unfold smallValid; decide +kernel

private theorem sp436 : smallValid 436 54 := by unfold smallValid; decide +kernel

private theorem sp490 : smallValid 490 55 := by unfold smallValid; decide +kernel

private theorem sp545 : smallValid 545 54 := by unfold smallValid; decide +kernel

private theorem sp599 : smallValid 599 55 := by unfold smallValid; decide +kernel

private theorem sp654 : smallValid 654 54 := by unfold smallValid; decide +kernel

private theorem sp708 : smallValid 708 55 := by unfold smallValid; decide +kernel

private theorem sp763 : smallValid 763 54 := by unfold smallValid; decide +kernel

private theorem sp817 : smallValid 817 55 := by unfold smallValid; decide +kernel

private theorem sp872 : smallValid 872 54 := by unfold smallValid; decide +kernel

private theorem sp926 : smallValid 926 55 := by unfold smallValid; decide +kernel

private theorem sp981 : smallValid 981 54 := by unfold smallValid; decide +kernel

private theorem sp1035 : smallValid 1035 55 := by unfold smallValid; decide +kernel

private theorem sp1090 : smallValid 1090 54 := by unfold smallValid; decide +kernel

private theorem sp1144 : smallValid 1144 55 := by unfold smallValid; decide +kernel

private theorem sp1199 : smallValid 1199 54 := by unfold smallValid; decide +kernel

private theorem sp1253 : smallValid 1253 55 := by unfold smallValid; decide +kernel

private theorem sp1308 : smallValid 1308 54 := by unfold smallValid; decide +kernel

private theorem sp1362 : smallValid 1362 55 := by unfold smallValid; decide +kernel

private theorem sp1417 : smallValid 1417 54 := by unfold smallValid; decide +kernel

private theorem sp1471 : smallValid 1471 55 := by unfold smallValid; decide +kernel

private theorem sp1526 : smallValid 1526 54 := by unfold smallValid; decide +kernel

private theorem sp1580 : smallValid 1580 55 := by unfold smallValid; decide +kernel

private theorem sp1635 : smallValid 1635 55 := by unfold smallValid; decide +kernel

private theorem sp1690 : smallValid 1690 55 := by unfold smallValid; decide +kernel

private theorem sp1745 : smallValid 1745 54 := by unfold smallValid; decide +kernel

private theorem sp1799 : smallValid 1799 55 := by unfold smallValid; decide +kernel

private theorem sp1854 : smallValid 1854 54 := by unfold smallValid; decide +kernel

private theorem sp1908 : smallValid 1908 55 := by unfold smallValid; decide +kernel

private theorem sp1963 : smallValid 1963 54 := by unfold smallValid; decide +kernel

private theorem sp2017 : smallValid 2017 55 := by unfold smallValid; decide +kernel

private theorem sp2072 : smallValid 2072 54 := by unfold smallValid; decide +kernel

private theorem sp2126 : smallValid 2126 55 := by unfold smallValid; decide +kernel

private theorem sp2181 : smallValid 2181 54 := by unfold smallValid; decide +kernel

private theorem sp2235 : smallValid 2235 55 := by unfold smallValid; decide +kernel

private theorem sp2290 : smallValid 2290 54 := by unfold smallValid; decide +kernel

private theorem sp2344 : smallValid 2344 55 := by unfold smallValid; decide +kernel

private theorem sp2399 : smallValid 2399 54 := by unfold smallValid; decide +kernel

private theorem sp2453 : smallValid 2453 55 := by unfold smallValid; decide +kernel

private theorem sp2508 : smallValid 2508 55 := by unfold smallValid; decide +kernel

private theorem sp2563 : smallValid 2563 55 := by unfold smallValid; decide +kernel

private theorem sp2618 : smallValid 2618 54 := by unfold smallValid; decide +kernel

private theorem sp2672 : smallValid 2672 55 := by unfold smallValid; decide +kernel

private theorem sp2727 : smallValid 2727 54 := by unfold smallValid; decide +kernel

private theorem sp2781 : smallValid 2781 55 := by unfold smallValid; decide +kernel

private theorem sp2836 : smallValid 2836 54 := by unfold smallValid; decide +kernel

private theorem sp2890 : smallValid 2890 55 := by unfold smallValid; decide +kernel

private theorem sp2945 : smallValid 2945 54 := by unfold smallValid; decide +kernel

private theorem sp2999 : smallValid 2999 55 := by unfold smallValid; decide +kernel

private theorem sp3054 : smallValid 3054 54 := by unfold smallValid; decide +kernel

private theorem sp3108 : smallValid 3108 55 := by unfold smallValid; decide +kernel

private theorem sp3163 : smallValid 3163 54 := by unfold smallValid; decide +kernel

private theorem sp3217 : smallValid 3217 55 := by unfold smallValid; decide +kernel

private theorem sp3272 : smallValid 3272 54 := by unfold smallValid; decide +kernel

private theorem sp3326 : smallValid 3326 55 := by unfold smallValid; decide +kernel

private theorem sp3381 : smallValid 3381 55 := by unfold smallValid; decide +kernel

private theorem sp3436 : smallValid 3436 55 := by unfold smallValid; decide +kernel

private theorem sp3491 : smallValid 3491 54 := by unfold smallValid; decide +kernel

private theorem sp3545 : smallValid 3545 55 := by unfold smallValid; decide +kernel

private theorem sp3600 : smallValid 3600 54 := by unfold smallValid; decide +kernel

private theorem sp3654 : smallValid 3654 55 := by unfold smallValid; decide +kernel

private theorem sp3709 : smallValid 3709 54 := by unfold smallValid; decide +kernel

private theorem sp3763 : smallValid 3763 55 := by unfold smallValid; decide +kernel

private theorem sp3818 : smallValid 3818 54 := by unfold smallValid; decide +kernel

private theorem sp3872 : smallValid 3872 55 := by unfold smallValid; decide +kernel

private theorem sp3927 : smallValid 3927 54 := by unfold smallValid; decide +kernel

private theorem sp3981 : smallValid 3981 55 := by unfold smallValid; decide +kernel

private theorem sp4036 : smallValid 4036 54 := by unfold smallValid; decide +kernel

private theorem sp4090 : smallValid 4090 55 := by unfold smallValid; decide +kernel

private theorem sp4145 : smallValid 4145 54 := by unfold smallValid; decide +kernel

private theorem sp4199 : smallValid 4199 55 := by unfold smallValid; decide +kernel

private theorem sp4254 : smallValid 4254 54 := by unfold smallValid; decide +kernel

private theorem sp4308 : smallValid 4308 55 := by unfold smallValid; decide +kernel

private theorem sp4363 : smallValid 4363 54 := by unfold smallValid; decide +kernel

private theorem sp4417 : smallValid 4417 55 := by unfold smallValid; decide +kernel

private theorem sp4472 : smallValid 4472 54 := by unfold smallValid; decide +kernel

private theorem sp4526 : smallValid 4526 55 := by unfold smallValid; decide +kernel

private theorem sp4581 : smallValid 4581 54 := by unfold smallValid; decide +kernel

private theorem sp4635 : smallValid 4635 55 := by unfold smallValid; decide +kernel

private theorem sp4690 : smallValid 4690 54 := by unfold smallValid; decide +kernel

private theorem sp4744 : smallValid 4744 55 := by unfold smallValid; decide +kernel

private theorem sp4799 : smallValid 4799 54 := by unfold smallValid; decide +kernel

private theorem sp4853 : smallValid 4853 55 := by unfold smallValid; decide +kernel

private theorem sp4908 : smallValid 4908 54 := by unfold smallValid; decide +kernel

private theorem sp4962 : smallValid 4962 55 := by unfold smallValid; decide +kernel

private theorem sp5017 : smallValid 5017 54 := by unfold smallValid; decide +kernel

private theorem sp5071 : smallValid 5071 55 := by unfold smallValid; decide +kernel

private theorem sp5126 : smallValid 5126 55 := by unfold smallValid; decide +kernel

private theorem sp5181 : smallValid 5181 55 := by unfold smallValid; decide +kernel

private theorem sp5236 : smallValid 5236 54 := by unfold smallValid; decide +kernel

private theorem sp5290 : smallValid 5290 55 := by unfold smallValid; decide +kernel

private theorem sp5345 : smallValid 5345 54 := by unfold smallValid; decide +kernel

private theorem sp5399 : smallValid 5399 55 := by unfold smallValid; decide +kernel

private theorem sp5454 : smallValid 5454 54 := by unfold smallValid; decide +kernel

private theorem sp5508 : smallValid 5508 55 := by unfold smallValid; decide +kernel

private theorem sp5563 : smallValid 5563 54 := by unfold smallValid; decide +kernel

private theorem sp5617 : smallValid 5617 55 := by unfold smallValid; decide +kernel

private theorem sp5672 : smallValid 5672 54 := by unfold smallValid; decide +kernel

private theorem sp5726 : smallValid 5726 55 := by unfold smallValid; decide +kernel

private theorem sp5781 : smallValid 5781 54 := by unfold smallValid; decide +kernel

private theorem sp5835 : smallValid 5835 55 := by unfold smallValid; decide +kernel

private theorem sp5890 : smallValid 5890 54 := by unfold smallValid; decide +kernel

private theorem sp5944 : smallValid 5944 55 := by unfold smallValid; decide +kernel

private theorem sp5999 : smallValid 5999 55 := by unfold smallValid; decide +kernel

private theorem sp6054 : smallValid 6054 55 := by unfold smallValid; decide +kernel

private theorem sp6109 : smallValid 6109 54 := by unfold smallValid; decide +kernel

private theorem sp6163 : smallValid 6163 55 := by unfold smallValid; decide +kernel

private theorem sp6218 : smallValid 6218 54 := by unfold smallValid; decide +kernel

private theorem sp6272 : smallValid 6272 55 := by unfold smallValid; decide +kernel

private theorem sp6327 : smallValid 6327 54 := by unfold smallValid; decide +kernel

private theorem sp6381 : smallValid 6381 55 := by unfold smallValid; decide +kernel

private theorem sp6436 : smallValid 6436 54 := by unfold smallValid; decide +kernel

private theorem sp6490 : smallValid 6490 55 := by unfold smallValid; decide +kernel

private theorem sp6545 : smallValid 6545 54 := by unfold smallValid; decide +kernel

private theorem sp6599 : smallValid 6599 55 := by unfold smallValid; decide +kernel

private theorem sp6654 : smallValid 6654 54 := by unfold smallValid; decide +kernel

private theorem sp6708 : smallValid 6708 55 := by unfold smallValid; decide +kernel

private theorem sp6763 : smallValid 6763 54 := by unfold smallValid; decide +kernel

private theorem sp6817 : smallValid 6817 55 := by unfold smallValid; decide +kernel

private theorem sp6872 : smallValid 6872 55 := by unfold smallValid; decide +kernel

private theorem sp6927 : smallValid 6927 55 := by unfold smallValid; decide +kernel

private theorem sp6982 : smallValid 6982 54 := by unfold smallValid; decide +kernel

private theorem sp7036 : smallValid 7036 55 := by unfold smallValid; decide +kernel

private theorem sp7091 : smallValid 7091 54 := by unfold smallValid; decide +kernel

private theorem sp7145 : smallValid 7145 55 := by unfold smallValid; decide +kernel

private theorem sp7200 : smallValid 7200 54 := by unfold smallValid; decide +kernel

private theorem sp7254 : smallValid 7254 55 := by unfold smallValid; decide +kernel

private theorem sp7309 : smallValid 7309 54 := by unfold smallValid; decide +kernel

private theorem sp7363 : smallValid 7363 55 := by unfold smallValid; decide +kernel

private theorem sp7418 : smallValid 7418 54 := by unfold smallValid; decide +kernel

private theorem sp7472 : smallValid 7472 55 := by unfold smallValid; decide +kernel

private theorem sp7527 : smallValid 7527 54 := by unfold smallValid; decide +kernel

private theorem sp7581 : smallValid 7581 55 := by unfold smallValid; decide +kernel

private theorem sp7636 : smallValid 7636 54 := by unfold smallValid; decide +kernel

private theorem sp7690 : smallValid 7690 55 := by unfold smallValid; decide +kernel

private theorem sp7745 : smallValid 7745 54 := by unfold smallValid; decide +kernel

private theorem sp7799 : smallValid 7799 55 := by unfold smallValid; decide +kernel

private theorem sp7854 : smallValid 7854 54 := by unfold smallValid; decide +kernel

private theorem sp7908 : smallValid 7908 55 := by unfold smallValid; decide +kernel

private theorem sp7963 : smallValid 7963 54 := by unfold smallValid; decide +kernel

private theorem sp8017 : smallValid 8017 55 := by unfold smallValid; decide +kernel

private theorem sp8072 : smallValid 8072 54 := by unfold smallValid; decide +kernel

private theorem sp8126 : smallValid 8126 55 := by unfold smallValid; decide +kernel

private theorem sp8181 : smallValid 8181 54 := by unfold smallValid; decide +kernel

private theorem sp8235 : smallValid 8235 55 := by unfold smallValid; decide +kernel

private theorem sp8290 : smallValid 8290 54 := by unfold smallValid; decide +kernel

private theorem sp8344 : smallValid 8344 55 := by unfold smallValid; decide +kernel

private theorem sp8399 : smallValid 8399 54 := by unfold smallValid; decide +kernel

private theorem sp8453 : smallValid 8453 55 := by unfold smallValid; decide +kernel

private theorem sp8508 : smallValid 8508 54 := by unfold smallValid; decide +kernel

private theorem sp8562 : smallValid 8562 55 := by unfold smallValid; decide +kernel

private theorem sp8617 : smallValid 8617 55 := by unfold smallValid; decide +kernel

private theorem sp8672 : smallValid 8672 55 := by unfold smallValid; decide +kernel

private theorem sp8727 : smallValid 8727 54 := by unfold smallValid; decide +kernel

private theorem sp8781 : smallValid 8781 55 := by unfold smallValid; decide +kernel

private theorem sp8836 : smallValid 8836 54 := by unfold smallValid; decide +kernel

private theorem sp8890 : smallValid 8890 55 := by unfold smallValid; decide +kernel

private theorem sp8945 : smallValid 8945 54 := by unfold smallValid; decide +kernel

private theorem sp8999 : smallValid 8999 55 := by unfold smallValid; decide +kernel

private theorem sp9054 : smallValid 9054 54 := by unfold smallValid; decide +kernel

private theorem sp9108 : smallValid 9108 55 := by unfold smallValid; decide +kernel

private theorem sp9163 : smallValid 9163 54 := by unfold smallValid; decide +kernel

private theorem sp9217 : smallValid 9217 55 := by unfold smallValid; decide +kernel

private theorem sp9272 : smallValid 9272 54 := by unfold smallValid; decide +kernel

private theorem sp9326 : smallValid 9326 55 := by unfold smallValid; decide +kernel

private theorem sp9381 : smallValid 9381 54 := by unfold smallValid; decide +kernel

private theorem sp9435 : smallValid 9435 55 := by unfold smallValid; decide +kernel

private theorem sp9490 : smallValid 9490 55 := by unfold smallValid; decide +kernel

private theorem sp9545 : smallValid 9545 55 := by unfold smallValid; decide +kernel

private theorem sp9600 : smallValid 9600 54 := by unfold smallValid; decide +kernel

private theorem sp9654 : smallValid 9654 55 := by unfold smallValid; decide +kernel

private theorem sp9709 : smallValid 9709 54 := by unfold smallValid; decide +kernel

private theorem sp9763 : smallValid 9763 55 := by unfold smallValid; decide +kernel

private theorem sp9818 : smallValid 9818 54 := by unfold smallValid; decide +kernel

private theorem sp9872 : smallValid 9872 55 := by unfold smallValid; decide +kernel

private theorem sp9927 : smallValid 9927 54 := by unfold smallValid; decide +kernel

private theorem sp9981 : smallValid 9981 55 := by unfold smallValid; decide +kernel

private theorem sp10036 : smallValid 10036 54 := by unfold smallValid; decide +kernel

private theorem sp10090 : smallValid 10090 55 := by unfold smallValid; decide +kernel

private theorem sp10145 : smallValid 10145 54 := by unfold smallValid; decide +kernel

private theorem sp10199 : smallValid 10199 55 := by unfold smallValid; decide +kernel

private theorem sp10254 : smallValid 10254 54 := by unfold smallValid; decide +kernel

private theorem sp10308 : smallValid 10308 55 := by unfold smallValid; decide +kernel

private theorem sp10363 : smallValid 10363 55 := by unfold smallValid; decide +kernel

private theorem sp10418 : smallValid 10418 55 := by unfold smallValid; decide +kernel

private theorem sp10473 : smallValid 10473 54 := by unfold smallValid; decide +kernel

private theorem sp10527 : smallValid 10527 55 := by unfold smallValid; decide +kernel

private theorem sp10582 : smallValid 10582 54 := by unfold smallValid; decide +kernel

private theorem sp10636 : smallValid 10636 55 := by unfold smallValid; decide +kernel

private theorem sp10691 : smallValid 10691 54 := by unfold smallValid; decide +kernel

private theorem sp10745 : smallValid 10745 55 := by unfold smallValid; decide +kernel

private theorem sp10800 : smallValid 10800 54 := by unfold smallValid; decide +kernel

private theorem sp10854 : smallValid 10854 55 := by unfold smallValid; decide +kernel

private theorem sp10909 : smallValid 10909 54 := by unfold smallValid; decide +kernel

private theorem sp10963 : smallValid 10963 55 := by unfold smallValid; decide +kernel

private theorem sp11018 : smallValid 11018 54 := by unfold smallValid; decide +kernel

private theorem sp11072 : smallValid 11072 55 := by unfold smallValid; decide +kernel

private theorem sp11127 : smallValid 11127 54 := by unfold smallValid; decide +kernel

private theorem sp11181 : smallValid 11181 55 := by unfold smallValid; decide +kernel

private theorem sp11236 : smallValid 11236 55 := by unfold smallValid; decide +kernel

private theorem sp11291 : smallValid 11291 55 := by unfold smallValid; decide +kernel

private theorem sp11346 : smallValid 11346 54 := by unfold smallValid; decide +kernel

private theorem sp11400 : smallValid 11400 55 := by unfold smallValid; decide +kernel

private theorem sp11455 : smallValid 11455 54 := by unfold smallValid; decide +kernel

private theorem sp11509 : smallValid 11509 55 := by unfold smallValid; decide +kernel

private theorem sp11564 : smallValid 11564 54 := by unfold smallValid; decide +kernel

private theorem sp11618 : smallValid 11618 55 := by unfold smallValid; decide +kernel

private theorem sp11673 : smallValid 11673 54 := by unfold smallValid; decide +kernel

private theorem sp11727 : smallValid 11727 55 := by unfold smallValid; decide +kernel

private theorem sp11782 : smallValid 11782 54 := by unfold smallValid; decide +kernel

private theorem sp11836 : smallValid 11836 55 := by unfold smallValid; decide +kernel

private theorem sp11891 : smallValid 11891 54 := by unfold smallValid; decide +kernel

private theorem sp11945 : smallValid 11945 55 := by unfold smallValid; decide +kernel

private theorem sp12000 : smallValid 12000 54 := by unfold smallValid; decide +kernel

private theorem sp12054 : smallValid 12054 55 := by unfold smallValid; decide +kernel

private theorem sp12109 : smallValid 12109 55 := by unfold smallValid; decide +kernel

private theorem sp12164 : smallValid 12164 55 := by unfold smallValid; decide +kernel

private theorem sp12219 : smallValid 12219 54 := by unfold smallValid; decide +kernel

private theorem sp12273 : smallValid 12273 55 := by unfold smallValid; decide +kernel

private theorem sp12328 : smallValid 12328 54 := by unfold smallValid; decide +kernel

private theorem sp12382 : smallValid 12382 55 := by unfold smallValid; decide +kernel

private theorem sp12437 : smallValid 12437 54 := by unfold smallValid; decide +kernel

private theorem sp12491 : smallValid 12491 55 := by unfold smallValid; decide +kernel

private theorem sp12546 : smallValid 12546 54 := by unfold smallValid; decide +kernel

private theorem sp12600 : smallValid 12600 55 := by unfold smallValid; decide +kernel

private theorem sp12655 : smallValid 12655 54 := by unfold smallValid; decide +kernel

private theorem sp12709 : smallValid 12709 55 := by unfold smallValid; decide +kernel

private theorem sp12764 : smallValid 12764 54 := by unfold smallValid; decide +kernel

private theorem sp12818 : smallValid 12818 55 := by unfold smallValid; decide +kernel

private theorem sp12873 : smallValid 12873 54 := by unfold smallValid; decide +kernel

private theorem sp12927 : smallValid 12927 55 := by unfold smallValid; decide +kernel

private theorem sp12982 : smallValid 12982 55 := by unfold smallValid; decide +kernel

private theorem sp13037 : smallValid 13037 55 := by unfold smallValid; decide +kernel

private theorem sp13092 : smallValid 13092 54 := by unfold smallValid; decide +kernel

private theorem sp13146 : smallValid 13146 55 := by unfold smallValid; decide +kernel

private theorem sp13201 : smallValid 13201 54 := by unfold smallValid; decide +kernel

private theorem sp13255 : smallValid 13255 55 := by unfold smallValid; decide +kernel

private theorem sp13310 : smallValid 13310 54 := by unfold smallValid; decide +kernel

private theorem sp13364 : smallValid 13364 55 := by unfold smallValid; decide +kernel

private theorem sp13419 : smallValid 13419 54 := by unfold smallValid; decide +kernel

private theorem sp13473 : smallValid 13473 55 := by unfold smallValid; decide +kernel

private theorem sp13528 : smallValid 13528 54 := by unfold smallValid; decide +kernel

private theorem sp13582 : smallValid 13582 55 := by unfold smallValid; decide +kernel

private theorem sp13637 : smallValid 13637 54 := by unfold smallValid; decide +kernel

private theorem sp13691 : smallValid 13691 55 := by unfold smallValid; decide +kernel

private theorem sp13746 : smallValid 13746 54 := by unfold smallValid; decide +kernel

private theorem sp13800 : smallValid 13800 55 := by unfold smallValid; decide +kernel

private theorem sp13855 : smallValid 13855 55 := by unfold smallValid; decide +kernel

private theorem sp13910 : smallValid 13910 55 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤13964) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 13965 := (joinSmall (lo:=0) (a:=6982) (b:=6983) (joinSmall (lo:=0) (a:=3491) (b:=3491) (joinSmall (lo:=0) (a:=1745) (b:=1746) (joinSmall (lo:=0) (a:=872) (b:=873) (joinSmall (lo:=0) (a:=436) (b:=436) (joinSmall (lo:=0) (a:=218) (b:=218) (joinSmall (lo:=0) (a:=109) (b:=109) (joinSmall (lo:=0) (a:=54) (b:=55) sp0 sp54) (joinSmall (lo:=109) (a:=54) (b:=55) sp109 sp163)) (joinSmall (lo:=218) (a:=109) (b:=109) (joinSmall (lo:=218) (a:=54) (b:=55) sp218 sp272) (joinSmall (lo:=327) (a:=54) (b:=55) sp327 sp381))) (joinSmall (lo:=436) (a:=218) (b:=218) (joinSmall (lo:=436) (a:=109) (b:=109) (joinSmall (lo:=436) (a:=54) (b:=55) sp436 sp490) (joinSmall (lo:=545) (a:=54) (b:=55) sp545 sp599)) (joinSmall (lo:=654) (a:=109) (b:=109) (joinSmall (lo:=654) (a:=54) (b:=55) sp654 sp708) (joinSmall (lo:=763) (a:=54) (b:=55) sp763 sp817)))) (joinSmall (lo:=872) (a:=436) (b:=437) (joinSmall (lo:=872) (a:=218) (b:=218) (joinSmall (lo:=872) (a:=109) (b:=109) (joinSmall (lo:=872) (a:=54) (b:=55) sp872 sp926) (joinSmall (lo:=981) (a:=54) (b:=55) sp981 sp1035)) (joinSmall (lo:=1090) (a:=109) (b:=109) (joinSmall (lo:=1090) (a:=54) (b:=55) sp1090 sp1144) (joinSmall (lo:=1199) (a:=54) (b:=55) sp1199 sp1253))) (joinSmall (lo:=1308) (a:=218) (b:=219) (joinSmall (lo:=1308) (a:=109) (b:=109) (joinSmall (lo:=1308) (a:=54) (b:=55) sp1308 sp1362) (joinSmall (lo:=1417) (a:=54) (b:=55) sp1417 sp1471)) (joinSmall (lo:=1526) (a:=109) (b:=110) (joinSmall (lo:=1526) (a:=54) (b:=55) sp1526 sp1580) (joinSmall (lo:=1635) (a:=55) (b:=55) sp1635 sp1690))))) (joinSmall (lo:=1745) (a:=873) (b:=873) (joinSmall (lo:=1745) (a:=436) (b:=437) (joinSmall (lo:=1745) (a:=218) (b:=218) (joinSmall (lo:=1745) (a:=109) (b:=109) (joinSmall (lo:=1745) (a:=54) (b:=55) sp1745 sp1799) (joinSmall (lo:=1854) (a:=54) (b:=55) sp1854 sp1908)) (joinSmall (lo:=1963) (a:=109) (b:=109) (joinSmall (lo:=1963) (a:=54) (b:=55) sp1963 sp2017) (joinSmall (lo:=2072) (a:=54) (b:=55) sp2072 sp2126))) (joinSmall (lo:=2181) (a:=218) (b:=219) (joinSmall (lo:=2181) (a:=109) (b:=109) (joinSmall (lo:=2181) (a:=54) (b:=55) sp2181 sp2235) (joinSmall (lo:=2290) (a:=54) (b:=55) sp2290 sp2344)) (joinSmall (lo:=2399) (a:=109) (b:=110) (joinSmall (lo:=2399) (a:=54) (b:=55) sp2399 sp2453) (joinSmall (lo:=2508) (a:=55) (b:=55) sp2508 sp2563)))) (joinSmall (lo:=2618) (a:=436) (b:=437) (joinSmall (lo:=2618) (a:=218) (b:=218) (joinSmall (lo:=2618) (a:=109) (b:=109) (joinSmall (lo:=2618) (a:=54) (b:=55) sp2618 sp2672) (joinSmall (lo:=2727) (a:=54) (b:=55) sp2727 sp2781)) (joinSmall (lo:=2836) (a:=109) (b:=109) (joinSmall (lo:=2836) (a:=54) (b:=55) sp2836 sp2890) (joinSmall (lo:=2945) (a:=54) (b:=55) sp2945 sp2999))) (joinSmall (lo:=3054) (a:=218) (b:=219) (joinSmall (lo:=3054) (a:=109) (b:=109) (joinSmall (lo:=3054) (a:=54) (b:=55) sp3054 sp3108) (joinSmall (lo:=3163) (a:=54) (b:=55) sp3163 sp3217)) (joinSmall (lo:=3272) (a:=109) (b:=110) (joinSmall (lo:=3272) (a:=54) (b:=55) sp3272 sp3326) (joinSmall (lo:=3381) (a:=55) (b:=55) sp3381 sp3436)))))) (joinSmall (lo:=3491) (a:=1745) (b:=1746) (joinSmall (lo:=3491) (a:=872) (b:=873) (joinSmall (lo:=3491) (a:=436) (b:=436) (joinSmall (lo:=3491) (a:=218) (b:=218) (joinSmall (lo:=3491) (a:=109) (b:=109) (joinSmall (lo:=3491) (a:=54) (b:=55) sp3491 sp3545) (joinSmall (lo:=3600) (a:=54) (b:=55) sp3600 sp3654)) (joinSmall (lo:=3709) (a:=109) (b:=109) (joinSmall (lo:=3709) (a:=54) (b:=55) sp3709 sp3763) (joinSmall (lo:=3818) (a:=54) (b:=55) sp3818 sp3872))) (joinSmall (lo:=3927) (a:=218) (b:=218) (joinSmall (lo:=3927) (a:=109) (b:=109) (joinSmall (lo:=3927) (a:=54) (b:=55) sp3927 sp3981) (joinSmall (lo:=4036) (a:=54) (b:=55) sp4036 sp4090)) (joinSmall (lo:=4145) (a:=109) (b:=109) (joinSmall (lo:=4145) (a:=54) (b:=55) sp4145 sp4199) (joinSmall (lo:=4254) (a:=54) (b:=55) sp4254 sp4308)))) (joinSmall (lo:=4363) (a:=436) (b:=437) (joinSmall (lo:=4363) (a:=218) (b:=218) (joinSmall (lo:=4363) (a:=109) (b:=109) (joinSmall (lo:=4363) (a:=54) (b:=55) sp4363 sp4417) (joinSmall (lo:=4472) (a:=54) (b:=55) sp4472 sp4526)) (joinSmall (lo:=4581) (a:=109) (b:=109) (joinSmall (lo:=4581) (a:=54) (b:=55) sp4581 sp4635) (joinSmall (lo:=4690) (a:=54) (b:=55) sp4690 sp4744))) (joinSmall (lo:=4799) (a:=218) (b:=219) (joinSmall (lo:=4799) (a:=109) (b:=109) (joinSmall (lo:=4799) (a:=54) (b:=55) sp4799 sp4853) (joinSmall (lo:=4908) (a:=54) (b:=55) sp4908 sp4962)) (joinSmall (lo:=5017) (a:=109) (b:=110) (joinSmall (lo:=5017) (a:=54) (b:=55) sp5017 sp5071) (joinSmall (lo:=5126) (a:=55) (b:=55) sp5126 sp5181))))) (joinSmall (lo:=5236) (a:=873) (b:=873) (joinSmall (lo:=5236) (a:=436) (b:=437) (joinSmall (lo:=5236) (a:=218) (b:=218) (joinSmall (lo:=5236) (a:=109) (b:=109) (joinSmall (lo:=5236) (a:=54) (b:=55) sp5236 sp5290) (joinSmall (lo:=5345) (a:=54) (b:=55) sp5345 sp5399)) (joinSmall (lo:=5454) (a:=109) (b:=109) (joinSmall (lo:=5454) (a:=54) (b:=55) sp5454 sp5508) (joinSmall (lo:=5563) (a:=54) (b:=55) sp5563 sp5617))) (joinSmall (lo:=5672) (a:=218) (b:=219) (joinSmall (lo:=5672) (a:=109) (b:=109) (joinSmall (lo:=5672) (a:=54) (b:=55) sp5672 sp5726) (joinSmall (lo:=5781) (a:=54) (b:=55) sp5781 sp5835)) (joinSmall (lo:=5890) (a:=109) (b:=110) (joinSmall (lo:=5890) (a:=54) (b:=55) sp5890 sp5944) (joinSmall (lo:=5999) (a:=55) (b:=55) sp5999 sp6054)))) (joinSmall (lo:=6109) (a:=436) (b:=437) (joinSmall (lo:=6109) (a:=218) (b:=218) (joinSmall (lo:=6109) (a:=109) (b:=109) (joinSmall (lo:=6109) (a:=54) (b:=55) sp6109 sp6163) (joinSmall (lo:=6218) (a:=54) (b:=55) sp6218 sp6272)) (joinSmall (lo:=6327) (a:=109) (b:=109) (joinSmall (lo:=6327) (a:=54) (b:=55) sp6327 sp6381) (joinSmall (lo:=6436) (a:=54) (b:=55) sp6436 sp6490))) (joinSmall (lo:=6545) (a:=218) (b:=219) (joinSmall (lo:=6545) (a:=109) (b:=109) (joinSmall (lo:=6545) (a:=54) (b:=55) sp6545 sp6599) (joinSmall (lo:=6654) (a:=54) (b:=55) sp6654 sp6708)) (joinSmall (lo:=6763) (a:=109) (b:=110) (joinSmall (lo:=6763) (a:=54) (b:=55) sp6763 sp6817) (joinSmall (lo:=6872) (a:=55) (b:=55) sp6872 sp6927))))))) (joinSmall (lo:=6982) (a:=3491) (b:=3492) (joinSmall (lo:=6982) (a:=1745) (b:=1746) (joinSmall (lo:=6982) (a:=872) (b:=873) (joinSmall (lo:=6982) (a:=436) (b:=436) (joinSmall (lo:=6982) (a:=218) (b:=218) (joinSmall (lo:=6982) (a:=109) (b:=109) (joinSmall (lo:=6982) (a:=54) (b:=55) sp6982 sp7036) (joinSmall (lo:=7091) (a:=54) (b:=55) sp7091 sp7145)) (joinSmall (lo:=7200) (a:=109) (b:=109) (joinSmall (lo:=7200) (a:=54) (b:=55) sp7200 sp7254) (joinSmall (lo:=7309) (a:=54) (b:=55) sp7309 sp7363))) (joinSmall (lo:=7418) (a:=218) (b:=218) (joinSmall (lo:=7418) (a:=109) (b:=109) (joinSmall (lo:=7418) (a:=54) (b:=55) sp7418 sp7472) (joinSmall (lo:=7527) (a:=54) (b:=55) sp7527 sp7581)) (joinSmall (lo:=7636) (a:=109) (b:=109) (joinSmall (lo:=7636) (a:=54) (b:=55) sp7636 sp7690) (joinSmall (lo:=7745) (a:=54) (b:=55) sp7745 sp7799)))) (joinSmall (lo:=7854) (a:=436) (b:=437) (joinSmall (lo:=7854) (a:=218) (b:=218) (joinSmall (lo:=7854) (a:=109) (b:=109) (joinSmall (lo:=7854) (a:=54) (b:=55) sp7854 sp7908) (joinSmall (lo:=7963) (a:=54) (b:=55) sp7963 sp8017)) (joinSmall (lo:=8072) (a:=109) (b:=109) (joinSmall (lo:=8072) (a:=54) (b:=55) sp8072 sp8126) (joinSmall (lo:=8181) (a:=54) (b:=55) sp8181 sp8235))) (joinSmall (lo:=8290) (a:=218) (b:=219) (joinSmall (lo:=8290) (a:=109) (b:=109) (joinSmall (lo:=8290) (a:=54) (b:=55) sp8290 sp8344) (joinSmall (lo:=8399) (a:=54) (b:=55) sp8399 sp8453)) (joinSmall (lo:=8508) (a:=109) (b:=110) (joinSmall (lo:=8508) (a:=54) (b:=55) sp8508 sp8562) (joinSmall (lo:=8617) (a:=55) (b:=55) sp8617 sp8672))))) (joinSmall (lo:=8727) (a:=873) (b:=873) (joinSmall (lo:=8727) (a:=436) (b:=437) (joinSmall (lo:=8727) (a:=218) (b:=218) (joinSmall (lo:=8727) (a:=109) (b:=109) (joinSmall (lo:=8727) (a:=54) (b:=55) sp8727 sp8781) (joinSmall (lo:=8836) (a:=54) (b:=55) sp8836 sp8890)) (joinSmall (lo:=8945) (a:=109) (b:=109) (joinSmall (lo:=8945) (a:=54) (b:=55) sp8945 sp8999) (joinSmall (lo:=9054) (a:=54) (b:=55) sp9054 sp9108))) (joinSmall (lo:=9163) (a:=218) (b:=219) (joinSmall (lo:=9163) (a:=109) (b:=109) (joinSmall (lo:=9163) (a:=54) (b:=55) sp9163 sp9217) (joinSmall (lo:=9272) (a:=54) (b:=55) sp9272 sp9326)) (joinSmall (lo:=9381) (a:=109) (b:=110) (joinSmall (lo:=9381) (a:=54) (b:=55) sp9381 sp9435) (joinSmall (lo:=9490) (a:=55) (b:=55) sp9490 sp9545)))) (joinSmall (lo:=9600) (a:=436) (b:=437) (joinSmall (lo:=9600) (a:=218) (b:=218) (joinSmall (lo:=9600) (a:=109) (b:=109) (joinSmall (lo:=9600) (a:=54) (b:=55) sp9600 sp9654) (joinSmall (lo:=9709) (a:=54) (b:=55) sp9709 sp9763)) (joinSmall (lo:=9818) (a:=109) (b:=109) (joinSmall (lo:=9818) (a:=54) (b:=55) sp9818 sp9872) (joinSmall (lo:=9927) (a:=54) (b:=55) sp9927 sp9981))) (joinSmall (lo:=10036) (a:=218) (b:=219) (joinSmall (lo:=10036) (a:=109) (b:=109) (joinSmall (lo:=10036) (a:=54) (b:=55) sp10036 sp10090) (joinSmall (lo:=10145) (a:=54) (b:=55) sp10145 sp10199)) (joinSmall (lo:=10254) (a:=109) (b:=110) (joinSmall (lo:=10254) (a:=54) (b:=55) sp10254 sp10308) (joinSmall (lo:=10363) (a:=55) (b:=55) sp10363 sp10418)))))) (joinSmall (lo:=10473) (a:=1746) (b:=1746) (joinSmall (lo:=10473) (a:=873) (b:=873) (joinSmall (lo:=10473) (a:=436) (b:=437) (joinSmall (lo:=10473) (a:=218) (b:=218) (joinSmall (lo:=10473) (a:=109) (b:=109) (joinSmall (lo:=10473) (a:=54) (b:=55) sp10473 sp10527) (joinSmall (lo:=10582) (a:=54) (b:=55) sp10582 sp10636)) (joinSmall (lo:=10691) (a:=109) (b:=109) (joinSmall (lo:=10691) (a:=54) (b:=55) sp10691 sp10745) (joinSmall (lo:=10800) (a:=54) (b:=55) sp10800 sp10854))) (joinSmall (lo:=10909) (a:=218) (b:=219) (joinSmall (lo:=10909) (a:=109) (b:=109) (joinSmall (lo:=10909) (a:=54) (b:=55) sp10909 sp10963) (joinSmall (lo:=11018) (a:=54) (b:=55) sp11018 sp11072)) (joinSmall (lo:=11127) (a:=109) (b:=110) (joinSmall (lo:=11127) (a:=54) (b:=55) sp11127 sp11181) (joinSmall (lo:=11236) (a:=55) (b:=55) sp11236 sp11291)))) (joinSmall (lo:=11346) (a:=436) (b:=437) (joinSmall (lo:=11346) (a:=218) (b:=218) (joinSmall (lo:=11346) (a:=109) (b:=109) (joinSmall (lo:=11346) (a:=54) (b:=55) sp11346 sp11400) (joinSmall (lo:=11455) (a:=54) (b:=55) sp11455 sp11509)) (joinSmall (lo:=11564) (a:=109) (b:=109) (joinSmall (lo:=11564) (a:=54) (b:=55) sp11564 sp11618) (joinSmall (lo:=11673) (a:=54) (b:=55) sp11673 sp11727))) (joinSmall (lo:=11782) (a:=218) (b:=219) (joinSmall (lo:=11782) (a:=109) (b:=109) (joinSmall (lo:=11782) (a:=54) (b:=55) sp11782 sp11836) (joinSmall (lo:=11891) (a:=54) (b:=55) sp11891 sp11945)) (joinSmall (lo:=12000) (a:=109) (b:=110) (joinSmall (lo:=12000) (a:=54) (b:=55) sp12000 sp12054) (joinSmall (lo:=12109) (a:=55) (b:=55) sp12109 sp12164))))) (joinSmall (lo:=12219) (a:=873) (b:=873) (joinSmall (lo:=12219) (a:=436) (b:=437) (joinSmall (lo:=12219) (a:=218) (b:=218) (joinSmall (lo:=12219) (a:=109) (b:=109) (joinSmall (lo:=12219) (a:=54) (b:=55) sp12219 sp12273) (joinSmall (lo:=12328) (a:=54) (b:=55) sp12328 sp12382)) (joinSmall (lo:=12437) (a:=109) (b:=109) (joinSmall (lo:=12437) (a:=54) (b:=55) sp12437 sp12491) (joinSmall (lo:=12546) (a:=54) (b:=55) sp12546 sp12600))) (joinSmall (lo:=12655) (a:=218) (b:=219) (joinSmall (lo:=12655) (a:=109) (b:=109) (joinSmall (lo:=12655) (a:=54) (b:=55) sp12655 sp12709) (joinSmall (lo:=12764) (a:=54) (b:=55) sp12764 sp12818)) (joinSmall (lo:=12873) (a:=109) (b:=110) (joinSmall (lo:=12873) (a:=54) (b:=55) sp12873 sp12927) (joinSmall (lo:=12982) (a:=55) (b:=55) sp12982 sp13037)))) (joinSmall (lo:=13092) (a:=436) (b:=437) (joinSmall (lo:=13092) (a:=218) (b:=218) (joinSmall (lo:=13092) (a:=109) (b:=109) (joinSmall (lo:=13092) (a:=54) (b:=55) sp13092 sp13146) (joinSmall (lo:=13201) (a:=54) (b:=55) sp13201 sp13255)) (joinSmall (lo:=13310) (a:=109) (b:=109) (joinSmall (lo:=13310) (a:=54) (b:=55) sp13310 sp13364) (joinSmall (lo:=13419) (a:=54) (b:=55) sp13419 sp13473))) (joinSmall (lo:=13528) (a:=218) (b:=219) (joinSmall (lo:=13528) (a:=109) (b:=109) (joinSmall (lo:=13528) (a:=54) (b:=55) sp13528 sp13582) (joinSmall (lo:=13637) (a:=54) (b:=55) sp13637 sp13691)) (joinSmall (lo:=13746) (a:=109) (b:=110) (joinSmall (lo:=13746) (a:=54) (b:=55) sp13746 sp13800) (joinSmall (lo:=13855) (a:=55) (b:=55) sp13855 sp13910))))))))
  have good : (List.range 13965).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 195000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 13964 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 13964 := by
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


private def packet (i : ℕ) : ℕ := (if i < 50 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 10 then 0 else (if i < 11 then 0 else 0)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0 else (if i < 14 then 0 else 0)) else (if i < 16 then 0 else (if i < 17 then 0 else 0))) else (if i < 21 then (if i < 19 then 0 else (if i < 20 then 0 else 0)) else (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else 0))))) else (if i < 37 then (if i < 31 then (if i < 28 then (if i < 26 then 0 else (if i < 27 then 0 else 0)) else (if i < 29 then 0 else (if i < 30 then 0 else 0))) else (if i < 34 then (if i < 32 then 0 else (if i < 33 then 0 else 0)) else (if i < 35 then 0 else (if i < 36 then 0 else 0)))) else (if i < 43 then (if i < 40 then (if i < 38 then 0 else (if i < 39 then 0 else 0)) else (if i < 41 then 0 else (if i < 42 then 0 else 0))) else (if i < 46 then (if i < 44 then 0 else (if i < 45 then 0 else 0)) else (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else 0)))))) else (if i < 75 then (if i < 62 then (if i < 56 then (if i < 53 then (if i < 51 then 0 else (if i < 52 then 0 else 0)) else (if i < 54 then 0 else (if i < 55 then 0 else 0))) else (if i < 59 then (if i < 57 then 0 else (if i < 58 then 0 else 0)) else (if i < 60 then 0 else (if i < 61 then 0 else 0)))) else (if i < 68 then (if i < 65 then (if i < 63 then 0 else (if i < 64 then 0 else 0)) else (if i < 66 then 0 else (if i < 67 then 0 else 0))) else (if i < 71 then (if i < 69 then 0 else (if i < 70 then 0 else 0)) else (if i < 73 then (if i < 72 then 0 else 0) else (if i < 74 then 0 else 0))))) else (if i < 87 then (if i < 81 then (if i < 78 then (if i < 76 then 0 else (if i < 77 then 0 else 0)) else (if i < 79 then 0 else (if i < 80 then 0 else 0))) else (if i < 84 then (if i < 82 then 0 else (if i < 83 then 0 else 0)) else (if i < 85 then 0 else (if i < 86 then 0 else 0x91d3722f215f0a2a4b92278fac70e32115b893c3e018d08f83180ce00091cceb30f96d8a844d92348fd872632a15c894c3d818409583040c200091c6ae2e915c4a284a621a8f746ea31f16109403c219009102fc0c600091c02f31016e0aba4e9244907075a34c17509d440a1a40a1037c0e600091b9e42f295fca364b92328fc472832516189683ec18709883080a600091b3a32ee161ca3c4c922f100473032916389783fe19e09e833c0d000091ad1d31016b0a864d523a906c76a34f17489b040019709c03340ce00091a6dc2ed15bca0a49621b8f606fe31d15a89603e618f09502f80ca00091a0892fb1624a4e4c122f8ff474634117089d441a19e0a083540d2000919a562e715b0a1c49921c0f486d42fd14d88dc3aa17f09303200c00009193f62fb1608a384bb22d8fc871a32815d894c3f219909b83440d8000918d9a2f51648a5a4cf230101072032616089743de18108c02ec0d400091877d2d715209c448120f8efc6c230115109083dc18809103000be00091811b2ff166ca624be2330fc071432e16289803ea18c09883340d0000917ace2f815e0a2e4b62298f7c6fc31215a893c3ec19409603240be0009174772fb164ca604c82308ff473e33b16b899840a19a09c03680dc000916e2e2f89648a2e4ae2250fb071632e165099040c1a009883280ce0009167db2f89608a404be22b8fb871a32315f09403d018809082f80b80009161932f29624a424be22e0fd471c32416109503d018609003140b8000915b4a2f49624a4e4bd22a8fc871a32215a09583dc18f09503100b40009154f82fb1640a4a4c42318fd472032e15e89443e618c09382e40b8000914ea62f81640a6c4bd22b8fe0732331160896c3ee18909583080cc000914835309969ca8e4dd23a105874434516e89d44201a909e03540e00009142042ec15e4a284b822a0fc471032115b09583e819309783440ca000913bac2f81620a4e4bd22b0fd472832b162898440619e09d83500ce0009135442fc963ca424b922f0fe472e32e161099840619509703300ca000912f062f01600a384bf2300fd874033e16509983fe19009402fc0aa0009128c92e515b0a1e49f21d8f7c6fe31815809243bc17308902fc0b600091222e318170cace501243105c75a34716e09e84241a50a103680d6000911bd92fb1630a4e4c022f8fe872e32c161094c3ce18709603340c00009115793001680a784d4239904075434416a89cc40419b09783140ce000910f08307167ca8e4e823c904475e33e16509883da187092831c0c00009108ab2f29608a304aa2228f806fa31215909383e4188094031c0b000091024a2fc1668a6a4d1234901474432f16409683ea19809783240c400090fbe42fb9670a724cb2300fe472432a16889983ee195097031c0d200090f5c72da1584a144a62248f906fc31915809183c017f09383100d200090ef7d2ee15f4a324af2270fa870a31e15d897440619909583300c600090e9153059670a844d623b904875234b17489e44181ae09e035c0e000090e2da2ec95c0a244b12258f986fe31a15989343de17b09102e00b800090dc4331116d8a9e4eb245907877435516f89d841a1a50a483600de00090d6112eb15d4a204b32280f706f831015689383ee18609383140be00090cfc92f49614a404cc2328ff073233416989d040219409d83680ce00090c9603021678a6c4c72358fd472232716009743ee18e09703100c600090c3272e4957ca064a421e8f7c6e630815589243ce17908a02e00b200090bce32f195d4a1e4b02280fcc72e32915f89843f018a09903240ce00090b6962f99654a724da23f102476034c1708a0441c19e09603000ba00090b04b2f81630a604b722b8fec72432916489983fe1a309e835c0cc00090a9fd2f2961ca524b722b0fa071431d164099c3fe1a409703300d000090a394300163ca604bc22c8fe472632116289843f018f094831c0ca000909d2a2ff9688a724d523a103073a32516109343d619309b83300d40009096cc2fc1648a5c4d323a102473c33816e09b83f619b09b03400be0009090802f115d8a244b12248fa86fa31715c09643c817808802e80a8000908a342f91624a444bd22d8fbc73833216509803ec19409883440d20009083b330a16a8a864e023f107c76e34f16c8a044321b20a583880de000907d3330c16c4a904e023a107077c3521790a084221ab09d03580d80009076d42f89624a504c32268f886f831515909283be18509803100be00090707f2f71618a444c922d0fa470431c15f89403ea18f09203200c0000906a0d3091680a7c4d82368ff4732329161097840c19f09b83300ce00090639830896aca884d5233900874033916b09803fa19a09b03180c4000905d602ea95c0a2c4b322b0fe072232f16409843e818a09003240c800090572f2e4957c9e24a32298fd071632816209a0402193098031c0c60009050c72f6162ca5c4b62268fac71a33116209a040819a09983400c8000904a7f2f415eca3e4c522b8fb0722326160897c40819409a03280d60009044153019690a7c4df23a101074833616d09c840219a09783400c2000)))) else (if i < 93 then (if i < 90 then (if i < 88 then 0x9368873061684a624c42300fe472a32d15e09603ae17608e03280c000093622c2fa1644a444bf22d0fb072233916789cc40419e099832c0c4000935bf02f015fca444c122f100073c32d164898c3f219509a833c0dc0009355b72e895cca1c4a921e0f706f431215d896c3fe18f09703140c6000934f622fb164ca544c722f101874633416689a44101a509983580ca0009349102f595f8a3a4b22238f7c6da31b15a89303f018f09983240c00009342c42f8160ca4e4c32308ff072e33116289a041019209a03040b4000933c5d3029674a664cd22e901c74833616909983fc18c09403100c40009336172ef15f8a2e4b02238fa0712328167899440019709983200c6000932fc82f61640a464bf22a8fd871c32a162096c3e819609983140d20009329832ee15c8a2e4b42248f8c712325160095c3e419209683340c40009323312f7164ca684ce22f8fc0722328161899c41e1a009a03400ca000931ced2eb15a8a004a12230f686ee31015889403f019509483000c600093167630896d8a984cf2338fe872e33516989dc4261b50a3034c0d80009310472e59588a104ac2220f586e231615c09583e019209b03580ec0009309dd30196a8a8a4e023d905873e33416809d440a1a509c83580e400093038f2f49608a364b72280f9071032016089643f819b09903280c600092fd4a2e795789f24a221f8f9871032315e89483d818108982f40d200092f6f92f9963ca5e4c02280fb470632015e09643ec18f09a03240d400092f0b22f095c49fa49521d0f6870030a14c09103ce18409082f80c600092ea3b3071694a864e123a90487503471708a084461b80a603800ce00092e3ea2f415f0a324ad2240f9070431d161097c3f819809183100b600092dd8b2ff163ca424c42300fd871032215e899c3fa191096032c0c800092d7522e71598a1e4b42298fc471832c167098c40a19f09d833c0d400092d0db30f16dcaac4f024890c478634a16b89bc40619e09c833c0d200092ca8e2ed15fca204b62218f906fc31c154890c3bc18408f83100cc00092c43c2f51614a3c4c422e0fe071c326168097c3ec19109883440d000092bdde2f91628a364c322f0fc0728325167899440819409203040ba00092b7b72ea15989f84a221f8f3c6dc30915189043c818908f83000c800092b13e3071698a8e4e223e106478635617a0a184281a909a83240da00092aae72f715f8a404b82260f8c6fc31a16109843ee19009483300cc00092a48d2fe9630a484b42280fc872832416389d44221ad09a82f40b6000929e22302968ca884da23a104476634b17189c84201a40a003800e00009297ed2eb15e8a2a4ad21e0f586e830915089303c418309083100cc0009291982fd1638a544c82308fe871c32d168099840619409102f80c4000928b4b2fa9638a484bd22f8fc071a32516209743ee18709483440b60009285232e115949fc4a12190f406f632015c89543d817508d82fc0a8000927eca2ff1658a644c62308fe872e32916089443e418b09683440c000092785230d16c4a9a4e7241908c74e34917209f04121a30a083440e80009271f52fe9654a664da237902074e34617009c84321ad0a403600e8000926b9e2fb9648a5a4ca2318fd0732332166099c40019c09b033c0d800092653130816a4a804e423b906476a34116989903fc19a09483380be000925eb130a96aca8c4e023c905874e34517409f44301ae0a0836c0d20009258762eb15d0a224ad2208f6c6f030b15409383ce18609683040c600092523c2f195d0a144ab2298f9c6fa31e15b89483dc180095831c0c8000924c052e915d0a1e4a321b8f446e030c15589183c017808b82dc0b200092459f2f71628a424cf2310fd072c34217089f042a1a80a083580e2000923f8d2d715409ee4972190f686ee31715f099c3e818e09483040d00009239272ff9658a6e4cd22e8fc072432c16109743ea18d09783600e00009232b23039678a724ce2328fd472032415f09743e618b09203100b8000922c6d2ef95f4a2c4a921f0f446e4307155091c3d218c09483440d80009226143011658a624c122d100073a338168099040818f094030c0c2000921fa33099698a7c4da237101872832b16589b840e1a009a03500ce0009219622ed95e0a2a4b22270fac6f831215409083cc17a08902a809c0009213172fb9658a7a4d0238101071a32416209b440019309b031c0be000920cc62f81620a4e4c92360ff872032b16189843f219509c03600ca00092066e2f91634a524c72300fdc71e32816309ac3fe19d09c83280ca0009200082ff965ca584ba22f900c72032316709783e419909d83200c200091f984308168ca824da233900c75234616f09d84161a009f03600da00091f3442ed95e8a3a4b422a8fe872033416b09b04161a509d033c0c800091ecf02f4161ca444ae2250f7c6ee31115a09543e819109303000cc00091e66830996d4a9c4df23b102873633a16209683dc18409783200ce00091e0113001638a524c62310ff072e32f16709844061a409b03340cc00091d9bf2f91604a324b02288fb070a31a15b095c3e018f097831c0d2000 else (if i < 89 then 0x94fd1c3061670a644c422f0fd071632616109a43e619509d83440d200094f6f32ea15d4a2a4a42270fec716330161898841219a09d835c0d000094f09f2f99670a684d3239102874c32f16709d04281a409c83480d000094ea422fb961ca464c022c8fc871232015d89543f019409803380c600094e3d72ff9648a584bc2320fd071432a163898c3f0192098033c0ca00094ddaa2e315a4a164a92238f686f431415989543f218809282fc0c600094d7493021664a864d4239904075233f16a09a440419e09c03400d200094d0ff2f5961ca384b92298fc072632c16009683ea19309a02d80c600094ca7f30f96d8a984e423b101c74633e16e09f84241a709d83380be00094c4372f41628a444c2233900c73a33a16889dc4261a109b035c0dc00094be172de9594a0849f2220f986e231415b09543e818608c02f80c200094b7e62e515b0a1249e2200f4c6dc30814f09303c618408f83180c800094b1972f69664a724d42360ff871632416309a041019e09a03280bc00094ab532f195d0a264b822d8fac6fa31715e09443ee19009503400cc00094a5042f59600a264ae2200f8870231c16389b040219409583200d2000949ea82f39618a404be2318fe474033d16e09b040a18f09783080c00009498502fe966ca724c6232100c74a34517009e04141aa0a683a00de0009492132ef15c0a1c4a82240f706f231315809383ec189095032c0dc000948bce2f21608a484c6231100874a34616909a040419b09a833c0d400094859a2e495b4a164b322b0fb871232a16389a43fc199098031c0d0000947f323019644a6a4cf237901474233716f09cc3f219309a83300ae0009478f22f01614a384b822c8fec72631d16309783ea192099030c0c80009472982fb1620a544cc233901474c33f16789bc40e1b40a983a80e2000946c322fd164ca564be22b8fdc73433216889bc408197096832c0c80009465ed2f215e4a384bb22d8ffc73e327162897c3f618c09082f40ac000945f9b2ee95dca2a4ae2218f606f6312154093c3d418809503140da0009459532f195f0a1c4ac2270fa071c32e16a89903f81960a1034c0cc0009453082f5162ca6a4c92340fdc71831c157893c3d619009782fc0be000944cc92ea95e4a204b22298f986f231c15f09403d218c09903280c000094465130d96a8a784d1239900c74a34916e89bc4261a709f837c0e8000943fed3029698a744db2330ff472c32f16809b840619209b032c0ca00094398e2ff9654a5c4ce230100872e329162898440019609c03140d600094333b2f99624a444bf22d8fc071632416489983f019609783280ca000942ceb2f69600a264b62270f986fc33015d095c3d618609403180bc00094266d30c96f4ac24f624d90dc79c35f1838a444501b60a183780f200094204b2eb95e0a324b522a0fc070631d15e89803e418c09283180be0009419fb2f415fca384ae2218f906fc31915c09443e618e09483140d40009413b52f21618a564bc2270fa471632d163097c3fc1a709d03500d6000940d5a2fc165ca644c522b0fdc73033716689943f419c09183100bc0009407212e615949f449e2260f9c71031d15e89643fa1a00a1835c0dc0009400df2f59634a624ca22e101473032a16689c840019b09883340dc00093fa872f79630a504c32318fe872433516809ac4061a2097833c0c000093f41c3019650a504c622e8fd872633016089783e418e098036c0de00093ede32ee15cca2a4b02258fac71832d16509583e217f09303040b400093e78f2fa966ca6a4cb22a8fa870a32215e89303c418608e02fc0b600093e13f2f39610a5a4d823b102c75034016d8a0042e1b10a283700de00093dae72f315f8a444c32318ff473032d16609b43f018d094830c0b400093d4743041690a884e323e101874c33b16a09c442219c09d03440de00093ce102fc1624a3a4bd22c8fe072a33015c89383dc18909483040ba00093c7c82f09600a4a4c4232900873233716a09d840219409103080b800093c16a2fe1664a5e4c22278f8c6fe31715b09403dc19209583300cc00093baf430616d4a984e023e904876034f16e09f041e1af0a283680d000093b4a52f595eca364b92298f9871032a161897c3e618009102f40bc00093ae532f215d4a2c4a62268f986f831f160894c3ec18f09183200be00093a7e03049684a804dc241106c74e33b16689c441819b09803300c800093a1783039674a584ca22e0ff471c32415c896c3e418609483280e0000939b3f2ef961ca2c4a321d8f7070431915989783f419309783200e00009395032ed95e8a3e4ba2270fc871432916189683f819309703280ec000938ea92f79638a604c822d8fe871c32816089743ea19709a83400d60009388512f31610a4c4c822d8fd871832d167099c4181a009b03380d60009381f72f89640a4e4c12320ffc72831f15d097040619409603280d2000937bb62f095d4a2a4b122a0f8470832215a893c3de19209703200d800093755e2f71668a6e4d323a906875034117009d44161a409a83300e4000936ef82fe163ca664bf2288fb470232115c891c3ce19b09483080d0000 else 0x96923c3009688a6c4d023a103874e34016d89c4400194094831c0ba000968bed2fa961ca404b92250f886f631815d09443e218e09583440cc0009685c32df95749f649c2180f346d630b15589243d0186093031c0c2000967f672fc9648a444c22310fec72e33416d89d44201a509883180be0009678ff3019654a664ce237904873a33416a0a0042c1b10a203780e600096728d3029690a6a4c22240f946f2316157892c3d017d08e83100c2000966c183031674a584c322d8fd472432915d09803f819a09983400ba0009665ca2fb9600a204a92248f9872032d16809984061a209c03180c0000965f6f2fb1650a604bd22c8fe073233516809c040619c09d03580ca00096594d2df956c9f249b21a8f5c6e230615689343e418909303300c40009652e2304168ca764db23a103875233f16789b840c1a90a2835c0e4000964cb02ea95d8a164a721d8f586d030a15789483ea19509703400d20009646662f39618a424bb22d8ff474233e16e89c440619809683300c4000963ffa2fa9658a4e4c222e8ff471032815f89903fe19e097030c0bc00096399f2fb165ca584c322b8fd070e31f15f896c3e417f090831c0ca0009633512f59608a464bb22d0fe073e33e16709943f219309a83300c2000962d0a2fa1658a624ca23c900875633016389403e219809683300dc0009626b62fb967ca6e4d4237101874634517009fc41219d09b834c0c800096205b2fa9648a564cc233100073834016b09c03ea193097833c0d00009619fb2fc1628a484c8231900473632e15f89943ec19f09c033c0ce0009613b12f71610a524c72318ff873a33816789a840219e09b83500ca000960d802e695a0a1c4aa2260f806e231c160097c40419e09b83200c800096070530b16b4ab04e923d104075834e17409d44161a709c835c0e60009600c02f21600a3c4c322b8fb870832315f099840619109702f00b800095fa832ed15f0a324af2250fb871c31f15d09703f818909302f80c600095f42a2f79618a584c82358ff073033916789ac3f019509b032c0bc00095edff2e595a4a0c4a72218f9871032115e89683f2186093030c0d200095e7982ff9678a704d8237101475034516809a840e1a309a033c0c400095e1542f495dca384be22d8fc071032916489983ee19809383140c200095db0c2f29630a4c4c82310fd871232915e097c3fc19c09783000b200095d49b3041698a844d723c906076633f16509703ec19609603140ba00095ce322ff1670a784d8236101872e32a15889343d618f09603480d400095c7db2f99610a3e4b222b0fd0726325163898c4141a109e033c0e600095c18e2f39600a464b922b8ff473c33616b09cc42e1a609f83680e000095bb562ee15b8a0e4a421d8f7c6f231315d896c3ee18b08d82f80c200095b5052f41670a6a4c422e8fd472c32f16a09a041219809b034c0ea00095ae873069664a644d0233101875432c15c89383de18c09183400da00095a83e2ec95eca204ac2238f646ec31315809083ba17908f03140b800095a20c2e895b8a1a4ad2270f786fc31e158892c3c817f08e83180c4000959bc72f115f8a464c22328fe471c31e15789243d017e08f82e40b400095958d2eb95c8a184a121e8f546de30c158895c3ee19009a831c0d2000958f1730316aca944e3238906076234f17589ec42619a09c83780c40009588cb2f61620a324bd2288fc870231e15a89503de17a09083080c40009582af2dc95389e048b2138f086da30815588f83b617f08e02e40b2000957c2130d16d0a984ce2378ff472c33816609b43ee19109583240c20009575e62ea15e8a324b82258f886ee31a15b895c3d218a08f82dc0b8000956f952f39640a484c222e0fd070c31e15b89343d218208e82f40ba0009569422f81618a584c62318fe471a32b16509a03fc19209c032c0cc0009562e02fd165ca744ce23b8ff873c332164099842019f098030c0ce000955c7c30596a4a7c4d7235100073c33416709903fc19809b83340d200095563b2f215d4a284b021c8f706dc30e156890c3ca18208e82e40b6000954fc63031674a664d4239901873a33816b89ac3ea18c08f83000c000095497a2f8163ca584ca2300ffc72e331166899c3f819909183180b400095430030916a4a784d9239100c73a33416509803e819709883040b4000953c8b3039694a7a4d9233900872632215e09683d418709903440dc00095361a30996b8a984e723d906075c34316d89bc4101a209b83200d2000952faf302965ca564ce233903874e34a16f09bc40e1a509c83600ea00095297a2ec15c8a1a4b22218f6c6f030f157895c3d218908f83000b80009523232f7960ca404bb2290fb071232615c89643e418c09783180c2000951cd02f8164ca504c822f0fb871c32d164099840819909a83140ce0009516862ec15dca1c4b22270fb872032a15f095c3f019f09603440d00009510332fb9648a524ce2350fe074633716d09e041e1a00a083640d40009509db2f61604a304b922d0ffc73833616d89a04001a109a83380d200095038f2f41620a2a4b522c8fc8722329165899c400196092833c0cc000)) else (if i < 91 then 0x98270a2f99634a504c8234101473233516589a83f219209903440da00098208831096f0aa44da24110507543471738a204521ba0a6835c0e0000981a27301164ca684d1234902c74433115e09343d819509b83540e20009813c82fb1684a624cf2338fe072032315f09503ca18409483480d0000980d8a2e615dca324bc2320fd471032415f89a03e219709b834c0c40009807272fd1640a544cd22e8fe070432215f09643e618d09583340ca0009800e22f49604a4a4bc22c0fcc71e32916209603f0189095030c0b000097fa982eb15e4a3e4af2270f9470a32316509603f419109403200c000097f42e30216a8a7c4d322f101873e33616b89a43e818a09102d40b400097edf12ec15c0a0c4a521f8f7c6fa32115989483e018c092033c0d400097e7a72f51610a5a4cb2340fdc72032c16509a03ec19609803140ca00097e1532fa1678a4a4c3238100072e33d16d89b041c1a409183080c200097daed2ff9678a664c82340fc472833416909783de18409183200c200097d4b32ea15c8a564c9232100872233616d09b041819c09903280ba00097ce5d2fb1638a544c122d0fe072432e16889783ea18e091033c0d600097c8402db95509e648f2160f3c6ba2fe15309103b818108e02dc0c600097c1e82f99600a324ba22a8fb871a31c15b09503e2186091830c0ce00097bb982f71608a3a4b52290fa4718332168896c3e419809883240b200097b5522ee95eca304ac2220f7c70231b15b89343dc18c09382f80b600097af182e915c89f64972180f246cc2fb15188f83c617608b82f80b200097a9042dc15389d649021b8f506e231115489283d018f09483100bc00097a2b52f6961ca464d1235901475a34416d899840819809603140bc000979c5f2f89644a524c422a8fbc73632f16909a44041a609e83400d200097961b2f295f0a3c4b12240f606f631915709283ce18209303340bc000978f92314171cad04f824910a477c3581810a484501b50a183500d800097894f2f7161ca344b32280f9c70a32116289703f019609583280d80009782d030d16dca9c4f7243107c77a34a16e89cc4221aa09b034c0de000977c7f2f79610a4c4c122e0fc072032c16409903f619b09803280d20009776332f395f8a304b322e8fcc72c33216589583da18b09002ec0c0000976fe12f49620a544c622f100475234217089e441419c09603200c000097696f30616aca744d6238905476834a16b89d841e1ae0a003600ea0009763152f7162ca5a4c6230900473633316b09b43ec19508e82fc0c4000975cbc2f8963ca564bf22d0fc471232715c09643ec19209b83600c400097564930916cca9e4e6243106876434416e89dc40e1ae0a0032c0da0009750172e615a09f64a521f0f786ee30f15789283c418509183000be0009749a730996c4a8c4e2233103074a33916609743f6191094033c0ce00097434a2f89664a5e4d9239903c75235217209b841619a09883540ce000973d272dd15589dc48a2140ef06c62fc14988d83ba17708c02bc0bc0009736b130596a0a6c4d22370ff071432816289643e618709202e00c8000973041306167ca784da23b102474233316409943fa19a09a83400c60009729e72fe1684a664d4238903073c34516909cc41e1a40a383580c80009723bc2e19570a044a72200f786ee31715d09583d817e08e033c0c6000971d7d2f21620a4e4be2288fb470c32716809a841e1a009f83540ec000971716300165ca624c62318fb070832016309843ec19809683040cc0009710f42e3156c9fc49d21c8f746fc31e16009703e419409b03300cc000970a853019660a644ca239102873433716589a84141a409c83600ca000970423300967ca7a4d7237902873c33016b89c03ec19709382e40b200096fdd72f195e8a2c4a921f0f746f2312154894c3de18b08f03040c200096f7922eb15c4a264ae2218f646e831815e89243bc18209683340c800096f12a3031688a844d4238100873632116109583dc18d097031c0dc00096ead82f695cca1a4b02228f786fe31215b89683e618e09583140bc00096e48e2f6162ca444bc22f8ffc73e334167098840618e09483200c400096de3e2f215e0a1c4a821c0f586c62fd15089203ce18209082dc0ca00096d7ef2f81648a424c52308ff072032c166099c3f419c09d031c0c800096d1bc2e715b8a204aa2220f886f632315e89783e819109a03540e000096cb8b2e09584a0449321d0f646fe31a161098c3fe19d09983040c600096c5263061688a664cc2320fdc71e32f163098c3ee18e096830c0c600096bed42f995eca3c4b02248f986f431b15c89583e018d09583000b000096b86a3019640a6a4cf2330fe8724327161897c3fc19f09b032c0e000096b2232f495f4a184ac2260f8070431f15f896c3f419309082e00ba00096ab9c30a1688a924dc23990287583441718a044401b409d03680da00096a5502f8161ca504c52370fd070e31815e095c3f018e09603140c8000969efd2ff9630a504be2330fc471432a16309903f019109483340ca0009698992ff1690a724c6231901073c33816609983f419f09a03500d2000 else (if i < 92 then 0x99bb082e415649f249121c0f546e230715789183bc18108d82f00b400099b4ac2f31610a4c4ba2268f886e031915d094c3d818309403280dc00099ae6e2ef95f4a3e4b82260fb071232715e092c3ce18709383200d800099a80e2fc162ca444bd22b0fa070432716509883fe19609e83440d200099a1973061694a7e4c922e0fd073a33216909dc40019d09883300b6000999b622e995d0a1a4b422a0f9470832115c09403ea19a09602e00b20009995152f115d4a204b722b8fa86fa32216209643ee18909403000ce000998efa2db95449e84932170f3c6d430e15709383de18b09903140c20009988ad2f09608a324ab2228f7870031d16189683fa19d09c83400d40009982732ed95d4a204b32298fd871832016109603de18a09102e80b4000997c132fd164ca5e4c9238902875e34616d89b040619e09903240be0009975be2f99614a3c4b22280fb073433216589a03f619409683440cc000996f742f91634a524c32318fe472c32c15c896c3f419909983440da00099693a2eb95d8a1c4bd231100073c33116b898840819d09d831c0be0009962e62f9962ca4c4cb22f9000736333165899440c19b09c83280ca000995cb52ea95bca1c4af2200f506d431815889383d418a09182f00c40009956862e2159c9f64a02218f746ea30b15108e03ac18309183180ce00099500030896b4a864df23d106476234c16e89c03f619209583280d20009949bf2ec95a4a064b42298fa470c31a159894c3f019309703280d00009943802f09608a364a82250fc470a31d15c89883e818c09883280da000993d3e2f59614a3e4bd2278fac6fc31515889683e618e09a03240c60009936f32f5960ca3c4bb22b8fe472c33e16b898c40619909d83500c200099309d2fc960ca464b722c8fe872432f16389883fa19d09a83000b2000992a6d2e715c4a264b22260f586f031415909303d817e08d03080ce00099241a2f31614a304aa2240f646e031915909583ea19a09403240d8000991dbd2fd166ca784d7236102073c337168899840419009483200c20009917603039664a604cb234900872832c15e89383c017808802b80b00009910fd3011684a784d7239903474233d16f09dc42c1ae0a803a40ee000990ad82e595b0a0249d2240f8c6fa30f15789583e419b09f833c0d400099045d30d96b4aa44e223c1000738337164098c3fc19509283040c600098fe432e11590a004a62200f8870c31a15c09643f218d09b035c0d000098f7fd2ef95f8a3a4bb2270fc871632316209643e818b09503240c600098f19c2fa164ca564c222d8fec71c32215e896c3de19309483440e400098eb5f2ea15dca184ae2278f9070c32316409a43fc19909203040b200098e4da30d16f8aa44f1241903c7483451748a1444c1c70ad839c0e000098de9c2f09620a444b42270f906fa31415509303de18309503200c600098d8253039690a804db237103c74a33d16709c440e199099030c0b800098d1ba2f91644a4e4c42330fd471a33216589803f618f09303340d400098cb592fe1650a6c4c62290fbc72c32e167896c3ea18b09503280b800098c4f12ff967ca6c4c5230901c72632216389743ea19009302ec0c000098beaf2f69600a364b32288fd071031d15f098440019809a03200ac00098b85130216a0a8a4ce2318fd871e32616209b840a1a60a203740e200098b1e62fd964ca5c4be2318fd472633116189683d417f09003100b400098ab9d2f315dca424b422b8fe071c32515f89483f619909b03180ca00098a5572ef95f0a2e4ac2238f8470031c15c09343cc18309683200c2000989f022f71600a204ad2288fc071232415b096c3f819809e03400c80009898c12ef95f8a1e4a521c8f446d430415509283e818c09303100ce0009892732f395f0a2e4b12280f806fe31115809103da19109583140c6000988c0f2fc9648a504bb22e8fdc72632316009784021a40a103640c80009885a6301967ca624d0238900872c33115e09543da18709503100c6000987f482ff164ca5a4ca2340ff072832416189603e818909283240c400098790e2ea15b8a104aa21d8f546ee31415589203d018809503240ca0009872b72f81644a5c4c222e8ff473233316289303de18908f82dc0ac000986c5e2fa9640a424bf232902873433716189803e818f09603100be0009866272e915c4a1c4ad2220f906fc31015889203ba17d08c82e40b6000985fe52f11614a324ae2258fbc71231f159894c3d2187093831c0ca0009859882fa164ca5c4cf2350ff074833c16809983ea19509282fc0ca0009853262fc962ca4c4c522f8fc070832215e09303c017e09303280da000984cda2f295f4a384c122e8fe472032f16189703f019d094030c0b80009846862f3160ca344a921c8f406d230515389203d618a09203140c000098401b2ff96a0a7a4d6235901073433216709c840619a09c03700e00009839c62f89620a364aa2228fc471232a15b89583d418709583080de00098339c2e31598a0c4a72238f846d230515889183c818c09703140c6000982d682e515889f04a021f8f506e230714f08e83c417c08a02d40aa000 else 0x9b4d682ef15c8a284ad21d0f7c6ee30a15609103d818f09382c40ce0009b47232ef15f0a344ac2230f8c70c31b16089443d218609202e40ba0009b40dd2f49638a404b52268f986fc31d15f89683de18b09603280c20009b3ab72e315c4a2a4a921d8f706e830b15288f03b017708e03000b20009b34802e615bca2a4ba2290f946ec30815709143ca17a08c02f00c20009b2e542df95849e84a021f8f806e231115309003b417b08d82c80b00009b27f030296a8a864d52368ffc74634416c89c440619709b83440e20009b21962f5960ca384b022b0fcc70432115989783e418f09c03300d00009b1b4c2f5961ca524c42318fd471632d16689c04161b00a7836c0d00009b14f42f89618a3e4ae2288f986fc32116109703fa19a093030c0c80009b0eb92eb15d0a224ae22a0fd471a32716389a44081a009e834c0d80009b086b2fb1624a4c4c022d0ffc73633416c09b44161a009983140d20009b02102f8963ca524c422c8fb072232d162099c4001a609b036c0de0009afbe22e6959ca1c4ac2268f9070032515c89643ec191097033c0ca0009af5c72db15409dc48f2140f306bc302154894c3ce18109103000c00009aef812ec9598a044902180f206c630915389283ce18609102e00c80009ae92e2f11610a464ba2290fd073633016389583da19309a03200d20009ae2d92f31604a464a32210f746ee31915b89343d818f09c03600ca0009adc782fa95f8a324ad2268fac71232215b89543e818c09583100c20009ad6202f7161ca484c022e0fb471a32215909183bc17d08d02f40b20009acfeb2e815c0a1a4ae21c8f606e630915308ec3c418708e831c0c80009ac9892fe9644a504b92290fe472632b16109783f819309a033c0b80009ac3362f89644a524c1232100072231f16289543e018809482f40b80009abcf92e795a0a124ae2200f9c70431b15b097c3f619909503300ce0009ab6e12d595309d048d20e8f006c830515189043c218208a82e80b00009ab0892f99624a4a4c322a8f9c6f831915889283d018f09a831c0b80009aaa2c2fc9634a684ce2320ff072233216489783d817e09103000c20009aa3ea2e895a4a0649821a8f746fc32915c092c3c618109103200b40009a9d892fe9650a604c92318ff472a32716789b04141a109b834c0d80009a97512ed95c8a224b02280fbc71032215b89583e218609103140bc0009a90fe2ec15c4a324b922a8fd472032f16009803ea18909483180bc0009a8aeb2de95589f649521a8f346d231115808f83bc17d09083140b60009a84872f91640a584ca2348ff071e32715e89843f619209703200ca0009a7e0a30a16e4a944e423b902075a34916f89d840019a09583000c40009a77e72e89594a0e49d21f8f6870032315d09983fa19609403280b80009a718e2fb1644a4e4c12358ff474e33a16589903e819909a83080be0009a6b233099694a884e6241908878635817009c040018e09903100c80009a64af30516a8a8c4e323f103474e34216f89d441c1ab09e83300ca0009a5e46303168ca804d923d903473e34016b09a441219709483200d60009a58072ef15e8a1c4a52218f946fa31f15909243de18408f03040ca0009a51c92f115cca2c4ac2238f886e0315158892c3c417108a83100d40009a4ba42e395a8a1e4b22270fc070032215c89543c418409483340be0009a45642e815aca2c4b52280f7c6ea31215989443d218409103100de0009a3f0e2f81624a404b22240f8470a31b15c09883f2193096031c0d00009a38d72ee9610a3c4be22c8fd471832616109883e4190096033c0c00009a327c2f31618a304b22270fb070231a15e095c3e418a09b83300ba0009a2c422e115a0a1249a2160f286d831615588f03b418509603380bc0009a25f12f69624a544bb2308fe471a32215d09383d618b09383180c60009a1fc22e915989fc4972198f586fa32715e09483c417708e03000c20009a194d3061680a6c4d62371014740334162897c3f419609783200cc0009a130c2f095f0a364ba22c900874e33d16d8a0040619909c03240d20009a0cb52fc1650a564ae2288fcc71e32815b893c3ca18309603140ce0009a067c2ee15cca2e4b62260fa86f031c15809443de18a09002d40ae0009a00412e895dca064a821e0f586da30e15309143d818309203140ba00099f9ee2f51604a444bd2278fb070832b161094c3e618f09283200c400099f3af2e995909fe4a721e8f6870631f159091c3b217d08f02d00ba00099ed6b2f315cca124a521c0f7c6e8311150891c3c617c08e02c80b800099e71b2f315d8a1e4a72228f746e630915389143bc17508982e00b400099e0a530a16e4a9e4df242103075233616409a040619d099033c0d000099da422fc1648a4c4c32278f9071432316109483e619c09e837c0d800099d4272de15889f64a521f0f686e8305156095c3dc18e09602fc0ba00099cdda2f015f4a444ba2298f986fc32015e09543cc18108b02bc0a000099c7992ea95d4a064a02240f886fc31f15b89503d018308a03000c800099c1412f69650a524cb2340fd071832515f89643e418008b02dc0c0000))) else (if i < 96 then (if i < 94 then 0x9ce2002fa15f8a3a4c722c8fec72032715f899441c1ad0a083700e40009cdb982fb1620a584c922b0fec70e32215b09503c818009803200cc0009cd5402f79618a3e4c52310ff073433e16b89d841c1a909f03600d00009ccee42f99658a5e4c422d8fe470a31815b89303d218509203180d00009cc8912f89620a404b72280fd072233517009cc40e19f09803340de0009cc2372f4161ca444b32278f8870e31f15909183d018d08f83340ce0009cbbd82f49610a604be22a8f906fa31515b09383de18e09783180cc0009cb5a42eb95bca204b32258f9c71432715b89743ee19409a83240ce0009caf2c30b168ca6a4c72318fdc72032415d09583e0187092830c0c20009ca8d32fb1628a464bb2300fc871632516209743fa19909983100c60009ca27a2f61634a424b12240f6470232115f899840419909883380cc0009c9c2b2f21630a644cb2318fe471c32215b09403e019209a036c0da0009c95cd2ff1678a684ce236901074433a164896c3ee18b09202ec0be0009c8f662ff1660a564ca236900874234216889d04101ac09f03500e00009c88ee3099694a904f0241905c75033e16809b44101a509b03140c80009c82c12e41590a144a62238f7470232015f09643da188090830c0d80009c7c7a2f49638a444bd2310fe071c32d16109583e618809103080c00009c762c2f09604a424bb22a0fb470e320157093c3de19209483000c20009c6fc72f8162ca404c42258f846f031a15c89843f619c09d036c0e20009c69592ff1618a3e4c422b8fc071a329160894c3de18809303100bc0009c630f2f89614a424b922c0fc4714330168098c3fa19709c03200ca0009c5ca83011694a844d0234100473833d16c0a044341b20a6837c0f00009c567f2df954ca0049b21d0f686f231b15b89483cc17c09002fc0c40009c50482df958c9f249421c0f8470231415d89543de18909403180c00009c4a002f095c8a304b12248f9c71832816109783f819409803300d00009c43913019654a6a4c92330fc070832115b89703ec19b09b03400ca0009c3d3a2fc964ca704d22389010734336166899040c19209883340d00009c36d92fd9650a5c4d32310ff073a33c16a09bc3fa19209c03300ca0009c30792fb1628a484bd2290f886f431215b095c3f419b09903500ca0009c2a462e915c8a264b32240fa070231b15a89703e819309603000d00009c23f42f71648a644d223b906075633716909b83f819a0a083480de0009c1dc12e895d8a1e4bc2298fb071031a15a096c3e019109682f40c20009c177e2ec95c0a204a72220f786f831215e09283d218a09a83180be0009c11402f095e8a244af2268fd471032916109643f019a0a203600dc0009c0aee2f395fca424bb231101c73432215d89503e219509a03180b80009c04c22e5159c9e64a32200f446e6310153890c3b617309203280cc0009bfe4a30a1684a724ce22c8fe072832916389d842a1b50a083500e00009bf7f02f89638a3a4b12290f946f831b15e09483d619409503200bc0009bf1873059688a704d22370fe871e32716089783e619109783140bc0009beb422f115cca404ba2290fac70832215d897c3e618e09403480c40009be4d3305162ca304b322c0fc472033b16789ac410194097831c0c60009bde712f89628a484b42280fc070832216389884021a209683380c20009bd80d2fe9638a4e4c322e100873c33e16989c83fa19709c83400de0009bd19f3049684a9c4e723a901c73e33516789b441619d09382f80ca0009bcb762e1954c9f249421f8f9070031815d09583e818c091831c0c00009bc5073011654a5a4b822c8fc472033016289903f218f09283140c40009bbeb02fb1634a564c122f0ff473a32c15e898c3f819709202e00ba0009bb87a2e895a8a144a32200f6c6ee32415e89683de18c092831c0d00009bb2123021650a5e4c022f900472832b16689b440e19c09583340ca0009babbf2f89630a5e4c422d0fc870c31c15d096c3f619809c83600d80009ba56f2f495f4a2a4c42300fd872232016609d040a19b09903140ca0009b9f552da15449d44892138f2c6d631415f89903f819709503040c40009b99222e01598a0c4a02230fc871e32716209603d818d09403300ce0009b92a130d16b8a8e4d9237103073632415f89483f219c09603140c80009b8c582f31614a5a4d02310fb471e329167897c40a19509983340d40009b860f2ef9604a544c222b8ff073233716a09883ec1990a2835c0e60009b7fbb2f99650a504bb2270f8c6f4314155894c3e018609503240cc0009b79612fa1648a4a4c5232901473633216489743f819409903380c40009b73162fb962ca484b822b0fdc71c32515e09643e619109a03480d60009b6ce32ed15dca1849f2210f746ee31d15909283e818408d02fc0b60009b66a62f095f8a1c4a32230f646f6322160898c3ea18d09183180cc0009b602130f16b0a784d3238901c73232815a89543e218709303140b40009b59eb2e815eca264a821b0f846ea32015c895c3ec19109503200d00009b53b32e5156ca0a4a52290fa06f031915c09683e618309282f40b6000 else (if i < 95 then 0x9e757d2df95709fa4a22238f786ee31115809543e619509683580c20009e6f2e2f4162ca3e4ba235104874a33416f89e84261ad0a083740e60009e68db2f51620a304b62248fa871a32115f09203cc18809403340d00009e62952f095f8a344b022b8fd0738334166098840e19709883480de0009e5c1b3099694a9a4dd23e106076835617689fc4341ab0a483800e40009e55a630696a8aa64de238100473632816589883fc18d09203000be0009e4f542f495e8a3c4b82240fa471233116909a03fe19609683100c20009e491a2ec15cca3a4b42290fac71c32f16509943f419109a83300de0009e42ee2ea95c8a124a021c0f606fe31315688f83ce19209c83640d40009e3c982f81620a2c4ba22e0fb472c33216189443d818609903080c40009e364b2f39618a384b42290fd871432f15f099c40a19009383180b80009e2fe3303967ca6a4c72298fa871a32615f096c3dc194097030c0c60009e29b02e615b0a1249c21b0f506ea31615589043b017408802c80b60009e23493041694a7c4cf230901074233f16c09a440e19609903300d40009e1d042ee15e4a124a32210f4c6e030215389043ba17f09102f40be0009e16fd2d614fc9c047c20a0ec86a82f114e08c83b417c08e02f80b80009e108f2ff1678a644e123c905876834d17189ec4061a70a0837c0d80009e0a342ff1670a6c4d222f100473a34316e09cc4161a30a383740d60009e03d72f9164ca624c62310fe872a32916589b042019c09d03400ca0009dfd832fa1608a4a4c722f8fcc7423421710a084201a309f03580a20009df7532e4959ca0049f2208f806f031e15b89543dc188093831c0c00009df1162e915b0a104a52228f9070631315209203bc17d08f02ec0c80009deac42f41620a464b42238f7470431a15b89303d818c09503140ca0009de46d2f99624a3c4b42260fa06f6326160096c3ea19209503400ca0009dde3c2e49568a004942170f486e030d15389183d418e09603280ce0009dd7e92f61648a5a4ca2360ffc7443441728a084301ad0a103540d60009dd1892ff1648a444bf2300ff473033b16709b440618e09483300ca0009dcb3b2f7160ca4c4c92248fa8700321159092c3bc17808e02f80b60009dc4dc2f99628a464c32318ffc73e33516b89b442a1ac09c035c0da0009dbea32ea15a0a1c4a52238fc071832315c89403ce18709202f40bc0009db8602f015d8a1e4a32218f446ec31715388f83c819108f03000b00009db1f0307969ca764dd23d905476a33f17109d44301ab0a403480d00009dab9a2fe9670a7e4d4234103074434116a89a43fe19909f835c0f40009da5542ed95e0a284a822a8fbc72032a16489703d617f08a02f00ce0009d9f142f595f0a3e4ba2310fe471c330164899c3fe1a80a103440cc0009d98c92ee95eca3a4b62260f8c6fa31d15d895c3de18f09a03180d60009d928e2ec95b0a0a4aa21e0f386de30715889603fa19a09203000d40009d8c4e2e815aca164a321b0f3c6d830b15508e03c218309182f40b60009d86092f295f0a2c4bc2280f9c70231e15f09783e818e095031c0ba0009d7fc12f395f0a4a4bf22e0fc872232c16089783ec196099833c0c60009d79622fb1664a644c92320fe872833216709c44181a50a103440ca0009d73262ea95bca1049d21e8f7870431b15b09543ee19209603280c40009d6ce22f29604a2c4b422c0fd070e32d15e897c3e619009883380dc0009d667b2fe1620a604cc22c8fe474233716989dc42a19e09903400d80009d602d2f195eca3e4bb22c8fe470a320158895c3dc18308d02d00b60009d59cf30296aca684c3234902073e335164899440e19b09d83480d60009d53862f51618a3e4c122f900c74033d169899c3fe18a09203100c00009d4d5b2e395c0a2e4b92260fac70631615b090c3e018909683200dc0009d47202ee95d8a284ab2278fe472633316909a03fe19c099031c0d00009d40c02f81654a484c0230100472c33416b89a03ee19e09c83580d20009d3a702f9963ca484c022a8fc472833116489803f819609b833c0d00009d340f2fb1638a444bc22c8fe872633016889b43fc19909d83480ca0009d2da430396d0a9c4ea23f107077c34c16c89c842a1a209e83340ca0009d27402fd1620a524c322a8fc070a328163897c3e419009d834c0d00009d20c830696a8a8a4e0241907877234916d09d44181a409a83200c20009d1a872eb15c8a2c4ad2238fac70e31f16109a43ee192095032c0b80009d14562ea15dca304c5235901c74c34316a89cc4181a009883300b60009d0e202eb95f0a204bd2300fdc73834216b098c3e617c09083200ce0009d07ee2e415a4a0c4a421a0f346ec31415789103cc18a09103000b40009d01a52ef15f8a3e4bb22b0fd872432c16109883e619309702f80c80009cfb392ff963ca524ba22d0fcc71e32116209603d018a09703580ca0009cf4ca3019654a5a4d12370fe871833216889a03fc192096030c0be0009cee742fe9650a784d1239101474e33f16609c03fc18f09703100c60009ce8592e4958ca0449d2180f5c6d430f15088f03d018b093031c0ca000 else 0xa008522ea95b8a284a02200fb871a31d15c094c3ea197095830c0d2000a002102f69634a684d52340fd873433616689943e819009903400dc0009ffba7303165ca484c4237901073e33c16c09c44101a409903340d40009ff55d2ee95f4a284ab2220f586f831b160896c40619c09902dc0be0009fef002fc1654a544c922f0fc470632215f89303b217a08a03000ce0009fe8bc2f015e0a244b12270fac72232915f093c3e018209402f40b40009fe29d2d7152c9e04932190f606e030b15589483e819709983480ce0009fdc662e815d0a1e4a621e8f8870631c15a89643ea19109003140bc0009fd6142f4162ca404b62280fd872033116409ac40a19d09e03300bc0009fcfd12ee15dca344b022e8fcc71631d15d89643e419309303240e60009fc9922ee15d4a2a4b72230f9c71031b15a894c40819909f03380d20009fc33c2f99618a324b62288fbc70a32616189683f219609783300ca0009fbd002e595aca064a62248f906f231015509243c217508b82c80c80009fb6a52f89644a524bc22b0fe4722321164099c3fe19a09e83180b40009fb0522f19624a404c3233100474a334165899040619609503100c20009faa022f29620a504c92338fe872c33916889cc40e194099031c0d80009fa3cc2ef95e8a2c4b72290fe471832e162098c40819c09a03500d00009f9dc42d695549da4852138f386d430915689303ec18d08f82c80c20009f97842ed15d8a324ac2228f9070c32a15a89583e618108e83140c20009f91212fe9678a684c92300fec72a33116709683ea18609583040d00009f8ab73021674a864db23e104c7563401710a004301af0a283900e00009f84942df15749fa49a21a0f406ec31115709483f419409683200ca0009f7e22304969ca944f1241107475e33d16609984101a909c03300c00009f77c72f99654a6a4cc22e0fec71c33116489b040c19d099033c0c80009f71982e795909fa49c21c8f606f232015a09283b617a08b02d409a0009f6b2d2fe9644a404c523510287543441758a084261a809e835c0ca0009f64db2fa1634a404bc22a8ffc72e33916589883fa19c09783140be0009f5e5730716c4a9e4ec23f103874a3481710a0c44a1bd0a583ac0e60009f581a2ee15c0a184b12280fc471432916589b841019e09f03600ca0009f52062dd15289b447d20d8f006cc2fe15088e03b217308682d00a60009f4b8e30a9698a8c4d423a102c73c33916889bc4121ac09e83280b60009f45472f215f4a304ae21f8f7470031015d09443dc19709903440d40009f3eeb2fa1628a484c02280fe072e33016509803e618e09383400e40009f38a12f5163ca564c622b0f8c71032716389503d418109583200be0009f32502f5962ca404b922f0fd872833416689a83fc19009983380d20009f2c282e395809d04872130f1c6d630915489283ba16f08a82d80b40009f25e92f215f8a3c4b92288fe472832d165099840419709903200c40009f1fa52f395eca1e4a82250f746e031715a89583fc1a509c032c0bc0009f197a2e495c0a2c4a72238f8c6f431315609243dc17e09283040ce0009f13442e515a4a1e4a32278fa870232415e894c3ec19409403240c00009f0cfd2f89644a624c7234101074033e16c89c841c1a209d83540cc0009f06b82eb95d4a1e4ae2238f606ea30e15709203da18508f02d80c00009f00762f01610a564c82311004740335165099c3fe19509683400ce0009ef9df3199750abc4f9242907875c3491750a0c4381b00a403a40e40009ef36e30996a4a6c4d723a903874433816789a03f219609403100b60009eed3c2e5157ca104aa2268fac702329162894c3dc192099834c0d40009ee6ec2ef95dca284ab2208f9c71031e15c893c3c619209783240be0009ee0972fc9664a644d52358fe072c32b168098c40e19b09a83380d20009eda4b2f6961ca244b222b8f9870432515f09543ea19509703040b80009ed3ee2f81640a564c52338ff8728332164899440c1a109c03500de0009ecd8f2fc1638a484c92300fdc71e32f16709b440e19a09783240d60009ec723302165ca664c82300fcc70231415809383d618608e82d80a80009ec0d12f81634a4e4d22370fe072a33016909c840e19d09883680de0009eba852fb160ca424b72280ff871232215b897840a19c09903380de0009eb44b2eb95b8a084a321d8f7870431715d093c3d418a09703080c00009eadf72f61614a3e4b722b8fe872832a161099c4101aa09b83300cc0009ea7b22ee15f0a2a4aa2210f506e8311158092c3f018b09b03580d20009ea16a2f5960ca5e4da234102874433616c89c04261ae0a403880e40009e9b202f61654a564d3239106c76434716f89e041e19a097031c0d00009e950b2d515089ca47d20f0f1c6b830515009243d818209102e80b80009e8eb92f6163ca684cd2348fe873632816189b43fa19b09983000c80009e8847303167ca744da23a903074e33d17089dc41e1a809d83580c80009e81ec2fe9624a664c72298fb470e32315e896840619409603340ca0009e7b982f61648a5a4c4235100473a330169899c40c19709a83340c4000)) else (if i < 98 then (if i < 97 then 0xa19b612e0958ca244a32210f706e430c15709283ce17e09303200ca000a194f93029670a704d1235101073632815a89503e818d09603180c2000a18e953011674a724d0235901c74633d17189b83fc19909903140b4000a1885d2e995a4a0a4a52240f906f831e15e89683f019209682f80b2000a182242e495a49f24a121d0f706f231215889583f218d09383200b8000a17bef2e315949f048d2190f606e831e155092c3d817909182fc0bc000a175843041654a564be22c8fc471632c16509a83f219809803380c6000a16f472ed95f0a264b52280ffc73e32c16209783ee19009302ec0bc000a1691b2e515a0a124ac2268fa86fa32515b09503da18a08c83080ce000a162f42e095609ec49321c0f686f231315989103c818409803240c6000a15c8530b169ca944e5236900873633716809c040e1a00a0032c0ce000a156392f89608a364b92228f8c70831d15c89603f419709782ec0ba000a14fe92f21620a384c02288fa071e33216909a43fc19e09c033c0c8000a149a52f01608a424cb2310fe872a32a164097c3ec19a09503380ca000a1435c2f6960ca3a4b922a0fd472c33516109b83fc195099834c0d4000a13d172ed15e4a204a92208f746f232415f89603e618a095833c0d6000a136b92fb163ca404c92340ff473433516a09a43fe19e09f032c0d4000a130832e79598a024a32250fb071e32615f09483f819209883340cc000a12a2b2f99664a804d8238102474434216d09e04261b00a003740e0000a123f82ec1600a364ae22a0f9470031e16189743dc19509783100be000a11d972fb963ca504b92238f8071432e168097c3f81a309903480c2000a117362ff1654a664c82359050752340164899040a1a209e03500d4000a110fd2e795aca1c4a82218fbc71a321161899440019909503180bc000a10a93302165ca624c722c0fc470c31a157894c3e4194098832c0be000a104392fd165ca4a4bd22d8fd0728330161899c40019e09f836c0d8000a0fdfb2e51590a084a12240f886da31115589143ce18909403280c6000a0f790302966ca784ca233901074433e16989b840c19c09c036c0e0000a0f1512f19608a364ba2318fb870a31915c09443e218708f83000b4000a0eae73021664a6c4c62320ffc73232516109a43f619a09d83500d6000a0e4a32f79620a524be2310fd073033016989cc4201aa09f03200c2000a0de812db95749fe49d2208f686f431816189643f219f09b031c0dc000a0d7fe31116e4aac4e8244107075434917189e440c1a20a203540da000a0d1af2ee1610a504c22328fe471432515d89643fc19609803240ba000a0cb742ee95d8a1e4ad2280fc070432415d09403e019409b83500d8000a0c52c2f095e8a3c4b72248f746fa31a15d89303e619009303400ea000a0beaf3031688a844d423f105c7563421788a284281ab0a0835c0e0000a0b8b02d194f09aa47820c8edc6ba30114d09003ae17f08b82dc0bc000a0b2742e815d0a344b32290fa46f432815d09783fa19f09603080d2000a0ac642d695109c24752068ed06ae2f314c88d03ba17f08e02e00b8000a0a6122f89624a4a4b52280fb871432d165898c3f019608f02d80b6000a09fd32ef95e4a344b22260fa86f231e163896c3dc187095031c0cc000a0998e2f8962ca524cd2300fec73032f167099840619809603200aa000a0930c31096d8a7c4d7237902074e34316f89f44281aa09a83180c8000a08cdd2eb95d8a2a4ad2208fa071432215a09403e618508f02d40ba000a0867a2fe1648a604c1233101874233316b09d841c1ab09d03540ca000a0804a2e895e8a244af2248fa872433416589903f619909c03580ce000a079e53001688a744d123a103474c33c16a09b03f819709703200c0000a073b52e6957c9fa49321e0f606da30c15209003b618609383280ae000a06d6a2ef1610a464cb2328fd872432b16509ac40a19909803440d2000a067262e915c4a204ab2258fa070e32916409b83fe19509683280cc000a060c32f99628a2a4a42220f6c6e8317159894c3de192099834c0dc000a05a4a3049668a764d723b904076a3511730a044461b90a403600e2000a053f63019638a524b822b0fe071e332164898040019e09e83380d2000a04d8f2fc1620a4a4c822f8fe473633816b89bc3fa18b08f02ec0ae000a0473f2f595f0a244bf22e8fbc71e32c16089843f218f09a83380cc000a041092e915c8a164b22248f946f430d154092c3cc17f08b82b80a6000a03aab2fb1658a624b922b0fcc72032a15c89503ce18909803080d2000a0345e2f595fca464ba2308fc873632716409843f21a109482fc0ba000a02df33009670a7a4e1240902874c33a165899c40419b09583200c0000a027c82e715aca0a49e21c0f206b82f814d88fc3c418509002dc0ca000a0215f3021664a844c822f0fd071c32d165097c3d219509803400d2000a01b262ea95c0a244a621d8f5c6e2317153091c3ce19609b03300ce000a014d72fc1634a504ca2318fb870832215d89403da19209b03380ce000a00e852f495eca2a4a72270f746ee31e15a09683de18d09983540d4000 else 0xa32ce5317172cab84fa248109076034316a89a440419a09a83540c4000a326912fc1630a444c22328fd871432316189783fc18b09283280d2000a3203a2f81644a584ce22d8fd072432815f895c3ee192098035c0d2000a319e72f51628a344b322a0fe471e330163097c3e018f09503000b6000a313c82db15309e04952198f2c6dc30715409183c218209303100c0000a30d712f615f4a384b722b8fb070832116089a03fe19409702f40aa000a3073e2eb15d0a224ab2200f846f631d15689403dc18b08f032c0d4000a300f62eb95a89fc49c21c8f5c6ee30e15008fc3b217a08f83100ac000a2fab72e995a4a064a52210f806f831515a89103c617d08d82f40c4000a2f4662fc961ca404b322a0fb471031f15e89783dc18709102fc0ba000a2edea30e16cca8c4db237900c72832616309683e419309a832c0ce000a2e7a92f295e8a384ad21d0f346ee30a158093c3cc18309182dc0c0000a2e14a2ff1638a464c92310fd470a325162096c3f218f09483380d4000a2db102eb95fca284a62280fd072e33116489d041e19c09b83300cc000a2d4ca2f39620a5a4c52320ffc73232816189984021a40a00390100000a2ce732f59644a4e4c122e100473e339162899c40219a09683100d0000a2c7d43189710ab44f324a10a076e35a1748a104321a609b03540d8000a2c1be2d8152c9d64882100ee86b230215789403d018308d83080a0000a2bb812e915f0a0c4ab2200f686f8313158092c3c2180090831c0c2000a2b50230d96e8aa84f223c105476034e16d89c84101a40a283480ec000a2aef42d9156c9e449421c8f706f030f15689183c218409202f00b6000a2a8b82e695649ec49c21c0f486f831615909443da18d09282fc0d0000a2a27d2ec95dca044ab2258f8c716322164899840619f09e833c0d0000a29c1030b16e4aa44e8241108877835b17d8a5c44a1bb0a703900f4000a295d42e815d8a1a4a72288fb071432a163898840419f09803580d8000a28f982ea15b8a104922190f486da31515889583d218b08f83000ba000a289602e7957c9f849a2248f9c70031c15a89343de18d09403340d4000a283252ec95d8a164b82240f706f232015c094c3cc17c08b82ec0a8000a27cdb2f195f0a244a62200f586e831c15a09243da18a09282fc0bc000a276872f495f0a3a4b722e0fd871832d16209ac40a1a209a03300be000a2702d2f915fca2a4bf22a0fb071c32215e096c3f21a009c03000be000a269ec2f115f4a2e4b822d0fc071232e15c096c40219c09c832c0ce000a263992f49648a404ba22f8ff073033416809783ec18a09383200c8000a25d7c2d895689f84ab2248f6c6f030815189283cc18509283200c8000a257392f19604a344ad22a0f9c70c31e15809303da19709983400cc000a251182e2958c9e849c2218fa0726327165096c3e418f08f82e80b2000a24ab42fe967ca5c4c422c8fb871c32d16709803d418c093831c0cc000a244922df958ca0249b2208f746e831115b093c3dc18909183000ca000a23e442fa1638a564c322b0fa071231815909683e819409c83400c6000a237f32f715fca2e4b62210f846f831a15c094c3d218108c82f80bc000a231c42eb15c0a0a4a42238f886f032516409903fe19809583340de000a22b702f81644a5e4ca2318fec726337162097840a1a509802f80c4000a225472dc157c9f049c21c8f4c6fa31515809543e419109e03280c4000a21f012f215c8a3a4a82230fa470032215e09703f219109683040cc000a218c52ec15dca2c4b52278f6470232215789383de18f09483040be000a212782f29610a3a4b82248f846fa32a16189783dc18008e02cc0b4000a20c332ef95cca144bc2288fbc71a31d15c89743f819409403080d4000a205d72fc1650a684cd2300ffc73c33616f89d44201a709903400ce000a1ff8f2ef95fca324b12220f8070832715c095c3cc18609503200c8000a1f96c2de157c9ee4942168f506e030f15108e83bc182095032c0d8000a1f31a2f8964ca504ca232100473e32b160096c3d618809082f80bc000a1ecbb2fe1630a504c7238102075233f16809b841e1a709c832c0e0000a1e6792ee95b8a164b222b0fb071832d16209543e017e09082fc0be000a1e0112fe9660a6a4ca22f900072832b163098440619909e83300e4000a1d9d22ee15e0a224ad2228fb870031d15b095c3f218609183200be000a1d3aa2eb15c0a204a72210f746e431615809303ec19a09b032c0d2000a1cd6f2ed15b8a164ad2288fbc716320161896c3e219609603200c6000a1c7202f61600a344b822d8fe06fe322161096c40419b09503180bc000a1c0d52f41604a2e4b22280fb070e32215e09343b817b09583080aa000a1bab42df95749dc4902128f2c6ce30d15389143d219209583100b4000a1b4642f415e8a484c122e8fe0732333162898440e1a30a403500d0000a1ae0c2fa1634a444bb2268fbc70a322160094c3ec19909983100d6000a1a7da2e795d8a1a4af2228f8c712321161096c3e819b09d834c0de000a1a1942f09628a544c622e8ffc728333165096c3e619f097833c0c8000) else (if i < 99 then 0xa4c00f2ef15c4a1449e21f0f586dc315157092c3c618a09382fc0b8000a4b9be2fa962ca4c4cd2328fe472833b16609703ee19609603100d2000a4b3792f59630a504d0230900872232a160899040419c09a03480da000a4ad612d895789f04a121d8f786e230d152891c3e218c09503440cc000a4a71f2ea95aca084a82258fac70630815509283dc18f09103080c6000a4a0f22e8959ca124a521e0f586dc30c15689503d618b09383200d0000a49a902f9964ca664c32308fc871e33a16c09f84241ae0a703840e2000a4941030d96d4aa44ed249909074e33716909dc40819f09e83280d6000a48dcc2ed95d4a1c4a32200fb072232016009783f219709903480ce000a4878c2f195eca2e4b822f8fd073033416189943ec19609a03440e6000a481412f89640a4e4cb2338ff071832416089443de18209102f80b6000a47adc2fb164ca484bb2268f9070432616089383d818809403080c0000a474902f21608a284c322b0fbc71c33116409b040e19b09903280de000a46e592ea15c8a184a72208f7c6f030b15b89503d018a09603340da000a468122ee15c4a224ad2240f846f032315d89583f218809483440ca000a461c42f81604a444ba2288fb871231a15c895c3e818e09603340d2000a45b882f015dca164a321b8f8470431815c092c3e219009783180c0000a455362f9963ca5c4ca2348ff473c328166899c406195096835c0d6000a44eef2ee15d4a1e4b02248f9870e32b16409983f018f098031c0d8000a4489f2f61644a5c4c022e0fbc71e32015d09743f019509883580d4000a4424d2f71640a544c122b0f9c71e32b16109743e818208c02d40b0000a43c002f415e8a244b522a0fd872032715c092c3d418509283040c2000a435be2f51618a464c1230100073233a16609d44141a609b02f80c2000a42f6c2f79628a564be22e0fe872c332166899c40219109b03280de000a4291f2f095cca2a4ab2220f546da30e15088f43c818509183180d2000a422d82ef15f8a1a49b21f8f706f431a15689703e218709383240ca000a41c842f8961ca524c722f8fc472832316189ac40619309283240d0000a4160d3051680a664d8231100073a33b16d89d840e1a709903480d6000a40fce2f215f8a444bf2310fcc70c32c16009d041a19f09b83200d0000a409a22ea95b0a124a021d8f7870032315a093c3e619009683340ce000a403462fd1654a564c02318fdc71832f16089983f419809e83400e2000a3fcee2f5960ca3c4b422a0f9471032d16909943fe19c09d83500d6000a3f67a306969ca864de239905075434316e09ec4241a30a083440d8000a3f02d2f29600a3a4ba2310fc873233016389703f419b09b83400d8000a3e9dc2f79618a584cc230900072833816609ac40418f09a83580dc000a3e3812fd9678a864d4236901c74434616a098c3e4191099832c0d6000a3dd1d30916b4a844e8241107077234d16e09dc4301a609a83540da000a3d6dc2ec15b8a2a4ba22a8fdc72633516889ac3fc19009603200c4000a3d0673041664a4a4bb22a8fb870831c15b894c3d618e09202f80b6000a3ca252f0160ca4c4bf2280f746f031c15d09583e618e09603480d8000a3c3ff2e11588a0049d2190f446f631d15909503e618d09883280c6000a3bd9a3011680a744d3236902474e34016a09943f619b09c032c0d4000a3b7752de95909fc49e2200f4c6d830815188f03c818009002f40be000a3b1102f79600a3c4c022d8ff872c33116009743fa1a809e034c0d4000a3aacd2f39608a304b022a0f9470e32115d09543f219409c03300da000a3a4a82de15a49f049b21b8f786e631515588f83c417d08a82d00b0000a39e7a2e1156c9fa4a021b0f486de30114f88d039017709383180cc000a3981e2fb9620a564c12290fcc72c32b16789803ea19109303480d8000a391d82ee15e4a244a32218f9c70e31d15e09583e018e09b83400ca000a38b842f9163ca404b822a8fb8710319156893c3d218e09a03280c2000a385562e695aca224ae2278f686f030d15389083e018d09683040ae000a37f252e7959c9f849b21d0f5c6ee315158895c3f419409603340c8000a378d02f815f4a304b02270fa06ee316162099840619e09883380d4000a372822f51610a324b12208f7c6f631515689203d418d09383380c2000a36c0e3059690a7e4e0237102c74233716709b04181a00a303740da000a365e42e795b8a1049d2180f286ca2fd15589603ea19909a03140ce000a35f9a2f59608a464c12308fec71e31a15e09503f819b09b83380bc000a3594d2f89620a3a4c4230100873233316489903ee19609883340d0000a353082f11610a2e4af2270f7c6f631015809483e018d09183380d2000a34cb82f51614a4a4c622f900472e32a16309a440819b09b83300c0000a346502fe166ca724ce2370fe072633616409643ee19309483580d2000a340112e915c4a1e4a92200f746e430c15308f03bc18208902fc0ae000a339b12fd1658a4c4c322c0ffc74633816d89a84061a609f83600cc000a333752e895e4a324ad2230fb470e33016309683f419209803440c8000 else 0xa50bf400000000000002308ff072a32a16489803e018909002e00a8000a5059a2fa164ca4a4b822c101474e33816709ac40c1a109a83500ca000a4ff2a3041650a664cf235901873433316309543ee19709803180d4000a4f8f42e915fca504c22340fe872432816909904061a109883100de000a4f28e2fd1648a544c222e0fec74033316089703e618409103180b0000a4ec2d2fb165ca564c52300fe8738331168097c40a19809803300d4000a4e5d82f61628a584c822e901073a333164898840c19d09e83540d4000a4df7a2f99630a5c4ca235101073833316789a43fa19209b03380c6000a4d92f2f015b8a224ac2288fd471432516309803fc19d09c03440d4000a4d2fd2e515d4a284b42318fe472232b160895c3e018d09282f00c8000a4cc9d3011678a784d9238904474834216e89cc42a1a60a003480cc000a4c6502f495fca4a4b62268f8c71032615c095c3da18909003040b4000)))))))

private def checkpoint (i : ℕ) : ℕ :=
  let word := (packet (i/1024) >>> (232*((i%1024)/16))) % (2^232)
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



private theorem b88470 : covered 88470 88569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88569 : covered 88569 88668 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88668 : covered 88668 88767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88767 : covered 88767 88867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88867 : covered 88867 88966 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b88966 : covered 88966 89065 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89065 : covered 89065 89164 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89164 : covered 89164 89263 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89263 : covered 89263 89362 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89362 : covered 89362 89461 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89461 : covered 89461 89560 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89560 : covered 89560 89660 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89660 : covered 89660 89759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89759 : covered 89759 89858 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89858 : covered 89858 89957 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b89957 : covered 89957 90057 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90057 : covered 90057 90156 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90156 : covered 90156 90255 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90255 : covered 90255 90354 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90354 : covered 90354 90454 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90454 : covered 90454 90553 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90553 : covered 90553 90652 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90652 : covered 90652 90751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90751 : covered 90751 90850 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90850 : covered 90850 90949 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b90949 : covered 90949 91048 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91048 : covered 91048 91147 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91147 : covered 91147 91247 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91247 : covered 91247 91346 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91346 : covered 91346 91445 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91445 : covered 91445 91544 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91544 : covered 91544 91644 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91644 : covered 91644 91743 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91743 : covered 91743 91842 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91842 : covered 91842 91941 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b91941 : covered 91941 92041 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92041 : covered 92041 92140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92140 : covered 92140 92239 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92239 : covered 92239 92338 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92338 : covered 92338 92437 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92437 : covered 92437 92536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92536 : covered 92536 92635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92635 : covered 92635 92734 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92734 : covered 92734 92834 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92834 : covered 92834 92933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b92933 : covered 92933 93032 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93032 : covered 93032 93131 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93131 : covered 93131 93231 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93231 : covered 93231 93330 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93330 : covered 93330 93429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93429 : covered 93429 93528 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93528 : covered 93528 93628 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93628 : covered 93628 93727 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93727 : covered 93727 93826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93826 : covered 93826 93925 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b93925 : covered 93925 94024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94024 : covered 94024 94123 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94123 : covered 94123 94222 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94222 : covered 94222 94321 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94321 : covered 94321 94421 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94421 : covered 94421 94520 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94520 : covered 94520 94619 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94619 : covered 94619 94718 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94718 : covered 94718 94818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94818 : covered 94818 94917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b94917 : covered 94917 95016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95016 : covered 95016 95115 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95115 : covered 95115 95215 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95215 : covered 95215 95314 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95314 : covered 95314 95413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95413 : covered 95413 95512 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95512 : covered 95512 95611 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95611 : covered 95611 95710 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95710 : covered 95710 95809 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95809 : covered 95809 95908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b95908 : covered 95908 96008 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96008 : covered 96008 96107 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96107 : covered 96107 96206 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96206 : covered 96206 96305 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96305 : covered 96305 96405 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96405 : covered 96405 96504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96504 : covered 96504 96603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96603 : covered 96603 96702 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96702 : covered 96702 96802 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96802 : covered 96802 96901 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b96901 : covered 96901 97000 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97000 : covered 97000 97099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97099 : covered 97099 97198 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97198 : covered 97198 97297 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97297 : covered 97297 97396 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97396 : covered 97396 97495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97495 : covered 97495 97595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97595 : covered 97595 97694 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97694 : covered 97694 97793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97793 : covered 97793 97892 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97892 : covered 97892 97992 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b97992 : covered 97992 98091 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98091 : covered 98091 98190 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98190 : covered 98190 98289 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98289 : covered 98289 98389 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98389 : covered 98389 98488 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98488 : covered 98488 98587 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98587 : covered 98587 98686 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98686 : covered 98686 98785 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98785 : covered 98785 98884 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98884 : covered 98884 98983 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b98983 : covered 98983 99082 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99082 : covered 99082 99182 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99182 : covered 99182 99281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99281 : covered 99281 99380 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99380 : covered 99380 99479 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99479 : covered 99479 99579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99579 : covered 99579 99678 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99678 : covered 99678 99777 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99777 : covered 99777 99876 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99876 : covered 99876 99976 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b99976 : covered 99976 100075 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100075 : covered 100075 100174 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100174 : covered 100174 100273 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100273 : covered 100273 100372 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100372 : covered 100372 100471 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100471 : covered 100471 100570 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100570 : covered 100570 100669 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100669 : covered 100669 100769 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100769 : covered 100769 100868 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100868 : covered 100868 100967 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b100967 : covered 100967 101066 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101066 : covered 101066 101166 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101166 : covered 101166 101265 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101265 : covered 101265 101364 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101364 : covered 101364 101463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b101463 : covered 101463 101563 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 88470 101563 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b88470 b88569) (joinCoverage b88668 b88767)) (joinCoverage (joinCoverage b88867 b88966) (joinCoverage b89065 b89164))) (joinCoverage (joinCoverage (joinCoverage b89263 b89362) (joinCoverage b89461 b89560)) (joinCoverage (joinCoverage b89660 b89759) (joinCoverage b89858 b89957)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b90057 b90156) (joinCoverage b90255 b90354)) (joinCoverage (joinCoverage b90454 b90553) (joinCoverage b90652 b90751))) (joinCoverage (joinCoverage (joinCoverage b90850 b90949) (joinCoverage b91048 b91147)) (joinCoverage (joinCoverage b91247 b91346) (joinCoverage b91445 (joinCoverage b91544 b91644)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b91743 b91842) (joinCoverage b91941 b92041)) (joinCoverage (joinCoverage b92140 b92239) (joinCoverage b92338 b92437))) (joinCoverage (joinCoverage (joinCoverage b92536 b92635) (joinCoverage b92734 b92834)) (joinCoverage (joinCoverage b92933 b93032) (joinCoverage b93131 b93231)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b93330 b93429) (joinCoverage b93528 b93628)) (joinCoverage (joinCoverage b93727 b93826) (joinCoverage b93925 b94024))) (joinCoverage (joinCoverage (joinCoverage b94123 b94222) (joinCoverage b94321 b94421)) (joinCoverage (joinCoverage b94520 b94619) (joinCoverage b94718 (joinCoverage b94818 b94917))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b95016 b95115) (joinCoverage b95215 b95314)) (joinCoverage (joinCoverage b95413 b95512) (joinCoverage b95611 b95710))) (joinCoverage (joinCoverage (joinCoverage b95809 b95908) (joinCoverage b96008 b96107)) (joinCoverage (joinCoverage b96206 b96305) (joinCoverage b96405 b96504)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b96603 b96702) (joinCoverage b96802 b96901)) (joinCoverage (joinCoverage b97000 b97099) (joinCoverage b97198 b97297))) (joinCoverage (joinCoverage (joinCoverage b97396 b97495) (joinCoverage b97595 b97694)) (joinCoverage (joinCoverage b97793 b97892) (joinCoverage b97992 (joinCoverage b98091 b98190)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b98289 b98389) (joinCoverage b98488 b98587)) (joinCoverage (joinCoverage b98686 b98785) (joinCoverage b98884 b98983))) (joinCoverage (joinCoverage (joinCoverage b99082 b99182) (joinCoverage b99281 b99380)) (joinCoverage (joinCoverage b99479 b99579) (joinCoverage b99678 b99777)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b99876 b99976) (joinCoverage b100075 b100174)) (joinCoverage (joinCoverage b100273 b100372) (joinCoverage b100471 b100570))) (joinCoverage (joinCoverage (joinCoverage b100669 b100769) (joinCoverage b100868 b100967)) (joinCoverage (joinCoverage b101066 b101166) (joinCoverage b101265 (joinCoverage b101364 b101463))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 88470 ≤ index 170000000/512 := by decide +kernel
private theorem starting_value : fast 170000000=9503083 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 170000000=9503083) (n : ℕ) (low : 170000000≤n) (bound : n≤195000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=170000000
    · rw [first,anchor]
      exact starting_value
    · have past : 170000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤195000000 by omega)
        have within : index n / 512 < 101563 := by omega
        have lower : index 170000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤195000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ170000000To195000000
