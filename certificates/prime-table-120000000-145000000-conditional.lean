import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ120000000To145000000

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




private def radical : ℕ := 0x15799eadfb0bd4973123357e93c64a183d4d3b3c7e9cae7f032369ccbe3ef959e7638a25c445686b89b22774c743f74781ea1c5f84e32c09d875122ebda88125fdec7fef9283347f49218499d0d65567d160557bd74415e5a09d8993152e865d955a754de0f973eec6679129c19b49fc97227f315c2ab4c82d1facd09aa80cb61920066ae7c53372b991d8809694963c1fc205a71d9f0de90feb4de454376f4ccaff01a75a47825613499a185802ceb9216b94666709da8a60a9a594ee16fed4bb0aca16c5b6c6a37fb69bbadeb47c2f860bfacd4bd6c3eaa48acc41de3409db05580b6298ab21dfe38170fb04aad67171a69ddd4226a225be5446ee627cae5e94c4d8fd989e2da4a273242e6a1e2a94a65f85b8f51b04850b36da8016904fe687f2d6dae99184917030b83c1ebee1e616416c33d1fe9c181be5e479b5a29b9af4b2d22596ff095ee98f73ff4556012c17270ba71c4a6cbf40377e183c443f60dd9c63204868f05c634b047ae125d22ef660a25963ed9b10c9e11cc1506a39d4e6d66c8a4f621f489b371187fa21ee932bcc597c4b52e870ec6b516fcbe82f475374c416a38853b10e2288c4c6b8379e8bf642756128cf0bf06b646f9107972ed1c2d197a64cefcba849262b7f566962235e40a013b4f2e006fb9e45ed7e1cc9978dd2094d7d43837d252ac3b5257da1ed5933e1c7215646e2d62b6a2b3535e840cfba06ae57f43ff4aa7b352c31897ce14d776a937feae96e45106769e671ec8870634548a74aedd88b7ac8d6c72f85f05330ace408f4df1a949d64db8417066aa4e35210a09b4ef1d500e36b606eb72bcacd7308296c9a189b3f84209a37457ab916dae771e770d70ce2dc1a48ab840b05a6df8b08eef0e5be3c6b5e4b11317797a4b6b8238aadb19bdd96197279e0aa0c305a953e566c2e9c7ea560fce3c3c10fa683235241f4c92eb0c8bda2585d5a5171e22cba01322409b7def641476a4a228eb8d02d150c1b852fd85c718d43f22189e8da973854f78ba56a9b8ea32f0195925d428d44443b5a3645a564a16d0a9568ddb7f9d25014943962ce0638bd9860b548f930092572b2cdda20107180ca1306f9dce5f3521969fd73cd5a6741f52a8004f29837562d24a0ffedfef6bac5cb319909676ddc8dc611474e1b438d3f9f2957047698658ad12d834313c8e2a4d718e7ceda942340cbae5320fc3b7cc2fa0d43037d8df3285f35cc40b14cbce7037de7e37b4a92c5fd36155eba83ca908f5d58d0cc56892d30e29b99f508b050a0db5f35716e51bee7cc3d357623590f828741615394c6030e5832f1b3063ebb81d6788eda41540bd197cb96e66bcdbd4aedaacb0645809b311fa6938f5ac6fa12f3d22646302211035d035e6236f8ad3cb086a9c9e164172b9ff7aaaf9f8f323d7ec9308897d806d54897676f810352a7a7510177ae090f19adaf75e24c6c88e33df947d21fef05035c971096328e5f04f67056fdf5400dc7bd21549da28ec4f7a38f8d2f82a06feb52a09832ff2bfec7c9d5bd68ed5e4502880af05e6dd9e157bca63cce25de56566323bdd3362bcda0791f3a7e40a3fe9a79163f9067d84896ccd4317e37072f54039154b0d4054a9564e0cc917d71bbbef95020d2379d0c55dafff2ea9f224a5ce2b358fc40c21d36943ff9208f93bbbb97bc762e027ef578f6b2e1afda7091948df8220108f30c7c6a221b10e2dd2a7e54f821ef486d1965500920e1d074ae3e172b21b4d8265302370cbd51aa84cb4d3bf6c08619fe7f590dd97ccb560e886d08d912fcd70ec69e544b37341d847e0853b865354d83f4afba80ffbd45016d13e78d82d27ed97d3150a6de2421945b9814f79f7a5f9b13b66a8bc32db27c311796d76d9a1cda000a78ea779ec753e5c71e386783f4f54ab7e3788970507a65792f5870f194cf2d02733a0dfcc362a38b20beef0b5eda90d69f63925962bc6d41dd1829a4a8fdd496c70d321feea27cfa6191b7493fdb0aaf26bed03f13a7ff690cebe6edb5342012dc4f35241c5fab7350972e4610e83af838f26c7d3eb5d3c5124370b91ae955725d0c66db3cbee856a464502ecdebe0d696fe8f2dcae665c11be77fe451c9b559dac974ac57bb4aa570a5792e6996d5bcc63a4ea63de62a1768255998d686c19dc925b3a8679baa8d5ca415c2d07fa7877e6a41204aae1c5f8ace9d607badaefcf25c57eaaf019615d8831b99f89b956dd003d48eceab204cb7c0a37f788dbe4e7654978d8bcacec4cd99f5ac4ecb90dc91023da9ef30acc8493a1e8607e16058916d675d8636c31b19d2eb47b96d12466207b7308635fc529671a6455195b95827f09b5add92a24120564af8e8baf5391694530afa1747a39388de653331d2816fb9742651a57011f5f97adfaa8c3da20687409d3477c7b76f524e7361f6008b99e0296ecd4439346408d43796b0f574ba6c83a8eb044fbb7a2ef736fa3a74806263c968fd85c7d765d78152f304a8a2f40e82f1b2f4215d496efd23213e1466c0f798e438e75507c8b04c59b33990230b68a80e64c962b26df8995c84ed4db143710ab24df36d48adad00dd4c45a1ce9b7e08f6eb3a833cdd9c9e137b47c7107e5cf5f971f66cfc1ed3545cfc12191ac80668af6d42ce7e0c7abdf75c8ede6a0c1ce5b4bbb9d19c5003940a46a22cc727a69375aea996091b8743aa727298c7a47225d5b8a310740fa1c22e4f7328350a9e827650f00919359448367c67604a80d603e39f5b06d214b6650dd8f4c1742692e1fe0d4b8fada38981a18b3582dfd4b265fe0273e9088a376b05c43892c72bd195fb64dbfb0ee5ced1c987c79de9b7aa4e421cbba32cbf743c1ac8d23eebbde39765da44cb42d8a52e62bb2e2e9553e7bab082974c12cc9f6b64d73b10dca6e4ca86e620ef09e4aded3c68f60f7ac8584042fe6aeb413c2e7162e9bf155e046ef98f21c37a72836497250510c680418e0d6dde49a7816899da250db8aece6b1d11e3b80bf2ea206805f42

private def light (n : ℕ) : Bool :=
  if n≤109 then decide n.Prime else n.gcd 144385958320249358220488210246279753379312820313396029159834075622223337844983482099636001195615259277084033387619818092804737714758384244334160217374720000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤12041) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 109 = 144385958320249358220488210246279753379312820313396029159834075622223337844983482099636001195615259277084033387619818092804737714758384244334160217374720000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 109 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤12041 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 47 := by unfold smallValid; decide +kernel

private theorem sp47 : smallValid 47 47 := by unfold smallValid; decide +kernel

private theorem sp94 : smallValid 94 47 := by unfold smallValid; decide +kernel

private theorem sp141 : smallValid 141 47 := by unfold smallValid; decide +kernel

private theorem sp188 : smallValid 188 47 := by unfold smallValid; decide +kernel

private theorem sp235 : smallValid 235 47 := by unfold smallValid; decide +kernel

private theorem sp282 : smallValid 282 47 := by unfold smallValid; decide +kernel

private theorem sp329 : smallValid 329 47 := by unfold smallValid; decide +kernel

private theorem sp376 : smallValid 376 47 := by unfold smallValid; decide +kernel

private theorem sp423 : smallValid 423 47 := by unfold smallValid; decide +kernel

private theorem sp470 : smallValid 470 47 := by unfold smallValid; decide +kernel

private theorem sp517 : smallValid 517 47 := by unfold smallValid; decide +kernel

private theorem sp564 : smallValid 564 47 := by unfold smallValid; decide +kernel

private theorem sp611 : smallValid 611 47 := by unfold smallValid; decide +kernel

private theorem sp658 : smallValid 658 47 := by unfold smallValid; decide +kernel

private theorem sp705 : smallValid 705 47 := by unfold smallValid; decide +kernel

private theorem sp752 : smallValid 752 47 := by unfold smallValid; decide +kernel

private theorem sp799 : smallValid 799 47 := by unfold smallValid; decide +kernel

private theorem sp846 : smallValid 846 47 := by unfold smallValid; decide +kernel

private theorem sp893 : smallValid 893 47 := by unfold smallValid; decide +kernel

private theorem sp940 : smallValid 940 47 := by unfold smallValid; decide +kernel

private theorem sp987 : smallValid 987 47 := by unfold smallValid; decide +kernel

private theorem sp1034 : smallValid 1034 47 := by unfold smallValid; decide +kernel

private theorem sp1081 : smallValid 1081 47 := by unfold smallValid; decide +kernel

private theorem sp1128 : smallValid 1128 47 := by unfold smallValid; decide +kernel

private theorem sp1175 : smallValid 1175 47 := by unfold smallValid; decide +kernel

private theorem sp1222 : smallValid 1222 47 := by unfold smallValid; decide +kernel

private theorem sp1269 : smallValid 1269 47 := by unfold smallValid; decide +kernel

private theorem sp1316 : smallValid 1316 47 := by unfold smallValid; decide +kernel

private theorem sp1363 : smallValid 1363 47 := by unfold smallValid; decide +kernel

private theorem sp1410 : smallValid 1410 47 := by unfold smallValid; decide +kernel

private theorem sp1457 : smallValid 1457 48 := by unfold smallValid; decide +kernel

private theorem sp1505 : smallValid 1505 47 := by unfold smallValid; decide +kernel

private theorem sp1552 : smallValid 1552 47 := by unfold smallValid; decide +kernel

private theorem sp1599 : smallValid 1599 47 := by unfold smallValid; decide +kernel

private theorem sp1646 : smallValid 1646 47 := by unfold smallValid; decide +kernel

private theorem sp1693 : smallValid 1693 47 := by unfold smallValid; decide +kernel

private theorem sp1740 : smallValid 1740 47 := by unfold smallValid; decide +kernel

private theorem sp1787 : smallValid 1787 47 := by unfold smallValid; decide +kernel

private theorem sp1834 : smallValid 1834 47 := by unfold smallValid; decide +kernel

private theorem sp1881 : smallValid 1881 47 := by unfold smallValid; decide +kernel

private theorem sp1928 : smallValid 1928 47 := by unfold smallValid; decide +kernel

private theorem sp1975 : smallValid 1975 47 := by unfold smallValid; decide +kernel

private theorem sp2022 : smallValid 2022 47 := by unfold smallValid; decide +kernel

private theorem sp2069 : smallValid 2069 47 := by unfold smallValid; decide +kernel

private theorem sp2116 : smallValid 2116 47 := by unfold smallValid; decide +kernel

private theorem sp2163 : smallValid 2163 47 := by unfold smallValid; decide +kernel

private theorem sp2210 : smallValid 2210 47 := by unfold smallValid; decide +kernel

private theorem sp2257 : smallValid 2257 47 := by unfold smallValid; decide +kernel

private theorem sp2304 : smallValid 2304 47 := by unfold smallValid; decide +kernel

private theorem sp2351 : smallValid 2351 47 := by unfold smallValid; decide +kernel

private theorem sp2398 : smallValid 2398 47 := by unfold smallValid; decide +kernel

private theorem sp2445 : smallValid 2445 47 := by unfold smallValid; decide +kernel

private theorem sp2492 : smallValid 2492 47 := by unfold smallValid; decide +kernel

private theorem sp2539 : smallValid 2539 47 := by unfold smallValid; decide +kernel

private theorem sp2586 : smallValid 2586 47 := by unfold smallValid; decide +kernel

private theorem sp2633 : smallValid 2633 47 := by unfold smallValid; decide +kernel

private theorem sp2680 : smallValid 2680 47 := by unfold smallValid; decide +kernel

private theorem sp2727 : smallValid 2727 47 := by unfold smallValid; decide +kernel

private theorem sp2774 : smallValid 2774 47 := by unfold smallValid; decide +kernel

private theorem sp2821 : smallValid 2821 47 := by unfold smallValid; decide +kernel

private theorem sp2868 : smallValid 2868 47 := by unfold smallValid; decide +kernel

private theorem sp2915 : smallValid 2915 47 := by unfold smallValid; decide +kernel

private theorem sp2962 : smallValid 2962 48 := by unfold smallValid; decide +kernel

private theorem sp3010 : smallValid 3010 47 := by unfold smallValid; decide +kernel

private theorem sp3057 : smallValid 3057 47 := by unfold smallValid; decide +kernel

private theorem sp3104 : smallValid 3104 47 := by unfold smallValid; decide +kernel

private theorem sp3151 : smallValid 3151 47 := by unfold smallValid; decide +kernel

private theorem sp3198 : smallValid 3198 47 := by unfold smallValid; decide +kernel

private theorem sp3245 : smallValid 3245 47 := by unfold smallValid; decide +kernel

private theorem sp3292 : smallValid 3292 47 := by unfold smallValid; decide +kernel

private theorem sp3339 : smallValid 3339 47 := by unfold smallValid; decide +kernel

private theorem sp3386 : smallValid 3386 47 := by unfold smallValid; decide +kernel

private theorem sp3433 : smallValid 3433 47 := by unfold smallValid; decide +kernel

private theorem sp3480 : smallValid 3480 47 := by unfold smallValid; decide +kernel

private theorem sp3527 : smallValid 3527 47 := by unfold smallValid; decide +kernel

private theorem sp3574 : smallValid 3574 47 := by unfold smallValid; decide +kernel

private theorem sp3621 : smallValid 3621 47 := by unfold smallValid; decide +kernel

private theorem sp3668 : smallValid 3668 47 := by unfold smallValid; decide +kernel

private theorem sp3715 : smallValid 3715 47 := by unfold smallValid; decide +kernel

private theorem sp3762 : smallValid 3762 47 := by unfold smallValid; decide +kernel

private theorem sp3809 : smallValid 3809 47 := by unfold smallValid; decide +kernel

private theorem sp3856 : smallValid 3856 47 := by unfold smallValid; decide +kernel

private theorem sp3903 : smallValid 3903 47 := by unfold smallValid; decide +kernel

private theorem sp3950 : smallValid 3950 47 := by unfold smallValid; decide +kernel

private theorem sp3997 : smallValid 3997 47 := by unfold smallValid; decide +kernel

private theorem sp4044 : smallValid 4044 47 := by unfold smallValid; decide +kernel

private theorem sp4091 : smallValid 4091 47 := by unfold smallValid; decide +kernel

private theorem sp4138 : smallValid 4138 47 := by unfold smallValid; decide +kernel

private theorem sp4185 : smallValid 4185 47 := by unfold smallValid; decide +kernel

private theorem sp4232 : smallValid 4232 47 := by unfold smallValid; decide +kernel

private theorem sp4279 : smallValid 4279 47 := by unfold smallValid; decide +kernel

private theorem sp4326 : smallValid 4326 47 := by unfold smallValid; decide +kernel

private theorem sp4373 : smallValid 4373 47 := by unfold smallValid; decide +kernel

private theorem sp4420 : smallValid 4420 47 := by unfold smallValid; decide +kernel

private theorem sp4467 : smallValid 4467 48 := by unfold smallValid; decide +kernel

private theorem sp4515 : smallValid 4515 47 := by unfold smallValid; decide +kernel

private theorem sp4562 : smallValid 4562 47 := by unfold smallValid; decide +kernel

private theorem sp4609 : smallValid 4609 47 := by unfold smallValid; decide +kernel

private theorem sp4656 : smallValid 4656 47 := by unfold smallValid; decide +kernel

private theorem sp4703 : smallValid 4703 47 := by unfold smallValid; decide +kernel

private theorem sp4750 : smallValid 4750 47 := by unfold smallValid; decide +kernel

private theorem sp4797 : smallValid 4797 47 := by unfold smallValid; decide +kernel

private theorem sp4844 : smallValid 4844 47 := by unfold smallValid; decide +kernel

private theorem sp4891 : smallValid 4891 47 := by unfold smallValid; decide +kernel

private theorem sp4938 : smallValid 4938 47 := by unfold smallValid; decide +kernel

private theorem sp4985 : smallValid 4985 47 := by unfold smallValid; decide +kernel

private theorem sp5032 : smallValid 5032 47 := by unfold smallValid; decide +kernel

private theorem sp5079 : smallValid 5079 47 := by unfold smallValid; decide +kernel

private theorem sp5126 : smallValid 5126 47 := by unfold smallValid; decide +kernel

private theorem sp5173 : smallValid 5173 47 := by unfold smallValid; decide +kernel

private theorem sp5220 : smallValid 5220 48 := by unfold smallValid; decide +kernel

private theorem sp5268 : smallValid 5268 47 := by unfold smallValid; decide +kernel

private theorem sp5315 : smallValid 5315 47 := by unfold smallValid; decide +kernel

private theorem sp5362 : smallValid 5362 47 := by unfold smallValid; decide +kernel

private theorem sp5409 : smallValid 5409 47 := by unfold smallValid; decide +kernel

private theorem sp5456 : smallValid 5456 47 := by unfold smallValid; decide +kernel

private theorem sp5503 : smallValid 5503 47 := by unfold smallValid; decide +kernel

private theorem sp5550 : smallValid 5550 47 := by unfold smallValid; decide +kernel

private theorem sp5597 : smallValid 5597 47 := by unfold smallValid; decide +kernel

private theorem sp5644 : smallValid 5644 47 := by unfold smallValid; decide +kernel

private theorem sp5691 : smallValid 5691 47 := by unfold smallValid; decide +kernel

private theorem sp5738 : smallValid 5738 47 := by unfold smallValid; decide +kernel

private theorem sp5785 : smallValid 5785 47 := by unfold smallValid; decide +kernel

private theorem sp5832 : smallValid 5832 47 := by unfold smallValid; decide +kernel

private theorem sp5879 : smallValid 5879 47 := by unfold smallValid; decide +kernel

private theorem sp5926 : smallValid 5926 47 := by unfold smallValid; decide +kernel

private theorem sp5973 : smallValid 5973 48 := by unfold smallValid; decide +kernel

private theorem sp6021 : smallValid 6021 47 := by unfold smallValid; decide +kernel

private theorem sp6068 : smallValid 6068 47 := by unfold smallValid; decide +kernel

private theorem sp6115 : smallValid 6115 47 := by unfold smallValid; decide +kernel

private theorem sp6162 : smallValid 6162 47 := by unfold smallValid; decide +kernel

private theorem sp6209 : smallValid 6209 47 := by unfold smallValid; decide +kernel

private theorem sp6256 : smallValid 6256 47 := by unfold smallValid; decide +kernel

private theorem sp6303 : smallValid 6303 47 := by unfold smallValid; decide +kernel

private theorem sp6350 : smallValid 6350 47 := by unfold smallValid; decide +kernel

private theorem sp6397 : smallValid 6397 47 := by unfold smallValid; decide +kernel

private theorem sp6444 : smallValid 6444 47 := by unfold smallValid; decide +kernel

private theorem sp6491 : smallValid 6491 47 := by unfold smallValid; decide +kernel

private theorem sp6538 : smallValid 6538 47 := by unfold smallValid; decide +kernel

private theorem sp6585 : smallValid 6585 47 := by unfold smallValid; decide +kernel

private theorem sp6632 : smallValid 6632 47 := by unfold smallValid; decide +kernel

private theorem sp6679 : smallValid 6679 47 := by unfold smallValid; decide +kernel

private theorem sp6726 : smallValid 6726 47 := by unfold smallValid; decide +kernel

private theorem sp6773 : smallValid 6773 47 := by unfold smallValid; decide +kernel

private theorem sp6820 : smallValid 6820 47 := by unfold smallValid; decide +kernel

private theorem sp6867 : smallValid 6867 47 := by unfold smallValid; decide +kernel

private theorem sp6914 : smallValid 6914 47 := by unfold smallValid; decide +kernel

private theorem sp6961 : smallValid 6961 47 := by unfold smallValid; decide +kernel

private theorem sp7008 : smallValid 7008 47 := by unfold smallValid; decide +kernel

private theorem sp7055 : smallValid 7055 47 := by unfold smallValid; decide +kernel

private theorem sp7102 : smallValid 7102 47 := by unfold smallValid; decide +kernel

private theorem sp7149 : smallValid 7149 47 := by unfold smallValid; decide +kernel

private theorem sp7196 : smallValid 7196 47 := by unfold smallValid; decide +kernel

private theorem sp7243 : smallValid 7243 47 := by unfold smallValid; decide +kernel

private theorem sp7290 : smallValid 7290 47 := by unfold smallValid; decide +kernel

private theorem sp7337 : smallValid 7337 47 := by unfold smallValid; decide +kernel

private theorem sp7384 : smallValid 7384 47 := by unfold smallValid; decide +kernel

private theorem sp7431 : smallValid 7431 47 := by unfold smallValid; decide +kernel

private theorem sp7478 : smallValid 7478 48 := by unfold smallValid; decide +kernel

private theorem sp7526 : smallValid 7526 47 := by unfold smallValid; decide +kernel

private theorem sp7573 : smallValid 7573 47 := by unfold smallValid; decide +kernel

private theorem sp7620 : smallValid 7620 47 := by unfold smallValid; decide +kernel

private theorem sp7667 : smallValid 7667 47 := by unfold smallValid; decide +kernel

private theorem sp7714 : smallValid 7714 47 := by unfold smallValid; decide +kernel

private theorem sp7761 : smallValid 7761 47 := by unfold smallValid; decide +kernel

private theorem sp7808 : smallValid 7808 47 := by unfold smallValid; decide +kernel

private theorem sp7855 : smallValid 7855 47 := by unfold smallValid; decide +kernel

private theorem sp7902 : smallValid 7902 47 := by unfold smallValid; decide +kernel

private theorem sp7949 : smallValid 7949 47 := by unfold smallValid; decide +kernel

private theorem sp7996 : smallValid 7996 47 := by unfold smallValid; decide +kernel

private theorem sp8043 : smallValid 8043 47 := by unfold smallValid; decide +kernel

private theorem sp8090 : smallValid 8090 47 := by unfold smallValid; decide +kernel

private theorem sp8137 : smallValid 8137 47 := by unfold smallValid; decide +kernel

private theorem sp8184 : smallValid 8184 47 := by unfold smallValid; decide +kernel

private theorem sp8231 : smallValid 8231 47 := by unfold smallValid; decide +kernel

private theorem sp8278 : smallValid 8278 47 := by unfold smallValid; decide +kernel

private theorem sp8325 : smallValid 8325 47 := by unfold smallValid; decide +kernel

private theorem sp8372 : smallValid 8372 47 := by unfold smallValid; decide +kernel

private theorem sp8419 : smallValid 8419 47 := by unfold smallValid; decide +kernel

private theorem sp8466 : smallValid 8466 47 := by unfold smallValid; decide +kernel

private theorem sp8513 : smallValid 8513 47 := by unfold smallValid; decide +kernel

private theorem sp8560 : smallValid 8560 47 := by unfold smallValid; decide +kernel

private theorem sp8607 : smallValid 8607 47 := by unfold smallValid; decide +kernel

private theorem sp8654 : smallValid 8654 47 := by unfold smallValid; decide +kernel

private theorem sp8701 : smallValid 8701 47 := by unfold smallValid; decide +kernel

private theorem sp8748 : smallValid 8748 47 := by unfold smallValid; decide +kernel

private theorem sp8795 : smallValid 8795 47 := by unfold smallValid; decide +kernel

private theorem sp8842 : smallValid 8842 47 := by unfold smallValid; decide +kernel

private theorem sp8889 : smallValid 8889 47 := by unfold smallValid; decide +kernel

private theorem sp8936 : smallValid 8936 47 := by unfold smallValid; decide +kernel

private theorem sp8983 : smallValid 8983 48 := by unfold smallValid; decide +kernel

private theorem sp9031 : smallValid 9031 47 := by unfold smallValid; decide +kernel

private theorem sp9078 : smallValid 9078 47 := by unfold smallValid; decide +kernel

private theorem sp9125 : smallValid 9125 47 := by unfold smallValid; decide +kernel

private theorem sp9172 : smallValid 9172 47 := by unfold smallValid; decide +kernel

private theorem sp9219 : smallValid 9219 47 := by unfold smallValid; decide +kernel

private theorem sp9266 : smallValid 9266 47 := by unfold smallValid; decide +kernel

private theorem sp9313 : smallValid 9313 47 := by unfold smallValid; decide +kernel

private theorem sp9360 : smallValid 9360 47 := by unfold smallValid; decide +kernel

private theorem sp9407 : smallValid 9407 47 := by unfold smallValid; decide +kernel

private theorem sp9454 : smallValid 9454 47 := by unfold smallValid; decide +kernel

private theorem sp9501 : smallValid 9501 47 := by unfold smallValid; decide +kernel

private theorem sp9548 : smallValid 9548 47 := by unfold smallValid; decide +kernel

private theorem sp9595 : smallValid 9595 47 := by unfold smallValid; decide +kernel

private theorem sp9642 : smallValid 9642 47 := by unfold smallValid; decide +kernel

private theorem sp9689 : smallValid 9689 47 := by unfold smallValid; decide +kernel

private theorem sp9736 : smallValid 9736 47 := by unfold smallValid; decide +kernel

private theorem sp9783 : smallValid 9783 47 := by unfold smallValid; decide +kernel

private theorem sp9830 : smallValid 9830 47 := by unfold smallValid; decide +kernel

private theorem sp9877 : smallValid 9877 47 := by unfold smallValid; decide +kernel

private theorem sp9924 : smallValid 9924 47 := by unfold smallValid; decide +kernel

private theorem sp9971 : smallValid 9971 47 := by unfold smallValid; decide +kernel

private theorem sp10018 : smallValid 10018 47 := by unfold smallValid; decide +kernel

private theorem sp10065 : smallValid 10065 47 := by unfold smallValid; decide +kernel

private theorem sp10112 : smallValid 10112 47 := by unfold smallValid; decide +kernel

private theorem sp10159 : smallValid 10159 47 := by unfold smallValid; decide +kernel

private theorem sp10206 : smallValid 10206 47 := by unfold smallValid; decide +kernel

private theorem sp10253 : smallValid 10253 47 := by unfold smallValid; decide +kernel

private theorem sp10300 : smallValid 10300 47 := by unfold smallValid; decide +kernel

private theorem sp10347 : smallValid 10347 47 := by unfold smallValid; decide +kernel

private theorem sp10394 : smallValid 10394 47 := by unfold smallValid; decide +kernel

private theorem sp10441 : smallValid 10441 47 := by unfold smallValid; decide +kernel

private theorem sp10488 : smallValid 10488 48 := by unfold smallValid; decide +kernel

private theorem sp10536 : smallValid 10536 47 := by unfold smallValid; decide +kernel

private theorem sp10583 : smallValid 10583 47 := by unfold smallValid; decide +kernel

private theorem sp10630 : smallValid 10630 47 := by unfold smallValid; decide +kernel

private theorem sp10677 : smallValid 10677 47 := by unfold smallValid; decide +kernel

private theorem sp10724 : smallValid 10724 47 := by unfold smallValid; decide +kernel

private theorem sp10771 : smallValid 10771 47 := by unfold smallValid; decide +kernel

private theorem sp10818 : smallValid 10818 47 := by unfold smallValid; decide +kernel

private theorem sp10865 : smallValid 10865 47 := by unfold smallValid; decide +kernel

private theorem sp10912 : smallValid 10912 47 := by unfold smallValid; decide +kernel

private theorem sp10959 : smallValid 10959 47 := by unfold smallValid; decide +kernel

private theorem sp11006 : smallValid 11006 47 := by unfold smallValid; decide +kernel

private theorem sp11053 : smallValid 11053 47 := by unfold smallValid; decide +kernel

private theorem sp11100 : smallValid 11100 47 := by unfold smallValid; decide +kernel

private theorem sp11147 : smallValid 11147 47 := by unfold smallValid; decide +kernel

private theorem sp11194 : smallValid 11194 47 := by unfold smallValid; decide +kernel

private theorem sp11241 : smallValid 11241 48 := by unfold smallValid; decide +kernel

private theorem sp11289 : smallValid 11289 47 := by unfold smallValid; decide +kernel

private theorem sp11336 : smallValid 11336 47 := by unfold smallValid; decide +kernel

private theorem sp11383 : smallValid 11383 47 := by unfold smallValid; decide +kernel

private theorem sp11430 : smallValid 11430 47 := by unfold smallValid; decide +kernel

private theorem sp11477 : smallValid 11477 47 := by unfold smallValid; decide +kernel

private theorem sp11524 : smallValid 11524 47 := by unfold smallValid; decide +kernel

private theorem sp11571 : smallValid 11571 47 := by unfold smallValid; decide +kernel

private theorem sp11618 : smallValid 11618 47 := by unfold smallValid; decide +kernel

private theorem sp11665 : smallValid 11665 47 := by unfold smallValid; decide +kernel

private theorem sp11712 : smallValid 11712 47 := by unfold smallValid; decide +kernel

private theorem sp11759 : smallValid 11759 47 := by unfold smallValid; decide +kernel

private theorem sp11806 : smallValid 11806 47 := by unfold smallValid; decide +kernel

private theorem sp11853 : smallValid 11853 47 := by unfold smallValid; decide +kernel

private theorem sp11900 : smallValid 11900 47 := by unfold smallValid; decide +kernel

private theorem sp11947 : smallValid 11947 47 := by unfold smallValid; decide +kernel

private theorem sp11994 : smallValid 11994 48 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤12041) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 12042 := (joinSmall (lo:=0) (a:=6021) (b:=6021) (joinSmall (lo:=0) (a:=3010) (b:=3011) (joinSmall (lo:=0) (a:=1505) (b:=1505) (joinSmall (lo:=0) (a:=752) (b:=753) (joinSmall (lo:=0) (a:=376) (b:=376) (joinSmall (lo:=0) (a:=188) (b:=188) (joinSmall (lo:=0) (a:=94) (b:=94) (joinSmall (lo:=0) (a:=47) (b:=47) sp0 sp47) (joinSmall (lo:=94) (a:=47) (b:=47) sp94 sp141)) (joinSmall (lo:=188) (a:=94) (b:=94) (joinSmall (lo:=188) (a:=47) (b:=47) sp188 sp235) (joinSmall (lo:=282) (a:=47) (b:=47) sp282 sp329))) (joinSmall (lo:=376) (a:=188) (b:=188) (joinSmall (lo:=376) (a:=94) (b:=94) (joinSmall (lo:=376) (a:=47) (b:=47) sp376 sp423) (joinSmall (lo:=470) (a:=47) (b:=47) sp470 sp517)) (joinSmall (lo:=564) (a:=94) (b:=94) (joinSmall (lo:=564) (a:=47) (b:=47) sp564 sp611) (joinSmall (lo:=658) (a:=47) (b:=47) sp658 sp705)))) (joinSmall (lo:=752) (a:=376) (b:=377) (joinSmall (lo:=752) (a:=188) (b:=188) (joinSmall (lo:=752) (a:=94) (b:=94) (joinSmall (lo:=752) (a:=47) (b:=47) sp752 sp799) (joinSmall (lo:=846) (a:=47) (b:=47) sp846 sp893)) (joinSmall (lo:=940) (a:=94) (b:=94) (joinSmall (lo:=940) (a:=47) (b:=47) sp940 sp987) (joinSmall (lo:=1034) (a:=47) (b:=47) sp1034 sp1081))) (joinSmall (lo:=1128) (a:=188) (b:=189) (joinSmall (lo:=1128) (a:=94) (b:=94) (joinSmall (lo:=1128) (a:=47) (b:=47) sp1128 sp1175) (joinSmall (lo:=1222) (a:=47) (b:=47) sp1222 sp1269)) (joinSmall (lo:=1316) (a:=94) (b:=95) (joinSmall (lo:=1316) (a:=47) (b:=47) sp1316 sp1363) (joinSmall (lo:=1410) (a:=47) (b:=48) sp1410 sp1457))))) (joinSmall (lo:=1505) (a:=752) (b:=753) (joinSmall (lo:=1505) (a:=376) (b:=376) (joinSmall (lo:=1505) (a:=188) (b:=188) (joinSmall (lo:=1505) (a:=94) (b:=94) (joinSmall (lo:=1505) (a:=47) (b:=47) sp1505 sp1552) (joinSmall (lo:=1599) (a:=47) (b:=47) sp1599 sp1646)) (joinSmall (lo:=1693) (a:=94) (b:=94) (joinSmall (lo:=1693) (a:=47) (b:=47) sp1693 sp1740) (joinSmall (lo:=1787) (a:=47) (b:=47) sp1787 sp1834))) (joinSmall (lo:=1881) (a:=188) (b:=188) (joinSmall (lo:=1881) (a:=94) (b:=94) (joinSmall (lo:=1881) (a:=47) (b:=47) sp1881 sp1928) (joinSmall (lo:=1975) (a:=47) (b:=47) sp1975 sp2022)) (joinSmall (lo:=2069) (a:=94) (b:=94) (joinSmall (lo:=2069) (a:=47) (b:=47) sp2069 sp2116) (joinSmall (lo:=2163) (a:=47) (b:=47) sp2163 sp2210)))) (joinSmall (lo:=2257) (a:=376) (b:=377) (joinSmall (lo:=2257) (a:=188) (b:=188) (joinSmall (lo:=2257) (a:=94) (b:=94) (joinSmall (lo:=2257) (a:=47) (b:=47) sp2257 sp2304) (joinSmall (lo:=2351) (a:=47) (b:=47) sp2351 sp2398)) (joinSmall (lo:=2445) (a:=94) (b:=94) (joinSmall (lo:=2445) (a:=47) (b:=47) sp2445 sp2492) (joinSmall (lo:=2539) (a:=47) (b:=47) sp2539 sp2586))) (joinSmall (lo:=2633) (a:=188) (b:=189) (joinSmall (lo:=2633) (a:=94) (b:=94) (joinSmall (lo:=2633) (a:=47) (b:=47) sp2633 sp2680) (joinSmall (lo:=2727) (a:=47) (b:=47) sp2727 sp2774)) (joinSmall (lo:=2821) (a:=94) (b:=95) (joinSmall (lo:=2821) (a:=47) (b:=47) sp2821 sp2868) (joinSmall (lo:=2915) (a:=47) (b:=48) sp2915 sp2962)))))) (joinSmall (lo:=3010) (a:=1505) (b:=1506) (joinSmall (lo:=3010) (a:=752) (b:=753) (joinSmall (lo:=3010) (a:=376) (b:=376) (joinSmall (lo:=3010) (a:=188) (b:=188) (joinSmall (lo:=3010) (a:=94) (b:=94) (joinSmall (lo:=3010) (a:=47) (b:=47) sp3010 sp3057) (joinSmall (lo:=3104) (a:=47) (b:=47) sp3104 sp3151)) (joinSmall (lo:=3198) (a:=94) (b:=94) (joinSmall (lo:=3198) (a:=47) (b:=47) sp3198 sp3245) (joinSmall (lo:=3292) (a:=47) (b:=47) sp3292 sp3339))) (joinSmall (lo:=3386) (a:=188) (b:=188) (joinSmall (lo:=3386) (a:=94) (b:=94) (joinSmall (lo:=3386) (a:=47) (b:=47) sp3386 sp3433) (joinSmall (lo:=3480) (a:=47) (b:=47) sp3480 sp3527)) (joinSmall (lo:=3574) (a:=94) (b:=94) (joinSmall (lo:=3574) (a:=47) (b:=47) sp3574 sp3621) (joinSmall (lo:=3668) (a:=47) (b:=47) sp3668 sp3715)))) (joinSmall (lo:=3762) (a:=376) (b:=377) (joinSmall (lo:=3762) (a:=188) (b:=188) (joinSmall (lo:=3762) (a:=94) (b:=94) (joinSmall (lo:=3762) (a:=47) (b:=47) sp3762 sp3809) (joinSmall (lo:=3856) (a:=47) (b:=47) sp3856 sp3903)) (joinSmall (lo:=3950) (a:=94) (b:=94) (joinSmall (lo:=3950) (a:=47) (b:=47) sp3950 sp3997) (joinSmall (lo:=4044) (a:=47) (b:=47) sp4044 sp4091))) (joinSmall (lo:=4138) (a:=188) (b:=189) (joinSmall (lo:=4138) (a:=94) (b:=94) (joinSmall (lo:=4138) (a:=47) (b:=47) sp4138 sp4185) (joinSmall (lo:=4232) (a:=47) (b:=47) sp4232 sp4279)) (joinSmall (lo:=4326) (a:=94) (b:=95) (joinSmall (lo:=4326) (a:=47) (b:=47) sp4326 sp4373) (joinSmall (lo:=4420) (a:=47) (b:=48) sp4420 sp4467))))) (joinSmall (lo:=4515) (a:=753) (b:=753) (joinSmall (lo:=4515) (a:=376) (b:=377) (joinSmall (lo:=4515) (a:=188) (b:=188) (joinSmall (lo:=4515) (a:=94) (b:=94) (joinSmall (lo:=4515) (a:=47) (b:=47) sp4515 sp4562) (joinSmall (lo:=4609) (a:=47) (b:=47) sp4609 sp4656)) (joinSmall (lo:=4703) (a:=94) (b:=94) (joinSmall (lo:=4703) (a:=47) (b:=47) sp4703 sp4750) (joinSmall (lo:=4797) (a:=47) (b:=47) sp4797 sp4844))) (joinSmall (lo:=4891) (a:=188) (b:=189) (joinSmall (lo:=4891) (a:=94) (b:=94) (joinSmall (lo:=4891) (a:=47) (b:=47) sp4891 sp4938) (joinSmall (lo:=4985) (a:=47) (b:=47) sp4985 sp5032)) (joinSmall (lo:=5079) (a:=94) (b:=95) (joinSmall (lo:=5079) (a:=47) (b:=47) sp5079 sp5126) (joinSmall (lo:=5173) (a:=47) (b:=48) sp5173 sp5220)))) (joinSmall (lo:=5268) (a:=376) (b:=377) (joinSmall (lo:=5268) (a:=188) (b:=188) (joinSmall (lo:=5268) (a:=94) (b:=94) (joinSmall (lo:=5268) (a:=47) (b:=47) sp5268 sp5315) (joinSmall (lo:=5362) (a:=47) (b:=47) sp5362 sp5409)) (joinSmall (lo:=5456) (a:=94) (b:=94) (joinSmall (lo:=5456) (a:=47) (b:=47) sp5456 sp5503) (joinSmall (lo:=5550) (a:=47) (b:=47) sp5550 sp5597))) (joinSmall (lo:=5644) (a:=188) (b:=189) (joinSmall (lo:=5644) (a:=94) (b:=94) (joinSmall (lo:=5644) (a:=47) (b:=47) sp5644 sp5691) (joinSmall (lo:=5738) (a:=47) (b:=47) sp5738 sp5785)) (joinSmall (lo:=5832) (a:=94) (b:=95) (joinSmall (lo:=5832) (a:=47) (b:=47) sp5832 sp5879) (joinSmall (lo:=5926) (a:=47) (b:=48) sp5926 sp5973))))))) (joinSmall (lo:=6021) (a:=3010) (b:=3011) (joinSmall (lo:=6021) (a:=1505) (b:=1505) (joinSmall (lo:=6021) (a:=752) (b:=753) (joinSmall (lo:=6021) (a:=376) (b:=376) (joinSmall (lo:=6021) (a:=188) (b:=188) (joinSmall (lo:=6021) (a:=94) (b:=94) (joinSmall (lo:=6021) (a:=47) (b:=47) sp6021 sp6068) (joinSmall (lo:=6115) (a:=47) (b:=47) sp6115 sp6162)) (joinSmall (lo:=6209) (a:=94) (b:=94) (joinSmall (lo:=6209) (a:=47) (b:=47) sp6209 sp6256) (joinSmall (lo:=6303) (a:=47) (b:=47) sp6303 sp6350))) (joinSmall (lo:=6397) (a:=188) (b:=188) (joinSmall (lo:=6397) (a:=94) (b:=94) (joinSmall (lo:=6397) (a:=47) (b:=47) sp6397 sp6444) (joinSmall (lo:=6491) (a:=47) (b:=47) sp6491 sp6538)) (joinSmall (lo:=6585) (a:=94) (b:=94) (joinSmall (lo:=6585) (a:=47) (b:=47) sp6585 sp6632) (joinSmall (lo:=6679) (a:=47) (b:=47) sp6679 sp6726)))) (joinSmall (lo:=6773) (a:=376) (b:=377) (joinSmall (lo:=6773) (a:=188) (b:=188) (joinSmall (lo:=6773) (a:=94) (b:=94) (joinSmall (lo:=6773) (a:=47) (b:=47) sp6773 sp6820) (joinSmall (lo:=6867) (a:=47) (b:=47) sp6867 sp6914)) (joinSmall (lo:=6961) (a:=94) (b:=94) (joinSmall (lo:=6961) (a:=47) (b:=47) sp6961 sp7008) (joinSmall (lo:=7055) (a:=47) (b:=47) sp7055 sp7102))) (joinSmall (lo:=7149) (a:=188) (b:=189) (joinSmall (lo:=7149) (a:=94) (b:=94) (joinSmall (lo:=7149) (a:=47) (b:=47) sp7149 sp7196) (joinSmall (lo:=7243) (a:=47) (b:=47) sp7243 sp7290)) (joinSmall (lo:=7337) (a:=94) (b:=95) (joinSmall (lo:=7337) (a:=47) (b:=47) sp7337 sp7384) (joinSmall (lo:=7431) (a:=47) (b:=48) sp7431 sp7478))))) (joinSmall (lo:=7526) (a:=752) (b:=753) (joinSmall (lo:=7526) (a:=376) (b:=376) (joinSmall (lo:=7526) (a:=188) (b:=188) (joinSmall (lo:=7526) (a:=94) (b:=94) (joinSmall (lo:=7526) (a:=47) (b:=47) sp7526 sp7573) (joinSmall (lo:=7620) (a:=47) (b:=47) sp7620 sp7667)) (joinSmall (lo:=7714) (a:=94) (b:=94) (joinSmall (lo:=7714) (a:=47) (b:=47) sp7714 sp7761) (joinSmall (lo:=7808) (a:=47) (b:=47) sp7808 sp7855))) (joinSmall (lo:=7902) (a:=188) (b:=188) (joinSmall (lo:=7902) (a:=94) (b:=94) (joinSmall (lo:=7902) (a:=47) (b:=47) sp7902 sp7949) (joinSmall (lo:=7996) (a:=47) (b:=47) sp7996 sp8043)) (joinSmall (lo:=8090) (a:=94) (b:=94) (joinSmall (lo:=8090) (a:=47) (b:=47) sp8090 sp8137) (joinSmall (lo:=8184) (a:=47) (b:=47) sp8184 sp8231)))) (joinSmall (lo:=8278) (a:=376) (b:=377) (joinSmall (lo:=8278) (a:=188) (b:=188) (joinSmall (lo:=8278) (a:=94) (b:=94) (joinSmall (lo:=8278) (a:=47) (b:=47) sp8278 sp8325) (joinSmall (lo:=8372) (a:=47) (b:=47) sp8372 sp8419)) (joinSmall (lo:=8466) (a:=94) (b:=94) (joinSmall (lo:=8466) (a:=47) (b:=47) sp8466 sp8513) (joinSmall (lo:=8560) (a:=47) (b:=47) sp8560 sp8607))) (joinSmall (lo:=8654) (a:=188) (b:=189) (joinSmall (lo:=8654) (a:=94) (b:=94) (joinSmall (lo:=8654) (a:=47) (b:=47) sp8654 sp8701) (joinSmall (lo:=8748) (a:=47) (b:=47) sp8748 sp8795)) (joinSmall (lo:=8842) (a:=94) (b:=95) (joinSmall (lo:=8842) (a:=47) (b:=47) sp8842 sp8889) (joinSmall (lo:=8936) (a:=47) (b:=48) sp8936 sp8983)))))) (joinSmall (lo:=9031) (a:=1505) (b:=1506) (joinSmall (lo:=9031) (a:=752) (b:=753) (joinSmall (lo:=9031) (a:=376) (b:=376) (joinSmall (lo:=9031) (a:=188) (b:=188) (joinSmall (lo:=9031) (a:=94) (b:=94) (joinSmall (lo:=9031) (a:=47) (b:=47) sp9031 sp9078) (joinSmall (lo:=9125) (a:=47) (b:=47) sp9125 sp9172)) (joinSmall (lo:=9219) (a:=94) (b:=94) (joinSmall (lo:=9219) (a:=47) (b:=47) sp9219 sp9266) (joinSmall (lo:=9313) (a:=47) (b:=47) sp9313 sp9360))) (joinSmall (lo:=9407) (a:=188) (b:=188) (joinSmall (lo:=9407) (a:=94) (b:=94) (joinSmall (lo:=9407) (a:=47) (b:=47) sp9407 sp9454) (joinSmall (lo:=9501) (a:=47) (b:=47) sp9501 sp9548)) (joinSmall (lo:=9595) (a:=94) (b:=94) (joinSmall (lo:=9595) (a:=47) (b:=47) sp9595 sp9642) (joinSmall (lo:=9689) (a:=47) (b:=47) sp9689 sp9736)))) (joinSmall (lo:=9783) (a:=376) (b:=377) (joinSmall (lo:=9783) (a:=188) (b:=188) (joinSmall (lo:=9783) (a:=94) (b:=94) (joinSmall (lo:=9783) (a:=47) (b:=47) sp9783 sp9830) (joinSmall (lo:=9877) (a:=47) (b:=47) sp9877 sp9924)) (joinSmall (lo:=9971) (a:=94) (b:=94) (joinSmall (lo:=9971) (a:=47) (b:=47) sp9971 sp10018) (joinSmall (lo:=10065) (a:=47) (b:=47) sp10065 sp10112))) (joinSmall (lo:=10159) (a:=188) (b:=189) (joinSmall (lo:=10159) (a:=94) (b:=94) (joinSmall (lo:=10159) (a:=47) (b:=47) sp10159 sp10206) (joinSmall (lo:=10253) (a:=47) (b:=47) sp10253 sp10300)) (joinSmall (lo:=10347) (a:=94) (b:=95) (joinSmall (lo:=10347) (a:=47) (b:=47) sp10347 sp10394) (joinSmall (lo:=10441) (a:=47) (b:=48) sp10441 sp10488))))) (joinSmall (lo:=10536) (a:=753) (b:=753) (joinSmall (lo:=10536) (a:=376) (b:=377) (joinSmall (lo:=10536) (a:=188) (b:=188) (joinSmall (lo:=10536) (a:=94) (b:=94) (joinSmall (lo:=10536) (a:=47) (b:=47) sp10536 sp10583) (joinSmall (lo:=10630) (a:=47) (b:=47) sp10630 sp10677)) (joinSmall (lo:=10724) (a:=94) (b:=94) (joinSmall (lo:=10724) (a:=47) (b:=47) sp10724 sp10771) (joinSmall (lo:=10818) (a:=47) (b:=47) sp10818 sp10865))) (joinSmall (lo:=10912) (a:=188) (b:=189) (joinSmall (lo:=10912) (a:=94) (b:=94) (joinSmall (lo:=10912) (a:=47) (b:=47) sp10912 sp10959) (joinSmall (lo:=11006) (a:=47) (b:=47) sp11006 sp11053)) (joinSmall (lo:=11100) (a:=94) (b:=95) (joinSmall (lo:=11100) (a:=47) (b:=47) sp11100 sp11147) (joinSmall (lo:=11194) (a:=47) (b:=48) sp11194 sp11241)))) (joinSmall (lo:=11289) (a:=376) (b:=377) (joinSmall (lo:=11289) (a:=188) (b:=188) (joinSmall (lo:=11289) (a:=94) (b:=94) (joinSmall (lo:=11289) (a:=47) (b:=47) sp11289 sp11336) (joinSmall (lo:=11383) (a:=47) (b:=47) sp11383 sp11430)) (joinSmall (lo:=11477) (a:=94) (b:=94) (joinSmall (lo:=11477) (a:=47) (b:=47) sp11477 sp11524) (joinSmall (lo:=11571) (a:=47) (b:=47) sp11571 sp11618))) (joinSmall (lo:=11665) (a:=188) (b:=189) (joinSmall (lo:=11665) (a:=94) (b:=94) (joinSmall (lo:=11665) (a:=47) (b:=47) sp11665 sp11712) (joinSmall (lo:=11759) (a:=47) (b:=47) sp11759 sp11806)) (joinSmall (lo:=11853) (a:=94) (b:=95) (joinSmall (lo:=11853) (a:=47) (b:=47) sp11853 sp11900) (joinSmall (lo:=11947) (a:=47) (b:=48) sp11947 sp11994))))))))
  have good : (List.range 12042).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 145000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 12041 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 12041 := by
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


private def packet (i : ℕ) : ℕ := (if i < 37 then (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else (if i < 8 then 0 else 0)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0 else 0) else (if i < 12 then 0 else 0)) else (if i < 15 then (if i < 14 then 0 else 0) else (if i < 16 then 0 else (if i < 17 then 0 else 0))))) else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then 0 else 0) else (if i < 21 then 0 else 0)) else (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else (if i < 26 then 0 else 0)))) else (if i < 32 then (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else (if i < 31 then 0 else 0))) else (if i < 34 then (if i < 33 then 0 else 0) else (if i < 35 then 0 else (if i < 36 then 0 else 0)))))) else (if i < 55 then (if i < 46 then (if i < 41 then (if i < 39 then (if i < 38 then 0 else 0) else (if i < 40 then 0 else 0)) else (if i < 43 then (if i < 42 then 0 else 0) else (if i < 44 then 0 else (if i < 45 then 0 else 0)))) else (if i < 50 then (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else 0)) else (if i < 52 then (if i < 51 then 0 else 0) else (if i < 53 then 0 else (if i < 54 then 0 else 0))))) else (if i < 64 then (if i < 59 then (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else 0)) else (if i < 61 then (if i < 60 then 0 else 0) else (if i < 62 then 0x69ec7a31016cca924e523d104475634416e89c441219a09603200bc00069e5f330e96f0a964f2244106076e34b1768a0c42a1af0a1833c0ca00069df873069684a744da23f10a476c34e16f89d442c1a309c03240ba00069d9552ed15d8a1c4b22240f906fa31a15989303ca18408f03100c200069d2ce30e96d8aa24e223b903476434716c09c841619a09b033c0ce00069cc4931416e0aa64f5245907076a3531730a084381b50a503600ee00069c5c431016e8ab44e623a0ffc72e332162897c3f419009783240d200069bf672f495fca484be22d8ff472032716189803f6194097031c0ca00069b93a2e115909ea48f2160f5c6d8309151890c3b818209282f80ae00069b2c33069668a684d7239903874e33716789a83fc19709783380e000069ac0d32717b4afa51325010dc7a236e17a8a244181a109d83340ba00069a5ba2f415f8a2a4b02278fa06f2313159091c3d017d09082f80b8000699f582fd1668a6e4c72310fe472032f15d09543d218509183100c00006998e7305169ca8a4ed244106c75c33c16b09d04261ac09c83400d000069924831e974cad250425090bc79635917489e84201a109d03240dc000698bc730816aca8c4e223f904876634e1760a0042a19b09803140d600069857e2f51600a524d32371020736324160897c3f418708f82ec0d0000697f232fb9654a704ce2310fa471832c16809843ec19609e83440c600069786932917a4b1451e258111c7ae36917e0a604461ad09d83540d40006972442dd15549e249221a0f486ee31215989783f419409603180bc000696bc530796a4a904d923e102474833316609d04281b30a8039c0d20006965732f41620a5a4cc234103073e33c16589603ea18c09482f40be000695efa30796d4a7e4e023d109877034716b89d84261ae09f833c0c600069587b30a96a8a804d3234101872c32d167898c40019d09b03540dc0006952222f81608a3e4c022b0f9c6f8319158094c3e218c097830c0c4000694b9331096fcabe4fe24d90a078234a16e89d041a1a709e036c0dc00069451630d96bca904e023d105875233d16c89ac3f819409503180c4000693e9f30696aca8c4da23b102c726327165097c3f419409783240c00006937f631a9700ac24ef246109077435017109e041c1a709c83400da000693159313170caae4f4248908c77435317a0a3c4541ba0a303880ec000692ae630296a0a824dd23d101873e3351700a144301ae0a6839c0e000069247f30896a8a7c4d923d106076434c1740a2444e1b60a3834c0d8000691e0430a16a0a8a4dd23c904073e3491710a004381ae09f83640da00069177c31296ecab24ee242108076a34617489e041a1a80a203740d2000691117301964ca664c522d8fb0716325160891c3c617e08d02f809a000690ad82ec15d8a264b22270fb46f831b15c094c3e8196095032c0e200069048a2f115f4a184b42280fbc6f8321161094c3e819409903280cc00068fe1a3071678a5e4c622f100873233616909e441e19c09a83100ca00068f7cc2ee9608a384b42268fb472433016c09f441e1a809f836c0da00068f14e30996b8a864d7236900073233d16989ac40019509903240cc00068eadb3059660a704dc236900873832c16509a041019e09b83300c400068e46030916a4a964e023c103875e34516d89b041219609983280d200068ddf130596aca824d22368ff4738334166096c3fc19d09483000c400068d7a12f015fca444af22b8ffc73033516489a03f619e09a83480c600068d11830b1688a7e4dd23d901c75633816689883ec19b09b03300ce00068cabd2fd1624a4e4c222d100874832f162898c40019e09a83300c400068c44930c16a8a8e4e323e905875c3481758a004461b00a303640e200068bdca30d16c0a824e723c107876634717209dc41419a097031c0dc00068b74f30b9700ac450124890b07803581738a1c4441b30a1834c0d000068b0ee3009668a544d12320ff072e332162097440219909c03380e000068aa922f99620a324c1235101c74634317109e04201a80a3836c0e400068a45b2e99598a084a221b0f786f031915a09403c618109803340ba000689dfc3001680a644cc2348fb070e31d15c89343ea18e09503280c600068977d31296fca9a4e323d105475435717609d441a1a209c83400ce0006890ef31216e8a8c4e2242104c74c33b163897c40819c0a003580de000688a6b3149724abe4f1245909877434816e89dc41619709b03200d00006884142f4961ca444b82240fa86fc30f15989443d018609603200d8000687dae2ff1694a744d0239104075634316e89a43fa19009683340d60006877463031688a884dc236901c74434316a89cc4181a209d83500d000068709f31c9740ad050624e10c07723501768a0842e1b60a203800ea000686a1530c16a0a6e4dc239103473c34517209ec40419b09803180d600068639230a9690a844e7242904875034b16f899c40219b09403300c8000685d1730796a0a984db23a903473433916889bc40c19a09b830c0ba00068569e30d96d8a984ea24710a079436717b0a3c4441b70a803740da000 else (if i < 63 then 0x6b89072fa163ca484c922d8fd472032516189743ec18909102c40ba0006b82993079680a6e4cb233100073232815e095c3ee19209403000ac0006b7c1230f16bcaa44ec23f103875234d16e09d841c1a3099032c0c80006b759130e96c4a944e0240106475234716f09c840e1a009b831c0ca0006b6f1330996d8aa64f1241905c75433c16789f04201a509f03480c40006b689d30b16a4a724db23b105074a34916f89f44201ac09f83500e40006b622330b96d0a824e123c101072833a169097c3e819609583280c80006b5bd32f315e8a124ac2288fc072a33116b09e04181ae0a103700d80006b553931b9724ad4502246908076e34516a09983fe19a09803080c80006b4ec13051670a7a4e223d104875234a17309f44201a20a083540ea0006b48503061670a844e3242903c77034e1770a104241ad0a383640da0006b41f92f79630a3a4ba22a0fc071432f163895c3dc18909603100b40006b3ba32f89624a3c4c32338ff873033616889ac40e1af0a183600ce0006b351c30e16dcaa64ef24a10c878835e17289d442c1a209d036c0e40006b2eb13019654a5c4cc2371024754336160899c3f819c09b03300c80006b282631316d4a8c4d9238102475633a16c89c040419709b83400d00006b21b43069668a664c9232900873032b15f896c3e218c09203280cc0006b1b692f215eca364a621f8f806f8321164097440419d09d83380ca0006b14e430a16a4a704d023490487683471700a004361b50a703700da0006b0e543151704ab44f3242904475c33d16889b440219c09783200c60006b07e32fd966ca804dc239101072a32b16689943f619309303240cc0006b016231416f4aa64dc237901873c33e163098c4161ab0a683900e20006afaee3029690a744d723b903475033816509903fa19209383000b40006af47e30796c0a884e523e105076633c17009f04321a80a0834c0c60006aee0130b16bca764d623c905476234816e89cc4001a409983540d20006ae76a31616fcab64f5244908476434617209f84121b20a203900ea0006ae1182f69644a584c7232900c73433a166097c3fe19409a83280d20006adad42f61634a644d22318fc070631515989303c418308c82f40be0006ad44930f16cca9e4e3241907c77435217489c441a1aa09a83200d00006acdf52f89650a5a4ca2338fe071633016689d44141a309c83440ca0006ac7aa2f39618a424b32278fc873a33116b897c3ec19509583200da0006ac13230c16dca8e4e8240104475a34616c09c84241a309b83400d80006abaa930f96fcabe4f9245106876a34817089f44321aa097833c0c00006ab43330b16e0aa04e7240903c76433f17089703e819309983300d20006aada630f16e4a9e4ee248106c76634516e09f44161a70a0033c0c80006aa7342ff1640a624c42300fd873433c16d09c83e618c09283040c00006aa09831f1780ae250c24a10bc78634d16e89b44061a809a03480d00006a9a2130c96cca9e4ed24110707683501738a104361ab0a203680d40006a93db2f115eca1e4aa2258f9c6ee31115709243e818c09283000d20006a8d4e31416d8aac4e823d902c74833316909b440e19c09803480da0006a86c63129704aa44ed245107877434d17309e84181a20a4838c0da0006a803531516e8a8c4de238106075a34f17109b4410199097032c0ca0006a79d82fa1608a264b822b0fe873033816b89a0402196091830c0c20006a735930b1690a944df244103c76e34c16d09b840a1a409c03780da0006a6d182f215f4a344b82270fb4702323164097c3ee19109603200ce0006a66c32f8161ca2c4b82278f9871231b15f89683f219f09d83280cc0006a604231116e8aa44ef243107c7683491770a204461bc0a8037c0e20006a59f92f4960ca5c4d12328ff473833e16d09d840c19b09983400d40006a538f2ff1678a7a4d823a101074e34516d89f84261a809e834c0d20006a4d342f81640a4a4cb2338ff072632b16309643e619d09503280cc0006a46aa31016d8aaa4f624690ac78a35817289d841a1ab0a1035c0ca0006a407a2e61598a284b32290fc473c33416f0984400199097831c0c20006a3a0130516b0a864d6239901875434216e09c84341a409d032c0c00006a337b30916a4aa44e5244907c75c34516d09a04021a309a83540d60006a2d0d2fc964ca5e4c622d0ff471a32a15e09843e419409a037c0e40006a26a52fb963ca4a4b522b8fd8724328162097c3f218508f82ec0b80006a20502f61630a5c4ce2331010722330164098c3f6199095030c0ca0006a19c73161708ab44f1246108c77634717309f04381b40a403600d20006a136a300165ca744d3237900473433316709883fa19909903140c80006a0ce730a9694a584d7238902c75034e17489e841c1a709c03500d20006a06633121708aa24e0239104475833d166899c41219f09d83540c600069ffd73109720aa84d823a902474234316e09f841819d09983380cc00069f9753019688a744d4235903074234116909903f819b09803400d200069f3003019660a584ce2308ff472232015e09583f418d09703040ba000 else 0x6d2552303969ca864dc23c104075033516a09ac41219a09703100d00006d1ecb30a16a8a8e4d52358fec73e33316289903fe19f09983340b80006d184730d96dca8a4d12308ff472a33015e896c3fe18c09402e40c40006d11b230d96e4ab44fa24d10b878a35a1770a184281a809983240ba0006d0b3f30a16d4a944d923b102c74c33716a09743f218a09682e80c60006d04ea2f51600a364ba2210f7070232a16109803dc18c092831c0bc0006cfe713059678a724d8239901873033616b09a840219909a03100c40006cf7f73061680a6c4d22328ff074834717189e03f619709683340c60006cf1aa2fe1640a584c72348fec71e32c16989cc402198097030c0c40006ceb652f295dca364bf22e0fd871c33016b09943fe19809d03340da0006ce4fa303967ca624cd2330fdc72e33016589843fa19a09583080be0006cde7131316b4a984d7238100c73031e15d89503fc19209a83400d20006cd8212f395fca464c32288fac71632d15e899840a19c09f03440e20006cd1b92ff1668a604bf22f901871c32f163097c3f619409603400c40006ccb2a31096d4a964e724090607803501700a144381ae0a103640dc0006cc4de2ee95e8a224b72298fb8718330167898041c1a509a03240b80006cbe4231396e0a884e5242107476234f16e89ec4181ad0a303680d60006cb7d030a16a4a904e9245908876634e17009e44161b20a983800d00006cb16e2fa963ca424b522b8fec73c33a16b09c04121a109b83700e20006caad630f16f4ab44fe24e10dc78c3581788a244501b70a383700de0006ca46c2fd1660a5a4c5230901c74633416589a040219c09903000c60006c9de431096fcaa64d7240104c75a33e16a89b43fe19909d03580d00006c97882fc962ca544c422e8fe473e32f164098041419d09983300d60006c91362f7961ca464b42280f8070c31c15d89503de18908f83140b80006c8ab730c16c4a984e123f904c75235016c09d84381af0a003700da0006c844f3021694a8a4e1237101072e33716689903e618f09403200cc0006c7ded2fd1628a364c72320ff473233416289883f619009683380c20006c7776303968ca7a4db239902074433d16c89c44041a109c03280e00006c71033079684a7c4d7236900875233316609903e619309a030c0be0006c6a8f304969ca884dc236100c72e32115909303ee19609583300ce0006c64213049680a784cc22d8fd873232515d09443ee18e09303180d60006c5da33061668a6a4db23a101072632316009783f21a209b83440da0006c573d2ff161ca444bb22f0fe871a32315d09843f219109083000c80006c50e62fa1620a564c422f8ffc74a33d16589683e619409d03380ba0006c4a6830e16c8a984dc23d106074233316d09d442a1a609d83580e00006c43ed30816a0a784d22340ff872c331161895c3e6184095030c0b60006c3d6a30e96e0aa24e023c905c78835717509e44141a009c03280de0006c36fa3039684a784d723b101c73832e164097c3e019809883240c20006c30a12f81634a4a4be2300fec74033416589884081a409f83400d20006c2a0f31396f8aa04e7241906c75433316309ac4141ac09e83680d60006c23a4300166ca644ca2358fe070632b16289583e418e09783180c20006c1d5f2f295e0a3a4b32248fb06fe32816289903ee195092831c0c80006c16f430696a8a6c4dd239906876234e17609d441c1a70a103780d60006c108c2ff167ca664c8236103c742335166096040c1a70a203380da0006c0a1d304968ca7a4d923a102073633216189a040819509882fc0ae0006c03a930996a0a844d723a907075033516d89c841e1a809a03140b20006bfd3b3031698a8c4dd23a905476833f16f09a84261ae0a103440be0006bf6da2fb9628a464bc2280ff0724332165898c40019409983580cc0006bf07a30196b0a6e4d8238902874233b16f09c441619a09383140c40006be9e9314970caa64eb23e904c73c34116a09c841419409f03340d60006be36e3089690a704cf238103475a34a16c89c84141a709e835c0d00006bdcd53159714ab44ef23e105c74a34317609f04361a209a036c0d20006bd64f317972caca4ff247108876434c17589f841e19f09e83740e60006bcfdf30716a8a864d3235902874633b167897c3fa18e09503080bc0006bc966303166ca844dc240102074c33116789a840a19909903080c80006bc3022ff963ca4a4af2230f8870232515f097c3fe19009883100d80006bbc9d3019688a644cd233100874033316b09ac3f219709883580ea0006bb64e2f415e4a084a621d8f8871232315c89703ec19209783240be0006bafe13011670a6c4d7235904075434316e09cc42419d09c83380ce0006ba94131e9768af450b25310c079636017d0a304441ab09c03480dc0006ba2e62fc9650a5a4b922a8fb870c31d159892c3d819309303080bc0006b9c60313170cabc4f0248905475633f16a09b84181ab0a0837c0e80006b95f130996a0a9a4e3240907876034117209bc4181aa0a203600d60006b8f6131316e0ab24f324710e47923641780a0842c1b70a1839c0e6000)))) else (if i < 69 then (if i < 66 then (if i < 65 then 0x6ec1162f3960ca464c52310fc872032715f89643d4182092031c0b60006ebaa730816b4a724c9236901873633216009643e819209783200c60006eb41831416fca944e123d102c77235616b89a040a19609402f40b00006ead8f31596e0a984de23b105c76435017109e04301a309e83580ce0006ea72a3021674a684ce231100472c32d16389a43f0191093830c0c20006ea0dc2fb95f8a424c122f901873234316b89e440819309282f40b40006e9a7d2f69618a4e4c8232902075034016d09c841019c09b03480d60006e941e300164ca624d4237902c74c33f16c09e84261a209d03440c60006e8db5303167ca644c9233101473033216689a44041a10a283600da0006e874d3021660a544cc2320fc472432616309643f219a09b03300da0006e80d430e16c8a8e4dc236903875634d17309f041e18f09303080d00006e7a4d31396f4aa04e923e905c75e33a16a899840619809703440d20006e73c1319971cab250024790b87923541768a2c4281a80a303740da0006e6d6f2fd166ca6a4c622f0fe470a32d165099c3f819e09e03700da0006e670d2fc9658a744e523b104073a34416f09e041419a0a003640d20006e60a33009668a664d523b904875033816789ac40e19c09c83600ca0006e5a482f8165ca5e4c7237902074433d16909a84141a409983180ca0006e53df306968ca5c4cd2328fdc72832d16a89a43fc1a709e83580d40006e4d8e2f69608a444c022c0fd471c32516289803f619409a83240e20006e47232fe1660a6a4cc2310ff473833616689a840619c09503240c40006e40c12fd164ca584cb2310fdc73833016909843dc18908b02d80c00006e3a633019684a804d32369004744339167898c40019c0a1037c0d20006e33de30d96e4aa04e5240905475c34a17089f44281a2099030c0bc0006e2d6e30196a8a844d6232902474633616589683f219009382f80ba0006e26d531816fcabc4ed241108c76c34716f09e44221a10a303980e40006e20533119708aae4e7242906876634817109cc42819709883380c60006e19e030796b8a864e1232900c73834116b09b83f819909b83280d60006e135730a96dca8c4d9237902874e34017089c44301bd0a3834c0d20006e0d122ef95e4a1a4bd2298f8471032016009603e819209183100c60006e06aa3039674a804dc239904875c34416b89c840e19f09902fc0c20006e00403001650a5e4c222f8ff075033916d89a44161a009983340d00006df9f02f195e4a364ba2298f7c6ea304150893c3e819c09402f00b60006df36630d9690a8a4da2338fe873633116289a040419e09b83400e00006ded132f8164ca5e4d02340fc870431615d09243d018608f03200be0006de6a33021634a4e4bf2288fa071232516189883fe19809a83300cc0006de02930596aca8e4dd239905c76c35116b89f44281ae09e03480d80006dd9cd2ff9654a5e4d02320ff073832e16709a040819509583180c00006dd34f30996e0aa44d8238902474633d17209c840a19b09a03200d80006dcce7300168ca7a4d72341004726330167898c41618f09303200c00006dc65531596eca944ef24610dc7a836317189f04201a50a083880d80006dbfe130596a4a7c4da239906c76034416909a04121a409783240ce0006db9802fc1628a564c122c8ff873832a16009784181a60a403980e40006db31f303967ca8c4e523c901c74633816e09d04261a309a83780de0006daca830416a4a904e823b105c75c3521710a1443e1bc0a883ac0ec0006da6462fe1664a7a4d723a902c76c3501760a1043a1b109f03280da0006d9fbf30a16b0a6c4c6230900073a33616309b44081a709b030c0c00006d9952302167ca6e4c62328fd472e330167899840619b098033c0cc0006d92e7300167ca7a4dd23b10547563481738a144241b10a203400d00006d8c6a30b16d0a9a4ef23f108077e34e17489d441c1a509983200c20006d85e7315172cabe4fd24890a078635417209fc42e1af09b836c0d20006d7fa12f1161ca404c82318ffc72633416109443de19809403340dc0006d790b3189740aca50024d10c079c35e17909ec42a1af0a2037c0dc0006d72be2f69644a5e4c522d8fdc72a32b16809a04101ac0a0034c0c40006d6c533011674a6c4cd22e0ffc72a333160897c3da18c09303200d00006d65cc30996b4ab04e223c107876234a16e09e84281a109f83480cc0006d5f54304167ca784d7235903475c34b17089e84161a709f03580e20006d58ef2ff9684a724d62360ff873833816709b840819c09c832c0de0006d52832fd9680a644c92348ff874433c16889843dc18609683380d40006d4c0230f16c4a804e323c904474233f16e09f44221aa0a503a00e80006d45783179720ab24f3243908876834217289e842c1b30a103680e20006d3f232f4961ca404bb22c8fd071a33116789783fe19709c03280ba0006d389830e96b4a884d1236103874434817089c040c19d09c83380cc0006d322d2ff164ca684d72390ffc73633115f89843dc18108e03180ca0006d2bc52fb963ca4c4bc22d0fe472232d16689883f818708e83080c2000 else 0x705d033201750ade50f25110ec79435c1780a0841e1a50a003400c800070568330e9704abe4f2248108876834a16f89d04321b30a403400e200070502a2f195e8a344a721e8f5c6de314154890c3d419009283000ba0007049b530816cca9e4ec240103475434a17009d04261b30a3037c0e200070434d3039658a4c4b622c8fd471032f162893c3de18f09983640dc000703cec2ff9684a6a4d42368ffc72832e16709943fc19609783300ce0007036813039668a644c522d0fc871c32515c09683f819809d03400c600070301b2ff9638a464b72288fc071832415f09803e418909583380c80007029ba2fe1658a584ce2338fe872a32616489843fc19d09b83380c800070232b31396e0aa64f1244906876634116709803e618b09403040c6000701cb830296aca764d2233901c74e34a17489e840419c09c83480d20007016473021660a624c7232100c74432916109743ee18c09303200d2000700fd130d16b0a864d6234100873c32a16609ac41019d09783600d600070094e30f96d0a7c4d82330ff872233316689983f419209a831c0c80007002d230896a8a964e8242108076c33f16c09dc4241aa09f83480d60006ffc6c3019660a6a4d72340ffc72c33716c89b840c1a209f83600e60006ff6132f7961ca3c4bb22f8ff072233a16789983ec19009403300c60006fef9a30896bca864e523a903875034416989e84221a109c03480d20006fe90d30e16ecab24f4248108877034e17189d440a1a70a003740dc0006fe29630c16c0a9c4dd239102474234116a099c4061a609d83500f20006fdc0f30e1730ac44fb248906475a34116c09cc41c1aa09d03340d80006fd5e92df157c9fa49321d8f446e831415709383be18708b82c80aa0006fcf7130816bca7e4d923e105475033b16a09bc41419e09b83540d80006fc9322ea15c8a204a72268f906fa31815d89683ee19209703140b20006fc2c53039694a744c4235103474e33c16909dc42419f09f837c0ec0006fbc4431416c0a9a4de23c903073232915f899c40e1a109b835c0dc0006fb5d33011644a464be2280fc472632d16689ac4161a009d032c0bc0006faf5d3061678a744e123d101c72e32816509b440819109b033c0d00006fa90d2f51614a424b72278fc071e32d165099c40419609803240c40006fa27831796e8a9e4ea24710b478635717709f842c1a509e83400d00006f9c083009668a704d5236101876033a16d09b44001a0096031c0c20006f959330916c0a884de23e906c75434417189ec4321ab09c03440d00006f8eea3171740acc4fc245907c75c35017289fc4321c40a403940e80006f887b30896a4a8a4e724190947783571768a104161a60a283600d40006f82192fd1670a844c92318fd071832316009483e618c09703180be0006f7b803161738ad450624f10b47903541780a284481ac0a1835c0d80006f751030c16aca8e4d8239905475034e17389e84261ae09d033c0d00006f6eb52fb966ca684cb2338fe871a326162897c3f419709b03380d00006f68393049688a904de240108876e34d16e89b841419d09b833c0d60006f619d3199734aac4e8241106075233516989a44141ac09c03380de0006f5b2430d96c4a924e8243108476834f16b09f84141a509b03700da0006f54b13029684a864cb235103c72a32a16589643ee19709a03180c60006f4e5b2fb9634a4e4c52320fec71c32d163896c3da19409783400ca0006f47fe301165ca4a4c7230901073233716809983f2194095832c0d60006f41923009648a5a4c722f8fd471e32d15e89603fe1a609a03380ba0006f3b2130a96b8a804d02360fe472432d164896c3e218b09503180d00006f34bc2fb1650a5e4bf2290fa0714326162096c3ee19309683140b40006f2e5d2fb9658a564c22310fec72e32d15d093c3da18d08e83040ba0006f28002f49638a5c4cb236903c74c3411740a184261af09e83300c00006f21b62ed15eca2e4b522b0fc871632915a89743e6192093030c0ba0006f1b38303167ca584c52308fe072032915f89483d818a09282f40b60006f14c030a9684a7c4de23b0fdc72c32b167899c40419c0a003700d00006f0e782ef95fca2a4a52208f8c6fe31815d09683f819f09e03480d80006f080e3001670a804d6238102c75833b16889d04221aa0a2837c0d40006f016c31f1738ad44f524810b478c35317489e442a1ac09c83480d00006efb1b2f71640a624c92318ff872a33016289603ec18d09402e40b80006ef4af3001674a6c4cc2308fc871c33116189583ea19009203100b80006eee113181724aba4f3242907878636117c8a104301a309d83500ca0006ee782316170caac4ec24410a876834d16d09cc4121a309c03100d80006ee10b30c16a4a764d32310ffc714332164099040619009803200ce0006edab02fe1658a564c422e0fdc73433616509b03f419409183340d20006ed4582fb964ca424bc2268f806f231e15689183b217c08f02fc0a20006ecdd730816c4aa04e8240904873833816809a4404196095834c0d60006ec76930696aca984ed240907c75434b16e09c84161a90a083680d0000) else (if i < 67 then 0x71f7ca3221764ada50324b10b478635d17f8a244361b30a303680c400071f14d30a16b4a884e223e905076235117509dc4141a109d83480de00071eac830e16a8a904e323b905475a34016989d44141a709b03240c800071e45e3021660a664d3232101873633a16589884061a509f03580de00071dde93081698a864dc238902475234416c09fc42219c09983200d000071d77930816a0a924da234901074633816809b440a19c09c83400ce00071d1542df156ca0e4b22230f6870631f15809183c418809483140b600071caca30a1698a7c4db238904475434416e09dc4061a409d833c0ca00071c4633041688a764d22340ffc72e32f16d09b440819e0a0834c0da00071be083029658a524cb234100473233716209683f619109483000ce00071b7a03061688a7a4e1238904874433b16d89b840219609503200aa00071b1343079688a8c4d5236101c75233416d89c84061a209b83500ca00071aa9531e9754aca503245107475a33f16c09d04081ac09a835c0e400071a42c2ff1668a5a4be2310ff472a330163898840a18b09502fc0b6000719dda2f195f8a224a321f0f6c6ea31015309743f018c093031c0c0000719767303168ca844d32330ff872c32f168898c3ea19309783180ca0007190f92fe9670a724d623a903875233316689944061a40a383840dc000718a9830496c0a9e4ef242908875234916c89c440419d09883380c40007184442f79650a4e4c32359018736332165897c3f81a109b03380ce000717dc430a96c8a8e4d6237101874433216609703f419609d03640e000071775f2f91628a3c4bb22c8fe072a32e15d09243ca18d098032c0c60007170f2308169ca744dc239906876034616d09c040c1a709e03600d2000716a6230d1690a684ca238102074434816a89f04121a209e03580ec00071640a2ff1638a404b522c0fc870631f162897c3f419609583180ca000715d7531a973caca4fb248108078235317309f84121a509b83440e40007157212f795f0a344ba2228f686e030a15489183e019009103000c40007150ad30396b8a864d82370fe872632516509583ee190097833c0d0000714a3b30516bca7a4d6238902872e331167095c3e417b09082f40b40007143a73151720ab64f4243102873033716b89e44221a509b83300ce000713d3c308967ca664ce238102074832e16489603f219c099831c0bc0007136d62fd9670a844d823d902c75c3421718a004101a80a403600e20007130772fd1628a464b12220f9471a32d16689a040019f0a003800e60007129ed3139700ac24f524790ac78835a17589f44381b50a483840dc00071237a30396a4a7c4cf2308fe870a31e15609383d418209303080be000711ce931116f8aa24e5246907c77a34817289e04381b80a6836c0f600071168d2f81640a604cb236103c74e33e17409f041e1a90a4835c0da0007110223039680a7c4d1239104075c339169099c3f2195097832c0ce00071099d30d16c0a904e123e106876e35517609f042e1aa09983540e60007103442fc1624a3a4b62240f9071632616509583e818709603280d000070fcfc2ea15f0a564bb230900474a33716509a440419e09a03240d000070f6863021664a684c622e8fc471432915c89203c618609202e80b600070f02d2f695f8a244a92228fa871432215e89643f619d09603240c800070e9bd3051694a824df23a1034746344165099c400196097832c0ca00070e3522fd9654a784c922d0fac716325166899c3e819109583200be00070dccc30e16c0a904dc240106074834116609b041019009903240ca00070d6673021648a5a4cd22f0fe073032616209543f418e09903300da00070d00e2fb1634a3e4c222b0fac70632015b89583f419b09683140b400070c98330b16d4a904e323e903873833116d89dc40a194096835c0de00070c3422eb15dca1a4ab2248f9870832516189503e419209203200d400070bcc830c16e0aae4eb23a904074233215f898c40619309c03300c600070b661304168ca7c4d1238906c76c34c16c09e04221a409f03200dc00070b0032fe164ca5e4c522e8fa871832c15f896840219309503080bc00070a99e2ff1648a604d0239104074a334166899040819809802f00b400070a3522ed1608a3a4ac21a0f746ec31b156092c3d819409483280c8000709cdc3069688a764d8239105475834716d89d44141a609983440d200070968f2f21618a524ae2220f786f430815489243e818909582fc0c80007090153099674a704d0235100c75234a16d099c3fc19809c83600d60007089dd2e515789ec4a02208f706f631c15609103ba17f09303000c000070836830916a0a7c4ce22e8fc870431f15c893c3cc18008f03040b4000707d282eb95e8a344ae2228f746e431315408fc3be18209103180c20007076c32fc9648a664c42290fbc710329162099c3dc19209803200dc0007070702f81638a4e4b92228fa471231d16109603e218b09383300ce000706a1a2f89604a324b221d0f6c6e030d15288e43be17f08883100cc0007063ad2ff16aca7e4d222e8fe470e31f16009683ee190096031c0be000 else (if i < 68 then 0x7391bd2ff1650a6c4cd238100071e32e169899c40019b09f83500c6000738b662f79634a604be22a0f9870031215789503e218409503200ca0007384f330716b4a864da236103075834b16e89d04121ac0a203640ce000737ea42f41614a6a4cb22b8fe070a31815c89643ea19509983000d00007378562ef95c4a0a4a12238f986fe32315e89703e218d09b03480c60007371e630b16b4a7e4dc23a102074833a16c89c041419b09583440da000736b8a2f79628a444bc22c8fc071432a16489b04121ab09a83480e80007365332ff167ca784d32349018722334168899c40219a09983300c8000735e823261788ade4fd24b90d479c36717a0a484401b30a7038c0e40007358332f41658a7c4db2368ffc73a33a163899040e19f0a083600d60007351c730816b0a7a4dd23a102474833716c89e441819a099032c0c6000734b3e31116d4a884e723f103874a33b16889783ee18909603340d00007344da3009668a6e4d2236904876033b16789ac40219708e82ec0bc000733e4931196d4a944e123e106c7703461728a044301b50a403640d400073382e2d5950c9c647f2128f046a02f914888ec3ac17008602e80ba0007331e12f39624a3c4c42318fec722331167899440019509803100c0000732bab2e915cca344b42298fcc71a32d167898c3ea19409602ec0c20007325363021674a624c822d8fd4730325163097440a19c09c83300c0000731eb830996b0aa24e7238902c76433f16e09d44341ae0a503840f200073183531396ecabe4fe243907c75e35217089c440a19b09a03500cc0007311b331016ccaa44e42399054742335164098c3fc19c09f03740ca000730b4b2fb9620a524c3235902c73033b16a09983f819e0a1037c0e40007304ce31296f8ab24e8239900473032615e09443cc18108f030c0be00072fe7e2fa1614a3e4b422a8fb470a32416009703e019f09e032c0da00072f8202fa9644a5c4c622e8fe072231f15408fc3ae17808d03140c200072f1b130716a4a804da235102073a330165099c3e8187091831c0ba00072eb2c31296cca8e4dc23d907875c35c1760a1c4321bc0a683600e000072e4c83069694a7e4d1239900872a33016709bc42019e09b83400d200072de593029670a544c622f900c74834816c89bc4181a309783100cc00072d7f03029660a5a4d0232900072a337165898840218f08f82e40b000072d1a02f4960ca644cc2310fe871232215c094c3e218d09903180c600072cb1a31196f8ab24ef247907c75c35216c09e042c1a609903240e800072c4b02ff9678a784db23f904475434916a09a440219408f832c0da00072be572f89638a6c4cd238902474a34616b89703e217c08f02e40b800072b80f2ef15d4a364bd22f0fcc72233015d09583e618808d82e40ae00072b1b92f89660a724be22d0ff473233016509b040219f09e83340ca00072ab453051670a624cf232902c76434017209ec43c1b50a103540c800072a4cf30996a8a9c4e6242907877835517a8a1c4481b10a483480de000729e5730896e8ab44f624910a476e35217009c842819f09d03580d40007297ee3021678a5e4d8239100473032716109a841219f099833c0da00072917e304166ca6c4cc22c0fe872632816589b04181a6099032c0b2000728b0f3029694a7e4e023d105875433616f89ec4241a80a5837c0e40007284ba2f79630a3a4bc22d0fbc72c32c15e895c3cc18b093830c0ae000727e3d30e16ccaa24df23d100075033316289903ec1a109c83240de0007277f02f4960ca424b92290fac70c31a16109a040219509903180b80007271952fa9684a704d4235900874a33c16489983fc19609e83500d4000726b1530c16e4a9a4f0241908076634c1770a244421b80a203580e400072649230816a4a8c4de23c104075633216609c44101a10a003500cc000725e3b2f99644a624d623f906877235217789c041019809a83380ce0007257ca3069684a7e4dc238101073833a16709bc40219d09a03580da00072512e31c1728ab24ee246109478234e17589c43fe19f099034c0c6000724ad92fd166ca7a4cd238103073e32f166899440a1a609c03580da0007244a52e5158ca084a52208f686e631015589143c217a08f03140ca000723e303001644a524bd2270fb06fe31315889443d618709082b80ac0007237cb3039650a6a4c222b8fac71c32315d89944081a109b03480d800072316c3001658a664d8238104074633f16a09d041819f0a0035c0d8000722aff3039688a6a4c7236902074a33916989c840e19f09602f80bc00072248f3051694a704d4238900471833015f095c3f019509a031c0c6000721e322fd9668a5e4be233901472432a16409a440619a09a83380be0007217c9302165ca4e4c22318fd072032d16589bc40e1a109903480dc0007211862f315e4a244ac2260f8c6ea31215d09283e019009803240c6000720b292f91648a524c522e8fe072032b16009843e418308d82f40b40007204d32f515eca244b22200f846f831d15e092c3d819209983380c000071fe782fb969ca6a4d02348fe071c330162096c3e619a09a83340d2000 else 0x752c032f2160ca304ba2288fe473232f16489a440c1a50a003540d60007525b62f315e8a1649c21b0f346e630d151091c3d818309203180d8000751f632f79618a4c4c022c8fb071231b15b895840219d094831c0b20007519102f5962ca3e4b12270f9c70e32215c09443c818109182e00bc0007512b92f495e4a1e4a92230f8c71032316009483ec19009883080c4000750c602fb9620a564c222d900071e32b15e89703fa19509683340dc0007505d930a96b0a884d0236902873033116789843f619409503100b400074ff5e30a168ca784d623b104c74a32e16609a440619209983380c200074f8fa2f9163ca544be22d0f806f432216009543d618409183000ba00074f2aa2f9161ca464bd22d8fd071232e16409703f219809603100b800074ec3230796aca7a4dd237100c72c33816c898440019c0a0832c0cc00074e5c330b16b0a8e4df23a903475033416889b04141a309b03640d600074df842eb15d0a1a49f2260f706e830b15009043b418a08d82f80c800074d91130716a4a824d922f8ff873034716d09c440c19b09903380dc00074d29d3061694a7c4e123e106876834b17589f441a19709a83240dc00074cc502f61620a484b52288fac70a31b15d89303d218709683100be00074c6072f015f4a464b72260fa86f231f161093c3d218809703240c600074bfa22fe1640a5a4c722f902473433a169099c40a19b09603180d800074b90f31296d0a904da234101472c33b16689a43f6198093832c0c200074b2943099694a8a4d02328fd072633216989bc3f019009803280c600074ac1e30916aca724d8237901473633b16b89c041a1a70a403680ea00074a5b43011658a684c82310ff473032516309a840619d09803000b8000749f543019660a704d622d8ff472e32e165097c4081a009c83340ca0007498d730896d0a9e4e724190607683531758a004241b20a383340d600074926530b16d0a904d6235902c74633616689983ea195096832c0c2000748be431016f8a904df23a101074633b16789ac41419d09a033c0d200074856a31316cca8c4e3243107075e34716d89f041e19f09b038c0de000747eed30b96b8a9c4e7240104c76834a17189e441019f09a83280d400074789f2fe9664a584cc22e0ffc72c33a169899840819d09e03180c000074721f30c96d4a9a4eb23a104075c34b16b89c84141a10a003700d8000746b8c319170cabe50124890a878c35b17009c440e19f09f03840e80007465382f61644a544bc2280fc871a33816589603de18608f02fc0bc000745ece3031658a544d6239902473632b16189483d619009c03300ca0007458683019688a6c4d6236100872c333167898c4061a109b031c0dc0007452062ff1650a484c12300fc871a32a15e098040a19a09c034c0cc000744ba92fa9660a6e4d52389040752335163098440619a09483300c600074455d2fb1640a604d72360ff872232a16389a43f21a40a103600ce000743f002fe1658a764cf233900472e32d165098040019f09703300c000074388130c96d8a9e4ef24410807723591790a0c4341ab0a0836c0ea00074320c30996a4a864e2238105474833916f89d44201af0a003500ce000742b983069688a724cf2318fcc71e31f16009543ea19a09c03480da0007425412f615f8a524ca2330fe872c33216c09c440c1aa09e03380ea000741ece30596a8a7a4ce235101073c34016d89c84121a30a403840f200074185f30596b4aa04e42368ff072e32415e093c3dc192095031c0ce0007411f13049678a664c122d8fdc72432616289583ea19008e02cc0b8000740b8030896c0a8c4de241104875633c16809b04021a009483200c00007404eb3159724ac850225010d47a835f17509ec4321ab0a383500de00073fe842ff165ca684da237900872633416689943fa19309783540e000073f8312f81644a604ce2308ff872e33216609803f619f09b83380d000073f1c43021654a504cf22d8fb873233016309543e419009b83400cc00073eb6a2f79628a3a4ba2278fc871232115a09503d818c09a03400de00073e4d931416fcab24f4249908877e34b1728a104461ac09f03600e800073de64307967ca624c622d100474434016d89bc4121a409f83180ce00073d8202ee95dca1e4ae2288fb071231e15e09543ea19709803280c200073d1943131700ab44f9247906076e3531758a284321aa0a5835c0ce00073cb422f395f0a444bc22c0fe072a33b16c89c440a19609883300c600073c4c43069678a7c4d8236902476233d16c09b840e19c09c83440b200073be922e515c0a204ab21f0fac70a322163098c3f219809483380d200073b81f30716c4a924e12369008746330165899040018d09183180bc00073b1bf2fc1640a504cd237901c73833816b89b841019a097833c0ca00073ab5030616aca8e4d723b901c73833216609683e618409183140da00073a4d130716d4a964db23c906c7543511770a044301a60a103840f6000739e8e2f61608a284af2260f886ec30815288fc39a16808b02e80c400073981e3039698a7c4d923c106475a33e16b09b44161a509a832c0ce000))) else (if i < 71 then (if i < 70 then 0x76c65430c16dcaa44ec23e105c75e33b16689b440219b09983300dc00076bff13001670a5a4c52328fe472432a16509944121a40a003540d000076b96f3061668a4a4b82230fac71232215e095c3e018b093832c0bc00076b31f2f51620a2e4aa2280fb472032215f09643e618f094830c0c600076ac8c31216c4a9a4e7240105074a33b167899c40219d09a83640d800076a61130a16a0a724cd2368fec72a32e16a09cc40e19f099032c0b6000769f8430f96dca964ec243909076834816d89d44141960a003480c20007699203081684a604cb22c8fc0702323159892c3d618809783100c000076928d310971cac04ef24210a077c35517709ec4341ad09c03400da000768c332fb1630a644c922b0fd072433015e89343e419409a033c0d60007685f52e995c8a3a4c522d8fd471e32716409683de18f093031c0ca000767f5d31296c4aa04e3240906876433f16b89b040a19209603180c00007678f93041688a6c4d4233101074033916789983fa19e09803280be0007672a72f015cca1c4bb2258f7c6f630f15989143c418a09182fc0c2000766c3c3021644a604c12318ff873832f160094c3ee188096030c0cc0007666022f11628a5e4cd235102874633316309b440419109483180d2000765f94304165ca464c62300fe472233216109a841c1a109a03280da000765927305167ca824cc2330fd873a33616509743e018a09083040b00007652cf2fa1614a5a4ca2338ff872c32515b89243de18c09483080d6000764c65301168ca6c4cd2300fdc72e32c16489843e619109403140ba0007645f2306169ca884db237102875434316f0a0442a1a309d03640e0000763fa02fa964ca664c622b8fd071032c16709b84021a90a083700de00076394a2f99648a604c42308fc071431c15b09443da189090030c0c40007632d33091690a884d12350fe872e32516109743f619c09583200be000762c722fc9638a4a4bd22b8fbc71231b15b09343dc17b09403000b400076262d2f115d0a1249e2218f7870831515709203ae17409283140ce000761fbc3021684a664d5234900c73e33b16809c840a1a909e83480d80007619802eb15c0a1a4ad2288f906ec30215289043c818509002f40b00007612eb31196c0a8e4dd239902873a33816c09983fe1a90a383700d6000760c7e30716a0a784cc2379010744335166099c3f2192094831c0ba0007606242f59608a384b12240fa0714326162093c3d418509583240bc00075ffa730b96bca864de23e905c7603501770a144401aa0a503500dc00075f91b30d16e0a944e523f105875433a16609c440419b096032c0c600075f2b3304167ca6a4c5235102876234716c09bc41c1b20a2034c0d200075ec3f30b16d4a9e4db240906476035217409d84241a1099835c0da00075e5ce30496b0a844d4238103c74632f16009743f218e09683180cc00075df802f99644a5c4c422e0fd8718325160098c3f219d09883080ca00075d8e43141704a964d423b105c7563471750a1c4261a909e83580d200075d25d30c96c4a824dc23b9044744333164099c3fc19509b03300c400075cbe330a96c0a864dd239103072033116389803e418309403040c800075c5553169710ac050424e10ac78a35f17b8a3843e1b40a6036c0de00075beed2ff96a0a724d323c101473833616a09dc4261a009e83380da00075b87b305167ca5e4ca2320fb471032f164896840419f09a83000bc00075b22b2f39628a564ce22e0fc071832815f898c40019c09c03600d600075abba30516a8a8e4d823a904c74433116909b04101aa0a283640de00075a557303967ca6e4cf235103c75834216e09e44201b309d833c0e0000759f312de9590a1a4b72298fcc70c32715e09583f418709002fc0ca00075987b3229750ac84ef240107c76e34b1728a004381af09f03480d20007592142fb9650a504be22f900472633016289783e418f09602f80c4000758bdb2e5958c9fe49921e8fb06f632716689b44121a409d83400d200075856030c969ca8c4d3239105474434816d0a1442c1ab0a183680d8000757f142f61634a3c4b42270fb070832615e09603e418809303240ce0007578a43031660a584c72310fe474033716589903ec19209503180c600075722930c16d4a8e4e1243907477434e17509e04141a40a083840d6000756bdb2f3961ca4c4ba22d900072e32c16289703fa19b0a083240da00075657a2f81640a544c7234900c73a33716a09c840e19509683080aa000755f202f29600a444b12240fc470632616589c04201a209f835c0d60007558b72fc1618a404bc22c8fe872833416709a440e1a30a0035c0c600075523d30b96eca8e4d623a901474433c165098c3f418c09282e00c4000754bfd2eb15d0a124a021c8f586dc2fd14908d43ae17d08d02f00c400075457830d16cca884e424410b877234a1710a0041e1ab0a383a40ee000753f193019688a684cc2340fec73433416009643f819a09883380e20007538c02fa1634a5a4c62311010738336166898c40019809483180d400075324930396a4a7e4de23b900874833b168099c41419e09a03340c0000 else 0x785f4c2f61614a464c422a8fcc72832915f89443e619909f03640dc0007858d230796c8a8a4df23d107075633816689cc4181a009903340be0007852832f51614a404c9232900473c33916289683e2189098833c0e4000784c282fa9628a464c822b0fc071c330166098c3f219909e83440d00007845ca2fc964ca684b422a0f986fa31915b89643d018509103040c0000783f40313172cada4f0240907077034716d09b84121a309d033c0d80007838c430616aca7e4d5232900872e33516489703f418809502f40b200078325430b16b4a904e623c903475034d17109d04201a009983340cc000782bf32f69644a4e4c422e0fe873e338163899040c1a709d83480be000782576304969ca744dd23a103075034116a89a040c1a409c03580e2000781f1b2f69650a624cb22e8fe472a32e16489b03f618f09202f00a60007818b72fc9648a3e4b72290fb86f831d15d094c3e4194099034c0d20007812562ff1678a584bd2270fa470432215f899c3fa18c093032c0d0000780c012f81620a404b92270fac72232315a89243d4184091031c0ce0007805a230296bca924ea239104874c33b16d09bc4161b009d834c0e800077ff422fb166ca724c9232100c72e33716609943f41a109c03640dc00077f8d6302968ca864cf237100873433f16f09c84121a209e03480dc00077f2792fa9600a524c422f8ff4736338167099840c19909703180cc00077ec352f29600a1a4ac2270f7c6fa32616309743da18e099032c0c200077e5b830c96d4a9c4e523e103874833d17209f84441af0a1834c0d600077df3d30b16c0a824da234900875433b16c09b441a1a809f03600d800077d8d02ff9630a4a4c4232900472033216509e041419e09b833c0d800077d28f2f21628a444bc22c8ff473832c16889e04161a109c83380da00077cbec31d1730ae650c24c90947863601770a204341b80a483580de00077c5773039688a8c4d32338ff074a33e16509903ec19509b83440d800077bf163019664a684cb231903074433816909b84081a009c03380d200077b8a430c16b8a9a4e823b104876434317009d04101a209e03440c800077b2542f71618a344b522c8fe072631e15989343c417f09002f80b800077abda30916c4a944d7237104474e34216b098c3f6195098833c0ca00077a56c30696a4a784d7239901474634b1798a084281b10a383440c8000779f132fb9668a784d623c904075c34a16809c43f4199097031c0cc0007798bf2f9963ca484bf22e8fe072e32e16589bc41a19c09f035c0da0007792712f71650a424be22f0fd473633e168098c4121a20a0036c0c6000778bf330916cca9c4ea23c903074e34116889c840819f09c03400d000077856c31116e4a9e4e9242104c74c34d1750a004281ad0a283640e0000777f0b2fd9640a5a4c322a900072c33616609a04081a109a83240ca0007778e42e795a8a164ad2280f9471c32916709803fe19509c03380c400077725f30a96d0aaa4e823e906c75233816a09cc41019b09b83240c8000776bf7304169ca724d4233101c73633817189cc4181a609b83440c80007765952f9163ca604d1234101075833a16409903f019809b03440ca000775f263031678a724dc23b902c75033f16489743da183091030c0c200077589f31216d8a8a4d8237104076234617009e040e1a809e033c0ce00077521f30896a8a864ce237101c73432e16289883d818c09983280dc000774c052dc95449f24982180f086d830215389083c818409283240d40007745a92fa9614a324ad2290fd071032416809743f619709883680e2000773f542fa964ca464ca22d0fc471431915b894c3d017c08a82e40ae0007738f42fb167ca6a4c622d0ff472833e16889a841019709703300c00007732483229750aba4f2245908475833716409943f819c09883440d8000772c1f2df159ca2049d21e8f806f431315a89543b818408e03040b40007725ce2f59628a3e4b822e0fe872433116789643f419009602f00b8000771f782f81634a3e4ba22a0fac71032115b89403f018b09503200ca0007718fb30a96a0a784d62300ff070a324160895040019809a03500c40007712cf2e015949ee49a2148f2c6ce30214d88e83aa17908b82f00c0000770c693029668a4e4c222f900c72a33516b09f0402190097030c0ca0007705f330f96dcaac4f7243908876c34816b89d84301af09f03580e400076ff8730a96b0a704d3235900c74033316609a840a19a09a03440ca00076f93b2f41610a4e4bd2288fb071832416009583dc18409603100be00076f2f62f115f0a3c4ba22c8fac6fc31b157893c3d218809403000b000076ec962fc163ca604c22300ffc74a34216a09743de19409803140c400076e61430c169ca724d523a100873e332167899440019709b03440cc00076dfc82f31608a344b52228f646f831a15b09443be17608d83200bc00076d9852ee95c8a0c4a721a8f606dc30915109283d8189094830c0be00076d31e2f6961ca444c12338ff874032e168898840419c09803180b600076ccdc2f495e4a1c4b922a0fe071831c15989443d018408d82d80ac000) else (if i < 72 then 0x79f81b30a965ca544c52280fb070632516209403e018c09403300b600079f1c92f39608a1c4a321d8f586ee31715989543ce18808f02f40c600079eb7f2f3961ca424bc2318fdc71a32416109743ee194096833c0dc00079e5162fb1644a5a4b822e0fec73c33a16a09c840219f09e833c0c600079def42de95389c248c2158f2c6d630515389143be18409303100aa00079d85831316eca9a4dd23d101474634916789a44041a209883280cc00079d1eb3031680a5a4ca2308fe471a32715e09383e418609382f80ae00079cb6930d16b8a9e4eb23f103075033e16a09943f81a109b83380c600079c4ec30d16cca8e4e5237101072432f16989a841219d09a83340de00079be5c31796ecaa84eb242108077435b1740a0842c1a80a483700e400079b7fa3011634a364b922c8ff873033816189603e6193097832c0d600079b1af2fe1664a6a4d42348fcc728338166098c3ce19009f03580d200079ab50300969ca724cf2360ffc73e33015f095c3e619008f02f40c800079a4f52fc1650a604cd2338fdc73433216909803ea19009803400cc000799e862fd169ca664d1233100475033916a09a040c1980a203780dc00079981030916b8a844e623d103474233716a89b84001a509d031c0d00007991cb2ef1618a4e4bb22c8fd471832c16409a040819b09403340de000798b6a3011660a544c322d8fc871c32d16689a040219209783080bc0007985192f51628a4c4bb2270f7c6f232716809a03f619b09a83600e6000797ebd2fd162ca324b32218f946f031215909643e618a095031c0ce00079783330d96b0a804de23d105475233716989cc40619709703140d60007972022eb95b09f24932178f446d030114f88e83b618408f83440b4000796bac2f51658a504b72218f646e430e15409343ce18609503280d00007965862de15549e649e21e0f446ee31615c09443e218b08e02f80b2000795f242fa1634a504c72330ff473232316209703e219009983340ce0007958d52f595dca284a62238f686fc31315a09543cc18809283280d00007952673031680a784da239904075e34517389ec43e1ac0a003640e8000794c073031684a684d3233102074e34016c09ec4201af0a403300d00007945903059680a5c4cc230901c732333164899040419609b03400d4000793f1c3091694a7a4df23e107875e33f16f89d84121a509e83480e00007938ca2f99634a424c322c0fd870432016089683e018d098835c0e200079323b30d96dca9c4d6233901073c33316a89b440619d09c03480de000792be22fb162ca384ba232101473c33516b89803e219309802f40ae0007925a32eb95d4a244b12270fb46f632015b89904021a109683140bc000791f4c2fc95f8a344b22290fa070831f16189803ec18f09083000d20007918cf30c96cca924e2237100473033216809883ea19809e03440ce00079127f2f19648a684d72340ffc72632315e894c3e818c08e83080ca000790c2e2f795eca284b522f8fd473033316889903f619109183000c60007905c830516b0a7c4ce22e8fe072c32d16389703f219009803400cc00078ff6e2f79604a3c4bf232100c73833916b89b840219909b032c0d400078f8f730796bca804e0240905876c34316a099c3f618809503240c200078f28c2ff9664a604bf22c8fd471a32816709b03f818c08f82d00ac00078ec412f11610a4a4c222a8fb06ee30f15989243d618b09282e00bc00078e5ec2fa1608a424bf22e0fb070031915b09743fa1a20a003400ca00078dfa92ee15d0a104a62240f946fe31c15f89483d017208882b80b000078d91031216e4aa64ef24910bc78835e1768a0c43a1a90a183600ce00078d2c02ee9608a404ba2280fb070231615d096c3ea18109202f40be00078cc752f015fca224b722c0fe073233716589a03fc19509882d80c200078c60c3041674a804d523d105476c34f17489d040e1a00a183580dc00078bf8e30c96aca9c4e1239104473433316089583ea18209103100c000078b92b3021660a704d322e0fd071e32315f09483f619c09d832c0d800078b2d12ff1660a5a4c422a8fe073633316889a840819609482e40b600078ac2e31b1748ad24fe24e90a476e35917509ec4301b30a603800d600078a5a131616f0aa84f1241905476034316e89e040e19e09e83380ca000789f5f2ed95f0a404b722c8fa471631c15c095c3fa19e096832c0b60007899252e9158c9ee4922190f7070a325162093c3d017d09083240c20007892b13059684a6c4d42360ff473e33216709b440419409603300c6000788c3130d16b4a804d7234900474a34516689a84121a009883400d20007885c92fd9630a384b722b100071a31c15f894c3f219a097033c0e2000787f4730b16a8a7c4e423c90707743581768a0c4401ae0a483780d00007878ea2ff16a0a884dc239901073e32e16709b04081aa0a203400d400078727d30816c0a904d9235103c74433b16b89c44381a30a0035c0d4000786c242f9163ca464cf235103076234b16f89d84161a309e83240c00007865a93059678a6e4da23b103072a33216709ac4101a209b035c0de000 else (if i < 73 then 0x7b92722f99608a3e4bb22b0fbc71232a15a89203bc17a08d82ac0b20007b8c142f91638a504b62238fa870831d15e89583ec19209603340be0007b858331196f4a964e9244908076835217209f041a19c09a834c0c60007b7f232fd9648a5e4c92318ffc72832f16009703f4195098833c0cc0007b78c82fc9654a624b82288fc070a31d15c89203d418a096033c0d60007b724330c96d8a8e4e523c901475634216b09a43fa1a50a183400de0007b6beb2f71634a524c72348ff873032d160096c3ec19209583480e60007b65773049688a784d0236100c73c33116a89bc41c1a90a3835c0da0007b5ef630916b4a8e4e423e104c75e34316c09e043e1bc0a683b80e20007b586a3131718aba4ec241109875c34b17209c040c19909903380dc0007b52212f99648a604c92370fe473833716789903ea18a09302f40bc0007b4bd42f09608a404bc2310fec72e32e16389943f619709b83380ca0007b45782fb9644a664c9236101874633c16b89f44161a409803180ba0007b3f322ef1608a324b72258fa870632016689683f2194096034c0d00007b38ac30e96c4aa84e623f10747663421720a1842a1aa0a003500dc0007b32472fe1640a404c122f8fc070c32416709bc40619609703180ba0007b2bbf30c16c8a944e523d904873633916789d041619d09a83480d20007b25612fb964ca604d3237902474833f16a099842019709c83400d20007b1f0a2fc1638a464bc2280f9c71832f162095c3dc18a09b03280bc0007b18a03029678a5a4bb2228f7c6e8308153092c3ca18a09702ec0c00007b123b2fb162ca5c4c9231102875834216c09e041a1ab09f83540de0007b0ba13191718ab64f024590c478836117b0a0842a19e09983340ba0007b05443021638a484b92300ff873a33a16c09b040819e09c03580c80007afec730816a0a7a4d1237901872c33f16c89d040e1a109a83280b20007af87a2f5962ca584cf234101473433816709b83fa19d09d034c0ce0007af2202f69614a484b32270fd072432e16209503e218f09a03140bc0007aeb8d31716fcaa64ef242106c77635917b8a2043a1a209a03540d80007ae5402f51610a324b922b8fd472632a16989743de18809503480ce0007adee22fe962ca4c4c522e8ff875234117089e44241a109703240c40007ad8733019660a724c82328ff0742336169898c3ec19709883500d40007ad2072fc164ca4a4d7238103474433e16d09c44141a30a003440cc0007acbb22f9161ca4a4c42280fec73432b15a89583ec18f09983240be0007ac5642f495f8a4e4bc22b0fb472432716489b440219f09d033c0cc0007abf1c2f31638a464cd2338fe871e32116089943fc19b09403080ca0007ab89931196d0a9c4f524b909877e35c1760a2442e1b20a083580bc0007ab25e2e815a4a204b822d0fa070a32216389643d618108f82f00be0007aac042f49634a6c4d4235101473c32a161895c3e018c099033c0cc0007aa56131c173cabe4f8248107075634c1768a104301b60a283440ec0007a9edb30c16b8a904df23e902473e34916d89c44161ac0a083500e60007a986e3071670a664c72330fe071832d16889c841e1a50a183500b40007a92143011688a844d9238900873032d16089a04221a109e033c0d20007a8bcb2f69638a504c622e0fdc72032616109743f819e09a03200c80007a854231416f0a9a4e3240903875c34917009c842a1ad09c03580f20007a7ebc31116dcaaa4f5244109076435217089f44321b10a183580dc0007a784a3049694a844dd23b904875433c167896c414190098833c0be0007a71f12fd9648a684d3232102473c33516509c041019309403140d20007a6b942fe9654a6a4db23b104475634716a899840a1ac0a1836c0dc0007a651a30916b4a7a4d0234103475a34a17109e040e19509982fc0ca0007a5eb230496a4a7e4d623e904476434916f89d44281aa09d83540d40007a583830b96b8a904ec23d104875a33d16189643ec18608c82d00c20007a51cd2fe1668a644c72350ff873c333166899c3fe19509903280dc0007a4b5b3091680a6c4d2235901874233616989b041819b09c83100c80007a44ed3019680a704cd235901073033016689ac3ec18c09303100d00007a3e7130c96b0a764d6234900473c32516409a04061a009d831c0cc0007a37e831316a8a924d8237102c73e33f16e0a0041a1a70a183540b80007a31c72e315a8a024a321c8f686e231915a89403d819309883280da0007a2b593049698a7e4dc239901873a34316c09dc41a1a90a103280c80007a24f82ff1664a5c4c322d0fe071a32515f899440019809803300c80007a1e8730a96d0a9a4e9240905876e3581758a0c41e1a609e83500d20007a18292fb165ca684d5232901c738341168099c41a1ae09e83440d20007a11ca3041668a724c322f8ff873e33816d89c040819e09883240ce0007a0b6d2f41634a424b92278fe871432c16089603f019909b83380cc0007a04e730e16a0a8c4e0238902474633116509b040c19f09e03400d600079fe8d2fc1634a5c4ca22f8fd072032d16109503e618f09883280d6000 else 0x7ccb3c00000000000000000000000000000000000000000000000ee0007cc4fb2f11600a3a4b02290fb86fe31115909283c217a094030c0b40007cbea42fb9624a4c4af2248f8c70e32115e89443e419d09c03480c00007cb82330896a8a8c4dc236100c73833016d09f040219d09d03640cc0007cb1d62f51648a504b722a0fb4700324163096c3e418909503200d20007cab9d2ee15dca2a4a92278f886fa32015a094c3e818408d03080c60007ca52d2fd9668a6c4cb2300ff8734332165896c3fa19809c83140c80007c9ed32fd1674a664c622d8fb871a32716609b440e19a09c034c0d20007c9876300167ca5e4c922f0fb071032315e895c3fa19309583300ca0007c923b2f31608a464bf22f8fe0728335165896c3fa19309303100b60007c8bd33021664a704c9234904c74634117089cc40219609a83200bc0007c85832ee95e4a4e4bf2298fc471831f15e09844221a709c83280c80007c7f172fe9660a4a4ca2320ff471a31e15f899040e1ab09f83440d60007c78a4309968ca684cc230901473e33917089b44081a009883540d00007c721c3141730aba4ee247109c7823561788a044241a109c03280ca0007c6bec2ee15f8a404ca22d8fc072a32d16509943f619909883600e80007c657f30796a8a7a4d423b906c75033d16f09c840819409883180d80007c5f402f095f0a444b822d8fd472432116209783f6191097831c0b80007c58f52f215d8a224be22e0fb471832a162095840219709d02fc0ba0007c52843071684a6c4c6230903075033b16809a040a19309403000b60007c4bee31a9734ae04ff25090b477c36417e0a544481bf0a903880dc0007c45862fa9640a4a4b42280fac6fe31d160097c3fa19609683440c60007c3f262fd1658a604c322f0fbc6fe31d16089a03ee19b09b03600c80007c38a930f16c8a884e223e106875c34e1760a0442c1a3099832c0ca0007c326f2f215dca104a121d0f446e431415689383d818f09783240de0007c2bf430916a0a864e123e906076434316b09b841c1a109903380ca0007c258f3051670a704db23d105074a34716c89ac40a197099032c0b80007c1f173099684a6c4d6239103c722321160899040018e09503000bc0007c18ab3051678a584c522e0fd472a32d16209a44181a409883400ba0007c123d3061684a684d123a104873e33a16d09c84041a309f833c0dc0007c0bd72fc9634a524cd2338ff873433115d89543ba17908e02c40ac0007c05862ee95f0a264ab21d8f786f431215089003c017c09203040b60007bff1430416a8a884e9240908876e34d1798a044261af0a5039c0ee0007bf8d42e715e4a284ab21d8f6c6f230515109483d2193095031c0ca0007bf25c30896c0a8e4e323f905075233916b09cc4101ae0a203880ca0007bebe6303968ca7e4d52338ff873033816a89983f619509703240ca0007be5862fb9664a564c222d8ff872e331164898c40c19f09b83200c80007bdeff319972caca4f3244107075e33c16689c041c1ad09d83540d00007bd8c52e595aca1c4b32298fac6fa32515e89783e019609c834c0ca0007bd25430796b0a9e4e5242906474634716e09d04121a009a03400c40007bcbf42ff9680a764dc23c107076634c17389c841c1a20a103500e20007bc58d3019670a5c4be2318ff871c32616509a440c1a709a83300d80007bbf03312170cab84ec240106875633f16e89c84121a6098032c0d40007bb89b30296b8a884cf238103873c33616909b44161a009803200d00007bb26d2e915c4a224ab2270f9c71031f15e894c3be17a08c82e40bc0007bac1a2f095e4a304b22220f7870232215c09603d619809883380d40007ba5b52fb162ca2a4c42268fc871a32b16009443f019a09703280bc0007b9f4d2fc1658a5c4ce2318fc070032816309a44101ab0a183500de0007b98d33061690a664d2236102473833716b09b040a1ab0a1833c0e4000)))))))

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



private theorem b62466 : covered 62466 62540 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62540 : covered 62540 62613 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62613 : covered 62613 62687 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62687 : covered 62687 62761 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62761 : covered 62761 62835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62835 : covered 62835 62908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62908 : covered 62908 62982 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b62982 : covered 62982 63056 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63056 : covered 63056 63130 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63130 : covered 63130 63203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63203 : covered 63203 63277 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63277 : covered 63277 63351 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63351 : covered 63351 63425 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63425 : covered 63425 63498 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63498 : covered 63498 63572 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63572 : covered 63572 63646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63646 : covered 63646 63720 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63720 : covered 63720 63793 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63793 : covered 63793 63867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63867 : covered 63867 63941 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b63941 : covered 63941 64015 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64015 : covered 64015 64088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64088 : covered 64088 64162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64162 : covered 64162 64236 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64236 : covered 64236 64310 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64310 : covered 64310 64383 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64383 : covered 64383 64457 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64457 : covered 64457 64531 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64531 : covered 64531 64605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64605 : covered 64605 64678 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64678 : covered 64678 64752 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64752 : covered 64752 64826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64826 : covered 64826 64900 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64900 : covered 64900 64973 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b64973 : covered 64973 65047 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65047 : covered 65047 65121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65121 : covered 65121 65195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65195 : covered 65195 65268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65268 : covered 65268 65342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65342 : covered 65342 65416 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65416 : covered 65416 65490 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65490 : covered 65490 65563 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65563 : covered 65563 65637 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65637 : covered 65637 65711 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65711 : covered 65711 65785 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65785 : covered 65785 65858 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65858 : covered 65858 65932 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b65932 : covered 65932 66006 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66006 : covered 66006 66080 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66080 : covered 66080 66153 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66153 : covered 66153 66227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66227 : covered 66227 66301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66301 : covered 66301 66375 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66375 : covered 66375 66448 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66448 : covered 66448 66522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66522 : covered 66522 66596 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66596 : covered 66596 66670 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66670 : covered 66670 66743 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66743 : covered 66743 66817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66817 : covered 66817 66891 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66891 : covered 66891 66965 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b66965 : covered 66965 67038 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67038 : covered 67038 67112 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67112 : covered 67112 67186 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67186 : covered 67186 67260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67260 : covered 67260 67333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67333 : covered 67333 67407 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67407 : covered 67407 67481 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67481 : covered 67481 67555 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67555 : covered 67555 67628 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67628 : covered 67628 67702 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67702 : covered 67702 67776 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67776 : covered 67776 67850 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67850 : covered 67850 67923 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67923 : covered 67923 67997 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b67997 : covered 67997 68071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68071 : covered 68071 68145 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68145 : covered 68145 68218 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68218 : covered 68218 68292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68292 : covered 68292 68366 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68366 : covered 68366 68440 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68440 : covered 68440 68513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68513 : covered 68513 68587 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68587 : covered 68587 68661 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68661 : covered 68661 68735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68735 : covered 68735 68808 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68808 : covered 68808 68882 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68882 : covered 68882 68956 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b68956 : covered 68956 69030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69030 : covered 69030 69103 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69103 : covered 69103 69177 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69177 : covered 69177 69251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69251 : covered 69251 69325 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69325 : covered 69325 69398 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69398 : covered 69398 69472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69472 : covered 69472 69546 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69546 : covered 69546 69620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69620 : covered 69620 69693 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69693 : covered 69693 69767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69767 : covered 69767 69841 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69841 : covered 69841 69915 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69915 : covered 69915 69988 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b69988 : covered 69988 70062 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70062 : covered 70062 70136 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70136 : covered 70136 70210 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70210 : covered 70210 70283 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70283 : covered 70283 70357 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70357 : covered 70357 70431 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70431 : covered 70431 70505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70505 : covered 70505 70578 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70578 : covered 70578 70652 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70652 : covered 70652 70726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70726 : covered 70726 70800 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70800 : covered 70800 70873 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70873 : covered 70873 70947 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70947 : covered 70947 71021 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71021 : covered 71021 71095 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71095 : covered 71095 71168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71168 : covered 71168 71242 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71242 : covered 71242 71316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71316 : covered 71316 71390 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71390 : covered 71390 71463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71463 : covered 71463 71537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71537 : covered 71537 71611 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71611 : covered 71611 71685 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71685 : covered 71685 71758 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71758 : covered 71758 71832 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71832 : covered 71832 71906 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71906 : covered 71906 71980 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b71980 : covered 71980 72053 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72053 : covered 72053 72127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72127 : covered 72127 72201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72201 : covered 72201 72275 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72275 : covered 72275 72348 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72348 : covered 72348 72422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72422 : covered 72422 72496 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72496 : covered 72496 72570 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72570 : covered 72570 72643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72643 : covered 72643 72717 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72717 : covered 72717 72791 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72791 : covered 72791 72865 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72865 : covered 72865 72938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b72938 : covered 72938 73012 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73012 : covered 73012 73086 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73086 : covered 73086 73160 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73160 : covered 73160 73233 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73233 : covered 73233 73307 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73307 : covered 73307 73381 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73381 : covered 73381 73455 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73455 : covered 73455 73528 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73528 : covered 73528 73602 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73602 : covered 73602 73676 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73676 : covered 73676 73750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73750 : covered 73750 73823 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73823 : covered 73823 73897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73897 : covered 73897 73971 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b73971 : covered 73971 74045 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74045 : covered 74045 74118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74118 : covered 74118 74192 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74192 : covered 74192 74266 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74266 : covered 74266 74340 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74340 : covered 74340 74413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74413 : covered 74413 74487 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74487 : covered 74487 74561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74561 : covered 74561 74635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74635 : covered 74635 74708 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74708 : covered 74708 74782 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74782 : covered 74782 74856 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74856 : covered 74856 74930 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b74930 : covered 74930 75003 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75003 : covered 75003 75077 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75077 : covered 75077 75151 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75151 : covered 75151 75225 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75225 : covered 75225 75299 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75299 : covered 75299 75373 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75373 : covered 75373 75447 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b75447 : covered 75447 75521 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 62466 75521 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b62466 b62540) (joinCoverage b62613 (joinCoverage b62687 b62761))) (joinCoverage (joinCoverage b62835 (joinCoverage b62908 b62982)) (joinCoverage b63056 (joinCoverage b63130 b63203)))) (joinCoverage (joinCoverage (joinCoverage b63277 b63351) (joinCoverage b63425 (joinCoverage b63498 b63572))) (joinCoverage (joinCoverage b63646 (joinCoverage b63720 b63793)) (joinCoverage b63867 (joinCoverage b63941 b64015))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b64088 b64162) (joinCoverage b64236 (joinCoverage b64310 b64383))) (joinCoverage (joinCoverage b64457 (joinCoverage b64531 b64605)) (joinCoverage b64678 (joinCoverage b64752 b64826)))) (joinCoverage (joinCoverage (joinCoverage b64900 b64973) (joinCoverage b65047 (joinCoverage b65121 b65195))) (joinCoverage (joinCoverage b65268 (joinCoverage b65342 b65416)) (joinCoverage b65490 (joinCoverage b65563 b65637)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b65711 b65785) (joinCoverage b65858 (joinCoverage b65932 b66006))) (joinCoverage (joinCoverage b66080 (joinCoverage b66153 b66227)) (joinCoverage b66301 (joinCoverage b66375 b66448)))) (joinCoverage (joinCoverage (joinCoverage b66522 b66596) (joinCoverage b66670 (joinCoverage b66743 b66817))) (joinCoverage (joinCoverage b66891 (joinCoverage b66965 b67038)) (joinCoverage b67112 (joinCoverage b67186 b67260))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b67333 b67407) (joinCoverage b67481 (joinCoverage b67555 b67628))) (joinCoverage (joinCoverage b67702 (joinCoverage b67776 b67850)) (joinCoverage b67923 (joinCoverage b67997 b68071)))) (joinCoverage (joinCoverage (joinCoverage b68145 b68218) (joinCoverage b68292 (joinCoverage b68366 b68440))) (joinCoverage (joinCoverage b68513 (joinCoverage b68587 b68661)) (joinCoverage b68735 (joinCoverage b68808 b68882))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b68956 b69030) (joinCoverage b69103 (joinCoverage b69177 b69251))) (joinCoverage (joinCoverage b69325 (joinCoverage b69398 b69472)) (joinCoverage b69546 (joinCoverage b69620 b69693)))) (joinCoverage (joinCoverage (joinCoverage b69767 b69841) (joinCoverage b69915 (joinCoverage b69988 b70062))) (joinCoverage (joinCoverage b70136 (joinCoverage b70210 b70283)) (joinCoverage b70357 (joinCoverage b70431 b70505))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b70578 b70652) (joinCoverage b70726 (joinCoverage b70800 b70873))) (joinCoverage (joinCoverage b70947 (joinCoverage b71021 b71095)) (joinCoverage b71168 (joinCoverage b71242 b71316)))) (joinCoverage (joinCoverage (joinCoverage b71390 b71463) (joinCoverage b71537 (joinCoverage b71611 b71685))) (joinCoverage (joinCoverage b71758 (joinCoverage b71832 b71906)) (joinCoverage b71980 (joinCoverage b72053 b72127)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b72201 b72275) (joinCoverage b72348 (joinCoverage b72422 b72496))) (joinCoverage (joinCoverage b72570 (joinCoverage b72643 b72717)) (joinCoverage b72791 (joinCoverage b72865 b72938)))) (joinCoverage (joinCoverage (joinCoverage b73012 b73086) (joinCoverage b73160 (joinCoverage b73233 b73307))) (joinCoverage (joinCoverage b73381 (joinCoverage b73455 b73528)) (joinCoverage b73602 (joinCoverage b73676 b73750))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b73823 b73897) (joinCoverage b73971 (joinCoverage b74045 b74118))) (joinCoverage (joinCoverage b74192 (joinCoverage b74266 b74340)) (joinCoverage b74413 (joinCoverage b74487 b74561)))) (joinCoverage (joinCoverage (joinCoverage b74635 (joinCoverage b74708 b74782)) (joinCoverage b74856 (joinCoverage b74930 b75003))) (joinCoverage (joinCoverage b75077 (joinCoverage b75151 b75225)) (joinCoverage b75299 (joinCoverage b75373 b75447))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 62466 ≤ index 120000000/512 := by decide +kernel
private theorem starting_value : fast 120000000=6841648 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 120000000=6841648) (n : ℕ) (low : 120000000≤n) (bound : n≤145000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=120000000
    · rw [first,anchor]
      exact starting_value
    · have past : 120000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤145000000 by omega)
        have within : index n / 512 < 75521 := by omega
        have lower : index 120000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤145000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ120000000To145000000
