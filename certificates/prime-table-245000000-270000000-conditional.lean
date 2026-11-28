import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ245000000To270000000

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




private def radical : ℕ := 0x8dbf452c04acf439988bfba17da39c5742c15075b2019955b4cc63d57f811eb26d5b2608d1ce81ddb61992c2bafd3fe780761175529caca71b03546736550a124214f196fdff453d44fb34a7ba6bcf6ff33e71f876296d44638a566bfc0dede767598c90dd2ea858e69dc335e31bd96b9be9ad868f7d986ef67e503805a8e4e3fc8bd3713495dd29c2a2e4f7221886492f5c7a13c9a8dad9c7b4511ecf34588d4414a151322418784c59b5830d3c83c2c3b43a1d5155968e9b34f1dc388e4cbd783d7b309d888346b2289dc522ba94df28e4e0a7fa5e17bec94d6f34672e058d40354b7fc3b578d7f47d01d8635fa00c425db3e4f1bc63fe7b86b987979ef1f54ff6612245d5c29b1ef9d74763d5d94409d93ad074a45f57f1e2d488d2802650e4e5905a9833b02bc916de8ccd7a7cbe9ed41e741cf19899cd8aa39083a4960895ad69c618984a5158ba49843fc9098012bbdf0fa98d8c31e05a2ac46283284e2d69c1bd382b3048393bbcf524bb6b360a91f144bf74e74fc24c43d21b6a0b7568b07922bbc643f18f8e8983b343437e35ffd6a1cd67c825fb605ff3ef1857026532441d5d799d3805d4174f92046e195589687f450585a1099c9e8664038969b8d32d01bfea09c532acda104b5c2edefff0a015043acc12b5f10b7f037bac026b46973b192e6794457dc94e88729b34d727be9927273c9775361896472fc2af915b1c55195c12a7b39bcfb493bff0f8f75d9b22b6ec079f055117f223f8735f0598c794781f24601dadf66196f25f4afe5c1dcffdb16e02f8014bae44dbb0267537251a1206cad2f0a7a6e8e2d93f69e5aaa22bda3e9a7dc6653656438784a6d6c92396b237a5e34c84ec1f7aaa7f15905f470a3a8e4fad907d02c35368c161b7c18f387c0df9755dfd953f30a3d73b3408e3a9376191a0215ef74b02e004fabc1eca5ccc6fa7cf14334a2321705df20a9f1e210a88eaea9073bed5ae97a9ff6eab83469921c7f3696458ac11dc2d533bc4bef1457b98e270cc71057c910c4aac5976d8b731adf40b7f105423982c1d4c47aade9eead279e109cb600b337b0a3d2da11efa3309a7e419a6f08a1a9ba5663f61e530e8d21498ead2a6a3cc77171eaa83485c58546c042c4818d0152d1f03dae547a82b4f59ae941a78b61aa93fb13d4f0cc95618b7d27c1581725d0c8036bc2e5ea621c03e7e6970e29705f73aca4758045f1178238795783fd38e7f71cd10822b9bdd0280b773fc7a2ceaf379f81d1a8b3a72b845e24749d9cd22f6ad9900d611359c76b70d9cff813e7a8272cc892097fadc7e19096ae5392aecf9df80900e7e81166a8752d11d751470738af0a9a1a1f9360b51959838fb127f2e65df8d04efc2fe149a169728dbb302ce43ae40d98d207916aa156019755413765380c0e8225794b1300349998ff68e8fbbca9092be45fedde2c68e12fa97702b36067c6a3f7be54512e53767020b53fdacd7e59d3ed5a52e43e3e4a28db86bfd289ad88a4b3fa0648d3851bd84001fc8d9cc21052a9c656cac52ef4b51fa2c8832826c3d82f8ea42f9a5b0b38b3cc5be68fc7a2872a23ff56ef47e4de891186f602a1053f5ae74824eda48dea9a9448afc446c8859d665d3684aab4a9ae5f39966367269c5705ce36cb7b34a8a771fb5114e2b1525176adb5520eb4e1502eb6fec8b3d83dbda3c915c544c3dddd448774b12119d2c8755b8e2da53924c5e2b2c2248e4074f9adaf45ccee43bf7722d9d129d7b60ca6f60c295251264af8a720fbc75211fba3ff48723691735adef119f8df5103b6d2e2ed1e9e2d361c8956a4a4a3642af9da6771c6a73c2b135b91172127680505fe149b6cd48a6a4e4dc04d89390868a456b5be0987f0bda1159769709562174752f12dbff2416ac295b4f5508ec7530f06009219b2cf2bfcbdc179b4eb5bf51d888b60bf5f307e1e97409f7110ae493a42ad11dbdf432f664160c35f8571f5c47f6514bc8dd9b970e12f664763bf5fcde1e887b18cc32909ef30617e251cd6e018c0674adb0e47e031a8dacc74b9c9a2249eb0ea7b5c8180373f9209485e83d388a7e0af621fcf62c0f93770683019790b033ca27599c75d159b6ab438bac92e240d6b79e485ef4caa8d95a1e7c4c1d33ce9df9ed0d615b8d2f000c8bd9a1e5bf6bc4dfa1943eda75632166d78af3e542b9094966aaa03d5e424598cc10ac630c7b5f48060efff351827b444119833f0c544906d0b9169dd868561355f957c8e43c8dd123793ae5ab04c9556555a309ede7ac61f76e083f298110e58ba0199d96a706944ef8cf53a3346174036ee12569290906d665838b4401eb950be376e58bae18bd4707208116f30d5048eb8844ccc91c81e070f9dc6ab68fdc0c4a7d4b4aadaf6290f7caa8ea12e0dcc3cb2a2b0e7890434f0abd6f4bff279904ef3cef54d4467305fe22e96e484057200d1164e4813d74572c4111edeeab10d8bc52663f35c91cf03f5b7b6aea7b13b1dd1918e0e1eaffc04667ea45f9738db904ae06459fdf44583194f80c45a678ce1b31235b934c59a41cc6a5936f63ef7fe9c37fd21eb874f86cc6f875bcc58c502aa2a5f22d9186842e55ff235f4bb32320b90e3f904c025740713f11a1d1517b7f9858c87dddbc764c3d346603cd5710ef34b12e8289a8f68e586c61c7d5ad69bc70717f91e5cc9444cce3552086bcf6ba6a5b91c6798cbc13d3132c30f804e396d344318ed7217ea33218c3963f15f60fcd06fde67ced297dce24ce5ab6096e99496eafd594eb761e13c51ca75929a575dfeb10b20a92f2e0e8184e4ef4a3d92e9e9ad5746bcae3ce019294c4d760915f2f9d50966a50a22c406f0bf92eaaa933a9a30d006a6cbf4bfb0ef414e2367359166553a14b9d8d56d6021d26babe05e91dbbb34a705053440d09b37176ea1859ec0872f1e93526036bc998afb42087867bb2927450c109a7d098d758f076f387fa39eacbf6b5102fd54fd1b9aac98f9f8a0289f0041f1f48fb1a1edaeb471efc89d4da2dcaae559c09a8cdec80014e9c1fc9f41a026d8f21d7d3c12bf91b53f1836eac4b9e2174f42177e00921132d24ba09977f7250d367a9b6ae9e81cc4c238136a809efff97445c77e2073426429eb83891e52e415ca97c6f6590e3c120de5e9b06fe31a25ff7e3c25633bd9fc4d93682ba9855c70a1bf49ed0cabec6801d2b0594741a1726a1cf87973254ec3729d8fca68dca82dde9f76741608b3002595cd8bd1d07e766bb9e641b82517ef4ada8a0ff095613bfcdd3da85221697e9c60546f456d5e2ce94f0abee84d9699fe611af55b6f60ee7a298fd7e537199fb7a3c6d9cff68c08ed53bef0472d016ff85021220a46b18296624db14d7f0e6eefcb0258410a60e7f0aa0bd0c45a788b20c2c24d9df7dfc26731306bf88cc29814e665784524b755f9ecc8e95381b477a1ba06fec378771faa6044dabf2fb65430b8e01d964bb8c11034602d87db936d11dada86b7bba8e3014a474ffd089cf6c5896ed2b13be58393cbef258708f30cb0df559bc09fd5ac82b38ab66deff905116895caf79c3eae3d11c9972b32e6242ef38e56313ea8cb60b7dca8d08b4ebf6cafc67188c226040478bf1267262feb288266dcb530c350e1acf1ac03cd1f3d3bce33bb2de6a204f8623091e345f74e004761e161974824f59cb266ec60a659f9159d311da750b95ef3075e40c009001dd15c5bffd7aff31fa99db8d929e5bcca04a1a0afe7052bae6dc03e07a14a1418973ada5b38ddea2cad7ed53354eab988f000ad77d6b13a671a33d743b9fc2f82c9f5b645bca9f6807297df13a76a446e8bbf5e7c3d66b66338acc861f113633b557de7b43d17f21ed82f9e55e78f0c713ce410e9949d0eb3bab5722e5c13477b77c5169a0712b11b4af0cf5d45effe50157cbf024a5f8675011c0c0889ed60c7f144e21c4c521643d3aaa8c2f786fd16ee5d54f1503f45c2c777897b2ef58020d596858f7227c665aa2eecc411ffe620d20a319fc67ade77d122b100e100251ac88d53e05c74d8409fe6d579002c71481d5a753a9ef5561b6a2586f8c96410f2ed32eab2e1d0c852b478e333c507a81e6ebb791172db870e05cebc035dc84e2c5213e1adcab25be8300a

private def light (n : ℕ) : Bool :=
  if n≤128 then decide n.Prime else n.gcd 385620482362580421735677065923463640617493109590223590278828403276373402575165543560686168588507361534030051833058916347592172932262498857766114955245039357760034644709279247692495585280000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤16431) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 128 = 385620482362580421735677065923463640617493109590223590278828403276373402575165543560686168588507361534030051833058916347592172932262498857766114955245039357760034644709279247692495585280000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 128 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤16431 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 64 := by unfold smallValid; decide +kernel

private theorem sp64 : smallValid 64 64 := by unfold smallValid; decide +kernel

private theorem sp128 : smallValid 128 64 := by unfold smallValid; decide +kernel

private theorem sp192 : smallValid 192 64 := by unfold smallValid; decide +kernel

private theorem sp256 : smallValid 256 64 := by unfold smallValid; decide +kernel

private theorem sp320 : smallValid 320 64 := by unfold smallValid; decide +kernel

private theorem sp384 : smallValid 384 64 := by unfold smallValid; decide +kernel

private theorem sp448 : smallValid 448 32 := by unfold smallValid; decide +kernel

private theorem sp480 : smallValid 480 33 := by unfold smallValid; decide +kernel

private theorem sp513 : smallValid 513 64 := by unfold smallValid; decide +kernel

private theorem sp577 : smallValid 577 64 := by unfold smallValid; decide +kernel

private theorem sp641 : smallValid 641 64 := by unfold smallValid; decide +kernel

private theorem sp705 : smallValid 705 32 := by unfold smallValid; decide +kernel

private theorem sp737 : smallValid 737 33 := by unfold smallValid; decide +kernel

private theorem sp770 : smallValid 770 64 := by unfold smallValid; decide +kernel

private theorem sp834 : smallValid 834 64 := by unfold smallValid; decide +kernel

private theorem sp898 : smallValid 898 64 := by unfold smallValid; decide +kernel

private theorem sp962 : smallValid 962 32 := by unfold smallValid; decide +kernel

private theorem sp994 : smallValid 994 33 := by unfold smallValid; decide +kernel

private theorem sp1027 : smallValid 1027 64 := by unfold smallValid; decide +kernel

private theorem sp1091 : smallValid 1091 64 := by unfold smallValid; decide +kernel

private theorem sp1155 : smallValid 1155 64 := by unfold smallValid; decide +kernel

private theorem sp1219 : smallValid 1219 64 := by unfold smallValid; decide +kernel

private theorem sp1283 : smallValid 1283 64 := by unfold smallValid; decide +kernel

private theorem sp1347 : smallValid 1347 64 := by unfold smallValid; decide +kernel

private theorem sp1411 : smallValid 1411 64 := by unfold smallValid; decide +kernel

private theorem sp1475 : smallValid 1475 32 := by unfold smallValid; decide +kernel

private theorem sp1507 : smallValid 1507 33 := by unfold smallValid; decide +kernel

private theorem sp1540 : smallValid 1540 64 := by unfold smallValid; decide +kernel

private theorem sp1604 : smallValid 1604 64 := by unfold smallValid; decide +kernel

private theorem sp1668 : smallValid 1668 64 := by unfold smallValid; decide +kernel

private theorem sp1732 : smallValid 1732 32 := by unfold smallValid; decide +kernel

private theorem sp1764 : smallValid 1764 33 := by unfold smallValid; decide +kernel

private theorem sp1797 : smallValid 1797 64 := by unfold smallValid; decide +kernel

private theorem sp1861 : smallValid 1861 64 := by unfold smallValid; decide +kernel

private theorem sp1925 : smallValid 1925 64 := by unfold smallValid; decide +kernel

private theorem sp1989 : smallValid 1989 32 := by unfold smallValid; decide +kernel

private theorem sp2021 : smallValid 2021 33 := by unfold smallValid; decide +kernel

private theorem sp2054 : smallValid 2054 64 := by unfold smallValid; decide +kernel

private theorem sp2118 : smallValid 2118 64 := by unfold smallValid; decide +kernel

private theorem sp2182 : smallValid 2182 64 := by unfold smallValid; decide +kernel

private theorem sp2246 : smallValid 2246 64 := by unfold smallValid; decide +kernel

private theorem sp2310 : smallValid 2310 64 := by unfold smallValid; decide +kernel

private theorem sp2374 : smallValid 2374 64 := by unfold smallValid; decide +kernel

private theorem sp2438 : smallValid 2438 64 := by unfold smallValid; decide +kernel

private theorem sp2502 : smallValid 2502 32 := by unfold smallValid; decide +kernel

private theorem sp2534 : smallValid 2534 33 := by unfold smallValid; decide +kernel

private theorem sp2567 : smallValid 2567 64 := by unfold smallValid; decide +kernel

private theorem sp2631 : smallValid 2631 64 := by unfold smallValid; decide +kernel

private theorem sp2695 : smallValid 2695 64 := by unfold smallValid; decide +kernel

private theorem sp2759 : smallValid 2759 32 := by unfold smallValid; decide +kernel

private theorem sp2791 : smallValid 2791 33 := by unfold smallValid; decide +kernel

private theorem sp2824 : smallValid 2824 64 := by unfold smallValid; decide +kernel

private theorem sp2888 : smallValid 2888 64 := by unfold smallValid; decide +kernel

private theorem sp2952 : smallValid 2952 64 := by unfold smallValid; decide +kernel

private theorem sp3016 : smallValid 3016 32 := by unfold smallValid; decide +kernel

private theorem sp3048 : smallValid 3048 33 := by unfold smallValid; decide +kernel

private theorem sp3081 : smallValid 3081 64 := by unfold smallValid; decide +kernel

private theorem sp3145 : smallValid 3145 64 := by unfold smallValid; decide +kernel

private theorem sp3209 : smallValid 3209 64 := by unfold smallValid; decide +kernel

private theorem sp3273 : smallValid 3273 64 := by unfold smallValid; decide +kernel

private theorem sp3337 : smallValid 3337 64 := by unfold smallValid; decide +kernel

private theorem sp3401 : smallValid 3401 64 := by unfold smallValid; decide +kernel

private theorem sp3465 : smallValid 3465 64 := by unfold smallValid; decide +kernel

private theorem sp3529 : smallValid 3529 32 := by unfold smallValid; decide +kernel

private theorem sp3561 : smallValid 3561 33 := by unfold smallValid; decide +kernel

private theorem sp3594 : smallValid 3594 64 := by unfold smallValid; decide +kernel

private theorem sp3658 : smallValid 3658 64 := by unfold smallValid; decide +kernel

private theorem sp3722 : smallValid 3722 64 := by unfold smallValid; decide +kernel

private theorem sp3786 : smallValid 3786 32 := by unfold smallValid; decide +kernel

private theorem sp3818 : smallValid 3818 33 := by unfold smallValid; decide +kernel

private theorem sp3851 : smallValid 3851 64 := by unfold smallValid; decide +kernel

private theorem sp3915 : smallValid 3915 64 := by unfold smallValid; decide +kernel

private theorem sp3979 : smallValid 3979 64 := by unfold smallValid; decide +kernel

private theorem sp4043 : smallValid 4043 32 := by unfold smallValid; decide +kernel

private theorem sp4075 : smallValid 4075 33 := by unfold smallValid; decide +kernel

private theorem sp4108 : smallValid 4108 64 := by unfold smallValid; decide +kernel

private theorem sp4172 : smallValid 4172 64 := by unfold smallValid; decide +kernel

private theorem sp4236 : smallValid 4236 64 := by unfold smallValid; decide +kernel

private theorem sp4300 : smallValid 4300 64 := by unfold smallValid; decide +kernel

private theorem sp4364 : smallValid 4364 64 := by unfold smallValid; decide +kernel

private theorem sp4428 : smallValid 4428 64 := by unfold smallValid; decide +kernel

private theorem sp4492 : smallValid 4492 64 := by unfold smallValid; decide +kernel

private theorem sp4556 : smallValid 4556 32 := by unfold smallValid; decide +kernel

private theorem sp4588 : smallValid 4588 33 := by unfold smallValid; decide +kernel

private theorem sp4621 : smallValid 4621 64 := by unfold smallValid; decide +kernel

private theorem sp4685 : smallValid 4685 64 := by unfold smallValid; decide +kernel

private theorem sp4749 : smallValid 4749 64 := by unfold smallValid; decide +kernel

private theorem sp4813 : smallValid 4813 32 := by unfold smallValid; decide +kernel

private theorem sp4845 : smallValid 4845 33 := by unfold smallValid; decide +kernel

private theorem sp4878 : smallValid 4878 64 := by unfold smallValid; decide +kernel

private theorem sp4942 : smallValid 4942 64 := by unfold smallValid; decide +kernel

private theorem sp5006 : smallValid 5006 64 := by unfold smallValid; decide +kernel

private theorem sp5070 : smallValid 5070 32 := by unfold smallValid; decide +kernel

private theorem sp5102 : smallValid 5102 33 := by unfold smallValid; decide +kernel

private theorem sp5135 : smallValid 5135 64 := by unfold smallValid; decide +kernel

private theorem sp5199 : smallValid 5199 64 := by unfold smallValid; decide +kernel

private theorem sp5263 : smallValid 5263 64 := by unfold smallValid; decide +kernel

private theorem sp5327 : smallValid 5327 64 := by unfold smallValid; decide +kernel

private theorem sp5391 : smallValid 5391 64 := by unfold smallValid; decide +kernel

private theorem sp5455 : smallValid 5455 64 := by unfold smallValid; decide +kernel

private theorem sp5519 : smallValid 5519 64 := by unfold smallValid; decide +kernel

private theorem sp5583 : smallValid 5583 32 := by unfold smallValid; decide +kernel

private theorem sp5615 : smallValid 5615 33 := by unfold smallValid; decide +kernel

private theorem sp5648 : smallValid 5648 64 := by unfold smallValid; decide +kernel

private theorem sp5712 : smallValid 5712 64 := by unfold smallValid; decide +kernel

private theorem sp5776 : smallValid 5776 64 := by unfold smallValid; decide +kernel

private theorem sp5840 : smallValid 5840 32 := by unfold smallValid; decide +kernel

private theorem sp5872 : smallValid 5872 33 := by unfold smallValid; decide +kernel

private theorem sp5905 : smallValid 5905 64 := by unfold smallValid; decide +kernel

private theorem sp5969 : smallValid 5969 64 := by unfold smallValid; decide +kernel

private theorem sp6033 : smallValid 6033 64 := by unfold smallValid; decide +kernel

private theorem sp6097 : smallValid 6097 32 := by unfold smallValid; decide +kernel

private theorem sp6129 : smallValid 6129 33 := by unfold smallValid; decide +kernel

private theorem sp6162 : smallValid 6162 64 := by unfold smallValid; decide +kernel

private theorem sp6226 : smallValid 6226 64 := by unfold smallValid; decide +kernel

private theorem sp6290 : smallValid 6290 64 := by unfold smallValid; decide +kernel

private theorem sp6354 : smallValid 6354 64 := by unfold smallValid; decide +kernel

private theorem sp6418 : smallValid 6418 64 := by unfold smallValid; decide +kernel

private theorem sp6482 : smallValid 6482 64 := by unfold smallValid; decide +kernel

private theorem sp6546 : smallValid 6546 64 := by unfold smallValid; decide +kernel

private theorem sp6610 : smallValid 6610 32 := by unfold smallValid; decide +kernel

private theorem sp6642 : smallValid 6642 33 := by unfold smallValid; decide +kernel

private theorem sp6675 : smallValid 6675 64 := by unfold smallValid; decide +kernel

private theorem sp6739 : smallValid 6739 64 := by unfold smallValid; decide +kernel

private theorem sp6803 : smallValid 6803 64 := by unfold smallValid; decide +kernel

private theorem sp6867 : smallValid 6867 32 := by unfold smallValid; decide +kernel

private theorem sp6899 : smallValid 6899 33 := by unfold smallValid; decide +kernel

private theorem sp6932 : smallValid 6932 64 := by unfold smallValid; decide +kernel

private theorem sp6996 : smallValid 6996 64 := by unfold smallValid; decide +kernel

private theorem sp7060 : smallValid 7060 64 := by unfold smallValid; decide +kernel

private theorem sp7124 : smallValid 7124 32 := by unfold smallValid; decide +kernel

private theorem sp7156 : smallValid 7156 33 := by unfold smallValid; decide +kernel

private theorem sp7189 : smallValid 7189 64 := by unfold smallValid; decide +kernel

private theorem sp7253 : smallValid 7253 64 := by unfold smallValid; decide +kernel

private theorem sp7317 : smallValid 7317 64 := by unfold smallValid; decide +kernel

private theorem sp7381 : smallValid 7381 64 := by unfold smallValid; decide +kernel

private theorem sp7445 : smallValid 7445 64 := by unfold smallValid; decide +kernel

private theorem sp7509 : smallValid 7509 64 := by unfold smallValid; decide +kernel

private theorem sp7573 : smallValid 7573 64 := by unfold smallValid; decide +kernel

private theorem sp7637 : smallValid 7637 32 := by unfold smallValid; decide +kernel

private theorem sp7669 : smallValid 7669 33 := by unfold smallValid; decide +kernel

private theorem sp7702 : smallValid 7702 64 := by unfold smallValid; decide +kernel

private theorem sp7766 : smallValid 7766 64 := by unfold smallValid; decide +kernel

private theorem sp7830 : smallValid 7830 64 := by unfold smallValid; decide +kernel

private theorem sp7894 : smallValid 7894 32 := by unfold smallValid; decide +kernel

private theorem sp7926 : smallValid 7926 33 := by unfold smallValid; decide +kernel

private theorem sp7959 : smallValid 7959 64 := by unfold smallValid; decide +kernel

private theorem sp8023 : smallValid 8023 64 := by unfold smallValid; decide +kernel

private theorem sp8087 : smallValid 8087 64 := by unfold smallValid; decide +kernel

private theorem sp8151 : smallValid 8151 32 := by unfold smallValid; decide +kernel

private theorem sp8183 : smallValid 8183 33 := by unfold smallValid; decide +kernel

private theorem sp8216 : smallValid 8216 64 := by unfold smallValid; decide +kernel

private theorem sp8280 : smallValid 8280 64 := by unfold smallValid; decide +kernel

private theorem sp8344 : smallValid 8344 64 := by unfold smallValid; decide +kernel

private theorem sp8408 : smallValid 8408 64 := by unfold smallValid; decide +kernel

private theorem sp8472 : smallValid 8472 64 := by unfold smallValid; decide +kernel

private theorem sp8536 : smallValid 8536 64 := by unfold smallValid; decide +kernel

private theorem sp8600 : smallValid 8600 64 := by unfold smallValid; decide +kernel

private theorem sp8664 : smallValid 8664 32 := by unfold smallValid; decide +kernel

private theorem sp8696 : smallValid 8696 33 := by unfold smallValid; decide +kernel

private theorem sp8729 : smallValid 8729 64 := by unfold smallValid; decide +kernel

private theorem sp8793 : smallValid 8793 64 := by unfold smallValid; decide +kernel

private theorem sp8857 : smallValid 8857 64 := by unfold smallValid; decide +kernel

private theorem sp8921 : smallValid 8921 32 := by unfold smallValid; decide +kernel

private theorem sp8953 : smallValid 8953 33 := by unfold smallValid; decide +kernel

private theorem sp8986 : smallValid 8986 64 := by unfold smallValid; decide +kernel

private theorem sp9050 : smallValid 9050 64 := by unfold smallValid; decide +kernel

private theorem sp9114 : smallValid 9114 64 := by unfold smallValid; decide +kernel

private theorem sp9178 : smallValid 9178 32 := by unfold smallValid; decide +kernel

private theorem sp9210 : smallValid 9210 33 := by unfold smallValid; decide +kernel

private theorem sp9243 : smallValid 9243 64 := by unfold smallValid; decide +kernel

private theorem sp9307 : smallValid 9307 64 := by unfold smallValid; decide +kernel

private theorem sp9371 : smallValid 9371 64 := by unfold smallValid; decide +kernel

private theorem sp9435 : smallValid 9435 64 := by unfold smallValid; decide +kernel

private theorem sp9499 : smallValid 9499 64 := by unfold smallValid; decide +kernel

private theorem sp9563 : smallValid 9563 64 := by unfold smallValid; decide +kernel

private theorem sp9627 : smallValid 9627 64 := by unfold smallValid; decide +kernel

private theorem sp9691 : smallValid 9691 32 := by unfold smallValid; decide +kernel

private theorem sp9723 : smallValid 9723 33 := by unfold smallValid; decide +kernel

private theorem sp9756 : smallValid 9756 64 := by unfold smallValid; decide +kernel

private theorem sp9820 : smallValid 9820 64 := by unfold smallValid; decide +kernel

private theorem sp9884 : smallValid 9884 64 := by unfold smallValid; decide +kernel

private theorem sp9948 : smallValid 9948 32 := by unfold smallValid; decide +kernel

private theorem sp9980 : smallValid 9980 33 := by unfold smallValid; decide +kernel

private theorem sp10013 : smallValid 10013 64 := by unfold smallValid; decide +kernel

private theorem sp10077 : smallValid 10077 64 := by unfold smallValid; decide +kernel

private theorem sp10141 : smallValid 10141 64 := by unfold smallValid; decide +kernel

private theorem sp10205 : smallValid 10205 32 := by unfold smallValid; decide +kernel

private theorem sp10237 : smallValid 10237 33 := by unfold smallValid; decide +kernel

private theorem sp10270 : smallValid 10270 64 := by unfold smallValid; decide +kernel

private theorem sp10334 : smallValid 10334 64 := by unfold smallValid; decide +kernel

private theorem sp10398 : smallValid 10398 64 := by unfold smallValid; decide +kernel

private theorem sp10462 : smallValid 10462 64 := by unfold smallValid; decide +kernel

private theorem sp10526 : smallValid 10526 64 := by unfold smallValid; decide +kernel

private theorem sp10590 : smallValid 10590 64 := by unfold smallValid; decide +kernel

private theorem sp10654 : smallValid 10654 64 := by unfold smallValid; decide +kernel

private theorem sp10718 : smallValid 10718 32 := by unfold smallValid; decide +kernel

private theorem sp10750 : smallValid 10750 33 := by unfold smallValid; decide +kernel

private theorem sp10783 : smallValid 10783 64 := by unfold smallValid; decide +kernel

private theorem sp10847 : smallValid 10847 64 := by unfold smallValid; decide +kernel

private theorem sp10911 : smallValid 10911 64 := by unfold smallValid; decide +kernel

private theorem sp10975 : smallValid 10975 32 := by unfold smallValid; decide +kernel

private theorem sp11007 : smallValid 11007 33 := by unfold smallValid; decide +kernel

private theorem sp11040 : smallValid 11040 64 := by unfold smallValid; decide +kernel

private theorem sp11104 : smallValid 11104 64 := by unfold smallValid; decide +kernel

private theorem sp11168 : smallValid 11168 64 := by unfold smallValid; decide +kernel

private theorem sp11232 : smallValid 11232 32 := by unfold smallValid; decide +kernel

private theorem sp11264 : smallValid 11264 33 := by unfold smallValid; decide +kernel

private theorem sp11297 : smallValid 11297 64 := by unfold smallValid; decide +kernel

private theorem sp11361 : smallValid 11361 64 := by unfold smallValid; decide +kernel

private theorem sp11425 : smallValid 11425 64 := by unfold smallValid; decide +kernel

private theorem sp11489 : smallValid 11489 64 := by unfold smallValid; decide +kernel

private theorem sp11553 : smallValid 11553 64 := by unfold smallValid; decide +kernel

private theorem sp11617 : smallValid 11617 64 := by unfold smallValid; decide +kernel

private theorem sp11681 : smallValid 11681 64 := by unfold smallValid; decide +kernel

private theorem sp11745 : smallValid 11745 32 := by unfold smallValid; decide +kernel

private theorem sp11777 : smallValid 11777 33 := by unfold smallValid; decide +kernel

private theorem sp11810 : smallValid 11810 64 := by unfold smallValid; decide +kernel

private theorem sp11874 : smallValid 11874 64 := by unfold smallValid; decide +kernel

private theorem sp11938 : smallValid 11938 64 := by unfold smallValid; decide +kernel

private theorem sp12002 : smallValid 12002 32 := by unfold smallValid; decide +kernel

private theorem sp12034 : smallValid 12034 33 := by unfold smallValid; decide +kernel

private theorem sp12067 : smallValid 12067 64 := by unfold smallValid; decide +kernel

private theorem sp12131 : smallValid 12131 64 := by unfold smallValid; decide +kernel

private theorem sp12195 : smallValid 12195 64 := by unfold smallValid; decide +kernel

private theorem sp12259 : smallValid 12259 32 := by unfold smallValid; decide +kernel

private theorem sp12291 : smallValid 12291 33 := by unfold smallValid; decide +kernel

private theorem sp12324 : smallValid 12324 64 := by unfold smallValid; decide +kernel

private theorem sp12388 : smallValid 12388 64 := by unfold smallValid; decide +kernel

private theorem sp12452 : smallValid 12452 64 := by unfold smallValid; decide +kernel

private theorem sp12516 : smallValid 12516 64 := by unfold smallValid; decide +kernel

private theorem sp12580 : smallValid 12580 64 := by unfold smallValid; decide +kernel

private theorem sp12644 : smallValid 12644 64 := by unfold smallValid; decide +kernel

private theorem sp12708 : smallValid 12708 64 := by unfold smallValid; decide +kernel

private theorem sp12772 : smallValid 12772 32 := by unfold smallValid; decide +kernel

private theorem sp12804 : smallValid 12804 33 := by unfold smallValid; decide +kernel

private theorem sp12837 : smallValid 12837 64 := by unfold smallValid; decide +kernel

private theorem sp12901 : smallValid 12901 64 := by unfold smallValid; decide +kernel

private theorem sp12965 : smallValid 12965 64 := by unfold smallValid; decide +kernel

private theorem sp13029 : smallValid 13029 32 := by unfold smallValid; decide +kernel

private theorem sp13061 : smallValid 13061 33 := by unfold smallValid; decide +kernel

private theorem sp13094 : smallValid 13094 64 := by unfold smallValid; decide +kernel

private theorem sp13158 : smallValid 13158 64 := by unfold smallValid; decide +kernel

private theorem sp13222 : smallValid 13222 64 := by unfold smallValid; decide +kernel

private theorem sp13286 : smallValid 13286 32 := by unfold smallValid; decide +kernel

private theorem sp13318 : smallValid 13318 33 := by unfold smallValid; decide +kernel

private theorem sp13351 : smallValid 13351 64 := by unfold smallValid; decide +kernel

private theorem sp13415 : smallValid 13415 64 := by unfold smallValid; decide +kernel

private theorem sp13479 : smallValid 13479 64 := by unfold smallValid; decide +kernel

private theorem sp13543 : smallValid 13543 64 := by unfold smallValid; decide +kernel

private theorem sp13607 : smallValid 13607 64 := by unfold smallValid; decide +kernel

private theorem sp13671 : smallValid 13671 64 := by unfold smallValid; decide +kernel

private theorem sp13735 : smallValid 13735 64 := by unfold smallValid; decide +kernel

private theorem sp13799 : smallValid 13799 32 := by unfold smallValid; decide +kernel

private theorem sp13831 : smallValid 13831 33 := by unfold smallValid; decide +kernel

private theorem sp13864 : smallValid 13864 64 := by unfold smallValid; decide +kernel

private theorem sp13928 : smallValid 13928 64 := by unfold smallValid; decide +kernel

private theorem sp13992 : smallValid 13992 64 := by unfold smallValid; decide +kernel

private theorem sp14056 : smallValid 14056 32 := by unfold smallValid; decide +kernel

private theorem sp14088 : smallValid 14088 33 := by unfold smallValid; decide +kernel

private theorem sp14121 : smallValid 14121 64 := by unfold smallValid; decide +kernel

private theorem sp14185 : smallValid 14185 64 := by unfold smallValid; decide +kernel

private theorem sp14249 : smallValid 14249 64 := by unfold smallValid; decide +kernel

private theorem sp14313 : smallValid 14313 32 := by unfold smallValid; decide +kernel

private theorem sp14345 : smallValid 14345 33 := by unfold smallValid; decide +kernel

private theorem sp14378 : smallValid 14378 64 := by unfold smallValid; decide +kernel

private theorem sp14442 : smallValid 14442 64 := by unfold smallValid; decide +kernel

private theorem sp14506 : smallValid 14506 64 := by unfold smallValid; decide +kernel

private theorem sp14570 : smallValid 14570 64 := by unfold smallValid; decide +kernel

private theorem sp14634 : smallValid 14634 64 := by unfold smallValid; decide +kernel

private theorem sp14698 : smallValid 14698 64 := by unfold smallValid; decide +kernel

private theorem sp14762 : smallValid 14762 64 := by unfold smallValid; decide +kernel

private theorem sp14826 : smallValid 14826 32 := by unfold smallValid; decide +kernel

private theorem sp14858 : smallValid 14858 33 := by unfold smallValid; decide +kernel

private theorem sp14891 : smallValid 14891 64 := by unfold smallValid; decide +kernel

private theorem sp14955 : smallValid 14955 64 := by unfold smallValid; decide +kernel

private theorem sp15019 : smallValid 15019 64 := by unfold smallValid; decide +kernel

private theorem sp15083 : smallValid 15083 32 := by unfold smallValid; decide +kernel

private theorem sp15115 : smallValid 15115 33 := by unfold smallValid; decide +kernel

private theorem sp15148 : smallValid 15148 64 := by unfold smallValid; decide +kernel

private theorem sp15212 : smallValid 15212 64 := by unfold smallValid; decide +kernel

private theorem sp15276 : smallValid 15276 64 := by unfold smallValid; decide +kernel

private theorem sp15340 : smallValid 15340 32 := by unfold smallValid; decide +kernel

private theorem sp15372 : smallValid 15372 33 := by unfold smallValid; decide +kernel

private theorem sp15405 : smallValid 15405 64 := by unfold smallValid; decide +kernel

private theorem sp15469 : smallValid 15469 64 := by unfold smallValid; decide +kernel

private theorem sp15533 : smallValid 15533 64 := by unfold smallValid; decide +kernel

private theorem sp15597 : smallValid 15597 64 := by unfold smallValid; decide +kernel

private theorem sp15661 : smallValid 15661 64 := by unfold smallValid; decide +kernel

private theorem sp15725 : smallValid 15725 64 := by unfold smallValid; decide +kernel

private theorem sp15789 : smallValid 15789 64 := by unfold smallValid; decide +kernel

private theorem sp15853 : smallValid 15853 32 := by unfold smallValid; decide +kernel

private theorem sp15885 : smallValid 15885 33 := by unfold smallValid; decide +kernel

private theorem sp15918 : smallValid 15918 64 := by unfold smallValid; decide +kernel

private theorem sp15982 : smallValid 15982 64 := by unfold smallValid; decide +kernel

private theorem sp16046 : smallValid 16046 64 := by unfold smallValid; decide +kernel

private theorem sp16110 : smallValid 16110 32 := by unfold smallValid; decide +kernel

private theorem sp16142 : smallValid 16142 33 := by unfold smallValid; decide +kernel

private theorem sp16175 : smallValid 16175 64 := by unfold smallValid; decide +kernel

private theorem sp16239 : smallValid 16239 64 := by unfold smallValid; decide +kernel

private theorem sp16303 : smallValid 16303 64 := by unfold smallValid; decide +kernel

private theorem sp16367 : smallValid 16367 32 := by unfold smallValid; decide +kernel

private theorem sp16399 : smallValid 16399 33 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤16431) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 16432 := (joinSmall (lo:=0) (a:=8216) (b:=8216) (joinSmall (lo:=0) (a:=4108) (b:=4108) (joinSmall (lo:=0) (a:=2054) (b:=2054) (joinSmall (lo:=0) (a:=1027) (b:=1027) (joinSmall (lo:=0) (a:=513) (b:=514) (joinSmall (lo:=0) (a:=256) (b:=257) (joinSmall (lo:=0) (a:=128) (b:=128) (joinSmall (lo:=0) (a:=64) (b:=64) sp0 sp64) (joinSmall (lo:=128) (a:=64) (b:=64) sp128 sp192)) (joinSmall (lo:=256) (a:=128) (b:=129) (joinSmall (lo:=256) (a:=64) (b:=64) sp256 sp320) (joinSmall (lo:=384) (a:=64) (b:=65) sp384 (joinSmall (lo:=448) (a:=32) (b:=33) sp448 sp480)))) (joinSmall (lo:=513) (a:=257) (b:=257) (joinSmall (lo:=513) (a:=128) (b:=129) (joinSmall (lo:=513) (a:=64) (b:=64) sp513 sp577) (joinSmall (lo:=641) (a:=64) (b:=65) sp641 (joinSmall (lo:=705) (a:=32) (b:=33) sp705 sp737))) (joinSmall (lo:=770) (a:=128) (b:=129) (joinSmall (lo:=770) (a:=64) (b:=64) sp770 sp834) (joinSmall (lo:=898) (a:=64) (b:=65) sp898 (joinSmall (lo:=962) (a:=32) (b:=33) sp962 sp994))))) (joinSmall (lo:=1027) (a:=513) (b:=514) (joinSmall (lo:=1027) (a:=256) (b:=257) (joinSmall (lo:=1027) (a:=128) (b:=128) (joinSmall (lo:=1027) (a:=64) (b:=64) sp1027 sp1091) (joinSmall (lo:=1155) (a:=64) (b:=64) sp1155 sp1219)) (joinSmall (lo:=1283) (a:=128) (b:=129) (joinSmall (lo:=1283) (a:=64) (b:=64) sp1283 sp1347) (joinSmall (lo:=1411) (a:=64) (b:=65) sp1411 (joinSmall (lo:=1475) (a:=32) (b:=33) sp1475 sp1507)))) (joinSmall (lo:=1540) (a:=257) (b:=257) (joinSmall (lo:=1540) (a:=128) (b:=129) (joinSmall (lo:=1540) (a:=64) (b:=64) sp1540 sp1604) (joinSmall (lo:=1668) (a:=64) (b:=65) sp1668 (joinSmall (lo:=1732) (a:=32) (b:=33) sp1732 sp1764))) (joinSmall (lo:=1797) (a:=128) (b:=129) (joinSmall (lo:=1797) (a:=64) (b:=64) sp1797 sp1861) (joinSmall (lo:=1925) (a:=64) (b:=65) sp1925 (joinSmall (lo:=1989) (a:=32) (b:=33) sp1989 sp2021)))))) (joinSmall (lo:=2054) (a:=1027) (b:=1027) (joinSmall (lo:=2054) (a:=513) (b:=514) (joinSmall (lo:=2054) (a:=256) (b:=257) (joinSmall (lo:=2054) (a:=128) (b:=128) (joinSmall (lo:=2054) (a:=64) (b:=64) sp2054 sp2118) (joinSmall (lo:=2182) (a:=64) (b:=64) sp2182 sp2246)) (joinSmall (lo:=2310) (a:=128) (b:=129) (joinSmall (lo:=2310) (a:=64) (b:=64) sp2310 sp2374) (joinSmall (lo:=2438) (a:=64) (b:=65) sp2438 (joinSmall (lo:=2502) (a:=32) (b:=33) sp2502 sp2534)))) (joinSmall (lo:=2567) (a:=257) (b:=257) (joinSmall (lo:=2567) (a:=128) (b:=129) (joinSmall (lo:=2567) (a:=64) (b:=64) sp2567 sp2631) (joinSmall (lo:=2695) (a:=64) (b:=65) sp2695 (joinSmall (lo:=2759) (a:=32) (b:=33) sp2759 sp2791))) (joinSmall (lo:=2824) (a:=128) (b:=129) (joinSmall (lo:=2824) (a:=64) (b:=64) sp2824 sp2888) (joinSmall (lo:=2952) (a:=64) (b:=65) sp2952 (joinSmall (lo:=3016) (a:=32) (b:=33) sp3016 sp3048))))) (joinSmall (lo:=3081) (a:=513) (b:=514) (joinSmall (lo:=3081) (a:=256) (b:=257) (joinSmall (lo:=3081) (a:=128) (b:=128) (joinSmall (lo:=3081) (a:=64) (b:=64) sp3081 sp3145) (joinSmall (lo:=3209) (a:=64) (b:=64) sp3209 sp3273)) (joinSmall (lo:=3337) (a:=128) (b:=129) (joinSmall (lo:=3337) (a:=64) (b:=64) sp3337 sp3401) (joinSmall (lo:=3465) (a:=64) (b:=65) sp3465 (joinSmall (lo:=3529) (a:=32) (b:=33) sp3529 sp3561)))) (joinSmall (lo:=3594) (a:=257) (b:=257) (joinSmall (lo:=3594) (a:=128) (b:=129) (joinSmall (lo:=3594) (a:=64) (b:=64) sp3594 sp3658) (joinSmall (lo:=3722) (a:=64) (b:=65) sp3722 (joinSmall (lo:=3786) (a:=32) (b:=33) sp3786 sp3818))) (joinSmall (lo:=3851) (a:=128) (b:=129) (joinSmall (lo:=3851) (a:=64) (b:=64) sp3851 sp3915) (joinSmall (lo:=3979) (a:=64) (b:=65) sp3979 (joinSmall (lo:=4043) (a:=32) (b:=33) sp4043 sp4075))))))) (joinSmall (lo:=4108) (a:=2054) (b:=2054) (joinSmall (lo:=4108) (a:=1027) (b:=1027) (joinSmall (lo:=4108) (a:=513) (b:=514) (joinSmall (lo:=4108) (a:=256) (b:=257) (joinSmall (lo:=4108) (a:=128) (b:=128) (joinSmall (lo:=4108) (a:=64) (b:=64) sp4108 sp4172) (joinSmall (lo:=4236) (a:=64) (b:=64) sp4236 sp4300)) (joinSmall (lo:=4364) (a:=128) (b:=129) (joinSmall (lo:=4364) (a:=64) (b:=64) sp4364 sp4428) (joinSmall (lo:=4492) (a:=64) (b:=65) sp4492 (joinSmall (lo:=4556) (a:=32) (b:=33) sp4556 sp4588)))) (joinSmall (lo:=4621) (a:=257) (b:=257) (joinSmall (lo:=4621) (a:=128) (b:=129) (joinSmall (lo:=4621) (a:=64) (b:=64) sp4621 sp4685) (joinSmall (lo:=4749) (a:=64) (b:=65) sp4749 (joinSmall (lo:=4813) (a:=32) (b:=33) sp4813 sp4845))) (joinSmall (lo:=4878) (a:=128) (b:=129) (joinSmall (lo:=4878) (a:=64) (b:=64) sp4878 sp4942) (joinSmall (lo:=5006) (a:=64) (b:=65) sp5006 (joinSmall (lo:=5070) (a:=32) (b:=33) sp5070 sp5102))))) (joinSmall (lo:=5135) (a:=513) (b:=514) (joinSmall (lo:=5135) (a:=256) (b:=257) (joinSmall (lo:=5135) (a:=128) (b:=128) (joinSmall (lo:=5135) (a:=64) (b:=64) sp5135 sp5199) (joinSmall (lo:=5263) (a:=64) (b:=64) sp5263 sp5327)) (joinSmall (lo:=5391) (a:=128) (b:=129) (joinSmall (lo:=5391) (a:=64) (b:=64) sp5391 sp5455) (joinSmall (lo:=5519) (a:=64) (b:=65) sp5519 (joinSmall (lo:=5583) (a:=32) (b:=33) sp5583 sp5615)))) (joinSmall (lo:=5648) (a:=257) (b:=257) (joinSmall (lo:=5648) (a:=128) (b:=129) (joinSmall (lo:=5648) (a:=64) (b:=64) sp5648 sp5712) (joinSmall (lo:=5776) (a:=64) (b:=65) sp5776 (joinSmall (lo:=5840) (a:=32) (b:=33) sp5840 sp5872))) (joinSmall (lo:=5905) (a:=128) (b:=129) (joinSmall (lo:=5905) (a:=64) (b:=64) sp5905 sp5969) (joinSmall (lo:=6033) (a:=64) (b:=65) sp6033 (joinSmall (lo:=6097) (a:=32) (b:=33) sp6097 sp6129)))))) (joinSmall (lo:=6162) (a:=1027) (b:=1027) (joinSmall (lo:=6162) (a:=513) (b:=514) (joinSmall (lo:=6162) (a:=256) (b:=257) (joinSmall (lo:=6162) (a:=128) (b:=128) (joinSmall (lo:=6162) (a:=64) (b:=64) sp6162 sp6226) (joinSmall (lo:=6290) (a:=64) (b:=64) sp6290 sp6354)) (joinSmall (lo:=6418) (a:=128) (b:=129) (joinSmall (lo:=6418) (a:=64) (b:=64) sp6418 sp6482) (joinSmall (lo:=6546) (a:=64) (b:=65) sp6546 (joinSmall (lo:=6610) (a:=32) (b:=33) sp6610 sp6642)))) (joinSmall (lo:=6675) (a:=257) (b:=257) (joinSmall (lo:=6675) (a:=128) (b:=129) (joinSmall (lo:=6675) (a:=64) (b:=64) sp6675 sp6739) (joinSmall (lo:=6803) (a:=64) (b:=65) sp6803 (joinSmall (lo:=6867) (a:=32) (b:=33) sp6867 sp6899))) (joinSmall (lo:=6932) (a:=128) (b:=129) (joinSmall (lo:=6932) (a:=64) (b:=64) sp6932 sp6996) (joinSmall (lo:=7060) (a:=64) (b:=65) sp7060 (joinSmall (lo:=7124) (a:=32) (b:=33) sp7124 sp7156))))) (joinSmall (lo:=7189) (a:=513) (b:=514) (joinSmall (lo:=7189) (a:=256) (b:=257) (joinSmall (lo:=7189) (a:=128) (b:=128) (joinSmall (lo:=7189) (a:=64) (b:=64) sp7189 sp7253) (joinSmall (lo:=7317) (a:=64) (b:=64) sp7317 sp7381)) (joinSmall (lo:=7445) (a:=128) (b:=129) (joinSmall (lo:=7445) (a:=64) (b:=64) sp7445 sp7509) (joinSmall (lo:=7573) (a:=64) (b:=65) sp7573 (joinSmall (lo:=7637) (a:=32) (b:=33) sp7637 sp7669)))) (joinSmall (lo:=7702) (a:=257) (b:=257) (joinSmall (lo:=7702) (a:=128) (b:=129) (joinSmall (lo:=7702) (a:=64) (b:=64) sp7702 sp7766) (joinSmall (lo:=7830) (a:=64) (b:=65) sp7830 (joinSmall (lo:=7894) (a:=32) (b:=33) sp7894 sp7926))) (joinSmall (lo:=7959) (a:=128) (b:=129) (joinSmall (lo:=7959) (a:=64) (b:=64) sp7959 sp8023) (joinSmall (lo:=8087) (a:=64) (b:=65) sp8087 (joinSmall (lo:=8151) (a:=32) (b:=33) sp8151 sp8183)))))))) (joinSmall (lo:=8216) (a:=4108) (b:=4108) (joinSmall (lo:=8216) (a:=2054) (b:=2054) (joinSmall (lo:=8216) (a:=1027) (b:=1027) (joinSmall (lo:=8216) (a:=513) (b:=514) (joinSmall (lo:=8216) (a:=256) (b:=257) (joinSmall (lo:=8216) (a:=128) (b:=128) (joinSmall (lo:=8216) (a:=64) (b:=64) sp8216 sp8280) (joinSmall (lo:=8344) (a:=64) (b:=64) sp8344 sp8408)) (joinSmall (lo:=8472) (a:=128) (b:=129) (joinSmall (lo:=8472) (a:=64) (b:=64) sp8472 sp8536) (joinSmall (lo:=8600) (a:=64) (b:=65) sp8600 (joinSmall (lo:=8664) (a:=32) (b:=33) sp8664 sp8696)))) (joinSmall (lo:=8729) (a:=257) (b:=257) (joinSmall (lo:=8729) (a:=128) (b:=129) (joinSmall (lo:=8729) (a:=64) (b:=64) sp8729 sp8793) (joinSmall (lo:=8857) (a:=64) (b:=65) sp8857 (joinSmall (lo:=8921) (a:=32) (b:=33) sp8921 sp8953))) (joinSmall (lo:=8986) (a:=128) (b:=129) (joinSmall (lo:=8986) (a:=64) (b:=64) sp8986 sp9050) (joinSmall (lo:=9114) (a:=64) (b:=65) sp9114 (joinSmall (lo:=9178) (a:=32) (b:=33) sp9178 sp9210))))) (joinSmall (lo:=9243) (a:=513) (b:=514) (joinSmall (lo:=9243) (a:=256) (b:=257) (joinSmall (lo:=9243) (a:=128) (b:=128) (joinSmall (lo:=9243) (a:=64) (b:=64) sp9243 sp9307) (joinSmall (lo:=9371) (a:=64) (b:=64) sp9371 sp9435)) (joinSmall (lo:=9499) (a:=128) (b:=129) (joinSmall (lo:=9499) (a:=64) (b:=64) sp9499 sp9563) (joinSmall (lo:=9627) (a:=64) (b:=65) sp9627 (joinSmall (lo:=9691) (a:=32) (b:=33) sp9691 sp9723)))) (joinSmall (lo:=9756) (a:=257) (b:=257) (joinSmall (lo:=9756) (a:=128) (b:=129) (joinSmall (lo:=9756) (a:=64) (b:=64) sp9756 sp9820) (joinSmall (lo:=9884) (a:=64) (b:=65) sp9884 (joinSmall (lo:=9948) (a:=32) (b:=33) sp9948 sp9980))) (joinSmall (lo:=10013) (a:=128) (b:=129) (joinSmall (lo:=10013) (a:=64) (b:=64) sp10013 sp10077) (joinSmall (lo:=10141) (a:=64) (b:=65) sp10141 (joinSmall (lo:=10205) (a:=32) (b:=33) sp10205 sp10237)))))) (joinSmall (lo:=10270) (a:=1027) (b:=1027) (joinSmall (lo:=10270) (a:=513) (b:=514) (joinSmall (lo:=10270) (a:=256) (b:=257) (joinSmall (lo:=10270) (a:=128) (b:=128) (joinSmall (lo:=10270) (a:=64) (b:=64) sp10270 sp10334) (joinSmall (lo:=10398) (a:=64) (b:=64) sp10398 sp10462)) (joinSmall (lo:=10526) (a:=128) (b:=129) (joinSmall (lo:=10526) (a:=64) (b:=64) sp10526 sp10590) (joinSmall (lo:=10654) (a:=64) (b:=65) sp10654 (joinSmall (lo:=10718) (a:=32) (b:=33) sp10718 sp10750)))) (joinSmall (lo:=10783) (a:=257) (b:=257) (joinSmall (lo:=10783) (a:=128) (b:=129) (joinSmall (lo:=10783) (a:=64) (b:=64) sp10783 sp10847) (joinSmall (lo:=10911) (a:=64) (b:=65) sp10911 (joinSmall (lo:=10975) (a:=32) (b:=33) sp10975 sp11007))) (joinSmall (lo:=11040) (a:=128) (b:=129) (joinSmall (lo:=11040) (a:=64) (b:=64) sp11040 sp11104) (joinSmall (lo:=11168) (a:=64) (b:=65) sp11168 (joinSmall (lo:=11232) (a:=32) (b:=33) sp11232 sp11264))))) (joinSmall (lo:=11297) (a:=513) (b:=514) (joinSmall (lo:=11297) (a:=256) (b:=257) (joinSmall (lo:=11297) (a:=128) (b:=128) (joinSmall (lo:=11297) (a:=64) (b:=64) sp11297 sp11361) (joinSmall (lo:=11425) (a:=64) (b:=64) sp11425 sp11489)) (joinSmall (lo:=11553) (a:=128) (b:=129) (joinSmall (lo:=11553) (a:=64) (b:=64) sp11553 sp11617) (joinSmall (lo:=11681) (a:=64) (b:=65) sp11681 (joinSmall (lo:=11745) (a:=32) (b:=33) sp11745 sp11777)))) (joinSmall (lo:=11810) (a:=257) (b:=257) (joinSmall (lo:=11810) (a:=128) (b:=129) (joinSmall (lo:=11810) (a:=64) (b:=64) sp11810 sp11874) (joinSmall (lo:=11938) (a:=64) (b:=65) sp11938 (joinSmall (lo:=12002) (a:=32) (b:=33) sp12002 sp12034))) (joinSmall (lo:=12067) (a:=128) (b:=129) (joinSmall (lo:=12067) (a:=64) (b:=64) sp12067 sp12131) (joinSmall (lo:=12195) (a:=64) (b:=65) sp12195 (joinSmall (lo:=12259) (a:=32) (b:=33) sp12259 sp12291))))))) (joinSmall (lo:=12324) (a:=2054) (b:=2054) (joinSmall (lo:=12324) (a:=1027) (b:=1027) (joinSmall (lo:=12324) (a:=513) (b:=514) (joinSmall (lo:=12324) (a:=256) (b:=257) (joinSmall (lo:=12324) (a:=128) (b:=128) (joinSmall (lo:=12324) (a:=64) (b:=64) sp12324 sp12388) (joinSmall (lo:=12452) (a:=64) (b:=64) sp12452 sp12516)) (joinSmall (lo:=12580) (a:=128) (b:=129) (joinSmall (lo:=12580) (a:=64) (b:=64) sp12580 sp12644) (joinSmall (lo:=12708) (a:=64) (b:=65) sp12708 (joinSmall (lo:=12772) (a:=32) (b:=33) sp12772 sp12804)))) (joinSmall (lo:=12837) (a:=257) (b:=257) (joinSmall (lo:=12837) (a:=128) (b:=129) (joinSmall (lo:=12837) (a:=64) (b:=64) sp12837 sp12901) (joinSmall (lo:=12965) (a:=64) (b:=65) sp12965 (joinSmall (lo:=13029) (a:=32) (b:=33) sp13029 sp13061))) (joinSmall (lo:=13094) (a:=128) (b:=129) (joinSmall (lo:=13094) (a:=64) (b:=64) sp13094 sp13158) (joinSmall (lo:=13222) (a:=64) (b:=65) sp13222 (joinSmall (lo:=13286) (a:=32) (b:=33) sp13286 sp13318))))) (joinSmall (lo:=13351) (a:=513) (b:=514) (joinSmall (lo:=13351) (a:=256) (b:=257) (joinSmall (lo:=13351) (a:=128) (b:=128) (joinSmall (lo:=13351) (a:=64) (b:=64) sp13351 sp13415) (joinSmall (lo:=13479) (a:=64) (b:=64) sp13479 sp13543)) (joinSmall (lo:=13607) (a:=128) (b:=129) (joinSmall (lo:=13607) (a:=64) (b:=64) sp13607 sp13671) (joinSmall (lo:=13735) (a:=64) (b:=65) sp13735 (joinSmall (lo:=13799) (a:=32) (b:=33) sp13799 sp13831)))) (joinSmall (lo:=13864) (a:=257) (b:=257) (joinSmall (lo:=13864) (a:=128) (b:=129) (joinSmall (lo:=13864) (a:=64) (b:=64) sp13864 sp13928) (joinSmall (lo:=13992) (a:=64) (b:=65) sp13992 (joinSmall (lo:=14056) (a:=32) (b:=33) sp14056 sp14088))) (joinSmall (lo:=14121) (a:=128) (b:=129) (joinSmall (lo:=14121) (a:=64) (b:=64) sp14121 sp14185) (joinSmall (lo:=14249) (a:=64) (b:=65) sp14249 (joinSmall (lo:=14313) (a:=32) (b:=33) sp14313 sp14345)))))) (joinSmall (lo:=14378) (a:=1027) (b:=1027) (joinSmall (lo:=14378) (a:=513) (b:=514) (joinSmall (lo:=14378) (a:=256) (b:=257) (joinSmall (lo:=14378) (a:=128) (b:=128) (joinSmall (lo:=14378) (a:=64) (b:=64) sp14378 sp14442) (joinSmall (lo:=14506) (a:=64) (b:=64) sp14506 sp14570)) (joinSmall (lo:=14634) (a:=128) (b:=129) (joinSmall (lo:=14634) (a:=64) (b:=64) sp14634 sp14698) (joinSmall (lo:=14762) (a:=64) (b:=65) sp14762 (joinSmall (lo:=14826) (a:=32) (b:=33) sp14826 sp14858)))) (joinSmall (lo:=14891) (a:=257) (b:=257) (joinSmall (lo:=14891) (a:=128) (b:=129) (joinSmall (lo:=14891) (a:=64) (b:=64) sp14891 sp14955) (joinSmall (lo:=15019) (a:=64) (b:=65) sp15019 (joinSmall (lo:=15083) (a:=32) (b:=33) sp15083 sp15115))) (joinSmall (lo:=15148) (a:=128) (b:=129) (joinSmall (lo:=15148) (a:=64) (b:=64) sp15148 sp15212) (joinSmall (lo:=15276) (a:=64) (b:=65) sp15276 (joinSmall (lo:=15340) (a:=32) (b:=33) sp15340 sp15372))))) (joinSmall (lo:=15405) (a:=513) (b:=514) (joinSmall (lo:=15405) (a:=256) (b:=257) (joinSmall (lo:=15405) (a:=128) (b:=128) (joinSmall (lo:=15405) (a:=64) (b:=64) sp15405 sp15469) (joinSmall (lo:=15533) (a:=64) (b:=64) sp15533 sp15597)) (joinSmall (lo:=15661) (a:=128) (b:=129) (joinSmall (lo:=15661) (a:=64) (b:=64) sp15661 sp15725) (joinSmall (lo:=15789) (a:=64) (b:=65) sp15789 (joinSmall (lo:=15853) (a:=32) (b:=33) sp15853 sp15885)))) (joinSmall (lo:=15918) (a:=257) (b:=257) (joinSmall (lo:=15918) (a:=128) (b:=129) (joinSmall (lo:=15918) (a:=64) (b:=64) sp15918 sp15982) (joinSmall (lo:=16046) (a:=64) (b:=65) sp16046 (joinSmall (lo:=16110) (a:=32) (b:=33) sp16110 sp16142))) (joinSmall (lo:=16175) (a:=128) (b:=129) (joinSmall (lo:=16175) (a:=64) (b:=64) sp16175 sp16239) (joinSmall (lo:=16303) (a:=64) (b:=65) sp16303 (joinSmall (lo:=16367) (a:=32) (b:=33) sp16367 sp16399)))))))))
  have good : (List.range 16432).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 270000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 16431 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 16431 := by
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


private def packet (i : ℕ) : ℕ := (if i < 69 then (if i < 34 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else 0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0 else 0) else (if i < 11 then 0 else 0)) else (if i < 14 then (if i < 13 then 0 else 0) else (if i < 15 then 0 else (if i < 16 then 0 else 0))))) else (if i < 25 then (if i < 21 then (if i < 19 then (if i < 18 then 0 else 0) else (if i < 20 then 0 else 0)) else (if i < 23 then (if i < 22 then 0 else 0) else (if i < 24 then 0 else 0))) else (if i < 29 then (if i < 27 then (if i < 26 then 0 else 0) else (if i < 28 then 0 else 0)) else (if i < 31 then (if i < 30 then 0 else 0) else (if i < 32 then 0 else (if i < 33 then 0 else 0)))))) else (if i < 51 then (if i < 42 then (if i < 38 then (if i < 36 then (if i < 35 then 0 else 0) else (if i < 37 then 0 else 0)) else (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0))) else (if i < 46 then (if i < 44 then (if i < 43 then 0 else 0) else (if i < 45 then 0 else 0)) else (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else (if i < 50 then 0 else 0))))) else (if i < 60 then (if i < 55 then (if i < 53 then (if i < 52 then 0 else 0) else (if i < 54 then 0 else 0)) else (if i < 57 then (if i < 56 then 0 else 0) else (if i < 58 then 0 else (if i < 59 then 0 else 0)))) else (if i < 64 then (if i < 62 then (if i < 61 then 0 else 0) else (if i < 63 then 0 else 0)) else (if i < 66 then (if i < 65 then 0 else 0) else (if i < 67 then 0 else (if i < 68 then 0 else 0))))))) else (if i < 103 then (if i < 86 then (if i < 77 then (if i < 73 then (if i < 71 then (if i < 70 then 0 else 0) else (if i < 72 then 0 else 0)) else (if i < 75 then (if i < 74 then 0 else 0) else (if i < 76 then 0 else 0))) else (if i < 81 then (if i < 79 then (if i < 78 then 0 else 0) else (if i < 80 then 0 else 0)) else (if i < 83 then (if i < 82 then 0 else 0) else (if i < 84 then 0 else (if i < 85 then 0 else 0))))) else (if i < 94 then (if i < 90 then (if i < 88 then (if i < 87 then 0 else 0) else (if i < 89 then 0 else 0)) else (if i < 92 then (if i < 91 then 0 else 0) else (if i < 93 then 0 else 0))) else (if i < 98 then (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else 0)) else (if i < 100 then (if i < 99 then 0 else 0) else (if i < 101 then 0 else (if i < 102 then 0 else 0)))))) else (if i < 120 then (if i < 111 then (if i < 107 then (if i < 105 then (if i < 104 then 0 else 0) else (if i < 106 then 0 else 0)) else (if i < 109 then (if i < 108 then 0 else 0) else (if i < 110 then 0 else 0))) else (if i < 115 then (if i < 113 then (if i < 112 then 0 else 0) else (if i < 114 then 0 else 0)) else (if i < 117 then (if i < 116 then 0 else 0) else (if i < 118 then 0 else (if i < 119 then 0 else 0))))) else (if i < 129 then (if i < 124 then (if i < 122 then (if i < 121 then 0 else 0) else (if i < 123 then 0 else 0)) else (if i < 126 then (if i < 125 then 0xcd5be42da15709ea48d2178f046bc30315389083c618909102f80c4000cd55bd2ea15bc9fa4992180f6870031215288e03a617008a82cc0a8000cd4fa22dc955c9e649b21c8f606dc30c15188e43b217c09103380d6000cd49413009660a7c4d4236100873433e169899c3ea19909a83280d0000cd43162e395949fc4982168f386dc30314c88fc3c218009083040ba000cd3d042d295189ba47e20d0ef86bc30315608e83ae17408c02f40bc000cd36e72d9156c9e44962148f3c6d030e15509203cc18909403280d4000cd30b92e915cca364b02298fbc72c32b167099c3fe19f09703000ba000cd2a6b2f315eca2e4b02278fbc71433316009683f218909882fc0be000cd24282ef15f8a3a4be22b0ff071e32d16709ac40a19609d03300ca000cd1ded2ec15c4a104a42198f3c6d030014c88f43b217c08d02f40b8000cd17ac2eb95d0a3a4aa2290fac70631815a093c3e418e09b83440ce000cd117b2ee95e4a324b122b0fd871e33716f89c83f4199096830c0ca000cd0b202ff9680a784d32318fdc71432715e89843f418e09503180ca000cd05052e0954c9da48b2160f086c230215188fc3c418309203140b6000ccfec92f3162ca544bf22f8fe072632d16289603d8189094832c0be000ccf8912e995a4a0449c2188f686e830e15409103b418c09803200be000ccf2412f61610a3c4be2318fd472232916389943fc19309683440ce000ccec0c2e795b09e64912190f4c6da30f15909483f419a09783440d0000cce5dd2e995cca1c4a622c8fdc73233116889e04101a70a303600d4000ccdf9b2f115f8a2a4a92238fa06fc32015c89283ca17708a02e00ae000ccd9602e8958c9fe4982188f3c6ec30e15509343b217d08b82dc0ba000ccd3522d815489e24972178f286d030315209143b016d08802f00ba000cccd172f495f0a1e4b42240f7870432c16189583de18909703400d6000ccc6e42e115909ea4922128f286bc30615189143c817c09183080be000ccc09a2f295f8a2c4b12290fbc70c32015c09343d018109182fc0c4000ccba472f81634a604ce2278fa86fe314153891c3ac17308a02e40b4000ccb40d2eb15e4a2c49f21b0f1c6ce30a15209143c218009103340bc000ccadb0300965ca7e4d02359010718317161094c3e218808f82fc0c2000cca7982de15609fe49c21a8efc6c430815409543e819709903400cc000cca10b31a9704abc4fc24890a477034f16e0a1c4301b10a303540e2000cc9ac92ee95dca164a32208f346d230d154094c3da19009d83500dc000cc94772f6963ca584c82308fec72e324162098040419a09d83480d0000cc8e552e41580a0449c21a0f546de30d15088fc3c618b09283000c2000cc87eb30a16c0a844d72310fe874c34616c89e442e1b00a403680cc000cc818f2fa1634a504cd2370ff072032916389703ea18c09503180c8000cc7b4c2ee15d0a2e4b02278f8471e32b16309743fc19209b83340de000cc75192ed95e8a1c4ac2268fb072832916189803f2197097831c0c8000cc6edf2e915bca244b92278f9070432c16589843f419209403340c6000cc68982f195dca304a72228f846f031415e09643e418909182ec0c4000cc62762e1958c9ce4832108ef86c830d15b09743f219409983340c8000cc5c083019640a564c622c100473c33616c09f44261b70a403640e6000cc55e22e495909ec4982198f586ec30e15389203da18309483080c0000cc4fc72da953c9de48a2120ef86ca2f214988e03be17808882b00ba000cc49872ed95f0a164972200f346f232215d095c3e219709603180c6000cc435e2e295709e049121a0f206ce30b15889303b817909002dc0b2000cc3d092f71600a384ad2258f946fc31915909883f619309903340d8000cc36c32f89644a4c4bd2280fbc72c339164099440a1a109c032c0cc000cc30a32dd956ca224a321f8f906fa32415e09703e4198095031c0c6000cc2a812e195489dc48e20e0ed86982eb14988a839c17008d02f40b0000cc24163019698a7e4d723c103474c34416f89f04221a609a83480d6000cc1ddd2e895c4a124b022a0f8c6f031715789403d418909503080b0000cc17b32e115a8a0849c2120efc6b82fc15208f83c418d09282f80c6000cc11612f7162ca364c122a0fb870e31715a89403ca18909603100c8000cc0b2b2ea95b0a0249c21a8f2c6c030815809403e4190096031c0c2000cc05182d895589f44932168f0c6c630b14e88f43bc17608e02f40a2000cbfee32e815dca224a62208f6c6f631215789483f019509482fc0a8000cbf8e32d3152c9d048a2168f2c6be30115108f83ac17d09182f80b6000cbf2ca2db95649f44992178f446dc31715909543fe18b09202f00c0000cbec952e895d8a204b02220f7c6f431616209743dc18808e02d00c2000cbe65b2ed95d0a224ab2220f806f032216409643e218e08f83100c0000cbe0022f79630a604d22300fec73833e16f09cc4381ab09f83740f0000cbd9b12ee15d0a244b62288fac70c31615789043d418408a82d40b0000cbd38e2e415b4a0e49b2168f486e830a15589403ce17f08e02e40c8000 else 0xcee8d52e115949fe49821c8f6c6de30915308f03ba17d08a82c40c6000cee2ac2e395bca1c4ac21d8f446f431015509203d218909183380c4000cedc682e795cca144ab2258fbc70232015d894c3de17f09282f40ba000ced63e2e11580a0449b21c0f3c6de312155091c3d618308982ec0c0000ced00e2e41598a0249e21a8f386c631115989283d818a09383380c0000cec9d02ea15c0a084a321b8f646de30d15b89583da18408b82c80c4000cec3b02da95349ea4952168f1c6d230015109143d017b08b03080bc000cebd8b2e715b4a284b722e8ffc72a32816089683e818d097034c0d6000ceb7472f4161ca344b62288fb471832215789383e019009082fc0c0000ceb11e2e215b0a084992200f706fa30e15889243d618a096032c0d6000ceaacc2f4961ca404ba22c0fd471e32a16209803f419509e03780e8000cea4842f295fca424c922f8ff074833a169097c3e819009802fc0ba000ce9e502ec15aca1a4b222b0f986fa30c14d08e83a416e08a82e40b8000ce97e62fc9648a544c42300ffc73c33516809d84181a80a303800d2000ce91c32e015789f449d2170f246e430f15008ec3ae17d09203140d0000ce8b952e295649de48a2130f0c6ca30814c08c83aa16d08702e80a6000ce859b2cf14fc9ba47520b8ee06ae2f914d08d03ac16d08482c80a4000ce7f432fa964ca524c922d0ff073832e16009883ee19c09703180a8000ce79152e795909ee4a421d0f586f231515489083dc18609583180d2000ce72f32df958ca0249e21c8f706fe31314f09303d618e09203200c6000ce6cb42e915dca264ab2248fb870c31b15f09703f619009b03240ca000ce668e2e695bca0e4b32298fa86f831615c8974400196097034c0dc000ce60642e595b8a1c4a92220f8871232315d89203d418809283140ca000ce5a2f2eb958c9f649f2190f606e431615709383d618508e83040d8000ce54022e415aca224b32248fb472031f15f098c40a1a209a03540d4000ce4df02d695209de4952140f0c6b430014b08d83b017408782c809a000ce47952fc164ca384b52238f8c6f631015809243c017f08f02f00b8000ce41702dd9598a1e4ad2240f9871031d15e09703e218b095032c0b6000ce3b462e395b8a284ae2228fcc70c31d161895c40619309582fc0c4000ce34f32f61610a424be2298fb46f031c16009703fa19e09782f40b4000ce2ed42e2156c9fc49e2188f306e230415089103c017c08c03100c2000ce28b22e2958ca044962138f606fc31f15d89343d617d09683480cc000ce22682ed15e8a284a42268f9070832b15a094c3de18609303040d8000ce1c292f19604a364c622c8fe8726330161897840819109283280ca000ce160b2e4159ca0649821d0f306e230c15289103d618208b82dc0c6000ce0fd52e7158c9f64a321e8f646f831d15d897c40e1a209f034c0de000ce098a2f215f0a364b62290fd871231e16389803f419609503280c8000ce03272ff1660a684d823e108076a34a17389e041219d09f03600da000cdfd082df95709ea48d21c0f6070031c15f89603e818d09783340c4000cdf6c72f115eca344ac2288f9c70631f16189783ea18f09783340c0000cdf09a2e315809f849c2198f806ec30d15b09503d618b08c82cc0bc000cdea2f300968ca964e023c905475c34016c09d84101a80a283500d4000cde40d2dc95689f44a221c0f546da30d15b893c3d618c095832c0b6000cddde32df156c9e84962230f946ec31215689203ba18408f832c0bc000cdd7a42ef15e0a204ae2208f9870432316089883ee18f09082f80c4000cdd1612eb95a49fe4a22240f9870031d15d89743f219409803100bc000cdcb182ee95a8a0e49f21c0f6470032015d09643e818e09a03400be000cdc4f22e195909f84a521b0f5c6d230e15509383cc17808d03000b6000cdbeea2d215149b848b2150f2c6d4309154894c3e218b09583080dc000cdb8a82ee9604a3a4b322a0fb070032116089583c018008f830c0b4000cdb2652f71624a544c822c8fd473433016289783f218809482e80b2000cdac4f2dd15749f449b2150f486dc30f15789543d418709382e40c2000cda6042f29604a364a52240f906f831215c895c3ec18a09483240bc000cda0152c714e49c048720c8eb46922f014688a03a417708f03000be000cd99d62e995bca204a221a8f586ee31815a89283da18f09483340d4000cd939f2eb95c4a1a4b32240f9870231e15b895c3c817d08f03080ce000cd8d8a2e1155c9e44842148ef86a42f414d08d439e17108582b40ac000cd87662de15809ea49d21d0f4c6dc30a15a09303be18d09303200b2000cd81352e595bca184a22228f706e2310159893c3c818309203200cc000cd7b0f2dd15809e449521b0f6c6fa31a15589203c017c08f02f80b6000cd74df2e715909fc4a321e0f4c6ea30a159892c3c618508c82f00ae000cd6e892f295fca344b62208f9c6fe31a15b09443e219109603280ce000cd682f2f89640a404bd2300fc472632b15f09843ee19f095833c0e2000cd61fc2e615c0a0449e21e8f746f231315a096840619d09903140c4000) else (if i < 127 then 0xd076662eb15a0a0c4a22230f886f832515b89683d418609483340d4000d0703f2e715989ec4982190f486da30c15909543ee19409583400ce000d06a032ea15a89f049421b8f5c6f431315b893c3dc18009382fc0c8000d063dd2e4159c9fc49521d0f7c6e231515a09483e418d095831c0d6000d05da82ee9608a3a4b72258f906f831f16009844021a60a183480ba000d0575f2ed95dca264ad21d0f3c6ee31115a89443d619409103040c4000d051282ea15d8a184a521e8f346ce300150892c3d618a08e02f80c2000d04b072dd152c9d44952158f306c630915489383d618409002f80ac000d044eb2db95249ec4a221d0f346ce30714b08e43c218409183300cc000d03eca2e015a0a244a621e8f746e431c15a89583e218308e02c40ba000d038922e815d4a224a82240f346d430b153090c3c6182090830c0c0000d0322a2f69620a444c02288fa070a31a15809303cc18009083100c2000d02c172d494e09b047220c8eec6ac2fd14c08dc3ae17008d02c40aa000d025ca2f015e0a224b12208f646de311156893c3d018c09002fc0b2000d01fa52dd956c9fa4912190f686dc30d155893c3d618909a833c0ca000d0196e2eb15fca304b92270fb06fe31315c89603f2184093030c0be000d0132e2ed1604a4c4bd22d901c73e330161098040819809d03640d4000d00d072de95609f648f2168f5c6d830715789203d0189093830c0be000d006b42fb964ca384b02248fb471832815f89643e618e09503080c6000d000602f4161ca3e4bb22b8fcc71e32915f89483d618809082f40ba000cffa412df955ca0e49c2208f646ec30215a89603e418409703340c6000cff40e2e5158ca064962170f3c6e430b15a09343e218b09903180d2000cfedb72f59614a384bd2270f806fa31516009603de18c09983240bc000cfe77d2ed15d0a1e4b82250fa070a32a16409803f818c09003440e4000cfe1482e915d4a1249d2208fa070a31f15f09783f619e09e83540c8000cfdb192eb95dca244aa2288f946f031c15a89183ce18409283140c2000cfd5032e0155c9f649321a8f446da31415189343be17d08e02d4098000cfcec42e215649e64962190f186d030c157892c3d418b09803240c2000cfc88a2f095e4a1c4b322c0ffc72c336165098440219c09603040b4000cfc27b2d695249d84872170f586f031015689303d218308682fc0d2000cfbc652da94fc9c048520e8ed06b02fc15108f43ac17508c82f00ba000cfb6442df9564a0c4af22a0fc472032415f89443cc18509103000b8000cfaffd2ee15dca244ab2228fb06fa32015a09043bc17e09083040be000cfa9b22f095c8a1a4b722b8fdc71632615f898040819b0a283580ce000cfa3612f6161ca504be22e8fec73433516409a43fa19809603200ca000cf9d2a2e89598a1e4ad21e0f746f6310155890c3d218a09983040c8000cf96f82e215aca164ae2280fa86f831215c09683ea19409583140d4000cf90a92f215eca3c4b52248f9870832815f89643dc19509603080be000cf8a7f2e815e0a324b32230f8c6f0315154890c3e619909a03380c6000cf84252f99650a5e4d2232100472233516a096c3e818808e830c0b4000cf7e212d214f49cc48020e0f006c430715088f43b617208c82f80b6000cf77fa2df15509d648a2178ef86bc30215288f43d218409703340cc000cf71a72f59608a2e4b122a8fac70631d15c89203d218209302f80b8000cf6b6b2e81588a004972170f186c02ff15009003c418209483100c2000cf65332e19590a084a72210f906f831c15f89703d618609203000c0000cf5f092e295a0a044a12200f646f431e15e093c3e818909283100d4000cf58c42f215dca0c49b2198f386b430015009043c6180094033c0ca000cf525e3001658a564c0233101874e33d165898440a19909983440ca000cf4c072fb964ca564c12310fbc72032216289b841c19e09a832c0e0000cf45cd2e515a8a0c4a62238f8c6e630d15c89583e218a09083200d4000cf3f8d2f01600a384bc22b0fb870e32816289883d419009303200c0000cf395e2e19594a0a49e2168f186cc30514f88e43aa17e08e83000ca000cf33362e815c0a1e4ab2200f506e630d15989103ce189093832c0ba000cf2d1e2d7953c9d84912190f4c6ee31415e89603e018e09683340b8000cf26e02f59628a5c4c62318fdc72632d15e89843f8199097832c0b4000cf20a02ed15e4a124ae21d8f546ea31015689503ee19c09e83400e0000cf1a462f99644a444cc2318fd473432716189383d818c09603280c6000cf14372d4951c9be47420e8f006a22f714b88c03ac17708b02c40b2000cf0dfd2ea95cca304b12208f8c6f0316160097c3f619a099833c0ca000cf07ce2e695c0a0c4a02228f946f031015c09343c018509083080c8000cf01ad2e515949f24952158f386d030114f091c3c818609102fc0c2000cefb672ef95d4a1a4ae2220fb06fa31c15b89643e218309402e40ac000cef5252eb95b4a184a82238f8870232916009683da18909183100ca000ceeeec2e895dca204b12218f806ea30f15789283e218409483180d2000 else (if i < 128 then 0xd203e42f39640a364b72268f9c71c33516409c040019b09903480d4000d1fdac2ee95f4a564c42358ff474233616d89b841419809883200b4000d1f7782e395809fc4952198f286e2312158092c3c6183090030c0ba000d1f10e30796b4aa44e823c905876434917389e44201a40a203840e4000d1eaf42da9588a124a12288f9472032f162099841219c09b83280e6000d1e4e02dc15509f649521f8f846e631715c09503de17c09182ec0bc000d1de9a2f015bca164ad2230f88706325160893c3da17b09082f40d0000d1d86f2e595849fa49921a8f7c70a32115989243dc18309102f80ca000d1d2442e695a4a164a321f8f5c6fc31c15c09143d019309603400d0000d1cc092ec95c8a184a221f8f806ee31615e89603e6193098031c0b6000d1c5bc2f59614a244a92210f706ec30c155894c3da18908e82f40cc000d1bf6e2f79604a2c4bb2288fbc72431d15e098440a1a109a034c0be000d1b9382e115649d24892138f3c6e030614888fc3c017f08f02cc0be000d1b3052e795d0a184ad2220fac71232f16209803ea18f094032c0ea000d1acc32f1962ca504c12318fd472032d166099040819a09683340de000d1a6862ef95fca2a4b922a0f8070031215b09683e819609a835c0d6000d1a07a2d8952c9de4872190f3c6de31415a09383d618a09102f80aa000d19a3a2ed95eca2e4bf22b0fc870231b15909143dc18809102e80c2000d193f22ee1604a404b82290fb06fe31415c89583da19009203180d2000d18dcf2df156c9ee49c21d0f606ee31315809283d2188098030c0c4000d1879d2eb15f0a244b12238f786f832215809383d018309382f00b2000d181462fc1644a4a4bf22d8fc871e32916909944021a209983500e4000d17b262e2157ca0a4a62218f746ee30715209143c818a09283100be000d174f22f0963ca484c022a0fd872c33716789a83fc1a209a02f80b4000d16ea82f595f0a304b12270fa8702324161898c4121a409b03340c4000d168452fc1640a4e4ba22c8fb8724335166099841419f09d032c0ca000d162282df95849ec4952148efc6be2f814d89083cc17f08d83040d0000d15bf92e21584a104a82268f9071c32c16189a440019d09a034c0c2000d155c82e895d8a464b82260f8c71431f15b09443c418909103040ca000d14f8e2ee15fca284b422b0fd071031f15d091c3ba17409002f80c0000d149672e495a8a164a72258fa471031c15b09283d218809302f80c2000d1430a2fe1634a404b62298fa471c32215d09744001a209983000c8000d13cf92da95609ee49a21d8f586e030314f09243ca17708b82f40ae000d136e12da15589e24902180f3c6d631515a09343d818c09403080c6000d1308c2fb961ca404b922c8fb470c31c15a099840619309b83240d4000d12a4a2ed95e0a2a4b22268fa070231815d09543d618909383280d4000d124152ea15b8a0849c2230f706f431b16009703ee18909383400e2000d11de72e815a4a224a82228f686e8310159893c3d418509083180ba000d117912ee95f0a224ae2238fb872a325159094c3e418709282fc0ce000d111982ca14f09b847b20d8f046b02f814f89103bc18109083280d6000d10b862d395109c248b2168f386de30715108dc3be17c08782940aa000d105312f9960ca3a4b72298f9c6f230b15609243c818709403380ce000d0fee52f29608a324ba2250f9470231515d09543e6188091033c0ca000d0f8a02f515f8a424bc2260f706ee31d15e09683fa19d098832c0ca000d0f26a2eb95dca2c4b62278f686ea31b15889403d817908a02c00ba000d0ec442df95609de4882110f186d030a15609283e819809483040c4000d0e6242e29590a104ac22c8f9c71632215f09703fa19d09703180d4000d0dfba3011670a864da239902475635017309c84081a709d03380d4000d0d9722f215f8a324bb22e0ffc72e33916189b441619c0a1034c0dc000d0d3622d815209d04792108ef86d231315a093c3e818609403240c8000d0cd262ec15d0a3a4ba2280fcc72432115b097c3f2193094831c0b2000d0c7032dd95789f649e2218fa870032316209503e419309703240c8000d0c0fa2d614fc9ae47a2128f006ae2ef14d09003b417a08e83000c4000d0bab32f115eca324a52248fb870831e15b09303cc187093831c0ca000d0b4992d995449de49221b8f586f232315e09983fa1a309683300c4000d0ae552e995aca004a32208f606ee31015789143ce17c08b02dc0bc000d0a8212e0958ca004a02218f386e431715f096c3dc18609102bc0b4000d0a1f02e4958ca0049821a8f206ca30515309103c218609103100c2000d09ba52f81628a424b62290fac70632416409a84061a609c83300bc000d0956f2e895a8a184aa21f8f706f431e15f89684041a009b83440da000d08f402e695a49fa4932178f546e0311159893c3e219509302f80b6000d089282da95309e84952140f306d030015008f43a617208682fc0ca000d082ed2ed15e0a224b622d0fd472233316409943f6190096833c0c6000d07c9a2f495e8a284b122b0fdc72e327162098440e19d0a1034c0d4000 else 0xd390982df1570a0049921c8f606ea31a15b096c3ee1a009e03580ea000d38a392f81640a664d5236100071e32a16489883fc1a309d83480ce000d383f52f095dca284af2260f986fe31d160097c3f419809e034c0d0000d37dea2d415189da47d2120f146b230715309203de19309a03580be000d377a52ee95f8a2c4b62298fc072a32f16389903f418f09283340c0000d371632f115fca484ba22a0fcc71032016389a040c19a09503300d6000d36b402e415a0a244ae2210fa471e32016489643d418109582e00a8000d365142e9959ca2a4ac2268f906fa31315c096c3e618909483140c6000d35ed72ee95dca224ab2248f886f432315f89983f419a0a083300d4000d358a82ea95e4a1449d21b0f306d830015788f43c217c08c83180be000d352492fc163ca404b622f0fe871a329161896c3ec19f09e03280d2000d34bd4307969ca764db239100872c33916909a440619d098832c0be000d345c82d395189ec4932198f6c6d430615209343ca18109183240ba000d33f8f2e715b8a0649c21f8f706ec30e154890c3c418209082f80c2000d339772db95609dc49c21c8f446d831415d09383c017f090830c0cc000d333252f61630a404ba22d0fe871631d15d092c3ce18109083140ba000d32ce02f095f4a2e4b72270f886fe31e15789303e019309483180ae000d326da2cc95289d647f2130f246d230315289143d818708e03000c6000d3209b2f215e8a304b722b8f9c71c32d162094c3e019809883240ca000d31a682e715a8a0e4aa2288fc470e32d16509743f218708f82f40b8000d3144e2df15689fa49a21b8f846f231015d896440019e09a83300c8000d30e372d915489c44942130f386d630c14e08e03a817a08d830c0d2000d307e02f29600a4a4b52280fc871a32916489943fc19709703280c2000d301cd2d915509f84962168f406ea30d152891c3c618709503240ce000d2fb703001668a5c4bf22f8fe471633016109603de18b099032c0d4000d2f5392f1961ca3c4b92300fc473033216d89c841a19809783480ca000d2eeee2f19638a484ba22b8fd872e33416889a03fc19409603240c2000d2e8d82dd15449e848e2188f4c6da30915189003c418609483100c6000d2e2a42ea15e0a2c4b42278fc872632b15f89583e219209683300d8000d2dc752ef15f8a344b62238f98718329163098c41a19a0a0834c0d0000d2d6362f31608a464b92250f786fc31d15d096c3fa19009783180d2000d2d04a2c794ac9a24682068e9c69c2f214908d03ba17e08c02f00b4000d2ca182e615a4a144ab21e8f586fa32616409583e419209303080da000d2c3e92e995b8a164a621f8f7c6e831415c8960408198099832c0d8000d2bdc02e415aca0a49a21c8f706f631515b09543ee18f08e82f40b8000d2b77a2f115f0a2a4a72200fa470832916289483ee18209203080ac000d2b1252f895f8a4c4c12300fec73833816e09f44201af0a383780da000d2aaec2f095fca304ba2260f606e431214b89043b017a08b02dc0ca000d2a4d52dc95549e64922150f046cc30715489003c418108f02e40a6000d29e882ee95e8a2e4b322c0fbc70a32c162897c3ea19909703100cc000d2983e2f79610a3e4ad2298fd471e32215f096c3f819c09a83400c8000d2921f2dd15389d448a2120f006c430014d88d83a417608882c40b4000d28be82ee95f0a1c4af2208f406da2fa14788b03aa17708d02d00b0000d285ce2d995509da4902170f5c6fa31f160096440219809282fc0c0000d27fba2da153c9e44992180f406d630c15889203d618309303100ce000d279882e515c4a1c4b32210fc470c32615f89583e218b09603140d4000d273332f61658a584c522c8f9c6fa31e16109743f6190097832c0ca000d26cdf2f99620a3c4b82288fa46f831115e895c3e618b09603200c6000d266d62d295149e04942158f006c22f614808b839c17c08c02f80b8000d260a82e695989d649421a0f106ce30414e88d83b817e08d02ec0be000d25a4e301966ca5a4bf22d8fd872232a168096c3da19309a83380cc000d254252e615a0a124a321c8f5c70632a16389883f819009682f80c2000d24dce2fb9648a384b422b8fb871032716289903fa19209483240de000d2479b2e795e4a1a49421f0f406c430114f88ec3b018008d02d00ac000d241692e91588a0049f2200f486d431215889403ca18b09383080c2000d23b3e2e3158c9e64892130eec6a02f114508b439817508c02d40ba000d234cc3041674a6c4d82358ffc71e32415c893c3e619009783440cc000d22e9c2ea15cca244aa2228f7c70031f15d89743ea19009a831c0c8000d228922d215009c047a20e0ee469e2f314708b039e16f08582d80ae000d222662e11598a064a121c8f886f830e15709303e018309182f40b6000d21c552d9154c9f24952178f586cc30314e89003d618c097030c0b2000d2162f2df15709ec48f2140f306ca30a15389003ca18b09883300d0000d210192d9956ca0649c21d0f6870631a15c898c4061a309983200c2000d20a322c894d09b647f20c8ec86a82f914808b837c16708302d80b4000)))) else (if i < 133 then (if i < 131 then (if i < 130 then 0xd51d7e2e11588a084b02268fbc71231715e09683e419009683340d4000d517412e89594a1a4b021e8f606ec31615e09703f0193099032c0dc000d511382d415049c847f20f8ee068e2eb14488a839416508282b80a0000d50ad52fc9644a544ca233900074233316409a440219d09783340cc000d504892fc9638a524ca234901874a34216b89cc40e1a909f03400d0000d4fe6b2e515ac9fc49f2218f706fc32016109a03f219909802f00be000d4f8392ed95f4a504b82268fb071a32315c89403ec19209b83140c8000d4f1d23009618a3c4bc22a8fa871832415e89983fc19809883500c0000d4eba42e915b4a0e49b21b8f606da31015509083b418009082e80ba000d4e5822e015849fe4982148f1c6be2ff14d89043c018209283240be000d4df662dd954c9f048f21a0f406e430914f88f03b217a08d83280ce000d4d9142f515f8a2c4b422d8fa872032f16609603dc18809202fc0c2000d4d2f12d9156c9ec49c2210f7470231e160898840018d09603180ba000d4ccce2e115689e048c20e8ef06b42f614b890c3d618a096033c0d6000d4c6a62dd156c9fa4a02200f8c6f431615f097c3f419a097032c0ce000d4c0662ef15cca364c222a0f9870e31d15c09403dc18909583180b4000d4ba4a2df1590a0049e2218f7c6ee30c15708f03ba18809002f00b6000d4b42c2d795549ea4a121e0f786f031315809383ec190098032c0ae000d4ade12ee1608a3a4c8233900073233616789943ec18b09783200ce000d4a7a82f015cca324bc22b8fb870831e15d893c3c018509383100ca000d4a1852e315589dc4892130f046d030b15009083d418509403200d2000d49b3c2f015c0a224ac22a0f9870e32215e89503ea190097031c0bc000d495172e715ac9fa49b21a0f786ec32115a09343ce18a09983440d4000d48ed92ee95f4a364be2278f7c6f631415b09403d219a09983580e8000d4888c2f495f0a2e4b42268fb46fa31f15989583e018708f02f40b4000d482532f09614a484bf22e900073833316109a04101a509b03500ca000d47c372de15609fa4a221e8f386e831b15d09443e218509503100c6000d476242d595349cc4892150f406ce305151892c3ce18509003140c0000d46ff62e515809f048d2140f206d630715409083de18308f03100d6000d469a92f61608a564c6237100072833816b899c3ec19709c83340e2000d4636c2ec95dca0a49b2188f706f431915d09743f218f099834c0ba000d45d252f51634a384b622e0fe072a33216309683e218809303180ca000d456e92e815cca0c49d21f0f0c6a82f714a88e83b017c08d02f80ba000d450c72e715849f84a92268fb070c31b15a894c3ec19209b833c0ce000d44a782f515eca2a4b22280fa470431f15f09804121a609f03540d4000d4445b2da15449e44912190f6c6f431c15c09603e419409202e00b4000d43e222ea95c4a264a321f0f886f831915909543e019909a03100ce000d437e22e715a8a1c4a52250fc071e32a15e09883c018b08f83140b6000d431aa2e915c8a1e4a82208f8470231f15889643f219b09a03300e8000d42b7c2e31584a0e49b2178f306dc30315689203da19109d034c0de000d4250b30716a4a984e323c9050748338169098840619e09803240d6000d41efd2d7955c9de49521c0f646f031f15b09783e818b09983500e0000d418d82dc95849f64a121d8f8470831415688fc3ac17e08e02f00ba000d412ab2e2159ca1e4a82270fc071e32b16589a840219a09703300ca000d40c552f29608a304bb22d8fa871232e164098c3e218409503300c6000d406032f71620a3e4c422d0ffc736335167099c4041a209c032c0c2000d3ffd02e695c4a2e4a62258f8871432e16709943f819f09d03100ba000d3f99c2eb95f4a2a4ac2280fdc70c32516109883ea190097832c0cc000d3f3942d395109c64872118edc6cc30d154093c3ca17d09383080ac000d3ed7c2db95389e44892140f086d430f15789283de18f09083000b0000d3e7412e715c4a244af2268fd071e31e15d09443da18c096835c0d2000d3e1152e915d0a324b12278fa4718331164897c3f019409282d80be000d3dadf2e995bca2a4b72268fbc6fe31615989783ee18c09183240be000d3d4a02eb15dca2c4ba2260fa471c32916289503e219109b83540f0000d3ce552fa163ca404c922e0fdc70c32415d09483ca18109183080bc000d3c8172ea15c4a0c4a321c8f586f231715b89603e219a09903240c6000d3c1e12eb15dca244b22208f806ee31c15889483d418409383180c6000d3bb9d2ee95f0a244ae2248f846ec30c15689283c6188093032c0c6000d3b5492f79614a444c222b0fd072832c16609a440a1a509d831c0da000d3af2c2dc154c9dc4972220f846f0318152091c3e818d091031c0ba000d3a8ed2ed95eca2e4b82260fa06fc32316289884101a20a783740da000d3a2f82cb94e499c4692050eb86a22f014c08f039816508602b00aa000d39cde2db95689fe4a02218f6c70431715989643ea19909803440de000d396c32dc153c9de4962180f186ce2fe14f890c3ca18709503380d2000 else 0xd6a9f92f415f0a264b221d8f6c6fc32b16809bc3f8194098033c0d6000d6a3943001658a604ca2318fe071e33216409a040219309583000c0000d69d6f2de15709f048920e0f086d0300152892c3d018109403180ca000d6974c2de956ca004a52248f746f631615c89703f619409b833c0e8000d691232e4957c9e24862120f046a82e714488903ac17d08902d00ca000d68ade2eb95d8a304ae2270f986f231c15b89583e418b09103040c4000d684ab2e395b4a004972180f186c631215789343d618909b83200e0000d67e982d49570a0c4a321e8f546e2318161094c3f218d09403040be000d678572eb9600a464c222d0ff074033d16809c442c1a709a834c0cc000d672242e795a4a1a4ab22a0fc071432015d89583f219609883480c0000d66be52ed95b4a2e4af2208f9472032215789603ea18e09583440da000d665a32f09604a464c02340ff8742339168098c3ee19a09f83640ce000d65f692e69594a1e4ae22a8fb070c32715f89a0402196095831c0e8000d6593e2e195b0a024912180f346c82f814e08f03cc18b09483040c2000d653052ed15d4a204a621c0f5c6ec31815b89543ec190091833c0c6000d64ce12e09580a0249e2208f3c6d830615309343d818209002f80ae000d646b22e815b4a064a721e0f506de308158094c3d017d08b02e80be000d6404f2fc963ca5c4c322f1018740338168097c41a1a009b83240d4000d63a112ea15d8a224a121f0f5c6e230c15208fc3c018309002f80ae000d633d02ed15bca0849f2218f7c6f431b157894c3ee18808b82f40c2000d62d802fc1628a584bf235901474633e16a09b440c1a509b03340ce000d627342f215eca244b42290fbc70831515b894c3de18409683040c6000d621092e315b8a1a49f21e8f546d230714d08fc3b417109202ec0ba000d61afa2d1151c9c448b2188f486f831b15a89703f81a309703440d0000d614b42f41600a344bd22a8fa871a32a16309643d218d09a83400d6000d60e7f2ef15f0a244a62208f506e230514d88f03dc18c09a83140d2000d608632dd95949ec48d2180f346dc30014888bc3b217e08c82d40a6000d602392e595b4a0849d2180f446d830f15709283c418809203100c6000d5fc092ea15c8a264a92270f946fc32816489943f8192093030c0c0000d5f5b52f41608a3a4b52278fa471432115c89643ea19d09e83500e0000d5ef9b2dc95689fa49b21a8f3c6d631415888fc3ba18208582cc09c000d5e9692e61594a2e4ac2240fac70a31915b09683f2185098030c0d2000d5e3672d3152c9d64852120f0c6c230e15409403c218b09703240cc000d5dd3e2e415a8a0049a2188f8470431515889383e819709b83440ea000d5d7482cc95149c447820e8ec06962f414f88fc3b418308f02f40b4000d5d11b2ea15a09fe49b21b8f506ea31315709283c818909182e00d4000d5cadf2e915dca224b02238f7c6e430d15589383de190093030c0c0000d5c4b02eb15c4a0a4a621d8f686fe32015a899440619c09c83440c6000d5be8d2dd9570a0449821c0f8c70a31f160895c40219d09d83440d8000d5b8862d495009a447f2128f006b22ed14488c43a818009583500d0000d5b2622db95589d84872110f0c6ba2f914c08ac39e17c08f03100ca000d5ac522de1570a044a62230f8470031915a09443dc18e09683200b4000d5a6162ed15e4a284bc22f0fc471831515a091c3d618b09983340d4000d59fdd2ec95d4a1c4ae21f0f9070832115e09703e018009603100b8000d599be2d7955c9ea4882180f486de30f15809343d618009102e00b6000d593992e6158ca0449f21b8f686d231e15d09403de18d09082e40b0000d58d392fe1628a5e4ce23b100472c32f16209803ec18e09783500e4000d586f22f315eca224a82258f806e631d16009683e018009182f80be000d580ce2e81588a204a721f8f486fc30c15889243da18309583480e0000d57aa72e4959c9f24932150f106ce30315108f43be18509002f00b0000d574992db153c9e24a02190f446e830c15489103c418a09083100d4000d56e5a2e31588a0a4a621f0fac70c33116889903fc19309803280cc000d5681f2ed95c0a104a82298fa871a33116609984021a609883200cc000d561dd2f015e0a344bf2270fa471233016789984081a409c83480be000d55bb32e495c8a1c49d2208f986f832c165899840019f09c834c0ca000d555842e01588a184a221c8f586fa31715809403c217c08e82ec0c4000d54f362f695eca1a4ac2210f506f231415909143ae17e09102f40b8000d549082e895b8a1249c21a8f686e631d15d898c3fe1a109d035c0ca000d542ac2fc963ca584b822c8f8c70432316689803fc1a909f03640dc000d53c992dc95689ea49821d8f746e831a15b09543d418708c82ec0b4000d536632e615b8a204b522a8fd472833216389503cc184090030c0be000d530382e19574a004a02210f9872a32f15f89b03ee19109303040bc000d529dc2fb9628a484c72340ff072833016589b44021a309b83440d4000d523ae2e495a4a0048e21c0f506fa31315189043bc17c09103080aa000) else (if i < 132 then 0xd836942f095e4a2e4a92260fbc70432015c89443ea19709703240d6000d830692de95749dc49521a0f286de314155893c3ce17d09003000b6000d82a3c2e595849f24a321c0f586de31c15c09343cc18709883240da000d823fe2eb95dca1a49d2240f7070032416209bc42619f09e03680c8000d81dcb2e6158c9f249c21d8f2c6dc30b158091c3da18f09803140cc000d8179c2ea9614a324b42268fc071e32016209883f618408d02f40b8000d811512fa9614a4c4ba22e0fcc710325163099c3f619609903400ea000d80b182ec95c8a1e4b62300fd471e33115f095c3f819c09903300da000d804b43009688a7c4da23f104c75c33e17389e041219f09b83440ca000d7fe6f2f195fca404c222b8fc870631415809303d617f08e83040ba000d7f85d2d895489f849a2190f4c6ee30c15409483e418c09383100c4000d7f23b2d995609d64892170f446e031815c09383e618d09603600ea000d7ebfd2ed15f0a1a4a421d8f7070231615b89403de19209903180c2000d7e5c82e895b0a1c4a92210f7470431b155091c3d41950a003240d0000d7df942e915e0a164ae2240fc071231f16309a83fe19e09a03480e0000d7d9602ed15e4a344b22268fb470e32515b89443dc19109383240cc000d7d3472de95709fe49521d0f2c6ce2f8153892c3ce18e09702f80bc000d7cd262dc15649ec49f2178f286e831015509143c4182092031c0b2000d7c7122d815109c047c2110f0c6c830815a89243c818808b02c80a0000d7c0ee2e21578a1c4a72250f986fc31915f09743fa19b09b03400d4000d7baac2f51610a3c4bb233900073631615b89383d017108982ec0a8000d7b4672ee15e0a304ad2260fb870c31816089b441019c09683200ce000d7ae242f215f8a2a4af2248fb470e32115f89803f618f09483040b6000d7a7fc2df15449e049121b0f486d230f15b09403e218c096032c0d4000d7a1d22df1598a0c49521b0f086d430914f08f43bc18009283100d2000d79bb02dc15489d64912178f446d831115b89043c618409103000ca000d7956e2f71610a544ca234900872634116d89d441e1a109c031c0c6000d78f362e3958c9fc4a021b8f906fa32515f89683e2188093032c0c8000d788f22f61608a3c4b82270fa470631815a89503d218d09c83300ce000d782d02e31584a0c4a72220f8471832716589883fc19108f830c0c6000d77c782f91630a444c12308fe872632916509803f019409803480da000d776612db15349ca4862110f0c6ae2fa14c08e43b417508a030c0c2000d7703e2e1957ca064a32218f806f030915209343b617d08e82d80b6000d769dc2ff9638a4c4c622a100073c32715e89743e618609803340d8000d763d52cf14c49ac47320f0f086c42ff15509103d018308982c409a000d75dbd2de1590a004922198f0c6c42fd14c08f039417908c831c0bc000d757792ec95d4a1a4a521b8f346d830b155890c3c018809703080be000d7512d2f49614a504c222b0ffc73433517109cc41a1aa0a603780d0000d74b052e415a09fe49f2220f9c70832a16089883fc18f09783200d2000d744e22df15809f44972188f3c6c830915809403e018f09203000ce000d73ec42e195b0a0449c2190f346d830315589543de18d09903180c2000d738742f69630a304b62260fa06fe31715e89503e619409883380c6000d732492e595a0a1a4a12258fa071231515a09503f81a20a383680e6000d72c002eb95fca424ba2318fdc71e32916089703d418809282fc0be000d725af2f8162ca5e4ca233100073c33e16a09883fe1a009a83740e0000d71f7e2e815d09fa49821c8f5c6da30a154893c3c818309103140bc000d719642de956ca0249c21a8f3c6f231415609343e218d09503500d4000d7134f2d714fc9ba47420c8ec06a02fa14c09043de18909503100c2000d70d222e89598a0a49b21b8f606f631d15a897c3da18d09403040bc000d706e32ec95fca4a4bc22a0fa471832b16289703f419109583200d2000d700b72e515b0a184a62198f406f031e15909303d217c09103140bc000d6fa8b2e795a09f649e21c0f3c6d22f414888d039016208e82e80a8000d6f44b2eb95c0a1049c2230f8070c31f15d095c3e018809403000b8000d6ee172e5958c9ee49021a0f406d630215309143bc17a093835c0c0000d6e7ec2e995c4a1a4a32218f8070632315d89543ee191095031c0d0000d6e1b72e515bca104992240f84708316159092c3d419009b03500ce000d6db8a2e295a4a084a521f0f4c6fc31915d894c3d019309883240ce000d6d5482ed95bca164a421a8f546d62f715188e83ae17a08e03080c2000d6cf3e2d395449d44832148ef86be2f914e08e43a017509083000b4000d6c90f2e715b0a1449621a0f346dc31115809283c818208e83000b6000d6c3072d294f89b847c20f0f146c22fd15689343d418609282e00c2000d6bcab2fd1620a424b52280f9470831f15889443d218a09283340cc000d6b67b2ed15f4a324ae2248f706e630415509003c418209383380c8000d6b0412ed95c8a204ae2288fa871832b16589c03f819709e03540ce000 else 0xd9c2fb2ee95a8a224a62278fc471432515d89343c417908e82e00ae000d9bcc52e495a0a164a021c0f286de31615989203de18f09783300ba000d9b6692f71630a5a4c42308ff072a32b164895c3ea19b097833c0be000d9b0072f89618a424c12300fd070e31a15a09403f61a109e03140d6000d9a9ee2db95549dc4892110eec6ca2ff15488f83c017e08883080ce000d9a3b72ee15a49fe4972150f5c6f2321161894c3e619809983140d0000d99d7a2f115f8a3c4bd2258fb070231b15909043c018809783180c0000d9974a2e395889fe4af2278f886f431e15f098c3fc19409683380c6000d9912a2df15849e649421d0f386d030815108ec3b818c08f82ec0c0000d98b1d2d6951c9d049721e8f806f230f15709403cc18209102e40be000d984ce2f79638a424b62290fe875034a16f09e84301b20a2035c0d0000d97e832f39624a4a4b72230f786de30315489103c217708a02d40a8000d9783f2f015f8a3a4bd22e900073833116589c04121a809f83440e4000d972172df9578a024aa2210f9870431f15b09443d618909383540de000d96c1d2d014d499e46b20b0ef86b02f714f88f03ac16a08602cc0b6000d965f42e295509ec48f2108f0c6d230514c08d03be18e09503280c8000d95faa2f39628a604c322c900473a333164897c3ea18909582fc0ba000d9596e2eb15b4a204a721c0f346f2306153891c3be17f09202f80c8000d953332e515c09f649a2248fb070432916589a83f019e09783140c0000d94d032ea95f0a344b222a0fc070831c16289703f819809783580dc000d946e12df956c9ea4982218f646e031515d89583e418c09603180b8000d9409f2ea95bca1a4a52240f786f431b15889403e819b096831c0bc000d93a492f91630a604cc232900072432f16589903ee19209683100c0000d934222e695bca184a32240f746ec31615e09743f418d09183000c6000d92dd02fb9664a764d523a0fec72632515c895c3f4198098830c0ca000d927a62e615989fc4a22240f8870032715a09503ee19609903480ca000d9217e2e115789e64862118f2c6e031615809303e2191096834c0ce000d91b5e2df95589de4912178f246e230e159095c3da19009202fc0c4000d915342e115689f24a02250fb0702319158894c3ee18a09883180be000d90edb2fd9634a544ce2308fe472432b167099840619309903380d4000d908842f99644a644cb22c8fcc72c33916d899c3e418f08e83280da000d9027f2d2150c9ba47d20a0ed06a42f314b09043bc188091030c0c0000d8fc2d2f2960ca4a4c72330ff074433116209a440619f09603240c6000d8f5f72e795ac9fe4a52210fac71632115e098040e1a509b03280cc000d8efd02df15689ee49321b0f286c82f514a88e43c017a08a83080b0000d8e9b72dc15449e64902120ef46d230815208d439a17608902e40be000d8e37e2ed95c0a1249621b8f646ee31115809343e618c09783080c6000d8dd3d2f49624a384b322b0fc071e32216289743fc19e09c03300d4000d8d7412cb94ec9d447f2088ed46ba2fc14c08f83b417709003080b0000d8d0f12f9165ca6c4cc236901472c33916689783ee19a09803540d0000d8cac52e715b4a144a82228f686ea31415709103d018c09403280d4000d8c4922e715a0a104a72210f786fc31515d09903f019809883440c2000d8be662e895d4a1c4a62208f686fa31615b89503ec18e09502f80c0000d8b8342e3956c9ea4892110f0c6b82ff15409083cc17e08d02e80ca000d8b20c2e01590a044a32200f746f4326163896c3ee192094832c0bc000d8abec2df1584a0049621b0f4070031a15d89683ec19009883440ce000d8a5ba2eb1608a484c4230900073433716609843ec19509583100d8000d89f882ea95d8a1449421a8f506ea31f15809283d018409082f40ba000d8992e2f89638a4a4c622e0fd870c32415e09743d618008d830c0ca000d893042e115949f84a021f0f7870231815c09643f619209203000c6000d88cdd2e49588a024a321c0f346d830315409143ce183093830c0be000d886ae2e015449f248d2148f146c030214c09083d418c09082fc0b0000d880892de9588a1c4af2248f806e632115d89843f418209103040c6000d87a572de157c9f449a21c8f846fa31815d895c3f619209903480c6000d874152e7959ca264a72270f8470032516409783f619609703300ac000d86e0c2d2952c9c04812128f186c030214f08e43bc17708f82e40c4000d867ce2e315a8a2449d21b0f506e631715909643f419809a034c0d0000d861de2c394a898a4652050e886902f214a88d039c17608e03100c2000d85baa2e895d8a3c4ad2238f706fe31c15609283da18309103300c6000d855962db15289ca48a2138f206d42fa14888d83b217208a02dc0c0000d84f8c2d114f89c44812140f146d830c15509103be17e08e03280be000d8495e2e915a8a1e4af21f0f6870031815909483e419a093033c0d4000d842f92fc1674a744d8235902874833716b09ec4221a709f834c0ca000d83cde2dc9588a104b92230fc070e324160093c3e018f09583040b0000)) else (if i < 135 then (if i < 134 then 0xdb4f692da951c9d048d2150f0c6ce300155090c3ba18909402fc0ba000db49392eb95eca2c4af2230f786fa31315c894c3c217d08a02e80a0000db43262d815349d648e2138f146c630b15409283d418909202ec0b8000db3cd32f41658a604cf2328fe072c33816d09f44201ac09c83480ec000db36b92df1590a0a49f21f0f586ca30a157093c3d618308e02fc0c6000db30d12c214b498e47220a8ed06ac2f414e88ec3b617a08f82ec0c4000db2acc2d314e89c648220d0ee86b22ed14b08b43ba17f08e03000c8000db24742fb9610a464b522d0fb871032116409883f218c09403000ce000db1e372ea95cca324a72258f9470631615e09683e619609b03340c8000db17f72eb95b4a124ac2270f9c6fa31615d09443e419109182f00ba000db11c52e9959ca0e4b62280f886f631d15b095c3e218909403140c4000db0ba72e295749f04a121d8f906fa32616109643e619109403340c0000db055e2f215fca0c4a82208f3c6dc30c15188f43c6180097031c0bc000daff622cc94cc9a44782058eb869c2f814c08cc3a216e08582d40b6000daf91e2f015d4a244b02210fa06f831715709243ea19a09a03340d0000daf2fe2e095a0a184b32278f9c70631315508fc3d218609183000c0000daecb52f71630a544ba2288fb870c32215d897c4061a109e83740d8000dae67a2eb95c8a2c4b922b8fc072632e16389643f419a09883340e0000dae0412f79600a424b922c0f9470031e16309383d619009402f40b8000dad9ff2f1161ca3a4ae2268fd873833116b89b440e1a509c83440d2000dad3a82fc9620a584c72338ff472032715f89683e418e098032c0be000dacd972d595449dc48a21b0f5c6e631b161894c3d819109483280d4000dac77a2dc15489ce4902108ec86a630114f08ec3b216f08982e80c8000dac15f2dc15509d64872180f3c6c42f814c88ec3aa17b08e83180c4000dabb342e2156c9e44892128f106b82fc14c08b03a817d08e83100d8000dab50d2df95a4a0a4a721d8f546de31315a09303c817e08f03080b2000daaec92f11614a484b92278f9871232415e09783d218409083100ca000daa8af2dc95549f849a2198f446e631015489143bc18209203200da000daa26e2f09610a524c322d8fc071432016189843f219009703240b4000da9c242f61634a4a4bb2230f806ec316157891c3c218a09383000c6000da96202cd94fc9c64832138ef86c430415609403e218a09403000c4000da8fd12f4161ca404ca22e8ffc714326158895c3dc19509b031c0ba000da89a92e015809fe4a421f0f4c6e2310154892c3be17e09002fc0a0000da83682ec95f4a344b12268fa870a328163097c3ec19c09983600d6000da7d332eb15cca2049d21d0f2c6ca2fb15289483d017a08b82ec0b2000da77042e51580a044a22210f4c6d230515089043c0182095030c0ba000da70de2e195889f249f21d8f6c6de30d158893c3d218b09403400dc000da6a8b2fa9624a464b822d0fe472c326162098040219309a03180c6000da645f2e115609f649621f8f746ea30e15a09443e218008d82fc0c0000da5e2e2e695c8a164a92278f686e830e15509183d218909603540ca000da57d12fb1670a7a4db23d105875e34b1738a2c44e1bd0a803780de000da51942f195e0a2e4aa21e8f886f231b161094040619509b036c0d8000da4b5f2e795a8a1249f21b8f646e631d15c89543e419809d035c0e2000da450c2f51638a464c22290fb871e32916709b03e819009a03340de000da3ea130596b8a8a4cc2358ff073033616809bc4181ac0a6838c0de000da38942cf94f89d04862128ef86c830415189203ca181093030c0d8000da323b2f71630a504c722e900873433116709b04061af0a183900ce000da2bff2ee95bca1c4b322b8fa070432315e89483dc18208c02e00c2000da25e42dc95709ee4942170f186c02f614b88bc3a017508b82d80bc000da1fdb2d8152c9da4942190f446e630b15109183d6183095831c0d2000da19912f015b4a124a62210f8c6fa32116509843ea19009403080c4000da13542f19608a404b822a0fc0708319160099c3ee18f09202f40b8000da0d332dc954c9d247e2108f086be307156893c3d218809683100c4000da06e82f49620a5a4be22c0fc070032016289903f219d09a032c0e0000da00b52e295789f048e2128f206b830815308f439c17a09003340ce000d9fa982dd9558a0c49f21d8f686f430815889683cc18d09083100ce000d9f4882d715309da4892120f246d4309153093c3d218b09703000c0000d9ee542e595789fa49621c0f5c6e030715789443e019009603400c4000d9e8162e495cca2e4ad2288fb070e326163099840019e09d83180d2000d9e1fe2db15389d448d2148f086b62f514688b43a017d09203080c8000d9dbc52e6958c9fc49f2188f3c6d631a15c89583e8191094832c0b8000d9d5912e915b0a184b02270fa870632115b09703e019009c03380c4000d9cf622ec15c8a364b522e8fdc71e32d162897c3fa19d09482f80c4000d9c9372df15549ee4962190f4c6dc31515b897c3f018f09603500ca000 else 0xdcdb352ef960ca364b02268f986f431915e89943f019809c03340ce000dcd4e02f49634a544cd2348fe873433616409703f019609a03100c4000dcce6f30b9680a704d3235901074a34017409e84241a40a083600d8000dcc8502de95709f849421d0f5c6f631c15d09643ea19d09703180ce000dcc2032f015d8a1c4a821f8f706fa31f15c09683c818b09083000ba000dcbbb12f51630a564c322b0fb071a32d16d09b04181ae0a203580e6000dcb5b12d4150c9c448420d0ec869e2e514588cc3a216808282c80b0000dcaf702ed95cca0e49e21d0f806fa31415789403de17f08b02bc09e000dca9352e515a4a084962188f2c6ca30714d08e03be17908902c40b0000dca2fb2e815b8a0e4a421b8f5c6e230c15189283ce17f08e02dc0c6000dc9cd12e21588a0a49c2218f446e430d15b095c3ea19509b03200d0000dc969a2e595a09fe4902138f306da30814d88f039c16408802c00b2000dc904f2f415fca304b02240f9c70631815909403ce19309983500d0000dc8a422d815349dc47c2120f006dc30815909303c618609083240d6000dc841e2df957c9fc49c2198f386dc30615209043b618009182cc0c0000dc7ddf2ef1604a384c32330fb871a32515f094c3d419009082f40b0000dc77ad2e495849f049e21a0f506e230c15289103d018009182fc0b0000dc71592ef95f0a344ad2210fb06fe316158893c3ea18a09903380d0000dc6b122f21610a404bf22c0fdc71432215889343e018c08f82e809e000dc64da2ec95d4a0e4ac2200f786ee31615a092c3c418709402fc0be000dc5eb92dd15789fa4952120f006c8305151090c3c618609103100b6000dc58952e19558a0049b2188f546e231315789483e017b08e82f00ba000dc52662e795a4a0449f21a0fa070031b160097c3f818b09603740d0000dc4c582d595249b04722070ea869c2ed14708ac38816b08682cc0a0000dc46242e89590a0049d2190f506d831615e09603d618b09082f00a6000dc3fe02ef15c4a184a82250f906f230d16009683dc18108d82f80b6000dc39a42e615c0a1e4a42258fa86fe32015689183e219209a83280d4000dc33932d495409ec49021a0f486dc31115c89583f419509383080bc000dc2d782da15749e64912138f286de30f15d09403d818908f83040cc000dc27492e915b8a044972160f086ce30714f090c3c6180090030c0c4000dc21382d815209dc49b21e0f506d631115c89583d619109603180d2000dc1b1c2dc958ca1a4ac21a0f3c6e030514e09003de19109183040ae000dc14d72ee95f8a344c022d0fd4726329165099c400195096031c0ba000dc0e932f31634a344af2268f846e830b15709483ca18608f03080b6000dc08462f5961ca484bb22c8fa870e32a16789d84141a309a03200ce000dc023a2d59544a0249921a0f5c6f031415789443f0190094831c0d2000dbfc182e595d4a184ac21f0f8871231d15f898c3fa19a09b03500c6000dbf5ae2fe964ca5a4cb2340fd471833016509783f819909b03500d4000dbef812ec95e4a3a4c222d0fbc702323159893c3c818608f83040b6000dbe9552e31590a144a32250f7872432d16709c040c196098831c0c0000dbe3072f1161ca3e4be2298fe472432e16409943f219309d03600ee000dbdcbd2ef15eca0449d2158f1c6da303154091c3dc19209783100b8000dbd6b32d495309ce4882120f1c6c030015288fc3ac17608702c00a4000dbd0742e915d0a1a4af22c0f9c70a32315e897c3ee18b09483240ce000dbca662d295149cc4902120f046b22f914908d43b616908a82d00c8000dbc4282eb95eca324b72220f706ee313157094c3dc19009783240bc000dbbe222d515189da4862128f186e430915609343e2192098830c0c0000dbb80b2da95649f049221d8f206c630115489003ba17708f82f80c2000dbb1db2e895dca084a721e0f706fc31915d89443d018309103100c4000dbaba02eb15e4a1c4b12268fc472e32b16489b040e1a409503040ae000dba58a2d915489d44902118f186b82fd14788bc3be17608e02ec0c4000db9f6d2e115689f849421b8f506f031715889343de18a08d02e40ae000db99472e79598a0c4a921f0f6c6e030515689103c617a08c02d00a6000db93032f11634a564c422f100072e339164095c3f619f09d832c0c4000db8ce52db15409e44922138f086b630414988dc3ba17e09082e80b8000db868b2fe964ca544c822e0fe872632a16289a03f419309583080c2000db806e2e1957ca004a721e0f546ea31415889243d618409383180d0000db7a4b2dc15509e64902178f386d430a153090c3b417308902c40b8000db74262d99544a044ab2268fb470832116109884041a009882ec0c0000db6e0b2db15689f44a22188f3c6e830f15589203ca18809383080d0000db68252c514b49ae47b2120f086d230915409103d0186092030c0be000db61e22ee95c0a1c4a921d0f2c6da31415589303cc17908f03300bc000db5bb32e615789f049e2240f8870e32215889403e218b09083240be000db55802e7959ca0c4a52290fc0712330166899041a1a009e03340c8000) else (if i < 136 then 0xde667a2ea9600a4e4be22e8fc870232215a09383dc18809403140d2000de604a2e615aca164ad2260f7c6fe31715b89383ce19109883300c6000de5a3e2d014fc9c64922190f3c6da30e15689203d018209403000ca000de54002ee95c8a0e4ab2210f386ee30f15109083ce18d09583280c2000de4dc52e795c8a1c4ad2230f8c6f631715809443da19309683440d8000de47b22db95789e648b2150edc6c42fd15088ec3b617208a02c40ae000de41782ec95e0a264b32288f906e831915889343e818709302e80ca000de3b572dc15609f249221d0f646ea31415e899c3fc19a09983040c4000de353f2e19584a0649f2210f806f631515c094c3da18009483240ca000de2f172e015909ee48f2198f346c630815c09403d018909183100be000de28e42e515a09f848b2138f3c6cc30815808e439e16d08902d80b4000de22992f49600a3c4b42238fb86f832615e895c3ea18709202f80be000de1c5e2ee9610a2a4ad2238f7c6e430815989283c618509103140ca000de16642cc94e89ba4802120ee86c030015389043c017708c82cc0b6000de104c2db15509d24892120f046a82f314d88c03bc17908d82dc0ae000de0a0f2f095e0a324b52288f9c6fa31c15c895c3d418109383100b4000de03a33019680a784ca235900472c329166098c40018f08e830c0b8000ddfd462f39628a564c9232104874c33b16889e040a19909d83440d6000ddf7392db958ca1e4a62248f846fc31b15d898c3ee19d09a03480da000ddf13d2c994d499a4682030e9c6962e414888f03ac17508c03000da000ddeb0b2ec95cca0c4ab21e0f8470832316589984141ae099031c0d6000dde4d62ea15c4a0449b21a0f686f831315d09643f618709283100b6000dddea32e8959ca0a49f21c8f706ec30a155092c3e618e09783340ce000ddd8682f215cca224b12248fb471232c16089743fe19a09883100b8000ddd20d2fc963ca564c9234100074a34a1728a084321b10a483680d6000ddcc252c2149c9944732060eb46bc303153092c3d618709302f00c8000ddc6002e41594a1e4a521d0f906fe31a15b09283da18309102f80ba000ddbfc42eb15cca184b62200f746f232016009543f019c09d033c0ce000ddb9ab2d794f89bc4802050ed06b030315109083cc17908e83140c2000ddb3992d495149c24872140f146b42f914d88d83ba17908802e40b8000ddad8c2d5953c9d448a21b8f586ec30f15589543d017a08e02d80b4000dda7692e215b49f84a02210f8c6e2312159894c3ee1a009d83440d4000dda1342ea15a8a0a49c21a8f586ea31815408f83b817108502bc0ac000dd9b352d015289dc4902178f586f031c16109583da18a094831c0d8000dd952a2d7155c9e04872160f206c230b14f88fc3ba17908e83000b2000dd8ef22ea95cca264bf2328fb071232015b89a040219b09603100b4000dd88b22ee15dca284b82250fbc6fa31815a09403e219309403180c8000dd82952dc158c9fa49521f8f686da30314e08fc3aa17308802e40be000dd7c5b2ea15bca264b622d8fd8734330166899840219d09883500c8000dd764d2da15609ec49a2198f306cc30a15709183be17d08f02d40ba000dd70142ea95aca064a62250f806fe31e15e09383ea18e08f03280b0000dd69ea2de95549c648020c8f446e030b15109083c018409703040b4000dd63bb2e61580a0049b2178f086c42f814988c839816508602c80a4000dd5d9b2e29588a064a221d0f2c6e630a15109183b817408d03140bc000dd574f2f61600a384bc22b0fd872033016689d44181ae0a203400d2000dd513e2d715589e649b2180f3c6bc307153090c3c818108f83040d0000dd4afa2ed95e0a1e4af2290fc471832b16309743fc19a09a83500d0000dd44ad2f29630a4c4c72298fd872832b16209783f819309883240d8000dd3e982da953c9cc4892108ee46cc2f314a88cc3b617f09002f409e000dd386c2e59580a064982188f606e630a15509143e619409583200d2000dd32442dd95849de49421a0f546f031315789343e618c095830c0ce000dd2bf02fb962ca404b522d0fe873c33516389ac41019d0a0833c0e4000dd25b42f095f4a2a4a92268fa86fa31c159093c3d218508f031c0b4000dd1f8f2db15289b647c2100ef86b22f814f09143ba17708982bc0c2000dd19542e995a8a1c4b32228fac72032215d896c3e818c09483240d6000dd13382e41598a0e4a22210f646e031115a09543f419209b83440c4000dd0cd82fb166ca7c4d6236103c74834c17209b44261a60a203700e4000dd06bf2dd95509dc4862158f3c6d430915389243c618009183200c8000dd00872ee15f8a2e4af22e0fc472633215f89643fa1a509a83380c4000dcfa552e715d0a364b52280fc072033316609ac40c1a509c83540e2000dcf41f2ea95cca3a4b32230f7870032415d897040418e096833c0e8000dcedd92ed95d0a284a22208f646f031a15b09283dc18e093831c0d6000dce7af2e795a09f849d21c8f846e430915309343d018409083380d8000dce1742ea95b4a244ac2258fc471a32215e093c3ec18509082e40aa000 else (if i < 137 then 0xdff2c92e915c4a224af2268f906fc31615a09443ea193097031c0c4000dfec862f31618a464b52298fa471c326161896c3e618009602fc0c0000dfe6542e995a8a024a22200f586d830d15389303d018708f82fc0c0000dfe00f2f0961ca564bf22d8ff873233a16a09a44081a409b03000c8000dfd9dc2e915c0a284af2208f886f431015909503ee18f09483140da000dfd3a62e5959ca204a021b0f306ce2fd14d88d03b216f08d02f80d8000dfcd532fb1670a844de23e905875634016d89c840419a09e83540d4000dfc7232ea95b8a004aa2218f586de31015b89283d417908882bc0ae000dfc10c2d5150c9c44872148f386c430014c88f43be18308c82f00b2000dfbafa2d995609f24942180f486e6312152090c3b216708482ac0a6000dfb4bb2e995b0a1e4a62258fac714323161096c3e819409b034c0d8000dfae962eb9614a564ba22a8f8870032015d897c40619c09983280ce000dfa8582ef15e4a204b12248f9c6e830e15489403cc18d09282d40be000dfa22b2e215a89f64952170f4c6de314158092c3c017c08f83000d0000df9be62f315e8a264a72238f646fa31b15e09603e818b09403280ce000df95ac2e615789ec49c21c0f346e031316209b040219e09a03200d0000df8f642e995809f84a32260f9c71231f15e093c3dc183090830c0b6000df89242e695a89f24922140f106ca306153090c3b017808f02e40b4000df83122db15849f048a2198f606fa31715309443e219009783280d0000df7d0a2d115209c64742068ec869e2f814a88d03a817308a83080bc000df76dc2e3958c9fe4a42228f8070e32115a89583dc18108f03240c4000df707f2fe9674a544c2233100c74a34416e09e04181a909c03380c4000df6a692d5950c9cc4882168f286d430014d88dc3b817d09303040b2000df643e2e995b8a204aa2208f786f4310157092c3e419109603180b4000df5de32fa9630a604c9234100c74834417289b44201a309d03340c6000df57c32e095749fc4992208f5c6fa31115609343d818e09603100e2000df519a2dd95409d44922158f186c830215608fc3b218108c829c0a0000df4b552f115c0a1a4a12230f786fc32115e89503c018b09582f80d6000df45222e4956c9fa4a021e0f586da31015409243d2189095832c0c6000df3ed72f895fca3a4b32270f9870231f15f09743f019709c03600d2000df38902f01608a284b32288fb070831915e09383d218509003180b2000df32692e31588a044a021a8f506fc31815a89783fe19409182cc0c2000df2c222f39614a484c62330ff471a32316589b040819d09903400d4000df26132db1590a0049621a8f3c6ea31015489443f219909c03740e2000df1fd22ea15c8a0a49d21d0f686d030e157090c3d818709282f80ba000df19b92db15689e24802108ef86cc30814e08dc3aa16c08982e80b6000df13872e69584a0249b2220f7c6e831015609443d419409783240da000df0d6f2dc95349d848120d8ee86b430814e88f83c817408a82d80aa000df073c2ef95f4a464b42258f8870631d15d89683d2188096831c0c8000df01252da95509d248a2198f386cc2fd14b08c03ae17c08c82f40b6000defb132d9154c9f64942168f406f231315789543f619c09983440d4000def4d22f61648a4c4c12278fc471032416289703ec193095030c0b8000deeeb82d795149c048120c0f1c6cc2fc14908d03a217208b02ec0ae000dee8822ec15e0a304c222d0fbc71432516189583d618b09583180d4000dee25e2dd95749fa4962188f3c6f631715d09603d018909583280b8000dedc1a2e915a8a1a4ae2260f9c70231a158894c3d818d08e02e80c8000ded5f82e41598a0e4a221f8f786fc30d155892c3d218508e02d40b2000decfbc2ea15dca344a721c0f5c6f230f15589383ea19a09e834c0d0000dec97b2ec95d0a1c4a521b0f546e231a16189843f219309703400d4000dec3352f31600a204ad2240fb873833c16809a040819809d832c0c4000debcda2f8163ca564bb22e8fcc71a33516a09b84121ac09e03140d0000deb6ca2da1594a1049c21b0f4c6c82ff14d88e43a216a08882d00ac000deb0992e315a8a124a92288fc070e32716109683e4194096832c0d0000deaa852db156c9ea4962178f2c6de31515a09583ec19509403340c2000dea44c2ed95b4a084b02250f606ec31115589343d618c094832c0d4000de9e1c2e41588a024a021c0f5c6f030c15109003ba17a08c02f40bc000de981b2d5152c9c648d2100ee069c2f714708b039416908882dc0be000de91ec2e595cca204b72240f786d831115789403e218d09383200c6000de8ba72ee15d0a0a4a821e8f686ea30b156893c3de18e09b03540c6000de85462fd1660a5e4cb230900872e32f16089683ee18b09202f40c8000de7f0a2ed15c8a1e4ac2258fb870032415e09583fa19609b834c0ce000de78f92dd95809ec49621a8f606ec30a15109043ba18809583300cc000de72d92de958ca0849f2208f7470432c164899440619b09c83440b4000de6ca72e11580a0e4a121a8f406f232116309603e618e09903240c8000 else 0xe079f9000000000000000000000000000000000000000000030c0b8000e073be2eb95a8a184a521c0f686f2313158091c3da19309383340cc000e06d872e4158ca0449b21a8f346c430415209043c0186092831c0cc000e067622e515709ea48c20e8ef86d830615109343d418909483100ce000e061272f015f4a304a92228f8c6e231b15209203d418609182f00b8000e05ae62ed15f0a2e4ae2268f786ea32215c097c3e618a09083080c6000e054e52d015049b64852120f406de30c15389103c618c08f83100bc000e04ebc2e215b8a184ab2290fc072c33416709c441a19809b03500c6000e0488d2e515c0a104b022c8fd4710324163099c4081a109c03540cc000e0429c2cd150c9e448e2168f446d630d158093c3d218809202f80c8000e03c662ea95c0a0649f2220f7c6f231c15d09543dc18b09403300ce000e036402e0957ca084b22270f906f631816489ac4181a309c03540d8000e030272df9578a1649e21d8f646e830d14d89143c218c08e82d40c2000e02a192d495049c84862138f206dc31015809303d818009203000c8000e024072d415309d44922198f4c6f231015389003ba17508c02f80ac000e01de42de95649ec48a20f8f106dc31215d09543de18c09282d00b6000e017b62ea95bca284a72248f8c70831615b09643de19209c03200c6000e0119e2d715509da48e2188f586ec31215b09343d018408f03080c8000e00b792dc15649ec49d21e8f746ec31d15789003bc17e08b82b80ac000e005592da152c9da48f2170f146be2fa14a88e43ae17808a02f00c2000dfff392dc95689ea48f2180f586cc30915809343dc19309583500d6000dff8f62f2160ca3e4cc22f8fc471632516089843ee18209303040c6000))))))))

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



private theorem b127578 : covered 127578 127646 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127646 : covered 127646 127715 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127715 : covered 127715 127783 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127783 : covered 127783 127852 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127852 : covered 127852 127921 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127921 : covered 127921 127990 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127990 : covered 127990 128058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128058 : covered 128058 128127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128127 : covered 128127 128195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128195 : covered 128195 128264 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128264 : covered 128264 128332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128332 : covered 128332 128401 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128401 : covered 128401 128470 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128470 : covered 128470 128539 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128539 : covered 128539 128607 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128607 : covered 128607 128676 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128676 : covered 128676 128744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128744 : covered 128744 128813 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128813 : covered 128813 128881 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128881 : covered 128881 128950 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b128950 : covered 128950 129019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129019 : covered 129019 129088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129088 : covered 129088 129156 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129156 : covered 129156 129225 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129225 : covered 129225 129294 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129294 : covered 129294 129363 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129363 : covered 129363 129431 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129431 : covered 129431 129500 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129500 : covered 129500 129569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129569 : covered 129569 129638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129638 : covered 129638 129706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129706 : covered 129706 129775 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129775 : covered 129775 129843 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129843 : covered 129843 129912 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129912 : covered 129912 129980 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b129980 : covered 129980 130049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130049 : covered 130049 130118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130118 : covered 130118 130187 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130187 : covered 130187 130255 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130255 : covered 130255 130324 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130324 : covered 130324 130393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130393 : covered 130393 130462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130462 : covered 130462 130530 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130530 : covered 130530 130599 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130599 : covered 130599 130668 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130668 : covered 130668 130737 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130737 : covered 130737 130805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130805 : covered 130805 130874 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130874 : covered 130874 130942 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b130942 : covered 130942 131011 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131011 : covered 131011 131079 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131079 : covered 131079 131148 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131148 : covered 131148 131217 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131217 : covered 131217 131286 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131286 : covered 131286 131354 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131354 : covered 131354 131423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131423 : covered 131423 131492 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131492 : covered 131492 131561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131561 : covered 131561 131629 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131629 : covered 131629 131698 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131698 : covered 131698 131767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131767 : covered 131767 131836 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131836 : covered 131836 131904 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131904 : covered 131904 131973 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b131973 : covered 131973 132041 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132041 : covered 132041 132110 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132110 : covered 132110 132178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132178 : covered 132178 132247 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132247 : covered 132247 132316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132316 : covered 132316 132385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132385 : covered 132385 132453 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132453 : covered 132453 132522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132522 : covered 132522 132590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132590 : covered 132590 132659 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132659 : covered 132659 132727 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132727 : covered 132727 132796 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132796 : covered 132796 132865 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132865 : covered 132865 132934 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b132934 : covered 132934 133002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133002 : covered 133002 133071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133071 : covered 133071 133139 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133139 : covered 133139 133208 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133208 : covered 133208 133276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133276 : covered 133276 133345 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133345 : covered 133345 133414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133414 : covered 133414 133483 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133483 : covered 133483 133551 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133551 : covered 133551 133620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133620 : covered 133620 133689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133689 : covered 133689 133758 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133758 : covered 133758 133826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133826 : covered 133826 133895 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133895 : covered 133895 133964 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b133964 : covered 133964 134033 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134033 : covered 134033 134101 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134101 : covered 134101 134170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134170 : covered 134170 134238 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134238 : covered 134238 134307 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134307 : covered 134307 134375 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134375 : covered 134375 134444 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134444 : covered 134444 134513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134513 : covered 134513 134582 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134582 : covered 134582 134650 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134650 : covered 134650 134719 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134719 : covered 134719 134788 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134788 : covered 134788 134857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134857 : covered 134857 134925 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134925 : covered 134925 134994 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b134994 : covered 134994 135063 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135063 : covered 135063 135132 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135132 : covered 135132 135200 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135200 : covered 135200 135269 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135269 : covered 135269 135337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135337 : covered 135337 135406 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135406 : covered 135406 135474 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135474 : covered 135474 135543 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135543 : covered 135543 135612 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135612 : covered 135612 135681 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135681 : covered 135681 135749 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135749 : covered 135749 135818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135818 : covered 135818 135887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135887 : covered 135887 135956 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b135956 : covered 135956 136024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136024 : covered 136024 136093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136093 : covered 136093 136162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136162 : covered 136162 136231 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136231 : covered 136231 136299 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136299 : covered 136299 136368 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136368 : covered 136368 136436 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136436 : covered 136436 136505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136505 : covered 136505 136573 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136573 : covered 136573 136642 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136642 : covered 136642 136711 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136711 : covered 136711 136780 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136780 : covered 136780 136848 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136848 : covered 136848 136917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136917 : covered 136917 136985 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b136985 : covered 136985 137054 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137054 : covered 137054 137122 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137122 : covered 137122 137191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137191 : covered 137191 137260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137260 : covered 137260 137329 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137329 : covered 137329 137397 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137397 : covered 137397 137466 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137466 : covered 137466 137534 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137534 : covered 137534 137603 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137603 : covered 137603 137671 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137671 : covered 137671 137740 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137740 : covered 137740 137809 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137809 : covered 137809 137878 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137878 : covered 137878 137946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b137946 : covered 137946 138015 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138015 : covered 138015 138084 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138084 : covered 138084 138153 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138153 : covered 138153 138221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138221 : covered 138221 138290 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138290 : covered 138290 138359 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138359 : covered 138359 138428 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138428 : covered 138428 138496 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138496 : covered 138496 138565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138565 : covered 138565 138633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138633 : covered 138633 138702 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138702 : covered 138702 138770 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138770 : covered 138770 138839 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138839 : covered 138839 138908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138908 : covered 138908 138977 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b138977 : covered 138977 139045 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139045 : covered 139045 139114 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139114 : covered 139114 139183 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139183 : covered 139183 139252 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139252 : covered 139252 139320 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139320 : covered 139320 139389 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139389 : covered 139389 139458 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139458 : covered 139458 139527 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139527 : covered 139527 139595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139595 : covered 139595 139664 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139664 : covered 139664 139732 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139732 : covered 139732 139801 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139801 : covered 139801 139869 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139869 : covered 139869 139938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b139938 : covered 139938 140007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140007 : covered 140007 140076 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140076 : covered 140076 140144 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140144 : covered 140144 140213 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140213 : covered 140213 140282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140282 : covered 140282 140351 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140351 : covered 140351 140419 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140419 : covered 140419 140488 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140488 : covered 140488 140557 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b140557 : covered 140557 140626 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 127578 140626 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b127578 b127646) (joinCoverage b127715 (joinCoverage b127783 b127852))) (joinCoverage (joinCoverage b127921 (joinCoverage b127990 b128058)) (joinCoverage b128127 (joinCoverage b128195 b128264)))) (joinCoverage (joinCoverage (joinCoverage b128332 (joinCoverage b128401 b128470)) (joinCoverage b128539 (joinCoverage b128607 b128676))) (joinCoverage (joinCoverage b128744 (joinCoverage b128813 b128881)) (joinCoverage b128950 (joinCoverage b129019 b129088))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b129156 (joinCoverage b129225 b129294)) (joinCoverage b129363 (joinCoverage b129431 b129500))) (joinCoverage (joinCoverage b129569 (joinCoverage b129638 b129706)) (joinCoverage b129775 (joinCoverage b129843 b129912)))) (joinCoverage (joinCoverage (joinCoverage b129980 (joinCoverage b130049 b130118)) (joinCoverage b130187 (joinCoverage b130255 b130324))) (joinCoverage (joinCoverage b130393 (joinCoverage b130462 b130530)) (joinCoverage b130599 (joinCoverage b130668 b130737)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b130805 (joinCoverage b130874 b130942)) (joinCoverage b131011 (joinCoverage b131079 b131148))) (joinCoverage (joinCoverage b131217 (joinCoverage b131286 b131354)) (joinCoverage b131423 (joinCoverage b131492 b131561)))) (joinCoverage (joinCoverage (joinCoverage b131629 (joinCoverage b131698 b131767)) (joinCoverage b131836 (joinCoverage b131904 b131973))) (joinCoverage (joinCoverage b132041 (joinCoverage b132110 b132178)) (joinCoverage b132247 (joinCoverage b132316 b132385))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b132453 (joinCoverage b132522 b132590)) (joinCoverage b132659 (joinCoverage b132727 b132796))) (joinCoverage (joinCoverage b132865 (joinCoverage b132934 b133002)) (joinCoverage b133071 (joinCoverage b133139 b133208)))) (joinCoverage (joinCoverage (joinCoverage b133276 (joinCoverage b133345 b133414)) (joinCoverage b133483 (joinCoverage b133551 b133620))) (joinCoverage (joinCoverage b133689 (joinCoverage b133758 b133826)) (joinCoverage b133895 (joinCoverage b133964 b134033))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b134101 b134170) (joinCoverage b134238 (joinCoverage b134307 b134375))) (joinCoverage (joinCoverage b134444 (joinCoverage b134513 b134582)) (joinCoverage b134650 (joinCoverage b134719 b134788)))) (joinCoverage (joinCoverage (joinCoverage b134857 (joinCoverage b134925 b134994)) (joinCoverage b135063 (joinCoverage b135132 b135200))) (joinCoverage (joinCoverage b135269 (joinCoverage b135337 b135406)) (joinCoverage b135474 (joinCoverage b135543 b135612))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b135681 (joinCoverage b135749 b135818)) (joinCoverage b135887 (joinCoverage b135956 b136024))) (joinCoverage (joinCoverage b136093 (joinCoverage b136162 b136231)) (joinCoverage b136299 (joinCoverage b136368 b136436)))) (joinCoverage (joinCoverage (joinCoverage b136505 (joinCoverage b136573 b136642)) (joinCoverage b136711 (joinCoverage b136780 b136848))) (joinCoverage (joinCoverage b136917 (joinCoverage b136985 b137054)) (joinCoverage b137122 (joinCoverage b137191 b137260)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b137329 (joinCoverage b137397 b137466)) (joinCoverage b137534 (joinCoverage b137603 b137671))) (joinCoverage (joinCoverage b137740 (joinCoverage b137809 b137878)) (joinCoverage b137946 (joinCoverage b138015 b138084)))) (joinCoverage (joinCoverage (joinCoverage b138153 (joinCoverage b138221 b138290)) (joinCoverage b138359 (joinCoverage b138428 b138496))) (joinCoverage (joinCoverage b138565 (joinCoverage b138633 b138702)) (joinCoverage b138770 (joinCoverage b138839 b138908))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b138977 (joinCoverage b139045 b139114)) (joinCoverage b139183 (joinCoverage b139252 b139320))) (joinCoverage (joinCoverage b139389 (joinCoverage b139458 b139527)) (joinCoverage b139595 (joinCoverage b139664 b139732)))) (joinCoverage (joinCoverage (joinCoverage b139801 (joinCoverage b139869 b139938)) (joinCoverage b140007 (joinCoverage b140076 b140144))) (joinCoverage (joinCoverage b140213 (joinCoverage b140282 b140351)) (joinCoverage b140419 (joinCoverage b140488 b140557))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 127578 ≤ index 245000000/512 := by decide +kernel
private theorem starting_value : fast 245000000=13420660 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 245000000=13420660) (n : ℕ) (low : 245000000≤n) (bound : n≤270000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=245000000
    · rw [first,anchor]
      exact starting_value
    · have past : 245000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤270000000 by omega)
        have within : index n / 512 < 140626 := by omega
        have lower : index 245000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤270000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ245000000To270000000
