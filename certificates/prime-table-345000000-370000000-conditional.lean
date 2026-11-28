import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ345000000To370000000

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




private def radical : ℕ := 0x3f07ee226adfd64f80ef7ccdd9ddfd05a68047b97f3963c4f48b656173b33bb7b067f7cba7e66a193c9e824c0cb40589fc2cf834c79b0f1506a38379dcab6d7b747ce32491455e449bd1026f12f725838fee985037a6b8de3ee83650a58b7f824f06a0df3378b12f9cbbe7e3c5ef65e06f928cbe1922225a88ee30075ed353c11ba033ba7db8f954a68194f23b0761f257babe1d8440e6f90567f92c209798ac3933d4f31c358cb09a57f16e02590c11a719c8040c8d95f22e749643d866b76aca193274638b41838a58be3eacdd9e920676eac064829092314dcd83fdcd60a6feb8d8e3fba2e330ab33a0fd10cb193581b8b2b44472a40db72114ac81998d5970fa8a2f8896af2730b8cdb92c7b4706ad76d5013f496c5e2275394c9f1fde0b90698ef088d9e62442f0877787bca011ca548f20dff820e2871d11e2db903383e00c497ad7edf14689e2fe45c8111911c69c58bc652917c958ad2871ab7e33b06e85cba603e789489a49324d2ee5ce64b0a36594644fcf6d34f8b72637e7e43118d1fa0c0e30434d189fdc65774e832575181bd1f205dd1d51cda2f2b02d4d419a27b2fc1f3af32da01f129c23ffcda0cbffeebdb7d26346525396410a3ed5c26e21dad33386f6beb48c8c3836067914d3aade04e6b22c56fcdbb7f3049ae26ab70fc84731930c0d6a55da4e12270b8eb31668f6fa6d49a0b8fe5c2e264859791b62d2f6253f267cd69a4c3aa43649da660b97bba7737226b77aece0fd09aae0c4d1aee343012f742b00b1c07bd024a018ac49e92ae645a6e3360362440157d22ab68fe05b00b01acc6d47dac9248c18907ed8ea4e2d35ae6241b2a442bed87f7e747fd98c8144df02bb99be344ab60916c6cfdb911d54f0688350897339cdef3f105b16f118c4c50b3f007514b767d881f841d521fc6f7501ec23bf9e0481bf712566acf38ec30834a36ab61c626d9f76474a10908e15437c0d06a2138a1a494cb78f0d6c9cbf7c4455dbe6c3874f9f423db0c963b8a7219f1b05f8ad1bf4d3ac8d2ddb988d237e3c35ed8ddb2d0a84eb2455a515fab5813b4d76cefe2b38aa31d0e1791a879f19b1bb47d3ed94269423547d154d533fc82e6feb682dc29f315df46f817031fdb532d6f7b24886ac2807bfada257a0b8cd13dcd81249cf8f1e2c50c097f4e7a70ff56342d9c6c55e8ca6206c7e15015debfc8b4e5fcd63d0ec9452fdc4001ef7414d6fbc511095b976c7203c7f2f7e889fd0cc17a3ed54005d3b40908f03798c1669a24f4111cf1e6c1cc6af8c1a315f50d03234a9823627cac193c44a516075d91df9290bb186e4ff374c24f87536bdadf0cca59d86ed218497ffaf73ad6e29ede697bad8baf09d3896e4238503fcc23be46a5c1bde561ed9d44032e022badcb83b80e324746ebc9db570d844a9dbfe76e5c28721d8b098efd3bd4117b1daae5bb28f2ff4821947a9aac6b606a9d54a1e179e0e666b6c0ff9f363fed303235c29aee28f2e4122f5d39cec7720d9be9c0555581f76e783f05636d65219783924aa9da5b601dbe0bcca3a3c0d8b143f6a3948681b91ba4a54cfe2b7b390b07f7f1ccb07e6717a3b9a25f43db893d4b642000c6ad1709864a6643b5904db085f8cd6d74857a919570345f939788617315146be577d8d5e62defba1cee30b50d6046be6f1767e55e664bab3513fbb6ca36a967b44fd9eb8c9045d5aa722fad448a03150e3bcfd58fea1c8fdad5ca372c949e8978618a2343bc58a7809b318389a53181aa770c85e956b6e0c29406696ce9aefef8f38ef74d296e2d2b958385f5195d10d9976c7fa1a7434b3c44143320466d0a1453da759ee8e7b9ddbb5f47feaea968340ba9fb1baafa74e939515a38308e602343bad504513cb7a947b26f9413e3c7acb5ddecaffc3c53461d46403b1f9d2f038f94d8243661ca3da543f9bc37bbd44633c2d227afbaddb71dd685da95dd0d50ffd6ed6b30fe1d34f6a403096fa2dd2b861f22fbc5d4925fb1981a11b8b746d67e6c11fad9d5a14e586e2156b6bbee92630fb55c8db37900ef46d5eb54821d52e5ae57a42bb2f3b47f925701fdec0d684d270e8cd904e279797a11178308e255c7dc34cfb81acf87731afaa28f13a1e1a5797fff737f97a921a2fc56159274c659b8fe69e9387894d84c42d2e678080828b5789eae51567d92fd6458330f2e8a5630250f435d9b9ff9ea77c21ba6c3b3a50b04419a33ebc6f71bc075c87cc16863db344f861ffa5078a6cfe65c8a6900079681c59092f516cf34e704ad432d4d01365328512333519e0345e9e35fa11adac6babb196d12995d18913d422d87852d10a3cecd90acad9f89f36dfc7e5cb6e4db2ba3bf63833eef0d9173fb8e1645235e931f1c1dd000d3b42229ef818dd41f8578ab14f161ef73bd674b00fcf25fb6bb084d92d28165ee82f0a9e625c1a5a699ef99a41dd8b9c1f6806c25aea5393e9c1e4f72d050d337f1730224ece6f4e771d21dca7cddbfa342392bc75d7c2606cf7c3ed7b62d730fa65254e360a3cec7194e2fe001e4b387690a6380c6ae9a77f9d82f063aa1beb6b001225508d20db42bffc62cbbf939df8f8e94920665c68b8a9e1816a322e2da68246f48789f8aac38f06c114012c88cb9c917d8bdeb78e4263a33eb7d6d176453912791f1fffcd805b783865782fed9d1f0f95d3e9da48e9f72fbd139acf6736d8b79a584ed726698fac2085c493b595e5599db96da01460317c4093a9b7aba7409110082a1c9645da3a1f9ce78234d4e07e1e8157139acbcbdf1ec06634ce94023c81605ec91eeb98885cfb805f161e5873aa7414c00cc1bc3673d4d4c4c5a4897d6bc166007ae09f0797c27f2a3b5030fda419ddc27904f3f02d37106b6b0db043bf6122a414eea1c01d1edb1cd21eced204f5903099f3d0c9396451a489c9c5ab767fd817717e19b61f66562380169238d84856fe6f07833768c79b684adcb4b15dd54eb9e2359312101274dc7f32efc07efa328710870b33489fd0e177a772599cd289b39387e3b36efba6ab65400cff73787167422781d1c0581a578c79a326ef2d2917d6d22e7a4df02432b1c4df949c72369e6b5efef560dc55545654c1c1e7a93e73a9b525117b4f84dc2f18501668e97eb1de90a0b1a417706702fcd09328aff5ff69a11721cffde200f5c1c3fd278c59bf42bfd8401c00a39cef49cd32afdf7a5db952d645b329c1501944280042c207578cbf85621ce5d72e378bf873abab5a72cc60b88cf6230a0b06d8cc186460aff373d2b092c75e4daa73166f27105977333da4df9a365818bd3b57de20d090e2ca47696640d9fcebf14773e0b4068cc3878772c9351d0b32637fea5a50a45d7bf96ebd9a8dbd6a621fdeb82ed9554e07c9f102b5b6d490b877ced2a2745c1187fddb333336fa0cce1c8106bf1facab0529595ccbc8aa64d38bd2703a95addcbc06c8e0c78294295cce472989b35d19e57725d8b32e5e12d2a6d91b0a4c76e4aa9ad941b3e2c74867e17c4d32d30b355a88fd9ac604b72985295181ce78105328feb83df9541053a98cab8ba4f50a4d659c90f9e6e5cff44d0aa25018b1c44a6cf34eb2b4bd642572fbc48a02ebf7765fe72de6e76d5f6ca50b1c2ace797fce08a605b2b321e4462a8f6ef1211ff399fe465e1b80cebebeda234bfbc5f8b7408cbd8849496087cb033df06155d097027383e142e5999ef1544981388b76d96569bc25969a1e9bb0414ec08f87ae9fa59b256d55e3392156017e4332cdb5b351dc768a0c27ea78cd4c0cb8870dabe130ad3b363c6a661ec41fbe841f82f2901deae05faa55aace771ed4163af334ef2392e5a93185f77e86291b183f34ae315a704cc2f5e983fd333add2eac980e5dff0f3cf3daa50fb6a6589b34a6d2ed0be4d81da672b5111361fc73ab115dbd5bcec15813bcb5196e8b32afde4d78b50fdc12195de4d2d4a881bac59dc475c0a80858b9355500f97eeb172119e0882b0c7d3b2743ab728e185ef6d71af4bb57b35d1eb3f397c6656e19606fbe96009631f7eb82cda485e68a77d2ac5f74c2785001dd9035c84073c54c32ef8a88cb12c9d3287e81a33531b11c4601787cc5a083e4bad0df1828a22521ca650ea92e5fcbc173bf6396be7dc49da4a365207bed25a1d668fc4bfbbe0ce5fef81e7dddee0c26f47ba2153918b759f36b69e5b2df45fe79f175887a70368fdc5ed8ef6410cf99259a389e3a712f65c5c925a9f6ef697e31ed0b29060df08b54322a76f919909ef974923fa54724bd15a3cfc2ac3bfe53a4699cfbc85e1c394757cee4f81eadaee79cc58b1bd801d6563fe64a4fb652c1e0a9be24cb5c32b55288b12778cda1dc911adae0729a3267af1782692b9318c2d4b111babd863c97fcfe17cf3a696361020697856364859aedaaf0efd18a4fc3fe827d37d076add2bf0b74e4d3ad97fa6e249f067ea3be4bc802ff6d41944b8ca3c4e4c7a1e8dad33d1fa3e7481f399eaf18a91ee9815ee75a47e694a327a2c292bd77dc245968cb713466dfdaa3ee0799614471a1e7f6f0195c18e74a8100da7d5e60762f66f420a08c60cdc86b0c579b2930c8dff3b5b243fff4444639a43749625e866ad71bbdc22b306985186c6421d5d5f07363a773287b452f094b0b18f7df07b5fd21655e3e0d2c5ca0cd7f5d1a3101e4ad560f262c4f8af263b90005dfb4547cbc42387a36343c4ef1fe59d6be6310a15b26e8e1c386386932521e2198a90514d5c6802260f285564ac38ae1ab2be40dddf396ef8d33cc806bafe66ac235dcf4bd8c5e58ff9b0a6da14788940713254001bba3fa9cbf8e4b2

private def light (n : ℕ) : Bool :=
  if n≤138 then decide n.Prime else n.gcd 691778647261948849222819828311491035886734385827028118707676848307166514238979223884785249055995983385450621636277440066920043595627074569065446040152660143904127838730788278294186615891819670506731208704000000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤19235) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 138 = 691778647261948849222819828311491035886734385827028118707676848307166514238979223884785249055995983385450621636277440066920043595627074569065446040152660143904127838730788278294186615891819670506731208704000000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 138 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤19235 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 37 := by unfold smallValid; decide +kernel

private theorem sp37 : smallValid 37 38 := by unfold smallValid; decide +kernel

private theorem sp75 : smallValid 75 37 := by unfold smallValid; decide +kernel

private theorem sp112 : smallValid 112 38 := by unfold smallValid; decide +kernel

private theorem sp150 : smallValid 150 37 := by unfold smallValid; decide +kernel

private theorem sp187 : smallValid 187 38 := by unfold smallValid; decide +kernel

private theorem sp225 : smallValid 225 37 := by unfold smallValid; decide +kernel

private theorem sp262 : smallValid 262 38 := by unfold smallValid; decide +kernel

private theorem sp300 : smallValid 300 37 := by unfold smallValid; decide +kernel

private theorem sp337 : smallValid 337 38 := by unfold smallValid; decide +kernel

private theorem sp375 : smallValid 375 37 := by unfold smallValid; decide +kernel

private theorem sp412 : smallValid 412 38 := by unfold smallValid; decide +kernel

private theorem sp450 : smallValid 450 37 := by unfold smallValid; decide +kernel

private theorem sp487 : smallValid 487 38 := by unfold smallValid; decide +kernel

private theorem sp525 : smallValid 525 38 := by unfold smallValid; decide +kernel

private theorem sp563 : smallValid 563 38 := by unfold smallValid; decide +kernel

private theorem sp601 : smallValid 601 37 := by unfold smallValid; decide +kernel

private theorem sp638 : smallValid 638 38 := by unfold smallValid; decide +kernel

private theorem sp676 : smallValid 676 37 := by unfold smallValid; decide +kernel

private theorem sp713 : smallValid 713 38 := by unfold smallValid; decide +kernel

private theorem sp751 : smallValid 751 37 := by unfold smallValid; decide +kernel

private theorem sp788 : smallValid 788 38 := by unfold smallValid; decide +kernel

private theorem sp826 : smallValid 826 37 := by unfold smallValid; decide +kernel

private theorem sp863 : smallValid 863 38 := by unfold smallValid; decide +kernel

private theorem sp901 : smallValid 901 37 := by unfold smallValid; decide +kernel

private theorem sp938 : smallValid 938 38 := by unfold smallValid; decide +kernel

private theorem sp976 : smallValid 976 37 := by unfold smallValid; decide +kernel

private theorem sp1013 : smallValid 1013 38 := by unfold smallValid; decide +kernel

private theorem sp1051 : smallValid 1051 37 := by unfold smallValid; decide +kernel

private theorem sp1088 : smallValid 1088 38 := by unfold smallValid; decide +kernel

private theorem sp1126 : smallValid 1126 38 := by unfold smallValid; decide +kernel

private theorem sp1164 : smallValid 1164 38 := by unfold smallValid; decide +kernel

private theorem sp1202 : smallValid 1202 37 := by unfold smallValid; decide +kernel

private theorem sp1239 : smallValid 1239 38 := by unfold smallValid; decide +kernel

private theorem sp1277 : smallValid 1277 37 := by unfold smallValid; decide +kernel

private theorem sp1314 : smallValid 1314 38 := by unfold smallValid; decide +kernel

private theorem sp1352 : smallValid 1352 37 := by unfold smallValid; decide +kernel

private theorem sp1389 : smallValid 1389 38 := by unfold smallValid; decide +kernel

private theorem sp1427 : smallValid 1427 37 := by unfold smallValid; decide +kernel

private theorem sp1464 : smallValid 1464 38 := by unfold smallValid; decide +kernel

private theorem sp1502 : smallValid 1502 37 := by unfold smallValid; decide +kernel

private theorem sp1539 : smallValid 1539 38 := by unfold smallValid; decide +kernel

private theorem sp1577 : smallValid 1577 37 := by unfold smallValid; decide +kernel

private theorem sp1614 : smallValid 1614 38 := by unfold smallValid; decide +kernel

private theorem sp1652 : smallValid 1652 37 := by unfold smallValid; decide +kernel

private theorem sp1689 : smallValid 1689 38 := by unfold smallValid; decide +kernel

private theorem sp1727 : smallValid 1727 38 := by unfold smallValid; decide +kernel

private theorem sp1765 : smallValid 1765 38 := by unfold smallValid; decide +kernel

private theorem sp1803 : smallValid 1803 37 := by unfold smallValid; decide +kernel

private theorem sp1840 : smallValid 1840 38 := by unfold smallValid; decide +kernel

private theorem sp1878 : smallValid 1878 37 := by unfold smallValid; decide +kernel

private theorem sp1915 : smallValid 1915 38 := by unfold smallValid; decide +kernel

private theorem sp1953 : smallValid 1953 37 := by unfold smallValid; decide +kernel

private theorem sp1990 : smallValid 1990 38 := by unfold smallValid; decide +kernel

private theorem sp2028 : smallValid 2028 37 := by unfold smallValid; decide +kernel

private theorem sp2065 : smallValid 2065 38 := by unfold smallValid; decide +kernel

private theorem sp2103 : smallValid 2103 37 := by unfold smallValid; decide +kernel

private theorem sp2140 : smallValid 2140 38 := by unfold smallValid; decide +kernel

private theorem sp2178 : smallValid 2178 37 := by unfold smallValid; decide +kernel

private theorem sp2215 : smallValid 2215 38 := by unfold smallValid; decide +kernel

private theorem sp2253 : smallValid 2253 37 := by unfold smallValid; decide +kernel

private theorem sp2290 : smallValid 2290 38 := by unfold smallValid; decide +kernel

private theorem sp2328 : smallValid 2328 38 := by unfold smallValid; decide +kernel

private theorem sp2366 : smallValid 2366 38 := by unfold smallValid; decide +kernel

private theorem sp2404 : smallValid 2404 37 := by unfold smallValid; decide +kernel

private theorem sp2441 : smallValid 2441 38 := by unfold smallValid; decide +kernel

private theorem sp2479 : smallValid 2479 37 := by unfold smallValid; decide +kernel

private theorem sp2516 : smallValid 2516 38 := by unfold smallValid; decide +kernel

private theorem sp2554 : smallValid 2554 37 := by unfold smallValid; decide +kernel

private theorem sp2591 : smallValid 2591 38 := by unfold smallValid; decide +kernel

private theorem sp2629 : smallValid 2629 37 := by unfold smallValid; decide +kernel

private theorem sp2666 : smallValid 2666 38 := by unfold smallValid; decide +kernel

private theorem sp2704 : smallValid 2704 37 := by unfold smallValid; decide +kernel

private theorem sp2741 : smallValid 2741 38 := by unfold smallValid; decide +kernel

private theorem sp2779 : smallValid 2779 37 := by unfold smallValid; decide +kernel

private theorem sp2816 : smallValid 2816 38 := by unfold smallValid; decide +kernel

private theorem sp2854 : smallValid 2854 37 := by unfold smallValid; decide +kernel

private theorem sp2891 : smallValid 2891 38 := by unfold smallValid; decide +kernel

private theorem sp2929 : smallValid 2929 38 := by unfold smallValid; decide +kernel

private theorem sp2967 : smallValid 2967 38 := by unfold smallValid; decide +kernel

private theorem sp3005 : smallValid 3005 37 := by unfold smallValid; decide +kernel

private theorem sp3042 : smallValid 3042 38 := by unfold smallValid; decide +kernel

private theorem sp3080 : smallValid 3080 37 := by unfold smallValid; decide +kernel

private theorem sp3117 : smallValid 3117 38 := by unfold smallValid; decide +kernel

private theorem sp3155 : smallValid 3155 37 := by unfold smallValid; decide +kernel

private theorem sp3192 : smallValid 3192 38 := by unfold smallValid; decide +kernel

private theorem sp3230 : smallValid 3230 37 := by unfold smallValid; decide +kernel

private theorem sp3267 : smallValid 3267 38 := by unfold smallValid; decide +kernel

private theorem sp3305 : smallValid 3305 37 := by unfold smallValid; decide +kernel

private theorem sp3342 : smallValid 3342 38 := by unfold smallValid; decide +kernel

private theorem sp3380 : smallValid 3380 37 := by unfold smallValid; decide +kernel

private theorem sp3417 : smallValid 3417 38 := by unfold smallValid; decide +kernel

private theorem sp3455 : smallValid 3455 37 := by unfold smallValid; decide +kernel

private theorem sp3492 : smallValid 3492 38 := by unfold smallValid; decide +kernel

private theorem sp3530 : smallValid 3530 38 := by unfold smallValid; decide +kernel

private theorem sp3568 : smallValid 3568 38 := by unfold smallValid; decide +kernel

private theorem sp3606 : smallValid 3606 37 := by unfold smallValid; decide +kernel

private theorem sp3643 : smallValid 3643 38 := by unfold smallValid; decide +kernel

private theorem sp3681 : smallValid 3681 37 := by unfold smallValid; decide +kernel

private theorem sp3718 : smallValid 3718 38 := by unfold smallValid; decide +kernel

private theorem sp3756 : smallValid 3756 37 := by unfold smallValid; decide +kernel

private theorem sp3793 : smallValid 3793 38 := by unfold smallValid; decide +kernel

private theorem sp3831 : smallValid 3831 37 := by unfold smallValid; decide +kernel

private theorem sp3868 : smallValid 3868 38 := by unfold smallValid; decide +kernel

private theorem sp3906 : smallValid 3906 37 := by unfold smallValid; decide +kernel

private theorem sp3943 : smallValid 3943 38 := by unfold smallValid; decide +kernel

private theorem sp3981 : smallValid 3981 37 := by unfold smallValid; decide +kernel

private theorem sp4018 : smallValid 4018 38 := by unfold smallValid; decide +kernel

private theorem sp4056 : smallValid 4056 37 := by unfold smallValid; decide +kernel

private theorem sp4093 : smallValid 4093 38 := by unfold smallValid; decide +kernel

private theorem sp4131 : smallValid 4131 38 := by unfold smallValid; decide +kernel

private theorem sp4169 : smallValid 4169 38 := by unfold smallValid; decide +kernel

private theorem sp4207 : smallValid 4207 37 := by unfold smallValid; decide +kernel

private theorem sp4244 : smallValid 4244 38 := by unfold smallValid; decide +kernel

private theorem sp4282 : smallValid 4282 37 := by unfold smallValid; decide +kernel

private theorem sp4319 : smallValid 4319 38 := by unfold smallValid; decide +kernel

private theorem sp4357 : smallValid 4357 37 := by unfold smallValid; decide +kernel

private theorem sp4394 : smallValid 4394 38 := by unfold smallValid; decide +kernel

private theorem sp4432 : smallValid 4432 38 := by unfold smallValid; decide +kernel

private theorem sp4470 : smallValid 4470 38 := by unfold smallValid; decide +kernel

private theorem sp4508 : smallValid 4508 37 := by unfold smallValid; decide +kernel

private theorem sp4545 : smallValid 4545 38 := by unfold smallValid; decide +kernel

private theorem sp4583 : smallValid 4583 37 := by unfold smallValid; decide +kernel

private theorem sp4620 : smallValid 4620 38 := by unfold smallValid; decide +kernel

private theorem sp4658 : smallValid 4658 37 := by unfold smallValid; decide +kernel

private theorem sp4695 : smallValid 4695 38 := by unfold smallValid; decide +kernel

private theorem sp4733 : smallValid 4733 38 := by unfold smallValid; decide +kernel

private theorem sp4771 : smallValid 4771 38 := by unfold smallValid; decide +kernel

private theorem sp4809 : smallValid 4809 37 := by unfold smallValid; decide +kernel

private theorem sp4846 : smallValid 4846 38 := by unfold smallValid; decide +kernel

private theorem sp4884 : smallValid 4884 37 := by unfold smallValid; decide +kernel

private theorem sp4921 : smallValid 4921 38 := by unfold smallValid; decide +kernel

private theorem sp4959 : smallValid 4959 37 := by unfold smallValid; decide +kernel

private theorem sp4996 : smallValid 4996 38 := by unfold smallValid; decide +kernel

private theorem sp5034 : smallValid 5034 37 := by unfold smallValid; decide +kernel

private theorem sp5071 : smallValid 5071 38 := by unfold smallValid; decide +kernel

private theorem sp5109 : smallValid 5109 37 := by unfold smallValid; decide +kernel

private theorem sp5146 : smallValid 5146 38 := by unfold smallValid; decide +kernel

private theorem sp5184 : smallValid 5184 37 := by unfold smallValid; decide +kernel

private theorem sp5221 : smallValid 5221 38 := by unfold smallValid; decide +kernel

private theorem sp5259 : smallValid 5259 37 := by unfold smallValid; decide +kernel

private theorem sp5296 : smallValid 5296 38 := by unfold smallValid; decide +kernel

private theorem sp5334 : smallValid 5334 38 := by unfold smallValid; decide +kernel

private theorem sp5372 : smallValid 5372 38 := by unfold smallValid; decide +kernel

private theorem sp5410 : smallValid 5410 37 := by unfold smallValid; decide +kernel

private theorem sp5447 : smallValid 5447 38 := by unfold smallValid; decide +kernel

private theorem sp5485 : smallValid 5485 37 := by unfold smallValid; decide +kernel

private theorem sp5522 : smallValid 5522 38 := by unfold smallValid; decide +kernel

private theorem sp5560 : smallValid 5560 37 := by unfold smallValid; decide +kernel

private theorem sp5597 : smallValid 5597 38 := by unfold smallValid; decide +kernel

private theorem sp5635 : smallValid 5635 37 := by unfold smallValid; decide +kernel

private theorem sp5672 : smallValid 5672 38 := by unfold smallValid; decide +kernel

private theorem sp5710 : smallValid 5710 37 := by unfold smallValid; decide +kernel

private theorem sp5747 : smallValid 5747 38 := by unfold smallValid; decide +kernel

private theorem sp5785 : smallValid 5785 37 := by unfold smallValid; decide +kernel

private theorem sp5822 : smallValid 5822 38 := by unfold smallValid; decide +kernel

private theorem sp5860 : smallValid 5860 37 := by unfold smallValid; decide +kernel

private theorem sp5897 : smallValid 5897 38 := by unfold smallValid; decide +kernel

private theorem sp5935 : smallValid 5935 38 := by unfold smallValid; decide +kernel

private theorem sp5973 : smallValid 5973 38 := by unfold smallValid; decide +kernel

private theorem sp6011 : smallValid 6011 37 := by unfold smallValid; decide +kernel

private theorem sp6048 : smallValid 6048 38 := by unfold smallValid; decide +kernel

private theorem sp6086 : smallValid 6086 37 := by unfold smallValid; decide +kernel

private theorem sp6123 : smallValid 6123 38 := by unfold smallValid; decide +kernel

private theorem sp6161 : smallValid 6161 37 := by unfold smallValid; decide +kernel

private theorem sp6198 : smallValid 6198 38 := by unfold smallValid; decide +kernel

private theorem sp6236 : smallValid 6236 37 := by unfold smallValid; decide +kernel

private theorem sp6273 : smallValid 6273 38 := by unfold smallValid; decide +kernel

private theorem sp6311 : smallValid 6311 37 := by unfold smallValid; decide +kernel

private theorem sp6348 : smallValid 6348 38 := by unfold smallValid; decide +kernel

private theorem sp6386 : smallValid 6386 37 := by unfold smallValid; decide +kernel

private theorem sp6423 : smallValid 6423 38 := by unfold smallValid; decide +kernel

private theorem sp6461 : smallValid 6461 37 := by unfold smallValid; decide +kernel

private theorem sp6498 : smallValid 6498 38 := by unfold smallValid; decide +kernel

private theorem sp6536 : smallValid 6536 38 := by unfold smallValid; decide +kernel

private theorem sp6574 : smallValid 6574 38 := by unfold smallValid; decide +kernel

private theorem sp6612 : smallValid 6612 37 := by unfold smallValid; decide +kernel

private theorem sp6649 : smallValid 6649 38 := by unfold smallValid; decide +kernel

private theorem sp6687 : smallValid 6687 37 := by unfold smallValid; decide +kernel

private theorem sp6724 : smallValid 6724 38 := by unfold smallValid; decide +kernel

private theorem sp6762 : smallValid 6762 37 := by unfold smallValid; decide +kernel

private theorem sp6799 : smallValid 6799 38 := by unfold smallValid; decide +kernel

private theorem sp6837 : smallValid 6837 37 := by unfold smallValid; decide +kernel

private theorem sp6874 : smallValid 6874 38 := by unfold smallValid; decide +kernel

private theorem sp6912 : smallValid 6912 37 := by unfold smallValid; decide +kernel

private theorem sp6949 : smallValid 6949 38 := by unfold smallValid; decide +kernel

private theorem sp6987 : smallValid 6987 37 := by unfold smallValid; decide +kernel

private theorem sp7024 : smallValid 7024 38 := by unfold smallValid; decide +kernel

private theorem sp7062 : smallValid 7062 37 := by unfold smallValid; decide +kernel

private theorem sp7099 : smallValid 7099 38 := by unfold smallValid; decide +kernel

private theorem sp7137 : smallValid 7137 38 := by unfold smallValid; decide +kernel

private theorem sp7175 : smallValid 7175 38 := by unfold smallValid; decide +kernel

private theorem sp7213 : smallValid 7213 37 := by unfold smallValid; decide +kernel

private theorem sp7250 : smallValid 7250 38 := by unfold smallValid; decide +kernel

private theorem sp7288 : smallValid 7288 37 := by unfold smallValid; decide +kernel

private theorem sp7325 : smallValid 7325 38 := by unfold smallValid; decide +kernel

private theorem sp7363 : smallValid 7363 37 := by unfold smallValid; decide +kernel

private theorem sp7400 : smallValid 7400 38 := by unfold smallValid; decide +kernel

private theorem sp7438 : smallValid 7438 37 := by unfold smallValid; decide +kernel

private theorem sp7475 : smallValid 7475 38 := by unfold smallValid; decide +kernel

private theorem sp7513 : smallValid 7513 37 := by unfold smallValid; decide +kernel

private theorem sp7550 : smallValid 7550 38 := by unfold smallValid; decide +kernel

private theorem sp7588 : smallValid 7588 37 := by unfold smallValid; decide +kernel

private theorem sp7625 : smallValid 7625 38 := by unfold smallValid; decide +kernel

private theorem sp7663 : smallValid 7663 37 := by unfold smallValid; decide +kernel

private theorem sp7700 : smallValid 7700 38 := by unfold smallValid; decide +kernel

private theorem sp7738 : smallValid 7738 38 := by unfold smallValid; decide +kernel

private theorem sp7776 : smallValid 7776 38 := by unfold smallValid; decide +kernel

private theorem sp7814 : smallValid 7814 37 := by unfold smallValid; decide +kernel

private theorem sp7851 : smallValid 7851 38 := by unfold smallValid; decide +kernel

private theorem sp7889 : smallValid 7889 37 := by unfold smallValid; decide +kernel

private theorem sp7926 : smallValid 7926 38 := by unfold smallValid; decide +kernel

private theorem sp7964 : smallValid 7964 37 := by unfold smallValid; decide +kernel

private theorem sp8001 : smallValid 8001 38 := by unfold smallValid; decide +kernel

private theorem sp8039 : smallValid 8039 37 := by unfold smallValid; decide +kernel

private theorem sp8076 : smallValid 8076 38 := by unfold smallValid; decide +kernel

private theorem sp8114 : smallValid 8114 37 := by unfold smallValid; decide +kernel

private theorem sp8151 : smallValid 8151 38 := by unfold smallValid; decide +kernel

private theorem sp8189 : smallValid 8189 37 := by unfold smallValid; decide +kernel

private theorem sp8226 : smallValid 8226 38 := by unfold smallValid; decide +kernel

private theorem sp8264 : smallValid 8264 37 := by unfold smallValid; decide +kernel

private theorem sp8301 : smallValid 8301 38 := by unfold smallValid; decide +kernel

private theorem sp8339 : smallValid 8339 38 := by unfold smallValid; decide +kernel

private theorem sp8377 : smallValid 8377 38 := by unfold smallValid; decide +kernel

private theorem sp8415 : smallValid 8415 37 := by unfold smallValid; decide +kernel

private theorem sp8452 : smallValid 8452 38 := by unfold smallValid; decide +kernel

private theorem sp8490 : smallValid 8490 37 := by unfold smallValid; decide +kernel

private theorem sp8527 : smallValid 8527 38 := by unfold smallValid; decide +kernel

private theorem sp8565 : smallValid 8565 37 := by unfold smallValid; decide +kernel

private theorem sp8602 : smallValid 8602 38 := by unfold smallValid; decide +kernel

private theorem sp8640 : smallValid 8640 37 := by unfold smallValid; decide +kernel

private theorem sp8677 : smallValid 8677 38 := by unfold smallValid; decide +kernel

private theorem sp8715 : smallValid 8715 37 := by unfold smallValid; decide +kernel

private theorem sp8752 : smallValid 8752 38 := by unfold smallValid; decide +kernel

private theorem sp8790 : smallValid 8790 37 := by unfold smallValid; decide +kernel

private theorem sp8827 : smallValid 8827 38 := by unfold smallValid; decide +kernel

private theorem sp8865 : smallValid 8865 37 := by unfold smallValid; decide +kernel

private theorem sp8902 : smallValid 8902 38 := by unfold smallValid; decide +kernel

private theorem sp8940 : smallValid 8940 38 := by unfold smallValid; decide +kernel

private theorem sp8978 : smallValid 8978 38 := by unfold smallValid; decide +kernel

private theorem sp9016 : smallValid 9016 37 := by unfold smallValid; decide +kernel

private theorem sp9053 : smallValid 9053 38 := by unfold smallValid; decide +kernel

private theorem sp9091 : smallValid 9091 37 := by unfold smallValid; decide +kernel

private theorem sp9128 : smallValid 9128 38 := by unfold smallValid; decide +kernel

private theorem sp9166 : smallValid 9166 37 := by unfold smallValid; decide +kernel

private theorem sp9203 : smallValid 9203 38 := by unfold smallValid; decide +kernel

private theorem sp9241 : smallValid 9241 38 := by unfold smallValid; decide +kernel

private theorem sp9279 : smallValid 9279 38 := by unfold smallValid; decide +kernel

private theorem sp9317 : smallValid 9317 37 := by unfold smallValid; decide +kernel

private theorem sp9354 : smallValid 9354 38 := by unfold smallValid; decide +kernel

private theorem sp9392 : smallValid 9392 37 := by unfold smallValid; decide +kernel

private theorem sp9429 : smallValid 9429 38 := by unfold smallValid; decide +kernel

private theorem sp9467 : smallValid 9467 37 := by unfold smallValid; decide +kernel

private theorem sp9504 : smallValid 9504 38 := by unfold smallValid; decide +kernel

private theorem sp9542 : smallValid 9542 38 := by unfold smallValid; decide +kernel

private theorem sp9580 : smallValid 9580 38 := by unfold smallValid; decide +kernel

private theorem sp9618 : smallValid 9618 37 := by unfold smallValid; decide +kernel

private theorem sp9655 : smallValid 9655 38 := by unfold smallValid; decide +kernel

private theorem sp9693 : smallValid 9693 37 := by unfold smallValid; decide +kernel

private theorem sp9730 : smallValid 9730 38 := by unfold smallValid; decide +kernel

private theorem sp9768 : smallValid 9768 37 := by unfold smallValid; decide +kernel

private theorem sp9805 : smallValid 9805 38 := by unfold smallValid; decide +kernel

private theorem sp9843 : smallValid 9843 37 := by unfold smallValid; decide +kernel

private theorem sp9880 : smallValid 9880 38 := by unfold smallValid; decide +kernel

private theorem sp9918 : smallValid 9918 37 := by unfold smallValid; decide +kernel

private theorem sp9955 : smallValid 9955 38 := by unfold smallValid; decide +kernel

private theorem sp9993 : smallValid 9993 37 := by unfold smallValid; decide +kernel

private theorem sp10030 : smallValid 10030 38 := by unfold smallValid; decide +kernel

private theorem sp10068 : smallValid 10068 37 := by unfold smallValid; decide +kernel

private theorem sp10105 : smallValid 10105 38 := by unfold smallValid; decide +kernel

private theorem sp10143 : smallValid 10143 38 := by unfold smallValid; decide +kernel

private theorem sp10181 : smallValid 10181 38 := by unfold smallValid; decide +kernel

private theorem sp10219 : smallValid 10219 37 := by unfold smallValid; decide +kernel

private theorem sp10256 : smallValid 10256 38 := by unfold smallValid; decide +kernel

private theorem sp10294 : smallValid 10294 37 := by unfold smallValid; decide +kernel

private theorem sp10331 : smallValid 10331 38 := by unfold smallValid; decide +kernel

private theorem sp10369 : smallValid 10369 37 := by unfold smallValid; decide +kernel

private theorem sp10406 : smallValid 10406 38 := by unfold smallValid; decide +kernel

private theorem sp10444 : smallValid 10444 37 := by unfold smallValid; decide +kernel

private theorem sp10481 : smallValid 10481 38 := by unfold smallValid; decide +kernel

private theorem sp10519 : smallValid 10519 37 := by unfold smallValid; decide +kernel

private theorem sp10556 : smallValid 10556 38 := by unfold smallValid; decide +kernel

private theorem sp10594 : smallValid 10594 37 := by unfold smallValid; decide +kernel

private theorem sp10631 : smallValid 10631 38 := by unfold smallValid; decide +kernel

private theorem sp10669 : smallValid 10669 37 := by unfold smallValid; decide +kernel

private theorem sp10706 : smallValid 10706 38 := by unfold smallValid; decide +kernel

private theorem sp10744 : smallValid 10744 38 := by unfold smallValid; decide +kernel

private theorem sp10782 : smallValid 10782 38 := by unfold smallValid; decide +kernel

private theorem sp10820 : smallValid 10820 37 := by unfold smallValid; decide +kernel

private theorem sp10857 : smallValid 10857 38 := by unfold smallValid; decide +kernel

private theorem sp10895 : smallValid 10895 37 := by unfold smallValid; decide +kernel

private theorem sp10932 : smallValid 10932 38 := by unfold smallValid; decide +kernel

private theorem sp10970 : smallValid 10970 37 := by unfold smallValid; decide +kernel

private theorem sp11007 : smallValid 11007 38 := by unfold smallValid; decide +kernel

private theorem sp11045 : smallValid 11045 37 := by unfold smallValid; decide +kernel

private theorem sp11082 : smallValid 11082 38 := by unfold smallValid; decide +kernel

private theorem sp11120 : smallValid 11120 37 := by unfold smallValid; decide +kernel

private theorem sp11157 : smallValid 11157 38 := by unfold smallValid; decide +kernel

private theorem sp11195 : smallValid 11195 37 := by unfold smallValid; decide +kernel

private theorem sp11232 : smallValid 11232 38 := by unfold smallValid; decide +kernel

private theorem sp11270 : smallValid 11270 37 := by unfold smallValid; decide +kernel

private theorem sp11307 : smallValid 11307 38 := by unfold smallValid; decide +kernel

private theorem sp11345 : smallValid 11345 38 := by unfold smallValid; decide +kernel

private theorem sp11383 : smallValid 11383 38 := by unfold smallValid; decide +kernel

private theorem sp11421 : smallValid 11421 37 := by unfold smallValid; decide +kernel

private theorem sp11458 : smallValid 11458 38 := by unfold smallValid; decide +kernel

private theorem sp11496 : smallValid 11496 37 := by unfold smallValid; decide +kernel

private theorem sp11533 : smallValid 11533 38 := by unfold smallValid; decide +kernel

private theorem sp11571 : smallValid 11571 37 := by unfold smallValid; decide +kernel

private theorem sp11608 : smallValid 11608 38 := by unfold smallValid; decide +kernel

private theorem sp11646 : smallValid 11646 37 := by unfold smallValid; decide +kernel

private theorem sp11683 : smallValid 11683 38 := by unfold smallValid; decide +kernel

private theorem sp11721 : smallValid 11721 37 := by unfold smallValid; decide +kernel

private theorem sp11758 : smallValid 11758 38 := by unfold smallValid; decide +kernel

private theorem sp11796 : smallValid 11796 37 := by unfold smallValid; decide +kernel

private theorem sp11833 : smallValid 11833 38 := by unfold smallValid; decide +kernel

private theorem sp11871 : smallValid 11871 37 := by unfold smallValid; decide +kernel

private theorem sp11908 : smallValid 11908 38 := by unfold smallValid; decide +kernel

private theorem sp11946 : smallValid 11946 38 := by unfold smallValid; decide +kernel

private theorem sp11984 : smallValid 11984 38 := by unfold smallValid; decide +kernel

private theorem sp12022 : smallValid 12022 37 := by unfold smallValid; decide +kernel

private theorem sp12059 : smallValid 12059 38 := by unfold smallValid; decide +kernel

private theorem sp12097 : smallValid 12097 37 := by unfold smallValid; decide +kernel

private theorem sp12134 : smallValid 12134 38 := by unfold smallValid; decide +kernel

private theorem sp12172 : smallValid 12172 37 := by unfold smallValid; decide +kernel

private theorem sp12209 : smallValid 12209 38 := by unfold smallValid; decide +kernel

private theorem sp12247 : smallValid 12247 37 := by unfold smallValid; decide +kernel

private theorem sp12284 : smallValid 12284 38 := by unfold smallValid; decide +kernel

private theorem sp12322 : smallValid 12322 37 := by unfold smallValid; decide +kernel

private theorem sp12359 : smallValid 12359 38 := by unfold smallValid; decide +kernel

private theorem sp12397 : smallValid 12397 37 := by unfold smallValid; decide +kernel

private theorem sp12434 : smallValid 12434 38 := by unfold smallValid; decide +kernel

private theorem sp12472 : smallValid 12472 37 := by unfold smallValid; decide +kernel

private theorem sp12509 : smallValid 12509 38 := by unfold smallValid; decide +kernel

private theorem sp12547 : smallValid 12547 38 := by unfold smallValid; decide +kernel

private theorem sp12585 : smallValid 12585 38 := by unfold smallValid; decide +kernel

private theorem sp12623 : smallValid 12623 37 := by unfold smallValid; decide +kernel

private theorem sp12660 : smallValid 12660 38 := by unfold smallValid; decide +kernel

private theorem sp12698 : smallValid 12698 37 := by unfold smallValid; decide +kernel

private theorem sp12735 : smallValid 12735 38 := by unfold smallValid; decide +kernel

private theorem sp12773 : smallValid 12773 37 := by unfold smallValid; decide +kernel

private theorem sp12810 : smallValid 12810 38 := by unfold smallValid; decide +kernel

private theorem sp12848 : smallValid 12848 37 := by unfold smallValid; decide +kernel

private theorem sp12885 : smallValid 12885 38 := by unfold smallValid; decide +kernel

private theorem sp12923 : smallValid 12923 37 := by unfold smallValid; decide +kernel

private theorem sp12960 : smallValid 12960 38 := by unfold smallValid; decide +kernel

private theorem sp12998 : smallValid 12998 37 := by unfold smallValid; decide +kernel

private theorem sp13035 : smallValid 13035 38 := by unfold smallValid; decide +kernel

private theorem sp13073 : smallValid 13073 37 := by unfold smallValid; decide +kernel

private theorem sp13110 : smallValid 13110 38 := by unfold smallValid; decide +kernel

private theorem sp13148 : smallValid 13148 38 := by unfold smallValid; decide +kernel

private theorem sp13186 : smallValid 13186 38 := by unfold smallValid; decide +kernel

private theorem sp13224 : smallValid 13224 37 := by unfold smallValid; decide +kernel

private theorem sp13261 : smallValid 13261 38 := by unfold smallValid; decide +kernel

private theorem sp13299 : smallValid 13299 37 := by unfold smallValid; decide +kernel

private theorem sp13336 : smallValid 13336 38 := by unfold smallValid; decide +kernel

private theorem sp13374 : smallValid 13374 37 := by unfold smallValid; decide +kernel

private theorem sp13411 : smallValid 13411 38 := by unfold smallValid; decide +kernel

private theorem sp13449 : smallValid 13449 37 := by unfold smallValid; decide +kernel

private theorem sp13486 : smallValid 13486 38 := by unfold smallValid; decide +kernel

private theorem sp13524 : smallValid 13524 37 := by unfold smallValid; decide +kernel

private theorem sp13561 : smallValid 13561 38 := by unfold smallValid; decide +kernel

private theorem sp13599 : smallValid 13599 37 := by unfold smallValid; decide +kernel

private theorem sp13636 : smallValid 13636 38 := by unfold smallValid; decide +kernel

private theorem sp13674 : smallValid 13674 37 := by unfold smallValid; decide +kernel

private theorem sp13711 : smallValid 13711 38 := by unfold smallValid; decide +kernel

private theorem sp13749 : smallValid 13749 38 := by unfold smallValid; decide +kernel

private theorem sp13787 : smallValid 13787 38 := by unfold smallValid; decide +kernel

private theorem sp13825 : smallValid 13825 37 := by unfold smallValid; decide +kernel

private theorem sp13862 : smallValid 13862 38 := by unfold smallValid; decide +kernel

private theorem sp13900 : smallValid 13900 37 := by unfold smallValid; decide +kernel

private theorem sp13937 : smallValid 13937 38 := by unfold smallValid; decide +kernel

private theorem sp13975 : smallValid 13975 37 := by unfold smallValid; decide +kernel

private theorem sp14012 : smallValid 14012 38 := by unfold smallValid; decide +kernel

private theorem sp14050 : smallValid 14050 38 := by unfold smallValid; decide +kernel

private theorem sp14088 : smallValid 14088 38 := by unfold smallValid; decide +kernel

private theorem sp14126 : smallValid 14126 37 := by unfold smallValid; decide +kernel

private theorem sp14163 : smallValid 14163 38 := by unfold smallValid; decide +kernel

private theorem sp14201 : smallValid 14201 37 := by unfold smallValid; decide +kernel

private theorem sp14238 : smallValid 14238 38 := by unfold smallValid; decide +kernel

private theorem sp14276 : smallValid 14276 37 := by unfold smallValid; decide +kernel

private theorem sp14313 : smallValid 14313 38 := by unfold smallValid; decide +kernel

private theorem sp14351 : smallValid 14351 38 := by unfold smallValid; decide +kernel

private theorem sp14389 : smallValid 14389 38 := by unfold smallValid; decide +kernel

private theorem sp14427 : smallValid 14427 37 := by unfold smallValid; decide +kernel

private theorem sp14464 : smallValid 14464 38 := by unfold smallValid; decide +kernel

private theorem sp14502 : smallValid 14502 37 := by unfold smallValid; decide +kernel

private theorem sp14539 : smallValid 14539 38 := by unfold smallValid; decide +kernel

private theorem sp14577 : smallValid 14577 37 := by unfold smallValid; decide +kernel

private theorem sp14614 : smallValid 14614 38 := by unfold smallValid; decide +kernel

private theorem sp14652 : smallValid 14652 37 := by unfold smallValid; decide +kernel

private theorem sp14689 : smallValid 14689 38 := by unfold smallValid; decide +kernel

private theorem sp14727 : smallValid 14727 37 := by unfold smallValid; decide +kernel

private theorem sp14764 : smallValid 14764 38 := by unfold smallValid; decide +kernel

private theorem sp14802 : smallValid 14802 37 := by unfold smallValid; decide +kernel

private theorem sp14839 : smallValid 14839 38 := by unfold smallValid; decide +kernel

private theorem sp14877 : smallValid 14877 37 := by unfold smallValid; decide +kernel

private theorem sp14914 : smallValid 14914 38 := by unfold smallValid; decide +kernel

private theorem sp14952 : smallValid 14952 38 := by unfold smallValid; decide +kernel

private theorem sp14990 : smallValid 14990 38 := by unfold smallValid; decide +kernel

private theorem sp15028 : smallValid 15028 37 := by unfold smallValid; decide +kernel

private theorem sp15065 : smallValid 15065 38 := by unfold smallValid; decide +kernel

private theorem sp15103 : smallValid 15103 37 := by unfold smallValid; decide +kernel

private theorem sp15140 : smallValid 15140 38 := by unfold smallValid; decide +kernel

private theorem sp15178 : smallValid 15178 37 := by unfold smallValid; decide +kernel

private theorem sp15215 : smallValid 15215 38 := by unfold smallValid; decide +kernel

private theorem sp15253 : smallValid 15253 37 := by unfold smallValid; decide +kernel

private theorem sp15290 : smallValid 15290 38 := by unfold smallValid; decide +kernel

private theorem sp15328 : smallValid 15328 37 := by unfold smallValid; decide +kernel

private theorem sp15365 : smallValid 15365 38 := by unfold smallValid; decide +kernel

private theorem sp15403 : smallValid 15403 37 := by unfold smallValid; decide +kernel

private theorem sp15440 : smallValid 15440 38 := by unfold smallValid; decide +kernel

private theorem sp15478 : smallValid 15478 37 := by unfold smallValid; decide +kernel

private theorem sp15515 : smallValid 15515 38 := by unfold smallValid; decide +kernel

private theorem sp15553 : smallValid 15553 38 := by unfold smallValid; decide +kernel

private theorem sp15591 : smallValid 15591 38 := by unfold smallValid; decide +kernel

private theorem sp15629 : smallValid 15629 37 := by unfold smallValid; decide +kernel

private theorem sp15666 : smallValid 15666 38 := by unfold smallValid; decide +kernel

private theorem sp15704 : smallValid 15704 37 := by unfold smallValid; decide +kernel

private theorem sp15741 : smallValid 15741 38 := by unfold smallValid; decide +kernel

private theorem sp15779 : smallValid 15779 37 := by unfold smallValid; decide +kernel

private theorem sp15816 : smallValid 15816 38 := by unfold smallValid; decide +kernel

private theorem sp15854 : smallValid 15854 37 := by unfold smallValid; decide +kernel

private theorem sp15891 : smallValid 15891 38 := by unfold smallValid; decide +kernel

private theorem sp15929 : smallValid 15929 37 := by unfold smallValid; decide +kernel

private theorem sp15966 : smallValid 15966 38 := by unfold smallValid; decide +kernel

private theorem sp16004 : smallValid 16004 37 := by unfold smallValid; decide +kernel

private theorem sp16041 : smallValid 16041 38 := by unfold smallValid; decide +kernel

private theorem sp16079 : smallValid 16079 37 := by unfold smallValid; decide +kernel

private theorem sp16116 : smallValid 16116 38 := by unfold smallValid; decide +kernel

private theorem sp16154 : smallValid 16154 38 := by unfold smallValid; decide +kernel

private theorem sp16192 : smallValid 16192 38 := by unfold smallValid; decide +kernel

private theorem sp16230 : smallValid 16230 37 := by unfold smallValid; decide +kernel

private theorem sp16267 : smallValid 16267 38 := by unfold smallValid; decide +kernel

private theorem sp16305 : smallValid 16305 37 := by unfold smallValid; decide +kernel

private theorem sp16342 : smallValid 16342 38 := by unfold smallValid; decide +kernel

private theorem sp16380 : smallValid 16380 37 := by unfold smallValid; decide +kernel

private theorem sp16417 : smallValid 16417 38 := by unfold smallValid; decide +kernel

private theorem sp16455 : smallValid 16455 37 := by unfold smallValid; decide +kernel

private theorem sp16492 : smallValid 16492 38 := by unfold smallValid; decide +kernel

private theorem sp16530 : smallValid 16530 37 := by unfold smallValid; decide +kernel

private theorem sp16567 : smallValid 16567 38 := by unfold smallValid; decide +kernel

private theorem sp16605 : smallValid 16605 37 := by unfold smallValid; decide +kernel

private theorem sp16642 : smallValid 16642 38 := by unfold smallValid; decide +kernel

private theorem sp16680 : smallValid 16680 37 := by unfold smallValid; decide +kernel

private theorem sp16717 : smallValid 16717 38 := by unfold smallValid; decide +kernel

private theorem sp16755 : smallValid 16755 38 := by unfold smallValid; decide +kernel

private theorem sp16793 : smallValid 16793 38 := by unfold smallValid; decide +kernel

private theorem sp16831 : smallValid 16831 37 := by unfold smallValid; decide +kernel

private theorem sp16868 : smallValid 16868 38 := by unfold smallValid; decide +kernel

private theorem sp16906 : smallValid 16906 37 := by unfold smallValid; decide +kernel

private theorem sp16943 : smallValid 16943 38 := by unfold smallValid; decide +kernel

private theorem sp16981 : smallValid 16981 37 := by unfold smallValid; decide +kernel

private theorem sp17018 : smallValid 17018 38 := by unfold smallValid; decide +kernel

private theorem sp17056 : smallValid 17056 37 := by unfold smallValid; decide +kernel

private theorem sp17093 : smallValid 17093 38 := by unfold smallValid; decide +kernel

private theorem sp17131 : smallValid 17131 37 := by unfold smallValid; decide +kernel

private theorem sp17168 : smallValid 17168 38 := by unfold smallValid; decide +kernel

private theorem sp17206 : smallValid 17206 37 := by unfold smallValid; decide +kernel

private theorem sp17243 : smallValid 17243 38 := by unfold smallValid; decide +kernel

private theorem sp17281 : smallValid 17281 37 := by unfold smallValid; decide +kernel

private theorem sp17318 : smallValid 17318 38 := by unfold smallValid; decide +kernel

private theorem sp17356 : smallValid 17356 38 := by unfold smallValid; decide +kernel

private theorem sp17394 : smallValid 17394 38 := by unfold smallValid; decide +kernel

private theorem sp17432 : smallValid 17432 37 := by unfold smallValid; decide +kernel

private theorem sp17469 : smallValid 17469 38 := by unfold smallValid; decide +kernel

private theorem sp17507 : smallValid 17507 37 := by unfold smallValid; decide +kernel

private theorem sp17544 : smallValid 17544 38 := by unfold smallValid; decide +kernel

private theorem sp17582 : smallValid 17582 37 := by unfold smallValid; decide +kernel

private theorem sp17619 : smallValid 17619 38 := by unfold smallValid; decide +kernel

private theorem sp17657 : smallValid 17657 37 := by unfold smallValid; decide +kernel

private theorem sp17694 : smallValid 17694 38 := by unfold smallValid; decide +kernel

private theorem sp17732 : smallValid 17732 37 := by unfold smallValid; decide +kernel

private theorem sp17769 : smallValid 17769 38 := by unfold smallValid; decide +kernel

private theorem sp17807 : smallValid 17807 37 := by unfold smallValid; decide +kernel

private theorem sp17844 : smallValid 17844 38 := by unfold smallValid; decide +kernel

private theorem sp17882 : smallValid 17882 37 := by unfold smallValid; decide +kernel

private theorem sp17919 : smallValid 17919 38 := by unfold smallValid; decide +kernel

private theorem sp17957 : smallValid 17957 38 := by unfold smallValid; decide +kernel

private theorem sp17995 : smallValid 17995 38 := by unfold smallValid; decide +kernel

private theorem sp18033 : smallValid 18033 37 := by unfold smallValid; decide +kernel

private theorem sp18070 : smallValid 18070 38 := by unfold smallValid; decide +kernel

private theorem sp18108 : smallValid 18108 37 := by unfold smallValid; decide +kernel

private theorem sp18145 : smallValid 18145 38 := by unfold smallValid; decide +kernel

private theorem sp18183 : smallValid 18183 37 := by unfold smallValid; decide +kernel

private theorem sp18220 : smallValid 18220 38 := by unfold smallValid; decide +kernel

private theorem sp18258 : smallValid 18258 37 := by unfold smallValid; decide +kernel

private theorem sp18295 : smallValid 18295 38 := by unfold smallValid; decide +kernel

private theorem sp18333 : smallValid 18333 37 := by unfold smallValid; decide +kernel

private theorem sp18370 : smallValid 18370 38 := by unfold smallValid; decide +kernel

private theorem sp18408 : smallValid 18408 37 := by unfold smallValid; decide +kernel

private theorem sp18445 : smallValid 18445 38 := by unfold smallValid; decide +kernel

private theorem sp18483 : smallValid 18483 37 := by unfold smallValid; decide +kernel

private theorem sp18520 : smallValid 18520 38 := by unfold smallValid; decide +kernel

private theorem sp18558 : smallValid 18558 38 := by unfold smallValid; decide +kernel

private theorem sp18596 : smallValid 18596 38 := by unfold smallValid; decide +kernel

private theorem sp18634 : smallValid 18634 37 := by unfold smallValid; decide +kernel

private theorem sp18671 : smallValid 18671 38 := by unfold smallValid; decide +kernel

private theorem sp18709 : smallValid 18709 37 := by unfold smallValid; decide +kernel

private theorem sp18746 : smallValid 18746 38 := by unfold smallValid; decide +kernel

private theorem sp18784 : smallValid 18784 37 := by unfold smallValid; decide +kernel

private theorem sp18821 : smallValid 18821 38 := by unfold smallValid; decide +kernel

private theorem sp18859 : smallValid 18859 38 := by unfold smallValid; decide +kernel

private theorem sp18897 : smallValid 18897 38 := by unfold smallValid; decide +kernel

private theorem sp18935 : smallValid 18935 37 := by unfold smallValid; decide +kernel

private theorem sp18972 : smallValid 18972 38 := by unfold smallValid; decide +kernel

private theorem sp19010 : smallValid 19010 37 := by unfold smallValid; decide +kernel

private theorem sp19047 : smallValid 19047 38 := by unfold smallValid; decide +kernel

private theorem sp19085 : smallValid 19085 37 := by unfold smallValid; decide +kernel

private theorem sp19122 : smallValid 19122 38 := by unfold smallValid; decide +kernel

private theorem sp19160 : smallValid 19160 38 := by unfold smallValid; decide +kernel

private theorem sp19198 : smallValid 19198 38 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤19235) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 19236 := (joinSmall (lo:=0) (a:=9618) (b:=9618) (joinSmall (lo:=0) (a:=4809) (b:=4809) (joinSmall (lo:=0) (a:=2404) (b:=2405) (joinSmall (lo:=0) (a:=1202) (b:=1202) (joinSmall (lo:=0) (a:=601) (b:=601) (joinSmall (lo:=0) (a:=300) (b:=301) (joinSmall (lo:=0) (a:=150) (b:=150) (joinSmall (lo:=0) (a:=75) (b:=75) (joinSmall (lo:=0) (a:=37) (b:=38) sp0 sp37) (joinSmall (lo:=75) (a:=37) (b:=38) sp75 sp112)) (joinSmall (lo:=150) (a:=75) (b:=75) (joinSmall (lo:=150) (a:=37) (b:=38) sp150 sp187) (joinSmall (lo:=225) (a:=37) (b:=38) sp225 sp262))) (joinSmall (lo:=300) (a:=150) (b:=151) (joinSmall (lo:=300) (a:=75) (b:=75) (joinSmall (lo:=300) (a:=37) (b:=38) sp300 sp337) (joinSmall (lo:=375) (a:=37) (b:=38) sp375 sp412)) (joinSmall (lo:=450) (a:=75) (b:=76) (joinSmall (lo:=450) (a:=37) (b:=38) sp450 sp487) (joinSmall (lo:=525) (a:=38) (b:=38) sp525 sp563)))) (joinSmall (lo:=601) (a:=300) (b:=301) (joinSmall (lo:=601) (a:=150) (b:=150) (joinSmall (lo:=601) (a:=75) (b:=75) (joinSmall (lo:=601) (a:=37) (b:=38) sp601 sp638) (joinSmall (lo:=676) (a:=37) (b:=38) sp676 sp713)) (joinSmall (lo:=751) (a:=75) (b:=75) (joinSmall (lo:=751) (a:=37) (b:=38) sp751 sp788) (joinSmall (lo:=826) (a:=37) (b:=38) sp826 sp863))) (joinSmall (lo:=901) (a:=150) (b:=151) (joinSmall (lo:=901) (a:=75) (b:=75) (joinSmall (lo:=901) (a:=37) (b:=38) sp901 sp938) (joinSmall (lo:=976) (a:=37) (b:=38) sp976 sp1013)) (joinSmall (lo:=1051) (a:=75) (b:=76) (joinSmall (lo:=1051) (a:=37) (b:=38) sp1051 sp1088) (joinSmall (lo:=1126) (a:=38) (b:=38) sp1126 sp1164))))) (joinSmall (lo:=1202) (a:=601) (b:=601) (joinSmall (lo:=1202) (a:=300) (b:=301) (joinSmall (lo:=1202) (a:=150) (b:=150) (joinSmall (lo:=1202) (a:=75) (b:=75) (joinSmall (lo:=1202) (a:=37) (b:=38) sp1202 sp1239) (joinSmall (lo:=1277) (a:=37) (b:=38) sp1277 sp1314)) (joinSmall (lo:=1352) (a:=75) (b:=75) (joinSmall (lo:=1352) (a:=37) (b:=38) sp1352 sp1389) (joinSmall (lo:=1427) (a:=37) (b:=38) sp1427 sp1464))) (joinSmall (lo:=1502) (a:=150) (b:=151) (joinSmall (lo:=1502) (a:=75) (b:=75) (joinSmall (lo:=1502) (a:=37) (b:=38) sp1502 sp1539) (joinSmall (lo:=1577) (a:=37) (b:=38) sp1577 sp1614)) (joinSmall (lo:=1652) (a:=75) (b:=76) (joinSmall (lo:=1652) (a:=37) (b:=38) sp1652 sp1689) (joinSmall (lo:=1727) (a:=38) (b:=38) sp1727 sp1765)))) (joinSmall (lo:=1803) (a:=300) (b:=301) (joinSmall (lo:=1803) (a:=150) (b:=150) (joinSmall (lo:=1803) (a:=75) (b:=75) (joinSmall (lo:=1803) (a:=37) (b:=38) sp1803 sp1840) (joinSmall (lo:=1878) (a:=37) (b:=38) sp1878 sp1915)) (joinSmall (lo:=1953) (a:=75) (b:=75) (joinSmall (lo:=1953) (a:=37) (b:=38) sp1953 sp1990) (joinSmall (lo:=2028) (a:=37) (b:=38) sp2028 sp2065))) (joinSmall (lo:=2103) (a:=150) (b:=151) (joinSmall (lo:=2103) (a:=75) (b:=75) (joinSmall (lo:=2103) (a:=37) (b:=38) sp2103 sp2140) (joinSmall (lo:=2178) (a:=37) (b:=38) sp2178 sp2215)) (joinSmall (lo:=2253) (a:=75) (b:=76) (joinSmall (lo:=2253) (a:=37) (b:=38) sp2253 sp2290) (joinSmall (lo:=2328) (a:=38) (b:=38) sp2328 sp2366)))))) (joinSmall (lo:=2404) (a:=1202) (b:=1203) (joinSmall (lo:=2404) (a:=601) (b:=601) (joinSmall (lo:=2404) (a:=300) (b:=301) (joinSmall (lo:=2404) (a:=150) (b:=150) (joinSmall (lo:=2404) (a:=75) (b:=75) (joinSmall (lo:=2404) (a:=37) (b:=38) sp2404 sp2441) (joinSmall (lo:=2479) (a:=37) (b:=38) sp2479 sp2516)) (joinSmall (lo:=2554) (a:=75) (b:=75) (joinSmall (lo:=2554) (a:=37) (b:=38) sp2554 sp2591) (joinSmall (lo:=2629) (a:=37) (b:=38) sp2629 sp2666))) (joinSmall (lo:=2704) (a:=150) (b:=151) (joinSmall (lo:=2704) (a:=75) (b:=75) (joinSmall (lo:=2704) (a:=37) (b:=38) sp2704 sp2741) (joinSmall (lo:=2779) (a:=37) (b:=38) sp2779 sp2816)) (joinSmall (lo:=2854) (a:=75) (b:=76) (joinSmall (lo:=2854) (a:=37) (b:=38) sp2854 sp2891) (joinSmall (lo:=2929) (a:=38) (b:=38) sp2929 sp2967)))) (joinSmall (lo:=3005) (a:=300) (b:=301) (joinSmall (lo:=3005) (a:=150) (b:=150) (joinSmall (lo:=3005) (a:=75) (b:=75) (joinSmall (lo:=3005) (a:=37) (b:=38) sp3005 sp3042) (joinSmall (lo:=3080) (a:=37) (b:=38) sp3080 sp3117)) (joinSmall (lo:=3155) (a:=75) (b:=75) (joinSmall (lo:=3155) (a:=37) (b:=38) sp3155 sp3192) (joinSmall (lo:=3230) (a:=37) (b:=38) sp3230 sp3267))) (joinSmall (lo:=3305) (a:=150) (b:=151) (joinSmall (lo:=3305) (a:=75) (b:=75) (joinSmall (lo:=3305) (a:=37) (b:=38) sp3305 sp3342) (joinSmall (lo:=3380) (a:=37) (b:=38) sp3380 sp3417)) (joinSmall (lo:=3455) (a:=75) (b:=76) (joinSmall (lo:=3455) (a:=37) (b:=38) sp3455 sp3492) (joinSmall (lo:=3530) (a:=38) (b:=38) sp3530 sp3568))))) (joinSmall (lo:=3606) (a:=601) (b:=602) (joinSmall (lo:=3606) (a:=300) (b:=301) (joinSmall (lo:=3606) (a:=150) (b:=150) (joinSmall (lo:=3606) (a:=75) (b:=75) (joinSmall (lo:=3606) (a:=37) (b:=38) sp3606 sp3643) (joinSmall (lo:=3681) (a:=37) (b:=38) sp3681 sp3718)) (joinSmall (lo:=3756) (a:=75) (b:=75) (joinSmall (lo:=3756) (a:=37) (b:=38) sp3756 sp3793) (joinSmall (lo:=3831) (a:=37) (b:=38) sp3831 sp3868))) (joinSmall (lo:=3906) (a:=150) (b:=151) (joinSmall (lo:=3906) (a:=75) (b:=75) (joinSmall (lo:=3906) (a:=37) (b:=38) sp3906 sp3943) (joinSmall (lo:=3981) (a:=37) (b:=38) sp3981 sp4018)) (joinSmall (lo:=4056) (a:=75) (b:=76) (joinSmall (lo:=4056) (a:=37) (b:=38) sp4056 sp4093) (joinSmall (lo:=4131) (a:=38) (b:=38) sp4131 sp4169)))) (joinSmall (lo:=4207) (a:=301) (b:=301) (joinSmall (lo:=4207) (a:=150) (b:=151) (joinSmall (lo:=4207) (a:=75) (b:=75) (joinSmall (lo:=4207) (a:=37) (b:=38) sp4207 sp4244) (joinSmall (lo:=4282) (a:=37) (b:=38) sp4282 sp4319)) (joinSmall (lo:=4357) (a:=75) (b:=76) (joinSmall (lo:=4357) (a:=37) (b:=38) sp4357 sp4394) (joinSmall (lo:=4432) (a:=38) (b:=38) sp4432 sp4470))) (joinSmall (lo:=4508) (a:=150) (b:=151) (joinSmall (lo:=4508) (a:=75) (b:=75) (joinSmall (lo:=4508) (a:=37) (b:=38) sp4508 sp4545) (joinSmall (lo:=4583) (a:=37) (b:=38) sp4583 sp4620)) (joinSmall (lo:=4658) (a:=75) (b:=76) (joinSmall (lo:=4658) (a:=37) (b:=38) sp4658 sp4695) (joinSmall (lo:=4733) (a:=38) (b:=38) sp4733 sp4771))))))) (joinSmall (lo:=4809) (a:=2404) (b:=2405) (joinSmall (lo:=4809) (a:=1202) (b:=1202) (joinSmall (lo:=4809) (a:=601) (b:=601) (joinSmall (lo:=4809) (a:=300) (b:=301) (joinSmall (lo:=4809) (a:=150) (b:=150) (joinSmall (lo:=4809) (a:=75) (b:=75) (joinSmall (lo:=4809) (a:=37) (b:=38) sp4809 sp4846) (joinSmall (lo:=4884) (a:=37) (b:=38) sp4884 sp4921)) (joinSmall (lo:=4959) (a:=75) (b:=75) (joinSmall (lo:=4959) (a:=37) (b:=38) sp4959 sp4996) (joinSmall (lo:=5034) (a:=37) (b:=38) sp5034 sp5071))) (joinSmall (lo:=5109) (a:=150) (b:=151) (joinSmall (lo:=5109) (a:=75) (b:=75) (joinSmall (lo:=5109) (a:=37) (b:=38) sp5109 sp5146) (joinSmall (lo:=5184) (a:=37) (b:=38) sp5184 sp5221)) (joinSmall (lo:=5259) (a:=75) (b:=76) (joinSmall (lo:=5259) (a:=37) (b:=38) sp5259 sp5296) (joinSmall (lo:=5334) (a:=38) (b:=38) sp5334 sp5372)))) (joinSmall (lo:=5410) (a:=300) (b:=301) (joinSmall (lo:=5410) (a:=150) (b:=150) (joinSmall (lo:=5410) (a:=75) (b:=75) (joinSmall (lo:=5410) (a:=37) (b:=38) sp5410 sp5447) (joinSmall (lo:=5485) (a:=37) (b:=38) sp5485 sp5522)) (joinSmall (lo:=5560) (a:=75) (b:=75) (joinSmall (lo:=5560) (a:=37) (b:=38) sp5560 sp5597) (joinSmall (lo:=5635) (a:=37) (b:=38) sp5635 sp5672))) (joinSmall (lo:=5710) (a:=150) (b:=151) (joinSmall (lo:=5710) (a:=75) (b:=75) (joinSmall (lo:=5710) (a:=37) (b:=38) sp5710 sp5747) (joinSmall (lo:=5785) (a:=37) (b:=38) sp5785 sp5822)) (joinSmall (lo:=5860) (a:=75) (b:=76) (joinSmall (lo:=5860) (a:=37) (b:=38) sp5860 sp5897) (joinSmall (lo:=5935) (a:=38) (b:=38) sp5935 sp5973))))) (joinSmall (lo:=6011) (a:=601) (b:=601) (joinSmall (lo:=6011) (a:=300) (b:=301) (joinSmall (lo:=6011) (a:=150) (b:=150) (joinSmall (lo:=6011) (a:=75) (b:=75) (joinSmall (lo:=6011) (a:=37) (b:=38) sp6011 sp6048) (joinSmall (lo:=6086) (a:=37) (b:=38) sp6086 sp6123)) (joinSmall (lo:=6161) (a:=75) (b:=75) (joinSmall (lo:=6161) (a:=37) (b:=38) sp6161 sp6198) (joinSmall (lo:=6236) (a:=37) (b:=38) sp6236 sp6273))) (joinSmall (lo:=6311) (a:=150) (b:=151) (joinSmall (lo:=6311) (a:=75) (b:=75) (joinSmall (lo:=6311) (a:=37) (b:=38) sp6311 sp6348) (joinSmall (lo:=6386) (a:=37) (b:=38) sp6386 sp6423)) (joinSmall (lo:=6461) (a:=75) (b:=76) (joinSmall (lo:=6461) (a:=37) (b:=38) sp6461 sp6498) (joinSmall (lo:=6536) (a:=38) (b:=38) sp6536 sp6574)))) (joinSmall (lo:=6612) (a:=300) (b:=301) (joinSmall (lo:=6612) (a:=150) (b:=150) (joinSmall (lo:=6612) (a:=75) (b:=75) (joinSmall (lo:=6612) (a:=37) (b:=38) sp6612 sp6649) (joinSmall (lo:=6687) (a:=37) (b:=38) sp6687 sp6724)) (joinSmall (lo:=6762) (a:=75) (b:=75) (joinSmall (lo:=6762) (a:=37) (b:=38) sp6762 sp6799) (joinSmall (lo:=6837) (a:=37) (b:=38) sp6837 sp6874))) (joinSmall (lo:=6912) (a:=150) (b:=151) (joinSmall (lo:=6912) (a:=75) (b:=75) (joinSmall (lo:=6912) (a:=37) (b:=38) sp6912 sp6949) (joinSmall (lo:=6987) (a:=37) (b:=38) sp6987 sp7024)) (joinSmall (lo:=7062) (a:=75) (b:=76) (joinSmall (lo:=7062) (a:=37) (b:=38) sp7062 sp7099) (joinSmall (lo:=7137) (a:=38) (b:=38) sp7137 sp7175)))))) (joinSmall (lo:=7213) (a:=1202) (b:=1203) (joinSmall (lo:=7213) (a:=601) (b:=601) (joinSmall (lo:=7213) (a:=300) (b:=301) (joinSmall (lo:=7213) (a:=150) (b:=150) (joinSmall (lo:=7213) (a:=75) (b:=75) (joinSmall (lo:=7213) (a:=37) (b:=38) sp7213 sp7250) (joinSmall (lo:=7288) (a:=37) (b:=38) sp7288 sp7325)) (joinSmall (lo:=7363) (a:=75) (b:=75) (joinSmall (lo:=7363) (a:=37) (b:=38) sp7363 sp7400) (joinSmall (lo:=7438) (a:=37) (b:=38) sp7438 sp7475))) (joinSmall (lo:=7513) (a:=150) (b:=151) (joinSmall (lo:=7513) (a:=75) (b:=75) (joinSmall (lo:=7513) (a:=37) (b:=38) sp7513 sp7550) (joinSmall (lo:=7588) (a:=37) (b:=38) sp7588 sp7625)) (joinSmall (lo:=7663) (a:=75) (b:=76) (joinSmall (lo:=7663) (a:=37) (b:=38) sp7663 sp7700) (joinSmall (lo:=7738) (a:=38) (b:=38) sp7738 sp7776)))) (joinSmall (lo:=7814) (a:=300) (b:=301) (joinSmall (lo:=7814) (a:=150) (b:=150) (joinSmall (lo:=7814) (a:=75) (b:=75) (joinSmall (lo:=7814) (a:=37) (b:=38) sp7814 sp7851) (joinSmall (lo:=7889) (a:=37) (b:=38) sp7889 sp7926)) (joinSmall (lo:=7964) (a:=75) (b:=75) (joinSmall (lo:=7964) (a:=37) (b:=38) sp7964 sp8001) (joinSmall (lo:=8039) (a:=37) (b:=38) sp8039 sp8076))) (joinSmall (lo:=8114) (a:=150) (b:=151) (joinSmall (lo:=8114) (a:=75) (b:=75) (joinSmall (lo:=8114) (a:=37) (b:=38) sp8114 sp8151) (joinSmall (lo:=8189) (a:=37) (b:=38) sp8189 sp8226)) (joinSmall (lo:=8264) (a:=75) (b:=76) (joinSmall (lo:=8264) (a:=37) (b:=38) sp8264 sp8301) (joinSmall (lo:=8339) (a:=38) (b:=38) sp8339 sp8377))))) (joinSmall (lo:=8415) (a:=601) (b:=602) (joinSmall (lo:=8415) (a:=300) (b:=301) (joinSmall (lo:=8415) (a:=150) (b:=150) (joinSmall (lo:=8415) (a:=75) (b:=75) (joinSmall (lo:=8415) (a:=37) (b:=38) sp8415 sp8452) (joinSmall (lo:=8490) (a:=37) (b:=38) sp8490 sp8527)) (joinSmall (lo:=8565) (a:=75) (b:=75) (joinSmall (lo:=8565) (a:=37) (b:=38) sp8565 sp8602) (joinSmall (lo:=8640) (a:=37) (b:=38) sp8640 sp8677))) (joinSmall (lo:=8715) (a:=150) (b:=151) (joinSmall (lo:=8715) (a:=75) (b:=75) (joinSmall (lo:=8715) (a:=37) (b:=38) sp8715 sp8752) (joinSmall (lo:=8790) (a:=37) (b:=38) sp8790 sp8827)) (joinSmall (lo:=8865) (a:=75) (b:=76) (joinSmall (lo:=8865) (a:=37) (b:=38) sp8865 sp8902) (joinSmall (lo:=8940) (a:=38) (b:=38) sp8940 sp8978)))) (joinSmall (lo:=9016) (a:=301) (b:=301) (joinSmall (lo:=9016) (a:=150) (b:=151) (joinSmall (lo:=9016) (a:=75) (b:=75) (joinSmall (lo:=9016) (a:=37) (b:=38) sp9016 sp9053) (joinSmall (lo:=9091) (a:=37) (b:=38) sp9091 sp9128)) (joinSmall (lo:=9166) (a:=75) (b:=76) (joinSmall (lo:=9166) (a:=37) (b:=38) sp9166 sp9203) (joinSmall (lo:=9241) (a:=38) (b:=38) sp9241 sp9279))) (joinSmall (lo:=9317) (a:=150) (b:=151) (joinSmall (lo:=9317) (a:=75) (b:=75) (joinSmall (lo:=9317) (a:=37) (b:=38) sp9317 sp9354) (joinSmall (lo:=9392) (a:=37) (b:=38) sp9392 sp9429)) (joinSmall (lo:=9467) (a:=75) (b:=76) (joinSmall (lo:=9467) (a:=37) (b:=38) sp9467 sp9504) (joinSmall (lo:=9542) (a:=38) (b:=38) sp9542 sp9580)))))))) (joinSmall (lo:=9618) (a:=4809) (b:=4809) (joinSmall (lo:=9618) (a:=2404) (b:=2405) (joinSmall (lo:=9618) (a:=1202) (b:=1202) (joinSmall (lo:=9618) (a:=601) (b:=601) (joinSmall (lo:=9618) (a:=300) (b:=301) (joinSmall (lo:=9618) (a:=150) (b:=150) (joinSmall (lo:=9618) (a:=75) (b:=75) (joinSmall (lo:=9618) (a:=37) (b:=38) sp9618 sp9655) (joinSmall (lo:=9693) (a:=37) (b:=38) sp9693 sp9730)) (joinSmall (lo:=9768) (a:=75) (b:=75) (joinSmall (lo:=9768) (a:=37) (b:=38) sp9768 sp9805) (joinSmall (lo:=9843) (a:=37) (b:=38) sp9843 sp9880))) (joinSmall (lo:=9918) (a:=150) (b:=151) (joinSmall (lo:=9918) (a:=75) (b:=75) (joinSmall (lo:=9918) (a:=37) (b:=38) sp9918 sp9955) (joinSmall (lo:=9993) (a:=37) (b:=38) sp9993 sp10030)) (joinSmall (lo:=10068) (a:=75) (b:=76) (joinSmall (lo:=10068) (a:=37) (b:=38) sp10068 sp10105) (joinSmall (lo:=10143) (a:=38) (b:=38) sp10143 sp10181)))) (joinSmall (lo:=10219) (a:=300) (b:=301) (joinSmall (lo:=10219) (a:=150) (b:=150) (joinSmall (lo:=10219) (a:=75) (b:=75) (joinSmall (lo:=10219) (a:=37) (b:=38) sp10219 sp10256) (joinSmall (lo:=10294) (a:=37) (b:=38) sp10294 sp10331)) (joinSmall (lo:=10369) (a:=75) (b:=75) (joinSmall (lo:=10369) (a:=37) (b:=38) sp10369 sp10406) (joinSmall (lo:=10444) (a:=37) (b:=38) sp10444 sp10481))) (joinSmall (lo:=10519) (a:=150) (b:=151) (joinSmall (lo:=10519) (a:=75) (b:=75) (joinSmall (lo:=10519) (a:=37) (b:=38) sp10519 sp10556) (joinSmall (lo:=10594) (a:=37) (b:=38) sp10594 sp10631)) (joinSmall (lo:=10669) (a:=75) (b:=76) (joinSmall (lo:=10669) (a:=37) (b:=38) sp10669 sp10706) (joinSmall (lo:=10744) (a:=38) (b:=38) sp10744 sp10782))))) (joinSmall (lo:=10820) (a:=601) (b:=601) (joinSmall (lo:=10820) (a:=300) (b:=301) (joinSmall (lo:=10820) (a:=150) (b:=150) (joinSmall (lo:=10820) (a:=75) (b:=75) (joinSmall (lo:=10820) (a:=37) (b:=38) sp10820 sp10857) (joinSmall (lo:=10895) (a:=37) (b:=38) sp10895 sp10932)) (joinSmall (lo:=10970) (a:=75) (b:=75) (joinSmall (lo:=10970) (a:=37) (b:=38) sp10970 sp11007) (joinSmall (lo:=11045) (a:=37) (b:=38) sp11045 sp11082))) (joinSmall (lo:=11120) (a:=150) (b:=151) (joinSmall (lo:=11120) (a:=75) (b:=75) (joinSmall (lo:=11120) (a:=37) (b:=38) sp11120 sp11157) (joinSmall (lo:=11195) (a:=37) (b:=38) sp11195 sp11232)) (joinSmall (lo:=11270) (a:=75) (b:=76) (joinSmall (lo:=11270) (a:=37) (b:=38) sp11270 sp11307) (joinSmall (lo:=11345) (a:=38) (b:=38) sp11345 sp11383)))) (joinSmall (lo:=11421) (a:=300) (b:=301) (joinSmall (lo:=11421) (a:=150) (b:=150) (joinSmall (lo:=11421) (a:=75) (b:=75) (joinSmall (lo:=11421) (a:=37) (b:=38) sp11421 sp11458) (joinSmall (lo:=11496) (a:=37) (b:=38) sp11496 sp11533)) (joinSmall (lo:=11571) (a:=75) (b:=75) (joinSmall (lo:=11571) (a:=37) (b:=38) sp11571 sp11608) (joinSmall (lo:=11646) (a:=37) (b:=38) sp11646 sp11683))) (joinSmall (lo:=11721) (a:=150) (b:=151) (joinSmall (lo:=11721) (a:=75) (b:=75) (joinSmall (lo:=11721) (a:=37) (b:=38) sp11721 sp11758) (joinSmall (lo:=11796) (a:=37) (b:=38) sp11796 sp11833)) (joinSmall (lo:=11871) (a:=75) (b:=76) (joinSmall (lo:=11871) (a:=37) (b:=38) sp11871 sp11908) (joinSmall (lo:=11946) (a:=38) (b:=38) sp11946 sp11984)))))) (joinSmall (lo:=12022) (a:=1202) (b:=1203) (joinSmall (lo:=12022) (a:=601) (b:=601) (joinSmall (lo:=12022) (a:=300) (b:=301) (joinSmall (lo:=12022) (a:=150) (b:=150) (joinSmall (lo:=12022) (a:=75) (b:=75) (joinSmall (lo:=12022) (a:=37) (b:=38) sp12022 sp12059) (joinSmall (lo:=12097) (a:=37) (b:=38) sp12097 sp12134)) (joinSmall (lo:=12172) (a:=75) (b:=75) (joinSmall (lo:=12172) (a:=37) (b:=38) sp12172 sp12209) (joinSmall (lo:=12247) (a:=37) (b:=38) sp12247 sp12284))) (joinSmall (lo:=12322) (a:=150) (b:=151) (joinSmall (lo:=12322) (a:=75) (b:=75) (joinSmall (lo:=12322) (a:=37) (b:=38) sp12322 sp12359) (joinSmall (lo:=12397) (a:=37) (b:=38) sp12397 sp12434)) (joinSmall (lo:=12472) (a:=75) (b:=76) (joinSmall (lo:=12472) (a:=37) (b:=38) sp12472 sp12509) (joinSmall (lo:=12547) (a:=38) (b:=38) sp12547 sp12585)))) (joinSmall (lo:=12623) (a:=300) (b:=301) (joinSmall (lo:=12623) (a:=150) (b:=150) (joinSmall (lo:=12623) (a:=75) (b:=75) (joinSmall (lo:=12623) (a:=37) (b:=38) sp12623 sp12660) (joinSmall (lo:=12698) (a:=37) (b:=38) sp12698 sp12735)) (joinSmall (lo:=12773) (a:=75) (b:=75) (joinSmall (lo:=12773) (a:=37) (b:=38) sp12773 sp12810) (joinSmall (lo:=12848) (a:=37) (b:=38) sp12848 sp12885))) (joinSmall (lo:=12923) (a:=150) (b:=151) (joinSmall (lo:=12923) (a:=75) (b:=75) (joinSmall (lo:=12923) (a:=37) (b:=38) sp12923 sp12960) (joinSmall (lo:=12998) (a:=37) (b:=38) sp12998 sp13035)) (joinSmall (lo:=13073) (a:=75) (b:=76) (joinSmall (lo:=13073) (a:=37) (b:=38) sp13073 sp13110) (joinSmall (lo:=13148) (a:=38) (b:=38) sp13148 sp13186))))) (joinSmall (lo:=13224) (a:=601) (b:=602) (joinSmall (lo:=13224) (a:=300) (b:=301) (joinSmall (lo:=13224) (a:=150) (b:=150) (joinSmall (lo:=13224) (a:=75) (b:=75) (joinSmall (lo:=13224) (a:=37) (b:=38) sp13224 sp13261) (joinSmall (lo:=13299) (a:=37) (b:=38) sp13299 sp13336)) (joinSmall (lo:=13374) (a:=75) (b:=75) (joinSmall (lo:=13374) (a:=37) (b:=38) sp13374 sp13411) (joinSmall (lo:=13449) (a:=37) (b:=38) sp13449 sp13486))) (joinSmall (lo:=13524) (a:=150) (b:=151) (joinSmall (lo:=13524) (a:=75) (b:=75) (joinSmall (lo:=13524) (a:=37) (b:=38) sp13524 sp13561) (joinSmall (lo:=13599) (a:=37) (b:=38) sp13599 sp13636)) (joinSmall (lo:=13674) (a:=75) (b:=76) (joinSmall (lo:=13674) (a:=37) (b:=38) sp13674 sp13711) (joinSmall (lo:=13749) (a:=38) (b:=38) sp13749 sp13787)))) (joinSmall (lo:=13825) (a:=301) (b:=301) (joinSmall (lo:=13825) (a:=150) (b:=151) (joinSmall (lo:=13825) (a:=75) (b:=75) (joinSmall (lo:=13825) (a:=37) (b:=38) sp13825 sp13862) (joinSmall (lo:=13900) (a:=37) (b:=38) sp13900 sp13937)) (joinSmall (lo:=13975) (a:=75) (b:=76) (joinSmall (lo:=13975) (a:=37) (b:=38) sp13975 sp14012) (joinSmall (lo:=14050) (a:=38) (b:=38) sp14050 sp14088))) (joinSmall (lo:=14126) (a:=150) (b:=151) (joinSmall (lo:=14126) (a:=75) (b:=75) (joinSmall (lo:=14126) (a:=37) (b:=38) sp14126 sp14163) (joinSmall (lo:=14201) (a:=37) (b:=38) sp14201 sp14238)) (joinSmall (lo:=14276) (a:=75) (b:=76) (joinSmall (lo:=14276) (a:=37) (b:=38) sp14276 sp14313) (joinSmall (lo:=14351) (a:=38) (b:=38) sp14351 sp14389))))))) (joinSmall (lo:=14427) (a:=2404) (b:=2405) (joinSmall (lo:=14427) (a:=1202) (b:=1202) (joinSmall (lo:=14427) (a:=601) (b:=601) (joinSmall (lo:=14427) (a:=300) (b:=301) (joinSmall (lo:=14427) (a:=150) (b:=150) (joinSmall (lo:=14427) (a:=75) (b:=75) (joinSmall (lo:=14427) (a:=37) (b:=38) sp14427 sp14464) (joinSmall (lo:=14502) (a:=37) (b:=38) sp14502 sp14539)) (joinSmall (lo:=14577) (a:=75) (b:=75) (joinSmall (lo:=14577) (a:=37) (b:=38) sp14577 sp14614) (joinSmall (lo:=14652) (a:=37) (b:=38) sp14652 sp14689))) (joinSmall (lo:=14727) (a:=150) (b:=151) (joinSmall (lo:=14727) (a:=75) (b:=75) (joinSmall (lo:=14727) (a:=37) (b:=38) sp14727 sp14764) (joinSmall (lo:=14802) (a:=37) (b:=38) sp14802 sp14839)) (joinSmall (lo:=14877) (a:=75) (b:=76) (joinSmall (lo:=14877) (a:=37) (b:=38) sp14877 sp14914) (joinSmall (lo:=14952) (a:=38) (b:=38) sp14952 sp14990)))) (joinSmall (lo:=15028) (a:=300) (b:=301) (joinSmall (lo:=15028) (a:=150) (b:=150) (joinSmall (lo:=15028) (a:=75) (b:=75) (joinSmall (lo:=15028) (a:=37) (b:=38) sp15028 sp15065) (joinSmall (lo:=15103) (a:=37) (b:=38) sp15103 sp15140)) (joinSmall (lo:=15178) (a:=75) (b:=75) (joinSmall (lo:=15178) (a:=37) (b:=38) sp15178 sp15215) (joinSmall (lo:=15253) (a:=37) (b:=38) sp15253 sp15290))) (joinSmall (lo:=15328) (a:=150) (b:=151) (joinSmall (lo:=15328) (a:=75) (b:=75) (joinSmall (lo:=15328) (a:=37) (b:=38) sp15328 sp15365) (joinSmall (lo:=15403) (a:=37) (b:=38) sp15403 sp15440)) (joinSmall (lo:=15478) (a:=75) (b:=76) (joinSmall (lo:=15478) (a:=37) (b:=38) sp15478 sp15515) (joinSmall (lo:=15553) (a:=38) (b:=38) sp15553 sp15591))))) (joinSmall (lo:=15629) (a:=601) (b:=601) (joinSmall (lo:=15629) (a:=300) (b:=301) (joinSmall (lo:=15629) (a:=150) (b:=150) (joinSmall (lo:=15629) (a:=75) (b:=75) (joinSmall (lo:=15629) (a:=37) (b:=38) sp15629 sp15666) (joinSmall (lo:=15704) (a:=37) (b:=38) sp15704 sp15741)) (joinSmall (lo:=15779) (a:=75) (b:=75) (joinSmall (lo:=15779) (a:=37) (b:=38) sp15779 sp15816) (joinSmall (lo:=15854) (a:=37) (b:=38) sp15854 sp15891))) (joinSmall (lo:=15929) (a:=150) (b:=151) (joinSmall (lo:=15929) (a:=75) (b:=75) (joinSmall (lo:=15929) (a:=37) (b:=38) sp15929 sp15966) (joinSmall (lo:=16004) (a:=37) (b:=38) sp16004 sp16041)) (joinSmall (lo:=16079) (a:=75) (b:=76) (joinSmall (lo:=16079) (a:=37) (b:=38) sp16079 sp16116) (joinSmall (lo:=16154) (a:=38) (b:=38) sp16154 sp16192)))) (joinSmall (lo:=16230) (a:=300) (b:=301) (joinSmall (lo:=16230) (a:=150) (b:=150) (joinSmall (lo:=16230) (a:=75) (b:=75) (joinSmall (lo:=16230) (a:=37) (b:=38) sp16230 sp16267) (joinSmall (lo:=16305) (a:=37) (b:=38) sp16305 sp16342)) (joinSmall (lo:=16380) (a:=75) (b:=75) (joinSmall (lo:=16380) (a:=37) (b:=38) sp16380 sp16417) (joinSmall (lo:=16455) (a:=37) (b:=38) sp16455 sp16492))) (joinSmall (lo:=16530) (a:=150) (b:=151) (joinSmall (lo:=16530) (a:=75) (b:=75) (joinSmall (lo:=16530) (a:=37) (b:=38) sp16530 sp16567) (joinSmall (lo:=16605) (a:=37) (b:=38) sp16605 sp16642)) (joinSmall (lo:=16680) (a:=75) (b:=76) (joinSmall (lo:=16680) (a:=37) (b:=38) sp16680 sp16717) (joinSmall (lo:=16755) (a:=38) (b:=38) sp16755 sp16793)))))) (joinSmall (lo:=16831) (a:=1202) (b:=1203) (joinSmall (lo:=16831) (a:=601) (b:=601) (joinSmall (lo:=16831) (a:=300) (b:=301) (joinSmall (lo:=16831) (a:=150) (b:=150) (joinSmall (lo:=16831) (a:=75) (b:=75) (joinSmall (lo:=16831) (a:=37) (b:=38) sp16831 sp16868) (joinSmall (lo:=16906) (a:=37) (b:=38) sp16906 sp16943)) (joinSmall (lo:=16981) (a:=75) (b:=75) (joinSmall (lo:=16981) (a:=37) (b:=38) sp16981 sp17018) (joinSmall (lo:=17056) (a:=37) (b:=38) sp17056 sp17093))) (joinSmall (lo:=17131) (a:=150) (b:=151) (joinSmall (lo:=17131) (a:=75) (b:=75) (joinSmall (lo:=17131) (a:=37) (b:=38) sp17131 sp17168) (joinSmall (lo:=17206) (a:=37) (b:=38) sp17206 sp17243)) (joinSmall (lo:=17281) (a:=75) (b:=76) (joinSmall (lo:=17281) (a:=37) (b:=38) sp17281 sp17318) (joinSmall (lo:=17356) (a:=38) (b:=38) sp17356 sp17394)))) (joinSmall (lo:=17432) (a:=300) (b:=301) (joinSmall (lo:=17432) (a:=150) (b:=150) (joinSmall (lo:=17432) (a:=75) (b:=75) (joinSmall (lo:=17432) (a:=37) (b:=38) sp17432 sp17469) (joinSmall (lo:=17507) (a:=37) (b:=38) sp17507 sp17544)) (joinSmall (lo:=17582) (a:=75) (b:=75) (joinSmall (lo:=17582) (a:=37) (b:=38) sp17582 sp17619) (joinSmall (lo:=17657) (a:=37) (b:=38) sp17657 sp17694))) (joinSmall (lo:=17732) (a:=150) (b:=151) (joinSmall (lo:=17732) (a:=75) (b:=75) (joinSmall (lo:=17732) (a:=37) (b:=38) sp17732 sp17769) (joinSmall (lo:=17807) (a:=37) (b:=38) sp17807 sp17844)) (joinSmall (lo:=17882) (a:=75) (b:=76) (joinSmall (lo:=17882) (a:=37) (b:=38) sp17882 sp17919) (joinSmall (lo:=17957) (a:=38) (b:=38) sp17957 sp17995))))) (joinSmall (lo:=18033) (a:=601) (b:=602) (joinSmall (lo:=18033) (a:=300) (b:=301) (joinSmall (lo:=18033) (a:=150) (b:=150) (joinSmall (lo:=18033) (a:=75) (b:=75) (joinSmall (lo:=18033) (a:=37) (b:=38) sp18033 sp18070) (joinSmall (lo:=18108) (a:=37) (b:=38) sp18108 sp18145)) (joinSmall (lo:=18183) (a:=75) (b:=75) (joinSmall (lo:=18183) (a:=37) (b:=38) sp18183 sp18220) (joinSmall (lo:=18258) (a:=37) (b:=38) sp18258 sp18295))) (joinSmall (lo:=18333) (a:=150) (b:=151) (joinSmall (lo:=18333) (a:=75) (b:=75) (joinSmall (lo:=18333) (a:=37) (b:=38) sp18333 sp18370) (joinSmall (lo:=18408) (a:=37) (b:=38) sp18408 sp18445)) (joinSmall (lo:=18483) (a:=75) (b:=76) (joinSmall (lo:=18483) (a:=37) (b:=38) sp18483 sp18520) (joinSmall (lo:=18558) (a:=38) (b:=38) sp18558 sp18596)))) (joinSmall (lo:=18634) (a:=301) (b:=301) (joinSmall (lo:=18634) (a:=150) (b:=151) (joinSmall (lo:=18634) (a:=75) (b:=75) (joinSmall (lo:=18634) (a:=37) (b:=38) sp18634 sp18671) (joinSmall (lo:=18709) (a:=37) (b:=38) sp18709 sp18746)) (joinSmall (lo:=18784) (a:=75) (b:=76) (joinSmall (lo:=18784) (a:=37) (b:=38) sp18784 sp18821) (joinSmall (lo:=18859) (a:=38) (b:=38) sp18859 sp18897))) (joinSmall (lo:=18935) (a:=150) (b:=151) (joinSmall (lo:=18935) (a:=75) (b:=75) (joinSmall (lo:=18935) (a:=37) (b:=38) sp18935 sp18972) (joinSmall (lo:=19010) (a:=37) (b:=38) sp19010 sp19047)) (joinSmall (lo:=19085) (a:=75) (b:=76) (joinSmall (lo:=19085) (a:=37) (b:=38) sp19085 sp19122) (joinSmall (lo:=19160) (a:=38) (b:=38) sp19160 sp19198)))))))))
  have good : (List.range 19236).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 370000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 19235 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 19235 := by
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


private def packet (i : ℕ) : ℕ := (if i < 94 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 0))) else (if i < 8 then (if i < 6 then 0 else (if i < 7 then 0 else 0)) else (if i < 9 then 0 else (if i < 10 then 0 else 0)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0 else (if i < 13 then 0 else 0)) else (if i < 15 then 0 else (if i < 16 then 0 else 0))) else (if i < 20 then (if i < 18 then 0 else (if i < 19 then 0 else 0)) else (if i < 21 then 0 else (if i < 22 then 0 else 0))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then 0 else (if i < 25 then 0 else 0)) else (if i < 27 then 0 else (if i < 28 then 0 else 0))) else (if i < 32 then (if i < 30 then 0 else (if i < 31 then 0 else 0)) else (if i < 33 then 0 else (if i < 34 then 0 else 0)))) else (if i < 41 then (if i < 38 then (if i < 36 then 0 else (if i < 37 then 0 else 0)) else (if i < 39 then 0 else (if i < 40 then 0 else 0))) else (if i < 44 then (if i < 42 then 0 else (if i < 43 then 0 else 0)) else (if i < 45 then 0 else (if i < 46 then 0 else 0)))))) else (if i < 70 then (if i < 58 then (if i < 52 then (if i < 49 then (if i < 48 then 0 else 0) else (if i < 50 then 0 else (if i < 51 then 0 else 0))) else (if i < 55 then (if i < 53 then 0 else (if i < 54 then 0 else 0)) else (if i < 56 then 0 else (if i < 57 then 0 else 0)))) else (if i < 64 then (if i < 61 then (if i < 59 then 0 else (if i < 60 then 0 else 0)) else (if i < 62 then 0 else (if i < 63 then 0 else 0))) else (if i < 67 then (if i < 65 then 0 else (if i < 66 then 0 else 0)) else (if i < 68 then 0 else (if i < 69 then 0 else 0))))) else (if i < 82 then (if i < 76 then (if i < 73 then (if i < 71 then 0 else (if i < 72 then 0 else 0)) else (if i < 74 then 0 else (if i < 75 then 0 else 0))) else (if i < 79 then (if i < 77 then 0 else (if i < 78 then 0 else 0)) else (if i < 80 then 0 else (if i < 81 then 0 else 0)))) else (if i < 88 then (if i < 85 then (if i < 83 then 0 else (if i < 84 then 0 else 0)) else (if i < 86 then 0 else (if i < 87 then 0 else 0))) else (if i < 91 then (if i < 89 then 0 else (if i < 90 then 0 else 0)) else (if i < 92 then 0 else (if i < 93 then 0 else 0))))))) else (if i < 141 then (if i < 117 then (if i < 105 then (if i < 99 then (if i < 96 then (if i < 95 then 0 else 0) else (if i < 97 then 0 else (if i < 98 then 0 else 0))) else (if i < 102 then (if i < 100 then 0 else (if i < 101 then 0 else 0)) else (if i < 103 then 0 else (if i < 104 then 0 else 0)))) else (if i < 111 then (if i < 108 then (if i < 106 then 0 else (if i < 107 then 0 else 0)) else (if i < 109 then 0 else (if i < 110 then 0 else 0))) else (if i < 114 then (if i < 112 then 0 else (if i < 113 then 0 else 0)) else (if i < 115 then 0 else (if i < 116 then 0 else 0))))) else (if i < 129 then (if i < 123 then (if i < 120 then (if i < 118 then 0 else (if i < 119 then 0 else 0)) else (if i < 121 then 0 else (if i < 122 then 0 else 0))) else (if i < 126 then (if i < 124 then 0 else (if i < 125 then 0 else 0)) else (if i < 127 then 0 else (if i < 128 then 0 else 0)))) else (if i < 135 then (if i < 132 then (if i < 130 then 0 else (if i < 131 then 0 else 0)) else (if i < 133 then 0 else (if i < 134 then 0 else 0))) else (if i < 138 then (if i < 136 then 0 else (if i < 137 then 0 else 0)) else (if i < 139 then 0 else (if i < 140 then 0 else 0)))))) else (if i < 165 then (if i < 153 then (if i < 147 then (if i < 144 then (if i < 142 then 0 else (if i < 143 then 0 else 0)) else (if i < 145 then 0 else (if i < 146 then 0 else 0))) else (if i < 150 then (if i < 148 then 0 else (if i < 149 then 0 else 0)) else (if i < 151 then 0 else (if i < 152 then 0 else 0)))) else (if i < 159 then (if i < 156 then (if i < 154 then 0 else (if i < 155 then 0 else 0)) else (if i < 157 then 0 else (if i < 158 then 0 else 0))) else (if i < 162 then (if i < 160 then 0 else (if i < 161 then 0 else 0)) else (if i < 163 then 0 else (if i < 164 then 0 else 0))))) else (if i < 177 then (if i < 171 then (if i < 168 then (if i < 166 then 0 else (if i < 167 then 0 else 0)) else (if i < 169 then 0 else (if i < 170 then 0 else 0))) else (if i < 174 then (if i < 172 then 0 else (if i < 173 then 0 else 0)) else (if i < 175 then 0 else (if i < 176 then 0x11bd0e22c814b09a84862110f046cc30414b88d83c216f08882b80b4000011bcabe2dd154c9e44862180f286c630315088fc3c617c08e02e40ba000011bc4852eb95c4a324b722c8fe072e33816889c84301a709c836c0e0000011bbe5c2e415c8a344b92280fa070831715b892c3e219309683400d8000011bb8562cf14f89a84742078eb46982f314f88fc3cc18c094032c0c0000011bb2422d2951c9bc48220c0efc6c031115809283ee19509883480de000011bac2e2d0151c9c047820d8ec46ae2fe15309203da18509303100b4000011ba6092e11598a024a32228f8c6ee30c15809403ec19109102f40c4000011b9fd32ee15e4a3a4b622d8fd471432815b89603e619c09d834c0d6000011b99bd2e015789fa49421b0f5c6de31515889603e618a09583380be000011b93ad2d295149da49821a8f306dc30c15389143c417b09403040ac000011b8d632ee15bca064a72280fcc70831b15c89783ee19a09d83580ca000011b87202f01600a164ab21f0f9071031c15d09343e0189095832c0ca000011b812f2c514dc9b247820b0eac6a42ef14e88e43b017709002f00c0000011b7b0c2df15589f64932170f486f031415889383d8183091032c0b2000011b74d22e995d0a1e4a721e0f746f631e15e09783e618609583100cc000011b6eb82da15509fc4922160f2c6d430f15309543f2195098032c0ca000011b68a52db152c9da4872110f386ec31315809143c819009a03540ce000011b62592f81638a604c1232102473433316789883ee18b098034c0d6000011b5c802bb144896e45c1fd8e606862f215189203d018409683300d4000011b56692dd15789ec48e2190f386ce31815a89503e018d09a03480c2000011b50532d515289da48a2120f046be30815408e43b418508f02f40b8000011b4a102ef1608a3c4c122e0fd471c32715e89683fa19d0a003780e2000011b44362bf94949964632038ea468a2e314688d83ca18609502f00c8000011b3e492cc14c09904672088ef46a22f114b89143cc18e096832c0bc000011b38332dc15889fc49e21e0f606c631015409243cc18c09403180ca000011b32242d795249ca48620d8f306c62f715009143b017908d82fc0c0000011b2c072df1570a084a321d0f806fe31b15d09784021a009803400e6000011b25f92d495209d648220e8f086ba30b15789643f819309d83340de000011b1fd12dd95289c047e20c0ee46be2fe14988cc3a817b08d03040c0000011b19b12dc15749e04952158f1c6d6304155890c3c017b08c03140c2000011b139c2dd15649ee49021a0f606e4315158091c3ca18609382e80ba000011b0d742e69594a0c4ae2258fdc72232c15f89703f219409a83340e6000011b07692d715449f04942170f406fc31815e094c3ce18e09603340e2000011b016a2d014e49aa47820e0f146d631a157090c3be17a091031c0be000011afb452eb15e4a424bb22a8fbc714329163897840019609683140ca000011af4ff2ef95c8a024a121b8f7c70a31115589083c217a08e82e80b8000011aeedf2e5159ca084a72258fa871a32316109883fe19009d03500d8000011ae8ed2c994f89b44822100ee86aa2f814688ac3a817d08d83200c4000011ae2ea2d795249d048a2170f386de31315f099c3f819109783340e4000011adcc72dc95449e648d20f8ee06b42f314a88c439c16c08c02d00be000011ad6b62d215049c647e20f8ef06aa2f014508b43a016e08202ac0a2000011ad0aa2d215049c247b20d8f0c6c230814e08fc3c418208e02d40bc000011aca912dd15649ee4a221c0f706f230d15b096c3f419f09c03440d2000011ac46f2e395809fc49921b8f4c6d62f8152890c3ce18509303140c6000011abe682d995689e448f2178f206dc30b15109343be18809583300d2000011ab8472e295c4a324a821b0f306e431615c09483f419309403140d6000011ab2282df1574a0049a21b0f706fa31d15889203cc17b09782f80c2000011aabdf2f115c8a124a221d8f7070432315d89403e219909802fc0c2000011aa5bc2e315c8a2e4b52278fb871a32716509803f218e09203040ae000011a9fe12c1145c94e4441f70e2c6582d213d083c37216c085829c0a4000011a99e22cd95209ce4862130f386d630215288e83ae17808e82fc0c0000011a93cb2dd15649f64992190f3c6ce30a15789543e219209883300c4000011a8daa2e6957c9fc49e21d8f546f631a15d89743f619b09883300da000011a878a2e095849ee4902168f406dc314158892c3da18d09803280d6000011a813b2f115eca284bb22c8fe872a33216889ac3fc19909c83200c6000011a7b0a2e795809f24972200f886e631715b89343de18e09603000b0000011a74d32e815bca1e4b32270fb471c31b15c09603fa19e09d83700ea000011a6ea82e495d8a1e4aa2218f846f6316158894c3e8194095830c0be000011a68872e295809f049821d0f1c6d630015108f83b818a09402fc0c2000011a62442ed9630a404c12308ff072231f15b096c3ec191096830c0d0000011a5c352d695409d84932160f106ce2fd15009183b618209103080c2000011a560a2e595909fc4a52230f8470231415989543e818f09c034c0dc000011a4fe52e695cca1a4a32228fb46f431415989603ec18d093032c0d0000 else 0x11d56ab2e915e8a344b02220f646fc31f16789703e618108f831c0b8000011d50942dc95509f44932150f186ca2fa15009043c0186096032c0d6000011d4a962cb14c89ac47420a0ea069a2ef15089243aa17408982f40ba000011d446c2e295c4a1e4b622b8fcc71e32c165897c4061ac0a103500d4000011d3e4e2e11580a024a221b0f546ec31d15b09843ea18d09682fc0bc000011d38612c594b09a246e2088ee46b230615309103b818009302ec0ba000011d32312e995b0a1c4aa2228f846fe31e15989683f419409c835c0dc000011d2c362cc95009b84832110f246d030a15188ec3aa17908b83080b8000011d26542c2948096a4501f28e206582d613d085838016d08202ac0ae000011d20392e0158c9fc49521c8f3c6ea32315809383de18e09883100d2000011d1a072ea95b4a224ac2260f94708323162898c3e819309703280d6000011d13bc2fb965ca504c72320ff071432715b094c3d218d09c03540ca000011d0dbd2d315249e648b2148f206d031415509543e818a08b82dc0b2000011d079c2e415709ec4a22248f9c70a32015e094c3e819d09c03480cc000011d01bc2c0949498045e1ff8e906862e113d889839017808e02e80cc000011cfb9f2dd95649de48020e8ec46902f714708c439416708682ac0b2000011cf5922d4952c9c248f21c0f646f2326165098c4001a009b035c0d2000011cef602e71590a024952168f286e430c15d898840819f09583100b4000011ce9492e0958ca0e4a12208fa070631415a89543f418c094033c0c8000011ce3432d195149b44832110f1c6d430215589243d217f08e03240be000011cdd172eb15aca124ad2210f746f431f15a89243d618b09402d00b0000011cd7052de95589ee48e2160f306d030415609183d2186092832c0d4000011cd0df2e495b0a1849d21e0f686e42fb14e08e839a17108602bc09e000011ccad02d5151c9e64932208f7c6fa32015c09403de18a09383040ca000011cc4b62dd95549fe4a72208f606fa31715689403ea18f09683100ca000011cbe9f2d695389d448b2118f046b42fd14c88e83d218509082f00ba000011cb8632ef15e8a2a4b22250f686f831315a89603d618e09503280be000011cb2432dc157c9ee48f2168f3c6ee32116189804041a109b03380c6000011cac472cf14fc9c04812150f2c6c830014c88b83aa17708c02e80b6000011ca6432d095409e248c20f0f146cc307152091c3d018708e02fc0ba000011ca04d2c5149898645a1fc0e7c6982ea14488883a417808c82dc0b2000011c9a3c2da955c9e249221b0f686e4309155891c3d418509183040ca000011c94112e795e4a324b62238fd071632116009343d819009083180c0000011c8dfa2d895449f44942138f2c6d830115008f03c017d08f03000ce000011c87e12db153c9c44922140ee06a430014c08f43aa16e08402c00ac000011c818e2f8963ca564d0236903875634317389e841c1a50a103480e0000011c7b7b2db15649e44952210f746f4321162895c3f2198098032c0da000011c753c2eb15dca1c4a921e8f9c6f430d15208e43b417f08d82d80b8000011c6f1e2e29590a0049d2218fcc71631e15b890c3d818808d02ec0c2000011c692b2c814d09c24792060ec06862f514b88ec3c617c09102f40c8000011c630e2de15509e44852128f346dc31a15b89603f419a09a03480d0000011c5d0f2ce14fc9c24882118f206a830714d09183c418809583180d4000011c56e02e515809fe4a22260fa070232115e096c3de18708f82d80a6000011c50c82d895689e448c2160f446d830915708e43ca18909082c00b8000011c4ad12c994ac9a84762088ec86aa2fb15088e43bc18509003280ca000011c44ab2e29570a024a42208fac71232115e897c3de17f09102f40c4000011c3eb82c514c49b447720e8ed86a62f615108dc3b218208f82c80bc000011c38a12d795009e848e20f0f2c6e231b15689243ca18809402e00ac000011c32912d8157c9f049521c0f346be30615088f83c817b08d82e80ba000011c2c762de958c9fc4932188f686f431515489003cc17f08c82f80b0000011c26682d415189be4842158f146e631d15909783e019109b83340c4000011c205b2db954c9ee49f21e0f606d431415689043d218809183040bc000011c1a672ce94ec9b447420a0ee46cc30b15409303d218b09683280ca000011c14742c694c89a247d20e8ee86b02fc15108ec3b617a089830c0b8000011c0e212f99610a464b92318ff472e33616789a83e818909483200b8000011c07f12e195649e649a21a0f646ca30514f88f83d418508f02dc0c2000011c01ad2e915c4a1649a2218f986fc31f15c09583d817709103000ca000011bfb952de95509e848c2148f0c6d831015488f03bc18609083100d0000011bf55a2e895d8a1a4b02288f9871832515c09603dc18d09203000dc000011bef642ce94cc9ac4752100f286e831015809543de19209383140c8000011be9252ee15dca404b822d0fd872433616889bc4181a80a703640d8000011be2f72e49578a084a22198f386e031015509103ba18809002d40be000011bdd032c594f09bc47620c0ec869a2e113e088c38a16b08502a00a4000011bd6d22e31590a0449e21d8f5c6fc318157096840019b09a83580d8000)))) else (if i < 183 then (if i < 180 then (if i < 178 then 0x11edd682e695b0a1e4af2260fac70231915609183d618c09683100c8000011ed73f2e295889f449421c0f446fe31615c09343dc19009503340f6000011ed11d2e11568a0a4a12218f7870432716209643f018b09583240ce000011ecaed2ea95b0a1a4a72180f186c22fe14f09103d618908d82f00b2000011ec4fb2c894c898c45f2028e7c6762dd14008983a217008702c40b0000011ebebb2e595989fc4a22210f646d230915289403ba17f08e02e00ca000011eb8a02dc953c9dc48620f8f406da30915289383d619309302fc0c2000011eb2892db15749f049d21a8f7870031e15f89683f218a09383480c8000011eac962d194f49a64742028ea86a62e914808bc3b017c08f03140ba000011ea64a2f09618a404b32298fb070031c15a09403e219009703040ba000011ea0472d394ec9ae4702010ea46942ec14508b43a617108c02d80b8000011e99ed2fd164ca6e4cd22f901073433516909b03fe1a409d03600de000011e93e82d615449da4962180f4c6e830915108ec3a417308a82cc0b6000011e8ddf2d494e89ae47420e8f086ba2f814e08f83b217e09003080ba000011e87b32e415789f248e2150f286e431115189243da18d09303280d0000011e818d2e395909fa4952190efc6b42f014a08e43ae17809403340d4000011e7b6c2e39598a0449821b0f446f8316155092c3de18b09403040b4000011e75722ca94c499c47e2108efc6ce30f15889383ca18e09883200ce000011e6f1c2fa961ca404ba2258fc472832c16489a43fc19b09783540de000011e69092db15349d247e20e8eec6ba2f114c08f43d618009003080c8000011e630f2ce14e49b247d2100ee46c830b15208fc3be18309183140ca000011e5ce22ea95b0a1249e21b8f406e630c15209043c018409082d00aa000011e56cb2de95609f249521d0f8c70031a156891c3ce18809483040ba000011e50b82da95389ce4862108f006ae2eb14808f039e17a08f83000d2000011e4a8a2e415b0a184b42258fa071232116189c84141a509983400c2000011e445b2e51578a0849e2180f0c6ca2fd15109103c018309102fc0be000011e3e492d915349de49c21e8f846fa31c15c89503e019609903080b6000011e38002f495d4a1e4ab21d8f5c6e831b15b89683de18008e83040ca000011e31db2e395a4a364ad2240f806f831a15b094c3d418609102f00be000011e2bc82dc9574a0048f2168f4c6e230c15609103bc18909382ec0b4000011e25a92df154c9f44922170f606d62f9150891c3ba17409003000c2000011e1f842de954c9de4902140f246c630515188fc3be17f09082e00c2000011e19772d595409e24902170f106d230015008f03b618408f03080d0000011e13502df15aca0c49b2180f386bc2f714488a83ac17908c02e80cc000011e0d492d295049be4832158f286dc30e15009103c618a09483240ca000011e07182e315c8a0c4a62238f806fe31a15e09703ec19709583180ca000011e01252ca14b89a646a2088ed06a62fb14c88c43ac17d08b82fc0c8000011dfb2a2ce14e49c44912168f246d630f158092c3ce18309383100c6000011df5262d1950c9d448220f0eec6d030215108f43ae17c08b82d40c8000011def082e195689f64a321c8f7070031715b09303d618d09082f40bc000011de8d72e915cca224b22280f8c71231a15d89583e819609a03500ca000011de29d2eb95c8a1c4ac22a0fa470632216489783e419109582f80b6000011ddc8b2d895209b247520c0ef46a82ec14408c4380160083829c0ba000011dd6812cf94c499e46e2018e946902e7140889039616a08882e00be000011dd0812d395009b647720b8edc6c230615309343ca18609383100d4000011dca772cd94ec9c44832138eec6c230115088f03c617d09183180be000011dc4362f1961ca3a4bc22c0fc871c31915909583e218a09583080d2000011dbe362d9153c9c64782090ee06a42f314708dc3ae17208c03000cc000011db8052e1156ca0049921d8f386c230215789283d018308c83040c6000011db1ed2df95b8a084aa2298fcc71a32e16889bc40a1a409f83480c4000011dabeb2d315149bc4822108ee869e30215088f83b217c08e02f80be000011da5d62d9153c9da49221c8f9871032916809b842e1ab09d83440de000011d9fd02d69564a0049e21e0f686d831a15a094c3e419109283300ce000011d99b12dd15449ec4892130f346e230815209083b618008f83040aa000011d936a2f095e8a264a421d8f8c70a32816409ac40c1a40a2036c0d8000011d8d652cd94ac9a047220f0f106ca31815989483d418909482f00b4000011d876a2cf94ec9ba4872118f006b22f214a88c03a017608c02dc0b8000011d81482de95709ec49921e0f4c6f8317154091c3c217f09283340d4000011d7b082ef15d0a104a021e8f906e02fe15209383e018809103180ca000011d751a2c714bc9a44792050e846862f114c08dc3ae17e08e82ec0be000011d6f0a2d315209e64862160f1c6cc2f414d88ec3ae17d08f02e80b8000011d69062cf14f89c24792130f086dc30d15489183b817609102f40be000011d62e02dc95289be47c2160ef86ac30215589383e217f09783280c8000011d5ce32cf94f89b44762060ec46902e4144889438a16d08502b80b0000 else (if i < 179 then 0x12063692bd147c98846a2040ec06a22f414c08dc3b017408f03040cc00001205d5f2d295389ca47e20f8f186e031015109203d018309383080b0000012057682d114dc9a047a2070ec06962f414d88e03c418109003240ba000012051402dc95689f04992168f506d02fe14f09103c418809a03300d400001204b132e295709e849a2220f706ea31315489283da17e08f031c0ca0000120450f2d694f89ca48c2190f606e231115189243e2184093033c0d600001203ee22e015689e648c2138f386da31415a09483c218508d82ec0d2000012038e92d0151c9da4932178f346d0313156095c3e618809403080cc000012032bd2e995bca0c4a221f8f9c70c31915e89683e418a096031c0c400001202c9f2e0959ca1a4a92218f786fa31315b097040619d09683240c40000120267a2e395b0a0c4a021f8f606f231415f09383e419709c03280c6000012020982bb947896c44c1f18e1864a2cc13a086036c15608002940a800001201a622e995d0a284b32278f906ee31315d09443f218f09503240c80000120143d2e7958ca044a12220f9c70c31f15d89683e418c09303340d600001200e402cd95249e048e21a0f386d6313153890c3ae17208b82d40c4000012008292e215949f248d2180f306c62fb14988d03b218308c02d40b6000012002272cf94d09ba47720b0ed86b02f314d88f83c417e09103280c8000011ffc062da15389e24932170f1c6b8304156894c3d018809403380d6000011ff5f42d415509e648a2180f386dc30315589283e0186097033c0d6000011feffb2ce14fc9ba47f20e8f106da30614f09143c417b09083200ba000011fe9f92d295289cc4912150f246d230f156893c3d418a09002fc0b2000011fe3f02d715109d44832148f58704327163099c3f418b09503040be000011fddad2ee95c0a004a321e8f506e2303154091c3ca18109282fc0bc000011fd7892dd15689f449221b0f546f031515589083c017e09203100ba000011fd1642dc95609f449821e0fa06fc32115f89703ea18b098832c0e6000011fcb262ee95d8a084a72280fc870831e15d89643e418c09503180de000011fc5072e5958ca0249e21c8f386da31415b89403ea19109402fc0c4000011fbef52d195189c44832168efc6c02fb14f89103c617f09183000c0000011fb8d72df9588a0e4a521f0f9870631e15f89703f019809403080ba000011fb2c32d6954c9f449d21b0f486e430f15609403d218809383080d0000011facce2d015189c84822130f0c6d431415909383d2188091030c0cc000011fa6932e7958ca0849421a8f3c6dc31e160095c3e418b09703300c8000011fa0762d9155c9de4882130f306c62fb14f88f43aa17108f03040c4000011f9a6d2d195389cc47e2120f306ce30614f88e83b017f09303180ca000011f942a2f21618a4e4c022b0fb070a32c16609703f418b09382ec0bc000011f8e0a2e29590a004aa2200f946ea31c159094c3d618d09803540d8000011f88062d895889f449a21d0f486ee31d15c095c3f018c09403240b8000011f820c2d014f09aa46f2098eb46982ea14588a839817808702dc0b4000011f7c0d2d4951c9be47a20d8f1469e30414f09143bc18b09482ec0ce000011f75fe2d495309e649521d8f6c6ee31515a092c3d2183096030c0d4000011f6fef2d014dc9b04792100edc6be30015488f83ce17d08c02dc0aa000011f6a022c194b09a44712070eb46922f415008ec3b418309403500de000011f63ed2d415189c84842168f386c230115009183be18008d02e80ba000011f5db32ef15d4a224a12270fcc71e32115f89803f819f09e83580c6000011f57a22d615349d44892140f406ce30a153891c3c418109483300d0000011f51852e195609d848e2170f486d830d15409203c617708982e80c0000011f4b602e41594a044922140f346c42fa152890c3ba17008c03040ce000011f455f2cf14cc9c247e2100ed06ba2f814a88f43c218809503380c8000011f3f5d2d315209e24932150f286d230615809643dc19409a83000c8000011f394e2d795209d448f20d0f006ac2ff15309103c618a096832c0d2000011f331d2e8157c9f44a021f8f406ea31315a89443ec18a09383080bc000011f2d2d2c614a89a446f20d8edc6b42f814988c83ae16e085029c0aa000011f270a2e0155ca0e49c2198f5c6da2fa14a08bc3a216f08903040be000011f20e82e315d4a144a52258f846f4314158093c3c4183094030c0ca000011f1ac12dd958c9d448c2130f386e230815689083c018f090031c0d2000011f14a02d695089ca47f20e8ef86aa2fe15008fc3a417308982f40b0000011f0e8b2d114dc9b84772088ed06ac2f614988bc3aa17c08b02dc0b2000011f086d2e615809ea4992200f546e631315989403d819709b834c0e4000011f02542db15109bc4852108edc6aa2f814c08e43b817a08a02b80a2000011efc452d7956ca0449421f0f746e831315889343d218108b02d40b0000011ef6272e215b8a1c4a72230f947223291630998404195093032c0d6000011ef00a2dc156ca0449c2208f746f231015d09503e818209302f40ac000011ee9e42e095809f449921a8f4c6da30c15a89383be18008a82e00ae000011ee39b2ef9604a404c022f0fe073633616d09a040819d0a183580ce000 else 0x121e9d02e015609e249821a8f506f0316159896c40019f09b03440ce0000121e3a82e695b4a004a82250fac6f831615c09283d618509a03480c80000121dd8c2db15489ca4842130ef86b42f314888e03b617f08c03140bc0000121d7632e215a4a164ae22a8fac70a31915d098c40219809c03000c40000121d12e2ec15dca3e4b22238f8c6fc30c15189083c417708d02d80be0000121cb082e715c8a0e4a92248f846f031415909503f019a09683280c80000121c4e52e295709fa4972180f506d630915989443e819809703280c80000121bedb2da15449c44852108f186ce30214e88f03b217008a02dc0b60000121b8be2de15709f448d2120ef06c230014d08dc3b218009203100cc0000121b2ba2d815409e648c2168f106bc30215308fc3d218109183040c80000121acbc2ce94c099847b2110f006ae2f214808d43a616708202c00b00000121a69f2da95409f64a022e8fec72633116589843f218c094032c0d40000121a0752e195a4a0449621d8f486e631215a094c3dc18a09503240c600001219a592dd95a09f048b21a8f186ce2fe15209143ce17c08e03040c6000012194632cb14d89a44732098ec46a42e914d08fc3bc18208f02f00b800001218e4a2d595209c648020d0efc6ba31215588f43ba17a09002d00b60000121884e2d194e09b84762098eb069e2ee14b88d83c417f08b83000ac000012182432d615389ca4842130f086cc30615288ec3b016c08c82d40b600001217c332d695209ca48c2108f186d230c15208fc3b017d09003000b4000012176222d715289c848720b8f146c4304153894c3f619009983300d200001216ff92e195649f44982188ee86b42f014508d43a017508b02b80b8000012169f12d594f89bc48320c8ee469c2f814588ac38416a08982b40b6000012163e62d415109be48520d0ef86a42f114708e43c018409082e80b800001215dda2d415249e049c21b8f1c6c62fc15489303ce182097032c0c0000012157942f015f4a224af2250fac71832816009443ca17e08d02c40bc000012151742e3158ca0a49b21a0f846fe31b15889403d818909082d40a200001214b4c2e595bca0449a21b8f246c830515408fc3bc17f09083000b4000012145132eb95b0a044992220f7471232a16209543f419209b03600d200001213f222c414909904672038e8869a2e914708e43a617d08d82f40c00000121391d2d115249c647c2120f406d630815009083ac18008b83100be0000121330b2db154c9d248f2170f486e630d15d095c3e218c09602f40b200001212cf82d9154c9ee4942188f606f831b15a89103be18f09303400e0000012126d52df954c9d64892168f246d430315909483fa19b09a833c0c6000012120b02e195789e84952148f1c6d831215e096c3f819c09482f80c200001211a972d995589ec48a2148f206c630114f89083c617f094031c0c2000012114732dc15289ba48320c0edc6b830214e09043ac17109283040be00001210e372f195f8a4a4c12290f9471032a15e89783fc19709d83500d80000121084d2c694649664622058e9c6982e814588ac39817008802fc0c2000012102442d7952c9f44952190f3c6f031615509243d418708f83000c20000120fc412d795889e849421b0f606f030b15709143d6187092831c0d80000120f62d2d495689e64922198f506d630b14f891c3ca18808d83200cc0000120f00b2d995309ee49521c0f546ea30915209383ea193099832c0c60000120e9bc2f09608a344b222d8fd472832616289603d618909203000ca0000120e3912e495b8a164a021d8f6c6e431c15d89583c8188092031c0d80000120dd652ea15b4a224a52258f846f2314159092c3d8182093034c0c20000120d72d2ec95f0a2a4b12250fac6fe31a15e89803f619309c036c0e60000120d1192de95689ea48f21a8f406da30915489203c618509283200c20000120cae92e895c4a0c4b12258f9471632c159892c3d218d09303140ce0000120c4bd2e315909f84902198f586ea308155892c3de19409783380c20000120bec32d395109da4822128f346d630715589243e617d097033c0ba0000120b89d2dd155c9dc48e2108f086c22fa14e890c3d218309303240c40000120b2732e415689f049821b0f2c6ce30e15609483dc18108c03080b80000120ac6f2d595149d04832138ed86b62fd15288d83a816908582c40bc0000120a64e2de954c9ec4a72228f846fe31916109583ee18b09703340bc0000120a0592c394849824682068e8c68e2e314408a039416a08402d00ae00001209a3f2db1558a044a221f8f646e231b15d89503e618b09603100c0000012093ec2fb964ca5c4c5234902475434216a09c440819809583200dc00001208e032c814dc9a24712030e9068e2e914188b43a616508b02f40be000012087d42e715949fe49421a0f506dc31315d093c3d218a09683240cc000012081b72dd15649f249b21b0f5c6ec31b15e893c3ec19609883240c600001207ba82d6151c9c248a2158f4c6f431215689783e218c09683100bc0000120758a2de154c9e44852140f046e631415889603d618d09a03540cc00001206f7d2dd9584a0449e2200f546fa31915f094c3dc18b098032c0c20000120693f2f09600a424bd22a8ff071c33016109743f619309c032c0c8000)) else (if i < 181 then 0x123700d2d415189d249021d0f486f431c158091c3d017f092033c0ca000012369c52f7961ca3c4b62240f9071232116189743f018d08c83040be000012363b52db15609ea48a2170f486e430c15689503e019109803380da00001235dbd2cc94c099446b2080eb06a42f814b88c03a817308882f00ae000012357ca2cc15009d24892160f1c6be2f414f08e43bc17d08b82d80b0000012351a82df154c9e648b2168f686f8307156094c3d4189090830c0d200001234ba52cd94e49a84752038e9c6942e614788e83b417808d02e80ba0000123458f2d915689d848b2188f546f232115c890c3b417e08f83240cc00001233f4f2f215fca2a4ad2230f8c70632315f89783ea18e09703340d2000012339272dc15509ea49d2200fa070e321161895c3d617908f83240b80000123333c2c794bc9824591fc0e586662e413d088838c16e08f831c0d600001232d092e51578a084962168f406d830d15389183be18108f02e80c2000012327172cc14e09b24712048ea869c2f514a08d43b417908982e00bc000012320f12e495889f849b2218f9470231815b894c3ea18f09583300ce00001231ae92ce94f49b44822118ee46c22fb14b08d83c017c090030c0b8000012314c22e495709f84912190f346d030315108d83b417708a02d40aa00001230ec92c794b49aa47c20a8edc6c22fe14c08f83be18209283140ca000012308b62d995049c848f2178f686e430c15188f83a817208d82ec0b4000012302682f715e4a284ba2238f9472232916109603e019809503280be0000122fc542da95809ec49c21d0f5c70231815a89683ec195097030c0c80000122f6272e895a0a104a02238f946f431a15889143cc18509102dc0c60000122f0442bf946896e45d1fe8eb06ac30414d88d43b218609182e40b00000122ea0b2e715c8a0e4a22208f706f031c16389803f819909b033c0c20000122e3e82dc956c9ec49521b0f506de31415a89403f41a009c834c0c80000122ddc62dc95549d849521a8f646da30b157092c3f2193097033c0c60000122d7c02d395109c24842110ee06c030715389383ce18309182f40bc0000122d1a42d595289c847d20e0ef86b830315309203c618008a02dc0bc0000122cb8e2db95749f049721b8f346ca30315208f83c2184097033c0c20000122c5582e41580a0049c21d0f5c6ee31015689683dc182091830c0b00000122bf302e0155c9e049021d0f646ea31a15e89483e019809803300c00000122b9192d815449e84922160f286e431415789143cc17e08d02e00ae0000122b2f72df15549e448a2128f006be2f814988f83d219109983500e20000122acc02ed95eca244ba22e8ff071a32b16189783f419209703180b20000122a6c32d415349e248e2170f146cc30515309043b818408d02d80ae0000122a0ca2ce14c49b248120f8eec6be2fc14c88ec3ca17808782e40b200001229ac42cf94f09c24842150ef06b62f615008fc3c819209383100c00000122948d2e615cca264b72270fa870a32416089883f4199096833c0e000001228e952cc14bc9be4782120f0c6dc31115889483de187091031c0d0000012288932cd14e09ae47b2100f106c42fc14b08d839c16908882f80ba000012282662de15689f049a21a0f3c6da30815909503d018409202f40c600001227c402de15609ec49421a0f286d82fc14c88e43be17e09203080ca000012276502cc14c89a64762060eb46a42f714f88ec3bc17d08e82f80be0000122702a2dc15189ce47e2130f1c6b02f014808b83a217708d83280ce00001226a082dc15389e849b21a8f246d430215289083d819209983200c6000012263f52d615349d64852140f346d430314e88c43a216b08582c00aa00001225de22d695449d64842108f006b22f614b88dc3b417808d83080be000012257c82dc15489e64a32240fa472632e16709b441a1a90a103200ca000012251852f215bca0249d21e8f786ea31015689183d418909003040c600001224b632e515909fc49621c0f8070631b15a896c3d419309b03580d6000012245732c814cc9a44762060ec06a02f214a08b039417008e83100c200001223f502e115a89fa4a22228fa071232816109a43fa19509f03540c60000122393c2db15249cc48b2180f386e831415b09443e018b09183340ba000012233292db95549f44932130f046c830e15709203ec19509a83080be00001222ce12f31604a324b32278fc471832015f89703f8198098830c0b2000012226ee2cb94d49aa4722038eac6922ee14988ac3ba17108c82c80a4000012220c02e0156c9f849a2208f5c6e031315c092c3ba17d08b830c0be00001221a9c2dd95849e64952148f2c6ce30315489283d2185096033c0c2000012214672e41588a044a72240f7c70631c15a89603ce17d09383140bc00001220e582da15609ea4932188f306ce30514f88f43b017808b02e80ac0000122085b2cd94d49a24752058ec86b42f214508c43ae17c08d82e80c60000122023f2d695389d44912148ef46b62ed14988b839617708e02ec0ae0000121fc3a2d0950c9d44882158f086c230915709283d618508e82d00aa0000121f6012e79594a0a49921e8f9070e32515889043bc18308e03100c80000121efee2da95589d648220b8ee06aa2f014b88c43ba17708a82e40aa000 else (if i < 182 then 0x124f5bc2d295289e448b2158f346ce30315188f43b217708e83040ac0000124efc62cd94b89a24772118ef86b82f515009303da19b09b83400c00000124e9972e795a4a164aa21e0f8872232816289943ea18f09a03440d80000124e38b2d895509f44aa21e8f9870a321163898c3fe198098830c0ba0000124dd7d2d7952c9da49321b8f506e030915688f83b217808d82f80c00000124d7742d595189d24912120ef46ce31015989303d418609483200d80000124d1502dd9578a0849e21c0f5c6de30c15509483da18d09303000b80000124cb302e31590a0a49a21d8f8070631a152092c3da19109883240cc0000124c5312d494ec9bc47a20f0ed06a82f314d88f83ba19008e02e40bc0000124bee92f415fca3a4b62288fa471e33015e89743e619909a83540d80000124b8e62d595409ca4812138f2c6cc30515089283c417609082e80a80000124b2d12da95489f24a121c8f506fa31d15d896840419509883000b80000124acde2c514b89ac47420b8f186c62fc14a88c039e17a09403480d60000124a6a42e895949ee4932180f406d830715709443d217e08f030c0c80000124a09c2d215089ac47b2110f246cc30b15809483e018a09103140c200001249a7a2df15649f64a32200f406c22fa14908dc3ac17e08c02c80a80000124947e2c894a49884672008eb06882de13b884c36216308602e80a600001248e612d815509e248f2148f306e230f15509343dc18d09702ec0a80000124884d2d815589fe4a12238f78706324163899840619c09c03680dc000012482382db15489ca4892118f0c6c830715609303dc18a09282e00b200001247c0e2e215889fa4a02240fac6f231c15a09283bc17c09382f00be000012476132d215189e24932198f606f031e15d89643e019609a831c0bc00001246fd82e895f4a224a22228f786f231c15d09683f019409703100c0000012469c42d595389dc4852128eec6be2f815109203ce187094830c0c20000124639a2df95a4a0648a2130ef46be2fd15188cc39617308f02e80b400001245d8a2d695589de48d2100f246da30515509383de17709083100be000012457812cf94e09a247b2108ef86c430a15809443e218509403240ce0000124516b2d99570a0049921b0f7c70632815d897c3ec1a609d83580dc00001244b662d194e09ac47b20d8f0c6ce30015208f43b816e08882e00c40000124456e2cd94d49a848120c8f0c6c630215589083d618309483280c600001243f552db9570a064a92280fd473632315a09283c418809383200bc000012439582cf152c9e048620e8ef06a42f214d08c83b018009503200ca000012433412dd95609ec4922160f146bc300150092c3d018d09903280c600001242d122ea15c8a224a62268f786f431c15b094c3da18b093031c0c0000012426fd2da15289da4902150f3c6d630a15208f83c418609603200c0000012420dc2db15509fe49f2228f746fc31515e897c3e818e09403100d000001241acd2df959ca144a02208f6c6fa31f15c89343d218909402e80c0000012414bc2db153c9e24902178f186be2f614d09083be17f09082e00c600001240e932e0953c9f04962190f646ec31715989383c617e08f83000b20000124088d2cd94f49c84872158f046cc30215208f83b217d08e02dc0ac0000124025a2e215a4a004a421f0f746f832716389783ec19309503300ce0000123fc512d595309e04992178f2c6d830215188d83b218109203440cc0000123f6282e695aca144b12230f8870830c153890c3ce18c09283040c20000123f0232d315189e24912130ef46bc2fc151092c3ca18308e82ec0b00000123e9f62e215789f849121b0f446da313158091c3cc18a094832c0c60000123e3ea2d395149b447b20c0ed06b22f614d08f03c818d093831c0c00000123ddce2de9574a0249a21f0f446dc30f15a89383de19509602fc0c80000123d7bd2d795149c047e20e0f246cc30115009143d018509503040bc0000123d1802ee15eca384b22278fa871a32716189603e219e09d83240d20000123cb8d2c694d09b247820f0f186e030015289303c218709202fc0c20000123c5822d495149c247920c8f186d230615209103c418209103040c60000123bf7a2d414ec9ae47d20a0ecc6a02ef14788b439a17008a82d80c20000123b9532e31594a164ae2238fa872032115a09643d818a09283280b80000123b36e2c894e49b048020e0ef06b22ee14a88bc3ae17408d03240c00000123ad1b2f79620a4c4c1233901c74433c17309b440419909803300c20000123a6e82e995bca204a82228fb070231715f098c4001a909803500d40000123a0b62e49598a044a32198f2c6ba30315709303c217908b830c0c200001239ab42d194f09ce48e2190f346e631e15b89403d218b099033c0da000012394962dd954c9f049a21a0f3c6e631015289143c018709383080c000001238e6e2e095589e249121b8f706fc31d15989743f019909a03240d4000012388602d795749f449821c8f3c6e630314f090c3b817508a82f00ce0000123824a2d695489dc4922150f306d02fe15789283d418909203140ba00001237c3a2d895509e849321c0f646ea30f15389243b817708d82fc0c00000123761b2e515aca384af22d0fac70a31a15c09643f419609103040bc000 else 0x1267b732e495949e64882120f246e031015509103c618009102fc0c80000126755e2dc955c9ec4902130f0c6ca2f714b88f83ae17808d02e40ba00001266f3c2dd95849da49421d0f686f232d160899c3f619909d03540c2000012669332d495209da47e20b0ef469e2fd15108e03ba18209083040bc000012663492c994cc9a847620e0efc6ba30715689103c018609203180c000001265d4a2d215109ba4862120f006cc30415809483ce187095830c0c60000126572f2df1570a0c4a62200f7870232d15f09643e618008982d80b20000126512f2d095149c84902168f286da30315108e03ac17c08f03000b800001264afe2e915e4a184b42208f8c712331167099c40c19f09d03000ba000012644ff2cc94bc9a04692030e9c69c2f014608d039a17008a82d80a800001263eda2e01590a024a32200f9070831d159893c3d2189090830c0ca000012638cd2d715109e24872150f3c6ba2f914808b83a818408d83080bc000012632b72df95749dc49421e0f886f831e15609343d818e09583280c800001262cb12da154c9f24912140f006b42f615289203c418409483040cc000012626892e195549e84822138f446d830e15188ec3d418a09103140ce000012620672e215a0a124a22230f7c6fe32015d094c3ea19a09b032c0d800001261a852c894989784612030e806842de13e08a838e17208d03080b0000012614662dc15409e64872128f286e230c15209103c817c08d82fc0be00001260e512dd15589e449921a0f806fa31615b093c3e219109803100d2000012608432d695489d848b2108ef06a82ee14b88e03a617208d02e40c4000012602222db95349ba47f20e0ef06942e6141089c39616f08a02cc0ae0000125fc112d395249ce4882140f406ce309151090c3ce17e08e83100d20000125f5fe2d5952c9de48420c8ee86b22f714d88f43ba17808d02e40ba0000125eff22cc14cc9a24641ff8ea06882e514588c039a17609083280b60000125e9c62e795b4a0849f21b8f506e631515a09343e419109683400d60000125e3a52dc95689f048c20f0f046b02f114d89143c418609203180d20000125dd942d595289ce4852128f186c431415889603d418508d03000ba0000125d75a2eb95c4a1e4a82248fa470e32015e89583ec19409283380be0000125d1182ef15bca2a4b12240fb871c32d162898440419e09b032c0d20000125cadb2ec15cca2a4b62268f946ea30d156894c4001a0094832c0cc0000125c4b82e315449e449621e8f5c6e431b15b09403dc18908c83000da0000125be9b2da15549ce4972180f5c6dc30f15289403ca182095031c0bc0000125b8942cc14c89a046820c0efc6c230115008cc39817608e02d40940000125b27f2d795249dc49321a0f386c02fb14b08c43a016708902c40b60000125ac722d895249c64852180ef06b62ee14b08ec3ba18009203140b60000125a66a2d294fc9ba4782160f346d030b15609343f0196097830c0ba0000125a02e2ef15eca2e4bc22a0fc473033516409a840019a099831c0cc00001259a292d515609e64942170f346d630215209043b618009083080d8000012594192d695089d447b20e0f006c22f714e08fc3b217608d83000ba00001258ddf2e49594a224a42228fb870632616089743ea18a08f83040bc000012587c82dd15589da48d2180f286d830e15909183be184098031c0d8000012581aa2dd15509f249a2198f406c830815388f83b618509383300d800001257b912e015749e448f21e0f5c6ea30f14f09203c218508f03140d2000012575902d715449e84962210f5c6f230b154892c3b618008d82f00bc00001256f622e595a0a1e4b62298fbc72432516209944101a909d83240da000012569772c094a898a4672068ea46a430115208fc3c818b09403000c00000125636e2d4952c9d04932178f1c6c830114f88f83b817d09683000c400001255d6d2d395389d047820f0f186bc2f714b89043ba18308e03240d6000012557552d895409c64842100f1c6dc30014f88f83cc18909283000ca000012551362e495989fc48b2108f206cc2fe14788b43ac17008a82f00c000001254b132e015409d648a2108f0c6c230915409243ce19509883400e60000125451c2c914c89a44742058eb46b630015189603e819009783280bc00001253f0b2d815489e64882148f5c6e231015709203de18e09583000c4000012538f42df1578a024a02200fb070632216609944001a109e033c0d0000012532dc2e1157ca184a42208f5c6e030315108e43b818909182f40c600001252ccf2db95609dc4882140f246c230115009003c019609882ec0b8000012526992e7958ca044a52238f806fc317159094c3f819009e03480d6000012520822d215209e249b21b8f346ea314155892c3dc19309b83340c600001251a552e915d8a4c4c12290f986f831015409343c818708f02ec0b20000125144f2d295009b847b20d0ecc6a22f314a88d43b217008982e00ac00001250e262e315889f849e2220f8470231c15c09383c6190095834c0ca000012508122d815589e64932138f106ba2ff14f08f83be17108982d00bc000012501fc2d895589e448c2168f186ca30215389083cc18308f83280ca0000124fbc62ec9590a144a32210f8c6fc32215989743f418909383100c8000))) else (if i < 186 then (if i < 184 then 0x12800c42e2157ca0e4a62278fa86f231915c894c3e818a09303280c00000127fabd2d314f89b446c2098ed86982ea14288c439216b08d02e40b60000127f4982e51594a1049d2198f446dc30c157093c3ee19a09d83480ce0000127ee7f2df15449ee49421e0f646fc32715e09783ea19409b83400d40000127e82b2fd1648a504d22340ff473c34017009b040e19909b83440e20000127e1ff2ec95dca344c622e900473233f16c89d441a1af0a483900e60000127dc022d115289cc4862160f086ba30c155093c3e218e09083040c40000127d6092d215189be4852160f3c6dc306150090c3ac17408802b80a60000127cfee2d895409d448420f0eec6c230315089083d418109083200ba0000127c9e32d414fc9b84862140f106b22f814f88f03c617909483000ca0000127c39f2ed95a8a1449b21b8f7c6e230e15689583f419e09a03340c40000127bd8b2d8953c9e04892148f046cc30c15589483f419b09b03440dc0000127b7632e11598a0a49a2198f146d830c15009143be17808782ec0ba0000127b15a2da95389f84972168f346b430515008e439c17108b02fc0b60000127ab472d9155c9e24972198f246c82fb15189343e219e09e033c0ce0000127a5392d7954c9f248920c8f146d030915889383da18c09603200cc00001279f132df15649f64962178f406be2fe14d89103b217c09282f40cc000012799032d6154c9da4852120f1c6c230314e08f03c817d08982d00b4000012792e22e015749e84942128f106ce316156093c3d018608f02f80b800001278cd92d294f09be4862170f086b42fd150090c3dc18709483200d4000012786c72df15689fa49e2218fb470a32616389703f218f09583100c2000012780cd2ca14f09c447b20f8ef069e2f214e88e83c4181095832c0cc00001277aaf2dd9598a0049d21d8f646de314157090c3de17d09002fc0ba0000127749d2d695109c24842150f186ca30014b88dc3bc17508c02f00c200001276e502f195fca4c4b822c8fc072032c15e096c3da18a09403080c2000012768282e01578a044a42270f9072632915c09683ec19b09c832c0cc000012762462c714a899246b1fd8e706762d4142087c39a17708d82e00b200001275c322da15449d248c2178f306ce30515208fc3c217b091831c0bc000012755ff2ec15f0a2a4b22220f986fc31716189403d818a09a033c0c400001274fd72e815a4a064a421e0f4c6ea32015d894c3e418b09503240ce000012749c12d715049c647820c8ed06a82f414508c03aa18009282e80ac000012743972e3158ca104a52240f8870232616009783e618f09583000c400001273d692e0954c9fc49b21a8f506ea30515689383ae18b095831c0c2000012737422e39598a0049b2188f746fe31c159093c3c618008d82e00b0000012731402d115349da4872158f246ee31915e89743ea190099833c0d800001272b382d695289ce4892178f3c6f031615a89643ea18d09383040be000012725422cc94d89a64782098ec06a42f514888d03b618c08f83040b000001271f1e2de15909f849b2168f5c6ce30415389343e419009182f80b8000012718f22e195809ec4922168f0c6be30c15389083c818308d03080c0000012712b02ee15d8a1a4a52240f7470e31915d89403d018309282f80c800001270cad2ca14e89b047920f0f206c830415a89543c818509703180de000012706922dc1594a124ac2258fb06f431715c09443c618409482f00bc000012700672eb95b4a124aa2218f706fc31a15b895c3e419109383240d20000126fa5f2d415349da4922130f1c6d231815b89443de190098031c0de0000126f4532d795309e44912138efc6c22f214b08cc3ac17908d02f00c80000126ee512d3950c9be4872138f0c6a22f514a88c83ca18709983400cc0000126e84b2d515449de4942170f3c6fa31715b09283dc18f09302e40ba0000126e23d2db15449ce48b2198f386be30015008e03a217c08802bc0b40000126dc4a2cf94f49b047a20a8eb868e2f214c88d839817208582980aa0000126d6522ca94e49b647e20d8f186b02fc15689383e219609b83340da0000126d0082f29628a5e4bc22a8fbc71e334166098c4161a20a503580c40000126ca212c994ac9a84772080eb069a2ed14a08c439e17a08782ec0b60000126c4142d114e89c049521b0f346ba30a14f08ec3ae17b08f82e00b80000126be1c2ca14b499e4742130f1c6e230715209043c617e09202ec0b20000126b82c2ca14c49a047820a8edc6b42fb14f08f43c618808f030c0d40000126b2352c814f49c248420e0ee06a82f1145889439216108502bc0bc0000126ac2e2d114f49c047b20a0ed86ba30814d890c3ba18708f82fc0c80000126a61b2e195689f249a21e8f586de30714a88e83b218008e82fc0c60000126a00a2de15989f84a021d8f406d430d15409103c818109403280c400001269a052d2151c9b84832108f3c6da31315d097c41419209083140d00000126940b2c614a89aa4752058ea86a82f114588c83a017d08f02e80c800001268de32e19594a064ac2268f8870632716309a040e1a109c03500d8000012687cc2da95609ec48a2188f5c6f631915c89803f419a09b83000ac000012681aa2db15249be4722088ea868e2f714c88e83a617308b82fc0b6000 else (if i < 185 then 0x129868b2e115a8a264ab2230f8c70831815d895c3f619409b03480c4000012980972cc14b89b048420b8ee46c02f414e08dc3b418308f82d80be00001297a962c994c499c4692090ed86b82fa15088f03a818408c02e80ba000012974592e595b0a0e49c2228f646dc316155094c3d8190098832c0c800001296e4e2d4952c9e24892138f186c42f715109203cc18f09883580d60000129684f2d095009a64622058eb46a02f214508b43a617a09103400ce000012962452d415149c84872118f1c6c230415509183b217a08c02e40ce00001295c402d4951c9ce47f2110f306d831a15e89683f219109082e40cc0000129563d2cd14d09a44712058e9c6a430414b890c3a617908d82d80b40000129501c2da151c9c44892100f006b42f714f090c3aa17b08b02dc0b8000012949ec2e615d4a2a4b42240fd070232215e097c3f019509a83400ce000012943b32ea15bca1c4ae2260fa070030f153090c3c618b09303140d200001293dce2cb14a099c4612040e9068c2e414408c03a417a08882e00b8000012937962f11608a464bd2298fbc70c31d160898440a19a09c03500cc000012931782e095749f04a22228f8072232815e09603e218208e030c0b000001292b922c594a098245d1ff8e706962e6144089838c17208b82ec0b60000129252e2fb9628a484c8237102074233d16d89ac4161a50a103500e000001291f112d815389c648921a8f646da30615389083c618109582f80b2000012918cb2ec95bca244ad22a0fbc72032315f09803f019309383200c8000012912a92de9590a004a72218f806fc32015a09483da18b09683240ba00001290cba2c294b09a847b2088f0c6c62fe14808dc3a817f08e82ec0b8000012906a62dd955c9fc4922188f0c6dc302150891c3c617a0858294096000012900672e9959ca1449e21a0f446fa31e15809583e618f09883440d20000128fa3e2df9594a0a49b2180f3c6c0304152891c3c017d08b82dc0bc0000128f4102e795dca1c4b822b8fcc72232d16709783fe1a4096833c0da0000128ee332c994c89ac4792098ed46ba2f114708b039c17708b02d80b60000128e81f2d895149b847b2098ec46ac2ef14588b439217308f02f40b80000128e2072d7951c9ea4972150f1c6d630714f88ec3d018909582f40c20000128dbd72ec15f0a3e4c122a8fa070832716809bc40019409382dc0ac0000128d5882f69634a564be22b0fd472031f160097440019b09283040d40000128cf932d0151c9d24922188f386d630d15609483e818e09883480d80000128c9a72c394a09a047520b8ec86a82fc15189343d018409783480c40000128c3912d9154c9f449c21f0f5c6e030815408f83c218509083100c40000128bd8f2d595489ce48e2158f046a62f3148089039217408a02d00a80000128b75e2e19580a004a92288fb471632416489803fc19009003040c40000128b15d2d114dc9b047620c0ef46bc30615089003c617b08c83200cc0000128ab3c2e215789fc49a2180f686f831b158090c3c019009183100c00000128a5492c814cc9b84782088ee06b230014e88f43ac184094831c0c000001289f112ea95d8a204ba2310fc070c32516089503cc17809002f40bc000012899152ce14e499046b2078e986a22f314a08b03a818108d02ec0c2000012892e62e415c4a1049f21a0f386d230414d08c039616808882fc0c200001288ce52d7154c9fa49721c8f6c6f832116389b04161a309c030c0ce000012886e22cd15049d647d20f0f106d030215289283d818609403100c8000012880c52dd155c9da48f2170f146d230a14f08f83be18008f03040c600001287aac2dc15449de49021a0f6c6f031215a892c3ce18108f02f80b00000128748d2e095489e84942150f486c62ff15089243cc18008e830c0bc00001286e672e515cca304b62298fd871a32316189883e418c09102ec0c2000012868602d495289de49a2180f446da30c15d894c3da18d09603300da0000128623e2e695c4a164a021e8f4c6fa316156892c3ca18008702dc0b000001285c022e7958ca0e4a221e8f3c6dc311158892c3c017e08c82d00be000012855e52df95849d24902140f006ac2ee14908a038e16c08c82e40be00001284fe22cf15009ca48d2180f2c6ce30615008f83a417808b82f00b8000012849bf2db957c9ea48e2118f106de30b15588f43b217f08d02e00b2000012843772ec15c4a1c4a12230f506dc317157895c3e019409502f80b800001283d6c2d5950c9c84842130ee86c2308156090c3cc18609002ec0b0000012837392e815a4a0e4a821d0f606f6321160097c3e818d09503380d00000128312d2db95189c84872140f3c6dc30615209003c217f09183000be00001282b172dd95449d848e2178f306e030f155094c3da18b09603080cc000012824f42e4956ca024922178f086ae30714f09343e019a09b03500dc00001281f132bd94c099246b2010e9c69a2ee14c88ec3bc17b08d82fc0ba000012819142ce94dc9b247a20f0ed86ac2f514a091c3d618e09883300c2000012813222cd15009c247f20c0f006be30114d88e43be17908d82d40bc00001280d082d995349d64822138f286cc30515609343d2187097830c0ba000012806f62d515649f24912130f286de30e15b09503e618f090030c0c0000 else 0x12b0c5c2db95349da4902140ef86ba30815989503fc19809b03540cc000012b06552d094f49d047f2120f406da31515989203c618809483200c4000012b004e2d815289d84932168f446d630715609243c419709703000c2000012afa462d295109be47f20b0ee469e2f614b08cc3b0180092031c0d4000012af4042f31610a404b322b8fcc71a32a16089883f419a09c83240d2000012aedca2ee15eca384a92218f806e031415b896c3f219a098832c0d6000012ae7b92da15649f449d2160f106e430515789683e819d09a032c0c8000012ae1922dc155c9da4892170f346c631115709583da18c09683100ca000012adb842d214fc9ca48f21a8f386d2304155091c3dc18b09482dc0b6000012ad5592df954c9f049821b0f3c6e230715389043ca18508a82d80b8000012acf212e795a4a0649a21e8f8871432415c09543da184092832c0ca000012ac8ef2e715aca024ac2220f9070432015f09643ee18d09683440d0000012ac2d92e095609f44912180f186b02f114b88e43c017908c82f40dc000012abca82eb95d8a104a92238f8070031815d89903fe19b09583340d8000012ab6942d91550a0249421f8f5c6f631a15989543f218f09b83400ea000012ab0bc2c314d09a447d20f0ee46c430314e88d43b018408f830c0be000012aaaa82d895349e049221b8f5870031915a89443d218109303140d0000012aa47e2e615aca0e4ac21c8f5c6d430e15909243c418608e83040d2000012a9e5f2e815aca0a4972210f8071031b15e09583e618909282fc0b4000012a983e2e115889f648d2170f586d031215909403d618f09883480cc000012a921d2e095749f448d2120eec6b630315389083c018508f83380d4000012a8bf62e2958ca104a82240f9c6ee31615388d03a217609102e40b6000012a85df2db95449ea49421c8f706f231515d096c3f819409783400f0000012a7fce2d995309ea49a21e0f806ea31615b89343ec19009402f40a0000012a799f2e495849f849c2168f206ce30814f08ec3be18008e02e80be000012a73922d7953c9de48c2120f206da30014c88e03a017208782e00ae000012a6d5b2e915b8a284b12230fb070a32615f09743f0197097833c0c6000012a674c2d795389e24892148f1c6bc2fb15008f83c818a09003040b6000012a613a2d995409d64902180f6c6ee30e15389483ce184094830c0c2000012a5b4f2c394c09b447820b8ee06ca30015589183c017908982d00ba000012a55422d795209c848c2108f186c030015289043bc17b08f82d80b0000012a4f212dc9590a004a521e0f706fa313158091039617508c83000cc000012a48f32e695b4a0a4a92258fac73033516709a440619709a03480d4000012a43232ba148499246b20a0ec86842e814c08ec3bc18008c82ec0aa000012a3cfc2e495a0a124aa2208f8470032015d89543e819409a83440dc000012a36e62d695289d047a20e0edc6c62fd14a88dc3ac17208902f40be000012a30ca2db15489d848f2190f306e831315409143d217e09283080be000012a2ab02d5151c9c847f20b8ee46c6307152890c3c018208f82fc0ba000012a24b02cd94f89bc47820c8f0c6c22f714888cc3a216f08702c80b6000012a1ea02da95789e64972198f206d430415189003c218309003240c0000012a18902d8155c9e44942168f006b82f614d88f03bc17a08b02f80cc000012a12a32cb94c89a847420a0ed06a030114a08b039c16608902d80aa000012a0c922d915209c448520a8ea46ac2f7150090c3ac17608e030c0c0000012a06532ed95fca1c4a121e0f606ec31615b896c3e4189094030c0c2000012a003b2dc15749ee4992208f8471032916489743e818e09282f80be0000129fa2e2d895549f04a02208f806fc31a15c095c3f018d091831c0be0000129f4502b8944897a4552040e8c6862de13d889438817008982d80ae0000129ee6e2c2147097c4582028e886842e214408a43a217708e83040d00000129e8212f71628a624c7231902472632215e09543e419f09f83700c40000129e1fe2e615cca164ab2208f8470032715f89783f018f098030c0b40000129dbe22db957ca004a62208f886ee31115489383e818f09c83240d00000129d5a12e895b4a0e4a32220f7c6e031515689443e619109683100be0000129cfa22cd94b89ba47e20c8ed86a42e814b88c83a017108682b80ac0000129c96c2eb95f0a224b922f8fcc71e32f161097c3ea19909483240cc0000129c35c2d715449e248e21a8f786fc31715b894c3fa1a30a683800f40000129bd592d7951c9ce48e2138f0c6d2309157896c3d218008f82d40ae0000129b7522d395049d04862148f306da30a154890c3be17408f02e40c40000129b14e2d295189da4882130f106ce30415109083d818b09983400d20000129ab3f2d595309e24872180f5c6f031916109603bc17c09203080b60000129a5302d715409f04a121e0f246d430515209043ae17608702cc0aa00001299f012e715809fa48d21f8f506ea30f157093c3e819409c03540c8000012999022d095049b447420a8ee86d42fa15288e83b018108b03080b6000012992e52e115989ec4962200f686f431515e89483e4189096832c0c400001298ca52f0961ca4c4b52280fac704326160097c3e218f09783000c0000)) else (if i < 187 then 0x12c92532da95389e848d2130f086c630114c08f43d017f08e83240ce000012c8c2b2de9584a044952178f286d02fc15308d83b018109382f80cc000012c861c2d615389f44912150f306e030815188fc3b217908c02e00ae000012c7ffa2de956c9f44922128ee06ba2fd15309083c618008e02fc0c8000012c79d42e2156c9e24902128ef06c4305154091c3b417108a82f80b6000012c73ba2d615349ea4912188f706ee31815c893c3da18a09103100ca000012c6da12d815549ea49821a8f446c230915489043d2185096830c0ce000012c67842db95609ee4912170f5c6e430815509283e419309b83400c2000012c617b2d895309ea49a21b8f8470430b15108d43c017e09303240bc000012c5b4d2ea15c0a1c4a92248fbc72833416509943ee18709502f40bc000012c553b2dc95649f64942150f1c6c030415389183b816f08982c80b2000012c4ef32f01624a584cc2310fe471e32e16589a43f618b09603080ba000012c48ed2d895989e649621d0f606f431015a09343c618208d02cc0b0000012c42e22d995489e24832100f046be30c156892c3ce18c09683400ce000012c3cd82d295289cc48120b0ee06aa2ec14588b83a217008502b40aa000012c36ce2d1150c9b64712088eb06902f314c88c43b218009183140ca000012c30ab2e595e4a224b02248fc0720332169097c3fa19d09603340be000012c2a8f2da95589f44992188f3c6cc30914f88e43ba17e09102f80c8000012c248c2d094e09ca48120e8eb46a630815089143c4188092833c0d6000012c1e702de15749f44972178f3c6ca30614c88fc3c618309403140be000012c18602da95289e248a2108ee86c62fc15009283ce18e09102f00ae000012c12602cd14e49a84752088ec469a2e4142889039e16d08602c00ba000012c0c4e2d9954c9f84952200f586f431315809503ea18809503240bc000012c061c2e01578a0e4942130f106c22f814d08fc3d018708e83140c6000012c00112d515049e24942168f606d230114e091c3bc18009002fc0b6000012bf9d82e515b4a1449f2220f706fa31a15d09683ec18e09583100d6000012bf3e62cb94f49c44832100edc6c631015889143d618009283400be000012bedd42db15709ee49721e0f406d830715189203d619009402fc0ca000012be7982ed15f8a344b02298fdc71632515f89803fa19d09d03480d4000012be17d2e29564a004a02220f8470a31a15d89ac4101a30a0834c0ce000012bdb732df154c9e84932158f246e430f15889303ee18e09303340c2000012bd5452e115889f449d21f0f386da31115c09303cc18508d02d80c0000012bcf552c714dc99c4702090ed86ae2f114508d03b617d09102e80be000012bc9542d7151c9b64812130ef069a2f114688bc3b218509483480cc000012bc3482d6153c9d449921f0f806f231315c89503dc18808f830c0bc000012bbd2b2dd95509e049021c0f586e231315609383ee19509603140d0000012bb7092e015589e84a521c8f6c6ec309159092c3d818409082f00c4000012bb0e52df15789fe4962150f046b42fb14d893c3e018c09182f80bc000012baad32d995489da48a2138f146c62fc14d88fc3c017d09083080be000012ba49e2e515cca2c4b722b8fdc708317158096440019a0a5836c0d8000012b9e7a2df95549f449e21c0fa46f431315709083d017d08c02f00c0000012b985f2dd9588a0a4a021d8f506e631815889283ca18409082f00b4000012b92572d5950c9be4852150f146c030314b08f03ae17508702d80bc000012b8c512cd14e09b647c20f0ef46bc30415209043cc18609103080bc000012b86452d395249d04832060eb86a62f814e09143cc18108e83000c4000012b80132e1956c9ea4972170f1c6dc30f15c09503de18f09503100ba000012b7a062d415389de4862148f006ca303156892c3ce17c09002ec0c0000012b74072d295349e647d20f0f1c6d030e15608e83ae16d08902c00ae000012b6dfc2da15189ba4882140f046c4305153891c3be18409183040c0000012b67bf2ee95d8a2e4ad2278fb471231a158894c3e618b09303140c2000012b618f2e695dca3a4ba2270fb871232a15f89603f019d09c03300de000012b5b592ee9600a384b42270fa071e329165897c41219c098032c0dc000012b55452d995449e04952168f3c6ca30314988ec39216708782ec0c0000012b4f1e2e49594a004a72208f8c6f431e15b89583d419109783040ca000012b48ea2e915c0a204aa2270fc070432515f89603ea19209303140d0000012b42ec2cb14dc9ae47520c0ed86ac2f614b88f43cc18609383140c2000012b3cda2d795089be47420b0ecc6a42f114a88f83c618309683300ca000012b36d72d394ec9c24742060ec46a22f814888cc3ac18008c82d80ca000012b30e12c714e09be4822130f086bc2f214c890c3d418e095030c0ce000012b2adf2cd14dc9b84812130ed46b430615189183ce188091031c0ca000012b24bc2e495c8a204b42270fc070632716309cc40a1a609f03480d6000012b1ea62d715509f04942168f3c6c230915a89343c018308d02e80cc000012b187f2ea15b4a0e4a221e8f606ec31315989443d819409903280d0000012b12672e0956c9fe4992160f486e830a15289043d218408d030c0c2000 else (if i < 188 then 0x12e16e72c394c898846b20c0f086ac30115109103b418209603240c8000012e10be2e095609f84a921f8f946f431115609443ea18e09603500d0000012e0aca2d395109ce48d2188f3c6d030615609203c818309402f40c2000012e04a42e715989f04942198f686f231415f09443d618509702f40be000012dfe7b2dc954c9f848c2180f406c030d15909283dc18f09783240d2000012df8632d594f09c248520f8ee46ca30614e08f43d618e09483100b8000012df2252f09604a2e4bd2278fac71432f16409643e018c09283100c2000012dec412c1947c96844e1fa8e786822d914108883a216d08e02ec0ae000012de62b2db15649e44872168f506dc31115f89603ca18309683200d0000012de0202d814f89b447e20e8efc6ba2fd14f89103c417208c83140cc000012dda182cf15389ee4942158f5c6ea31b15b09403da18a09783140d0000012dd3fc2dc95589ea49421c8f84700320158892c3d8187094830c0c4000012dcde72db954c9e64a22230fa070c31e16189a43fa191098831c0c8000012dc7ca2dc152c9e44902168f246dc30915389083c218009103080c8000012dc1d12c714e09b447c2098edc6ac2fe14b08e83a017108a82ec0b2000012dbbaa2e195689de48b2158f386d630015509203c618609003040d8000012db5b42cf95089ce4832100ef06ca30b15989303cc19009903300d2000012dafb12cf94fc9c248720e0ef86bc2fa14a08c83ac17b08b82cc0a8000012da99b2db95349c848020f0ee46be2f414e89183d618108e82cc0c2000012da38b2d815289c448e21a0f606e630f15989743f01a009983500cc000012d9d812cf95349ea48f21e0f7c71632415a89303d218008f82f80c6000012d978b2c694a49784632030ed06ba2ff14e08e43a417408502c00ba000012d915f2e09564a0449d21d8f6070031115709483d018508e02e40b6000012d8b302e515b4a0049621c0f446ec32215e09a840019f09a83340c6000012d852b2d4153c9e649021d0f6c6ec30915589383c618509603180c8000012d7f1a2d595489ea4862168f1c6d431015889403f018f09a83440ca000012d79082d515249e248f2198f306c430915889443e618a08f82e40ba000012d72dd2e895d0a364bb22d8fc473232f16389a440619a09683500d6000012d6cb82e19560a0a4a021d0f4c6f430b159094c3f219309303140d0000012d66d72c294a49964722068ec06942ed14988b83bc17708d83000b8000012d60a92e995b4a1c4a82230f8c6f831415889343dc18808f03040c0000012d5a942d215309d848b20f8f106bc30215308e83c218609583040c0000012d54732df95789ea49c21f8f546f031715989083be18509483180ce000012d4e5e2de959ca0049f2198f586ee31215c09483e619909b03280ca000012d483b2e095709e649c21d8f3c6e230f15508f83be17a092032c0cc000012d423f2cc94f09bc4772058ebc6ac2f814788c03a617308a83140c4000012d3c3c2cf15209e248f21b8f406ea31e15c09543ea18d08a82dc0ac000012d36112e595949e24892190f146bc2f814c88e83bc17608d02f00ae000012d2ff52df15709f049c2240f586f031715c894c3ee19809803400d4000012d29eb2db15789fe49b21b0f6470432115c89403d017c09103040b0000012d23bd2e29584a1c4ba2278fac71032316109683f819409e03500c4000012d1db72d895209c64882178f0c6d230615509403c218308e83000c4000012d17c12cc94a099a47120d0ee86a42f814e89403d218208982d009e000012d11b32d515189d648d2160f206cc30414f08d03ae17c09403180c0000012d0bc32c814a89a44681fe0e5c66e2db13c889c38816508382c40aa000012d05a62de155c9de48f2158f046be30715289283d6195095832c0ba000012cffa12d115249ce4812140f1c6d630c15509243de18209103000c8000012cf99b2d314e09aa47c20d0ef06bc30615489303c018108e02f40b6000012cf3ba2be14989864602038e8c68c2ee14308b039816808d82d40b4000012ced9d2db15489ee48e20f8f046b02f414908c83bc17808d030c0d4000012ce75f2ed15d0a144aa2240f9c6f231315889403d618108d03140d8000012ce1582d515309c24872138f306ba30614e08f43b617708c82e80b2000012cdb1a2f4160ca464c62328fe4722331163097c3ea19709603280b8000012cd51b2d014c09a047720f8efc6ba30415189243c418009182fc0c2000012ccf2e2c1148499a46720b8ebc6bc30e15909703f019809c832c0ce000012cc9252d4151c9ba47c20e0ee46ca30114e89143ba17f08e82c40b2000012cc3022dc15649e448d2118f1c6c22f614e08ec3ae17308182ac092000012cbce42d8151c9ce47d20c8ed06a62f414a88d83ca17a09183100ca000012cb6ec2ce94e89bc4842150f306d230415309083c8184091832c0ca000012cb0dc2d315049d248d2170f1c6e030915489643e418d09182fc0c8000012caab92e195609e44982188f686f231815b89583da18609183000d4000012ca48e2dc95809dc49621a0f486e630d15889583d018709302d40c8000012c9e992ca94d09be48220e8ef86c030014a08d839e17808902ec0c6000012c986a2dd1574a024a72210fa470431e15f09603ec19609883280dc000 else 0x12e661500000000000000000000000000000000039a16e08402dc0b6000012e5ff22dc15709ec4972198f346e030b15809283d218b097832c0c6000012e59e12d815549ec48b2170f4c6da30714f89003b218308f83080ca000012e53c72e0156c9fc49f21d0f806fe31a15b89303cc19909503340ca000012e4dab2e195809fa48d2148ef06c830715088c839e16f08702cc0b2000012e47642f415e0a244ad2240f7c6f231c15c092c3c818b09602c40ca000012e413f2e115aca1e4b022a8fa46fe31515b09583fc19509783240be000012e3b112e1156ca0e4b02240fa071431b15b09603e619109303040c6000012e35152d114e49c647720d0ec86a42ee14608c43b217f090031c0b8000012e2ed62f215cca204af2260fac70e32716109803fa19a09683140d8000012e28d32d095309d447e2160f506e430b14b08c43b618209203040c8000012e22cf2d495589d248f2140f006b62f914b88d43b217608802d40b2000012e1cd12c994d09ac4752050ec06ac2f714c09003c618608f82e40ba000))))))))

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



private theorem b179628 : covered 179628 179722 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179722 : covered 179722 179816 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179816 : covered 179816 179911 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b179911 : covered 179911 180005 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180005 : covered 180005 180099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180099 : covered 180099 180193 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180193 : covered 180193 180287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180287 : covered 180287 180381 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180381 : covered 180381 180475 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180475 : covered 180475 180569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180569 : covered 180569 180664 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180664 : covered 180664 180758 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180758 : covered 180758 180852 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180852 : covered 180852 180946 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b180946 : covered 180946 181040 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181040 : covered 181040 181134 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181134 : covered 181134 181228 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181228 : covered 181228 181322 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181322 : covered 181322 181416 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181416 : covered 181416 181510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181510 : covered 181510 181604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181604 : covered 181604 181698 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181698 : covered 181698 181792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181792 : covered 181792 181886 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181886 : covered 181886 181980 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b181980 : covered 181980 182074 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182074 : covered 182074 182169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182169 : covered 182169 182263 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182263 : covered 182263 182357 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182357 : covered 182357 182451 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182451 : covered 182451 182545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182545 : covered 182545 182639 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182639 : covered 182639 182733 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182733 : covered 182733 182827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182827 : covered 182827 182922 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b182922 : covered 182922 183016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183016 : covered 183016 183110 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183110 : covered 183110 183204 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183204 : covered 183204 183298 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183298 : covered 183298 183392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183392 : covered 183392 183486 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183486 : covered 183486 183580 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183580 : covered 183580 183675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183675 : covered 183675 183769 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183769 : covered 183769 183863 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183863 : covered 183863 183957 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b183957 : covered 183957 184051 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184051 : covered 184051 184145 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184145 : covered 184145 184239 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184239 : covered 184239 184333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184333 : covered 184333 184427 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184427 : covered 184427 184521 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184521 : covered 184521 184615 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184615 : covered 184615 184709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184709 : covered 184709 184803 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184803 : covered 184803 184897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184897 : covered 184897 184991 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b184991 : covered 184991 185085 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185085 : covered 185085 185180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185180 : covered 185180 185274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185274 : covered 185274 185368 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185368 : covered 185368 185462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185462 : covered 185462 185556 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185556 : covered 185556 185650 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185650 : covered 185650 185744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185744 : covered 185744 185838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185838 : covered 185838 185933 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b185933 : covered 185933 186027 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186027 : covered 186027 186121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186121 : covered 186121 186215 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186215 : covered 186215 186309 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186309 : covered 186309 186403 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186403 : covered 186403 186497 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186497 : covered 186497 186591 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186591 : covered 186591 186686 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186686 : covered 186686 186780 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186780 : covered 186780 186874 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186874 : covered 186874 186968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b186968 : covered 186968 187062 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187062 : covered 187062 187156 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187156 : covered 187156 187250 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187250 : covered 187250 187344 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187344 : covered 187344 187438 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187438 : covered 187438 187532 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187532 : covered 187532 187626 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187626 : covered 187626 187720 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187720 : covered 187720 187814 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187814 : covered 187814 187908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b187908 : covered 187908 188002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188002 : covered 188002 188096 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188096 : covered 188096 188191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188191 : covered 188191 188285 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188285 : covered 188285 188379 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188379 : covered 188379 188473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188473 : covered 188473 188567 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188567 : covered 188567 188661 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188661 : covered 188661 188755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188755 : covered 188755 188849 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188849 : covered 188849 188944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b188944 : covered 188944 189038 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189038 : covered 189038 189132 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189132 : covered 189132 189226 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189226 : covered 189226 189320 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189320 : covered 189320 189414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189414 : covered 189414 189508 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189508 : covered 189508 189602 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189602 : covered 189602 189697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189697 : covered 189697 189791 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189791 : covered 189791 189885 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189885 : covered 189885 189979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b189979 : covered 189979 190073 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190073 : covered 190073 190167 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190167 : covered 190167 190261 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190261 : covered 190261 190355 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190355 : covered 190355 190450 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190450 : covered 190450 190544 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190544 : covered 190544 190638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190638 : covered 190638 190732 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190732 : covered 190732 190826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190826 : covered 190826 190920 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b190920 : covered 190920 191014 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191014 : covered 191014 191108 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191108 : covered 191108 191203 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191203 : covered 191203 191297 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191297 : covered 191297 191391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191391 : covered 191391 191485 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191485 : covered 191485 191579 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191579 : covered 191579 191673 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191673 : covered 191673 191767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191767 : covered 191767 191861 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191861 : covered 191861 191956 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b191956 : covered 191956 192050 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192050 : covered 192050 192144 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192144 : covered 192144 192238 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192238 : covered 192238 192332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192332 : covered 192332 192426 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192426 : covered 192426 192520 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192520 : covered 192520 192614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b192614 : covered 192614 192709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 179628 192709 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b179628 b179722) (joinCoverage b179816 b179911)) (joinCoverage (joinCoverage b180005 b180099) (joinCoverage b180193 b180287))) (joinCoverage (joinCoverage (joinCoverage b180381 b180475) (joinCoverage b180569 b180664)) (joinCoverage (joinCoverage b180758 b180852) (joinCoverage b180946 (joinCoverage b181040 b181134))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b181228 b181322) (joinCoverage b181416 b181510)) (joinCoverage (joinCoverage b181604 b181698) (joinCoverage b181792 b181886))) (joinCoverage (joinCoverage (joinCoverage b181980 b182074) (joinCoverage b182169 b182263)) (joinCoverage (joinCoverage b182357 b182451) (joinCoverage b182545 (joinCoverage b182639 b182733)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b182827 b182922) (joinCoverage b183016 b183110)) (joinCoverage (joinCoverage b183204 b183298) (joinCoverage b183392 b183486))) (joinCoverage (joinCoverage (joinCoverage b183580 b183675) (joinCoverage b183769 b183863)) (joinCoverage (joinCoverage b183957 b184051) (joinCoverage b184145 (joinCoverage b184239 b184333))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b184427 b184521) (joinCoverage b184615 b184709)) (joinCoverage (joinCoverage b184803 b184897) (joinCoverage b184991 (joinCoverage b185085 b185180)))) (joinCoverage (joinCoverage (joinCoverage b185274 b185368) (joinCoverage b185462 b185556)) (joinCoverage (joinCoverage b185650 b185744) (joinCoverage b185838 (joinCoverage b185933 b186027))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b186121 b186215) (joinCoverage b186309 b186403)) (joinCoverage (joinCoverage b186497 b186591) (joinCoverage b186686 b186780))) (joinCoverage (joinCoverage (joinCoverage b186874 b186968) (joinCoverage b187062 b187156)) (joinCoverage (joinCoverage b187250 b187344) (joinCoverage b187438 (joinCoverage b187532 b187626))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b187720 b187814) (joinCoverage b187908 b188002)) (joinCoverage (joinCoverage b188096 b188191) (joinCoverage b188285 (joinCoverage b188379 b188473)))) (joinCoverage (joinCoverage (joinCoverage b188567 b188661) (joinCoverage b188755 b188849)) (joinCoverage (joinCoverage b188944 b189038) (joinCoverage b189132 (joinCoverage b189226 b189320)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b189414 b189508) (joinCoverage b189602 b189697)) (joinCoverage (joinCoverage b189791 b189885) (joinCoverage b189979 b190073))) (joinCoverage (joinCoverage (joinCoverage b190167 b190261) (joinCoverage b190355 b190450)) (joinCoverage (joinCoverage b190544 b190638) (joinCoverage b190732 (joinCoverage b190826 b190920))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b191014 b191108) (joinCoverage b191203 b191297)) (joinCoverage (joinCoverage b191391 b191485) (joinCoverage b191579 (joinCoverage b191673 b191767)))) (joinCoverage (joinCoverage (joinCoverage b191861 b191956) (joinCoverage b192050 b192144)) (joinCoverage (joinCoverage b192238 b192332) (joinCoverage b192426 (joinCoverage b192520 b192614))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 179628 ≤ index 345000000/512 := by decide +kernel
private theorem starting_value : fast 345000000=18549341 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 345000000=18549341) (n : ℕ) (low : 345000000≤n) (bound : n≤370000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=345000000
    · rw [first,anchor]
      exact starting_value
    · have past : 345000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤370000000 by omega)
        have within : index n / 512 < 192709 := by omega
        have lower : index 345000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤370000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ345000000To370000000
