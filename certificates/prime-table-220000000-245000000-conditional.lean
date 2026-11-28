import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ220000000To245000000

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




private def radical : ℕ := 0x312a84816450dd78d4c2e11d4b19f6bb78422161b6d1299a358e378cad1747c86efa1f526c0c119e38c9e8c7cee93ddb8f79c75dd83dfb2787cabad8af66683e208a2220359c55e31ba655cd0c702d103648850b270b8f2cf7afc1ff3ba31c9966cd23ae72b08e8221ffa766bd8667826b871b770ba5b3e0aa37d13ee093245e1abd968366f8f051b22cd4f7accad18c680f099d9612c6022e34b4da4fc6478cecc9c86336852b44be61e42dbb9c44f251e7aface4c13557eb6930d03f20bbac6b833d110314cbba0378e25963f3732717b86b32660a0ee90070416ba25fbd6d23a7f6d41639593cbbef21e7aada166f247be04bfcbdb1387ecdcd93201053235104a5b03534b5de0ff21d33a213e3690426854f2fe2c0780d8b471dd9f9e087182aed243076ed8ae421b52b9c2d74e96ae7cdc4238ed1ba5939edfb85e81e56ee4c505f977f724aaddb80732418280776ce238f5639f7015097fa949b0963dd06391b291c3ea7153d37bbd83f8ad2f07d34937e1f99ac975115425446d75a6eda100302044b24a6dcd97e65457521e90ef8498d90764c656052e09327a54e6450bfa5f8a4b0ce90adac3ad0242074cfcc08544f9614860b2aa7be5655a93517d0db2bef123d9cc0e484e50869a527608176a7a3617bb440735e09cb8377b60da9e13589728f637ae8100604aea88f7fdb23b09f0e538111259b4827897be09bdd935f107466455e788c5d1291b6ce9b49690df6ea838111168b9c78274e4b3f94637abdd2b20d966e87c85bf9290cccf0d43a6b0d8b1403bafe8418434ba03bcdf20bf9b6f8e0c9f3be27e91c370b20d599cbbb3ba307ee35f3440538d40de89528f433f24fdaf78b2a8a44dd08972fbda5271cf5e5fa93d7643f867dd2d75adcea77e24c103fa44f9ccc49241b3e3b92fb8924fc607304d9201fe783757ff8ae89c3d1c916adcb9d6d0ea0083880d5fb8e96d68fca4108de9b44c6c682c65b618950661ccbd5c8863b066cd50b324eb06e6a4ef4af50f8347dea4184fdbade166fce0ffd7b786f9d91327a45bedbb8d5d5fef126e9edcd67202b078a936547328afa0b5ffa0da44c56b181bb7d513a129f829acfdfb9a610b8d461a22913804c15d50f483425d22511b58a3f34bd0d588565e3018772e889342958d67054e19d1a09f580b38dbf2dfa75f6609798c8ff3c915841d4d7e2238d246afdd049e37219d04d91467db5a3cd35e0206000f327097296276a186bea0c0af765ae0e240fb6110699d4e18c156f3500fc4f2d91c4f90e9c9c2e54cc1cb62caeeb525a4392f37e5bc48db93da059f767bce8dbe725c737aa4e13f4fe77bbf1d6634301a54d0959cc05077cd06d3d65cee7ed82831bcfb9c187edf854b4016c490e2d3dc49ee36d42276b399a6cac8c2a168302883bb6ffd886402bee80b31b35d068f6fbf5c0d835323e916f0a34ee1bffdd6d5e2b1fa5bec5d8232234e02846d4a111c12114c6882f0912fc71cc5d72d968886baf2374140a8ac934f22ee765d10d45254c327cdb727dcb4659b82ca3ff94ad0d8386afd20d943030eaae12eeebf100847b6bbadebe1cb69c94c4a83a547ff103f8be7b826f0272e2523ebecd6088392a8efb5cafad79139bbce75baa41ad567d68a30ca8ef97a3e2071d0387f23aa0ee5c6b1d18fc296f71c880d08f67abaedf475e7fde846fde98765e2303ce33c62aec4ee6a57db2b7ad4b95817ede93872de04df5f6cc9e07e06966c2771476a8264a6a663e6793a8ebe07ae1c8ae969d838314234518a58e76b4d017487fce8a04a2144701812ac66987d4adac1d6abdad86a54cdc5695515f0781cb6dec26f77cf2fd378c83cca39393a192b943cccf7eca4f42cb70c7dc9e3908e7d547ac4ddbe6301079ec9327148e564ffda7e79393cb7bbde598feca751f5b6ce4edb0a0a3262c8f3da9b935d6e76ad36727e1b51034b1da3924aca3ba4095acb2ac90e64b88d43420107b6b1cf8a129584192b4682d01bd4711d329f65537b6e775ce0b09054456f54174f6b4e18583c21cf789cb00ecd6fba3c13915f06e5ca161a038d4fbeb6a83f3554f493e09700445a73887cb775e63a5e1a840c173853410cb46440c7a5c2d0f99875c9d7a7046a45f36897d0403f6eb6ee3b10b4bd15bab7202d50780651595edbde95ba4569450df37b72c6879c6df7a4b8057d9f6a760afe65f63af09fdc8351f93ab8c5ecf3105bcdca0600e49d943c7686268776b257b89799e51c2f7912a152797ef54098915598d1f32d8ca0095cf2dbb261d02541599eaa4e0b6cb27fd9d101b7083493c3abf5e3da6601bab153bd172e5a7c675a0e30263e8d108d81bd451f36464b965bee868110560f1139da8ca6b8ac9619cadfc3c43aceab627d90b9ffd1d308c2f77f56c4f880ef372879ecae0441873c1b2dd9b3552483cd3b592701dc21c0d7627bfe30b8a9986be242b765eacb40fa2c20738581b8d77dcae8fb6a850b93bd2066718c8f972f5d5afa3ca44f98fc9f4fe9e3b8e66720ea248feeab7b2d33796450bc3e1358a91d602cfb1e3b50e3e26c59f66065597e72d98058e0df82652c12484b84cba3cbf3076ca612947c7a6f75f15394019a35cf33946026a1dec65d9a5d2813556ed7e36df4c9b798eb51a66bb2354ffaf2ff285c98543bb7f0ac35f3dbd836d997701514e7d0f1c629814042af8f6946cda4ffd6d37da14cf00be9ebe7ec8e1898cac783817576af96b2c874e4df22dde7bb8c3c3b639c1c9db21b138208377cad2f1c19c9f0bea36e5c217ac2b9a650d5f260f32ac6a016dcbde72ab7ef54da98339c972f777513f83a41d1c10f4ac43b654dadedbe2ca879f02b97a179d68f60225ad35cd679daff8c24a98b793d9e9cabc3db65344ef7c6627c603fd88b989a2838226aacc6dcb8e211bfb8ebc578a4ecfdc591b216dc546a0b83710f04d6edcfe3598f272b2b6b7044f15dd583d1fa560f1a8ceff0a670e19faebef62d481775f3a2947e2df3f9e2ce37a0c35594b1330fcab0cf0b28a8976c91c8971d913aa42cc5f6d7e71723b97adc69a2b8b65dbd0aeffd2ca601250b954c56034323ff553858042a7bb54efa55652ec7c751b31ba4a9912252aae6cb6a3f1caf9e1a332fcefaf0b85995e55720f54dbc299dc051024c6c9ead4ca3d493d933eb5c9917c029ac2d48fcabb7b15c683adfd7f0f776e9d754a8d6525c4368438f8e946a2a3313db0feefbd70d1e3bcf7b264793ca592c606135c232f5d650f85a2399415c21ab8e5facb7772e8fe8c2fbeb88af4fb887af408bd27c5e860e7a0fdcee1050b3e824e3fad28a310c9c02cd3ff2825772040807b9551bd8f943eaf9b67726016a8e786b67e75779c2af30f4c061f5ebe5cd425be5e40522dfe497eefca65b29d931d2aed65e2fa34360ca5f5ece092a1b089e91c8a3f933b52f104ae91abb4abd2b2f88b3d916449221f752bc9703b9bc9ccc554de728ad69a5d1347664fbb37389ab139f1dd3da0e7ea7b00e32f16cb42f9acdc6a6c296ec2f3c797e88d53aa195d6c4d2a8de0dedff6c501c327bc0b8a90c71f5c91ffa0458dd8626af44f418f3091d3270b6837e0af3fb97201bc7a3c34373f9e9042502c573ad07a3b403d23e8a589ea1ddf63afc1f7995922959f20790065943f927574cc68030958d499a1ee0713cb450ca5da4a1628cca0c44ff3d2d00b90b218a837d500c991d26d03cf28e0f1da65450786ad2ffabe8fa10f90a7b1d7d09ce3b5b3aec157ee2b384656a08e7e732387b97927ca1b7ac3b1bfda364356cb1114e1807daa56b30d69bf8f13b36f8cf03cb5004ab68f63f44f4a539985097207e7b92bedbc2f4371f502a49c704a0f815b5ab4d1f175048d2177fd18618eb5a997d3f635d082253fdad9bebc55d71903107989e25f7baedaab88b47d330349f3f4ef9613cf24c584706

private def light (n : ℕ) : Bool :=
  if n≤125 then decide n.Prime else n.gcd 188267717688892609974376770249160085759540364871492425887598231508353156331613598866882932889495923133646405445930057740630161919341380597818883457558547055524326375565007131770880000000000000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤15652) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 125 = 188267717688892609974376770249160085759540364871492425887598231508353156331613598866882932889495923133646405445930057740630161919341380597818883457558547055524326375565007131770880000000000000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 125 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤15652 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 61 := by unfold smallValid; decide +kernel

private theorem sp61 : smallValid 61 61 := by unfold smallValid; decide +kernel

private theorem sp122 : smallValid 122 61 := by unfold smallValid; decide +kernel

private theorem sp183 : smallValid 183 61 := by unfold smallValid; decide +kernel

private theorem sp244 : smallValid 244 61 := by unfold smallValid; decide +kernel

private theorem sp305 : smallValid 305 61 := by unfold smallValid; decide +kernel

private theorem sp366 : smallValid 366 61 := by unfold smallValid; decide +kernel

private theorem sp427 : smallValid 427 62 := by unfold smallValid; decide +kernel

private theorem sp489 : smallValid 489 61 := by unfold smallValid; decide +kernel

private theorem sp550 : smallValid 550 61 := by unfold smallValid; decide +kernel

private theorem sp611 : smallValid 611 61 := by unfold smallValid; decide +kernel

private theorem sp672 : smallValid 672 61 := by unfold smallValid; decide +kernel

private theorem sp733 : smallValid 733 61 := by unfold smallValid; decide +kernel

private theorem sp794 : smallValid 794 61 := by unfold smallValid; decide +kernel

private theorem sp855 : smallValid 855 61 := by unfold smallValid; decide +kernel

private theorem sp916 : smallValid 916 62 := by unfold smallValid; decide +kernel

private theorem sp978 : smallValid 978 61 := by unfold smallValid; decide +kernel

private theorem sp1039 : smallValid 1039 61 := by unfold smallValid; decide +kernel

private theorem sp1100 : smallValid 1100 61 := by unfold smallValid; decide +kernel

private theorem sp1161 : smallValid 1161 61 := by unfold smallValid; decide +kernel

private theorem sp1222 : smallValid 1222 61 := by unfold smallValid; decide +kernel

private theorem sp1283 : smallValid 1283 61 := by unfold smallValid; decide +kernel

private theorem sp1344 : smallValid 1344 61 := by unfold smallValid; decide +kernel

private theorem sp1405 : smallValid 1405 62 := by unfold smallValid; decide +kernel

private theorem sp1467 : smallValid 1467 61 := by unfold smallValid; decide +kernel

private theorem sp1528 : smallValid 1528 61 := by unfold smallValid; decide +kernel

private theorem sp1589 : smallValid 1589 61 := by unfold smallValid; decide +kernel

private theorem sp1650 : smallValid 1650 61 := by unfold smallValid; decide +kernel

private theorem sp1711 : smallValid 1711 61 := by unfold smallValid; decide +kernel

private theorem sp1772 : smallValid 1772 61 := by unfold smallValid; decide +kernel

private theorem sp1833 : smallValid 1833 61 := by unfold smallValid; decide +kernel

private theorem sp1894 : smallValid 1894 62 := by unfold smallValid; decide +kernel

private theorem sp1956 : smallValid 1956 61 := by unfold smallValid; decide +kernel

private theorem sp2017 : smallValid 2017 61 := by unfold smallValid; decide +kernel

private theorem sp2078 : smallValid 2078 61 := by unfold smallValid; decide +kernel

private theorem sp2139 : smallValid 2139 61 := by unfold smallValid; decide +kernel

private theorem sp2200 : smallValid 2200 61 := by unfold smallValid; decide +kernel

private theorem sp2261 : smallValid 2261 61 := by unfold smallValid; decide +kernel

private theorem sp2322 : smallValid 2322 61 := by unfold smallValid; decide +kernel

private theorem sp2383 : smallValid 2383 62 := by unfold smallValid; decide +kernel

private theorem sp2445 : smallValid 2445 61 := by unfold smallValid; decide +kernel

private theorem sp2506 : smallValid 2506 61 := by unfold smallValid; decide +kernel

private theorem sp2567 : smallValid 2567 61 := by unfold smallValid; decide +kernel

private theorem sp2628 : smallValid 2628 61 := by unfold smallValid; decide +kernel

private theorem sp2689 : smallValid 2689 61 := by unfold smallValid; decide +kernel

private theorem sp2750 : smallValid 2750 61 := by unfold smallValid; decide +kernel

private theorem sp2811 : smallValid 2811 61 := by unfold smallValid; decide +kernel

private theorem sp2872 : smallValid 2872 62 := by unfold smallValid; decide +kernel

private theorem sp2934 : smallValid 2934 61 := by unfold smallValid; decide +kernel

private theorem sp2995 : smallValid 2995 61 := by unfold smallValid; decide +kernel

private theorem sp3056 : smallValid 3056 61 := by unfold smallValid; decide +kernel

private theorem sp3117 : smallValid 3117 61 := by unfold smallValid; decide +kernel

private theorem sp3178 : smallValid 3178 61 := by unfold smallValid; decide +kernel

private theorem sp3239 : smallValid 3239 61 := by unfold smallValid; decide +kernel

private theorem sp3300 : smallValid 3300 61 := by unfold smallValid; decide +kernel

private theorem sp3361 : smallValid 3361 62 := by unfold smallValid; decide +kernel

private theorem sp3423 : smallValid 3423 61 := by unfold smallValid; decide +kernel

private theorem sp3484 : smallValid 3484 61 := by unfold smallValid; decide +kernel

private theorem sp3545 : smallValid 3545 61 := by unfold smallValid; decide +kernel

private theorem sp3606 : smallValid 3606 62 := by unfold smallValid; decide +kernel

private theorem sp3668 : smallValid 3668 61 := by unfold smallValid; decide +kernel

private theorem sp3729 : smallValid 3729 61 := by unfold smallValid; decide +kernel

private theorem sp3790 : smallValid 3790 61 := by unfold smallValid; decide +kernel

private theorem sp3851 : smallValid 3851 62 := by unfold smallValid; decide +kernel

private theorem sp3913 : smallValid 3913 61 := by unfold smallValid; decide +kernel

private theorem sp3974 : smallValid 3974 61 := by unfold smallValid; decide +kernel

private theorem sp4035 : smallValid 4035 61 := by unfold smallValid; decide +kernel

private theorem sp4096 : smallValid 4096 61 := by unfold smallValid; decide +kernel

private theorem sp4157 : smallValid 4157 61 := by unfold smallValid; decide +kernel

private theorem sp4218 : smallValid 4218 61 := by unfold smallValid; decide +kernel

private theorem sp4279 : smallValid 4279 61 := by unfold smallValid; decide +kernel

private theorem sp4340 : smallValid 4340 62 := by unfold smallValid; decide +kernel

private theorem sp4402 : smallValid 4402 61 := by unfold smallValid; decide +kernel

private theorem sp4463 : smallValid 4463 61 := by unfold smallValid; decide +kernel

private theorem sp4524 : smallValid 4524 61 := by unfold smallValid; decide +kernel

private theorem sp4585 : smallValid 4585 61 := by unfold smallValid; decide +kernel

private theorem sp4646 : smallValid 4646 61 := by unfold smallValid; decide +kernel

private theorem sp4707 : smallValid 4707 61 := by unfold smallValid; decide +kernel

private theorem sp4768 : smallValid 4768 61 := by unfold smallValid; decide +kernel

private theorem sp4829 : smallValid 4829 62 := by unfold smallValid; decide +kernel

private theorem sp4891 : smallValid 4891 61 := by unfold smallValid; decide +kernel

private theorem sp4952 : smallValid 4952 61 := by unfold smallValid; decide +kernel

private theorem sp5013 : smallValid 5013 61 := by unfold smallValid; decide +kernel

private theorem sp5074 : smallValid 5074 61 := by unfold smallValid; decide +kernel

private theorem sp5135 : smallValid 5135 61 := by unfold smallValid; decide +kernel

private theorem sp5196 : smallValid 5196 61 := by unfold smallValid; decide +kernel

private theorem sp5257 : smallValid 5257 61 := by unfold smallValid; decide +kernel

private theorem sp5318 : smallValid 5318 62 := by unfold smallValid; decide +kernel

private theorem sp5380 : smallValid 5380 61 := by unfold smallValid; decide +kernel

private theorem sp5441 : smallValid 5441 61 := by unfold smallValid; decide +kernel

private theorem sp5502 : smallValid 5502 61 := by unfold smallValid; decide +kernel

private theorem sp5563 : smallValid 5563 61 := by unfold smallValid; decide +kernel

private theorem sp5624 : smallValid 5624 61 := by unfold smallValid; decide +kernel

private theorem sp5685 : smallValid 5685 61 := by unfold smallValid; decide +kernel

private theorem sp5746 : smallValid 5746 61 := by unfold smallValid; decide +kernel

private theorem sp5807 : smallValid 5807 62 := by unfold smallValid; decide +kernel

private theorem sp5869 : smallValid 5869 61 := by unfold smallValid; decide +kernel

private theorem sp5930 : smallValid 5930 61 := by unfold smallValid; decide +kernel

private theorem sp5991 : smallValid 5991 61 := by unfold smallValid; decide +kernel

private theorem sp6052 : smallValid 6052 61 := by unfold smallValid; decide +kernel

private theorem sp6113 : smallValid 6113 61 := by unfold smallValid; decide +kernel

private theorem sp6174 : smallValid 6174 61 := by unfold smallValid; decide +kernel

private theorem sp6235 : smallValid 6235 61 := by unfold smallValid; decide +kernel

private theorem sp6296 : smallValid 6296 62 := by unfold smallValid; decide +kernel

private theorem sp6358 : smallValid 6358 61 := by unfold smallValid; decide +kernel

private theorem sp6419 : smallValid 6419 61 := by unfold smallValid; decide +kernel

private theorem sp6480 : smallValid 6480 61 := by unfold smallValid; decide +kernel

private theorem sp6541 : smallValid 6541 61 := by unfold smallValid; decide +kernel

private theorem sp6602 : smallValid 6602 61 := by unfold smallValid; decide +kernel

private theorem sp6663 : smallValid 6663 61 := by unfold smallValid; decide +kernel

private theorem sp6724 : smallValid 6724 61 := by unfold smallValid; decide +kernel

private theorem sp6785 : smallValid 6785 62 := by unfold smallValid; decide +kernel

private theorem sp6847 : smallValid 6847 61 := by unfold smallValid; decide +kernel

private theorem sp6908 : smallValid 6908 61 := by unfold smallValid; decide +kernel

private theorem sp6969 : smallValid 6969 61 := by unfold smallValid; decide +kernel

private theorem sp7030 : smallValid 7030 61 := by unfold smallValid; decide +kernel

private theorem sp7091 : smallValid 7091 61 := by unfold smallValid; decide +kernel

private theorem sp7152 : smallValid 7152 61 := by unfold smallValid; decide +kernel

private theorem sp7213 : smallValid 7213 61 := by unfold smallValid; decide +kernel

private theorem sp7274 : smallValid 7274 62 := by unfold smallValid; decide +kernel

private theorem sp7336 : smallValid 7336 61 := by unfold smallValid; decide +kernel

private theorem sp7397 : smallValid 7397 61 := by unfold smallValid; decide +kernel

private theorem sp7458 : smallValid 7458 61 := by unfold smallValid; decide +kernel

private theorem sp7519 : smallValid 7519 62 := by unfold smallValid; decide +kernel

private theorem sp7581 : smallValid 7581 61 := by unfold smallValid; decide +kernel

private theorem sp7642 : smallValid 7642 61 := by unfold smallValid; decide +kernel

private theorem sp7703 : smallValid 7703 61 := by unfold smallValid; decide +kernel

private theorem sp7764 : smallValid 7764 62 := by unfold smallValid; decide +kernel

private theorem sp7826 : smallValid 7826 61 := by unfold smallValid; decide +kernel

private theorem sp7887 : smallValid 7887 61 := by unfold smallValid; decide +kernel

private theorem sp7948 : smallValid 7948 61 := by unfold smallValid; decide +kernel

private theorem sp8009 : smallValid 8009 61 := by unfold smallValid; decide +kernel

private theorem sp8070 : smallValid 8070 61 := by unfold smallValid; decide +kernel

private theorem sp8131 : smallValid 8131 61 := by unfold smallValid; decide +kernel

private theorem sp8192 : smallValid 8192 61 := by unfold smallValid; decide +kernel

private theorem sp8253 : smallValid 8253 62 := by unfold smallValid; decide +kernel

private theorem sp8315 : smallValid 8315 61 := by unfold smallValid; decide +kernel

private theorem sp8376 : smallValid 8376 61 := by unfold smallValid; decide +kernel

private theorem sp8437 : smallValid 8437 61 := by unfold smallValid; decide +kernel

private theorem sp8498 : smallValid 8498 61 := by unfold smallValid; decide +kernel

private theorem sp8559 : smallValid 8559 61 := by unfold smallValid; decide +kernel

private theorem sp8620 : smallValid 8620 61 := by unfold smallValid; decide +kernel

private theorem sp8681 : smallValid 8681 61 := by unfold smallValid; decide +kernel

private theorem sp8742 : smallValid 8742 62 := by unfold smallValid; decide +kernel

private theorem sp8804 : smallValid 8804 61 := by unfold smallValid; decide +kernel

private theorem sp8865 : smallValid 8865 61 := by unfold smallValid; decide +kernel

private theorem sp8926 : smallValid 8926 61 := by unfold smallValid; decide +kernel

private theorem sp8987 : smallValid 8987 61 := by unfold smallValid; decide +kernel

private theorem sp9048 : smallValid 9048 61 := by unfold smallValid; decide +kernel

private theorem sp9109 : smallValid 9109 61 := by unfold smallValid; decide +kernel

private theorem sp9170 : smallValid 9170 61 := by unfold smallValid; decide +kernel

private theorem sp9231 : smallValid 9231 62 := by unfold smallValid; decide +kernel

private theorem sp9293 : smallValid 9293 61 := by unfold smallValid; decide +kernel

private theorem sp9354 : smallValid 9354 61 := by unfold smallValid; decide +kernel

private theorem sp9415 : smallValid 9415 61 := by unfold smallValid; decide +kernel

private theorem sp9476 : smallValid 9476 61 := by unfold smallValid; decide +kernel

private theorem sp9537 : smallValid 9537 61 := by unfold smallValid; decide +kernel

private theorem sp9598 : smallValid 9598 61 := by unfold smallValid; decide +kernel

private theorem sp9659 : smallValid 9659 61 := by unfold smallValid; decide +kernel

private theorem sp9720 : smallValid 9720 62 := by unfold smallValid; decide +kernel

private theorem sp9782 : smallValid 9782 61 := by unfold smallValid; decide +kernel

private theorem sp9843 : smallValid 9843 61 := by unfold smallValid; decide +kernel

private theorem sp9904 : smallValid 9904 61 := by unfold smallValid; decide +kernel

private theorem sp9965 : smallValid 9965 61 := by unfold smallValid; decide +kernel

private theorem sp10026 : smallValid 10026 61 := by unfold smallValid; decide +kernel

private theorem sp10087 : smallValid 10087 61 := by unfold smallValid; decide +kernel

private theorem sp10148 : smallValid 10148 61 := by unfold smallValid; decide +kernel

private theorem sp10209 : smallValid 10209 62 := by unfold smallValid; decide +kernel

private theorem sp10271 : smallValid 10271 61 := by unfold smallValid; decide +kernel

private theorem sp10332 : smallValid 10332 61 := by unfold smallValid; decide +kernel

private theorem sp10393 : smallValid 10393 61 := by unfold smallValid; decide +kernel

private theorem sp10454 : smallValid 10454 61 := by unfold smallValid; decide +kernel

private theorem sp10515 : smallValid 10515 61 := by unfold smallValid; decide +kernel

private theorem sp10576 : smallValid 10576 61 := by unfold smallValid; decide +kernel

private theorem sp10637 : smallValid 10637 61 := by unfold smallValid; decide +kernel

private theorem sp10698 : smallValid 10698 62 := by unfold smallValid; decide +kernel

private theorem sp10760 : smallValid 10760 61 := by unfold smallValid; decide +kernel

private theorem sp10821 : smallValid 10821 61 := by unfold smallValid; decide +kernel

private theorem sp10882 : smallValid 10882 61 := by unfold smallValid; decide +kernel

private theorem sp10943 : smallValid 10943 61 := by unfold smallValid; decide +kernel

private theorem sp11004 : smallValid 11004 61 := by unfold smallValid; decide +kernel

private theorem sp11065 : smallValid 11065 61 := by unfold smallValid; decide +kernel

private theorem sp11126 : smallValid 11126 61 := by unfold smallValid; decide +kernel

private theorem sp11187 : smallValid 11187 62 := by unfold smallValid; decide +kernel

private theorem sp11249 : smallValid 11249 61 := by unfold smallValid; decide +kernel

private theorem sp11310 : smallValid 11310 61 := by unfold smallValid; decide +kernel

private theorem sp11371 : smallValid 11371 61 := by unfold smallValid; decide +kernel

private theorem sp11432 : smallValid 11432 62 := by unfold smallValid; decide +kernel

private theorem sp11494 : smallValid 11494 61 := by unfold smallValid; decide +kernel

private theorem sp11555 : smallValid 11555 61 := by unfold smallValid; decide +kernel

private theorem sp11616 : smallValid 11616 61 := by unfold smallValid; decide +kernel

private theorem sp11677 : smallValid 11677 62 := by unfold smallValid; decide +kernel

private theorem sp11739 : smallValid 11739 61 := by unfold smallValid; decide +kernel

private theorem sp11800 : smallValid 11800 61 := by unfold smallValid; decide +kernel

private theorem sp11861 : smallValid 11861 61 := by unfold smallValid; decide +kernel

private theorem sp11922 : smallValid 11922 61 := by unfold smallValid; decide +kernel

private theorem sp11983 : smallValid 11983 61 := by unfold smallValid; decide +kernel

private theorem sp12044 : smallValid 12044 61 := by unfold smallValid; decide +kernel

private theorem sp12105 : smallValid 12105 61 := by unfold smallValid; decide +kernel

private theorem sp12166 : smallValid 12166 62 := by unfold smallValid; decide +kernel

private theorem sp12228 : smallValid 12228 61 := by unfold smallValid; decide +kernel

private theorem sp12289 : smallValid 12289 61 := by unfold smallValid; decide +kernel

private theorem sp12350 : smallValid 12350 61 := by unfold smallValid; decide +kernel

private theorem sp12411 : smallValid 12411 61 := by unfold smallValid; decide +kernel

private theorem sp12472 : smallValid 12472 61 := by unfold smallValid; decide +kernel

private theorem sp12533 : smallValid 12533 61 := by unfold smallValid; decide +kernel

private theorem sp12594 : smallValid 12594 61 := by unfold smallValid; decide +kernel

private theorem sp12655 : smallValid 12655 62 := by unfold smallValid; decide +kernel

private theorem sp12717 : smallValid 12717 61 := by unfold smallValid; decide +kernel

private theorem sp12778 : smallValid 12778 61 := by unfold smallValid; decide +kernel

private theorem sp12839 : smallValid 12839 61 := by unfold smallValid; decide +kernel

private theorem sp12900 : smallValid 12900 61 := by unfold smallValid; decide +kernel

private theorem sp12961 : smallValid 12961 61 := by unfold smallValid; decide +kernel

private theorem sp13022 : smallValid 13022 61 := by unfold smallValid; decide +kernel

private theorem sp13083 : smallValid 13083 61 := by unfold smallValid; decide +kernel

private theorem sp13144 : smallValid 13144 62 := by unfold smallValid; decide +kernel

private theorem sp13206 : smallValid 13206 61 := by unfold smallValid; decide +kernel

private theorem sp13267 : smallValid 13267 61 := by unfold smallValid; decide +kernel

private theorem sp13328 : smallValid 13328 61 := by unfold smallValid; decide +kernel

private theorem sp13389 : smallValid 13389 62 := by unfold smallValid; decide +kernel

private theorem sp13451 : smallValid 13451 61 := by unfold smallValid; decide +kernel

private theorem sp13512 : smallValid 13512 61 := by unfold smallValid; decide +kernel

private theorem sp13573 : smallValid 13573 61 := by unfold smallValid; decide +kernel

private theorem sp13634 : smallValid 13634 62 := by unfold smallValid; decide +kernel

private theorem sp13696 : smallValid 13696 61 := by unfold smallValid; decide +kernel

private theorem sp13757 : smallValid 13757 61 := by unfold smallValid; decide +kernel

private theorem sp13818 : smallValid 13818 61 := by unfold smallValid; decide +kernel

private theorem sp13879 : smallValid 13879 61 := by unfold smallValid; decide +kernel

private theorem sp13940 : smallValid 13940 61 := by unfold smallValid; decide +kernel

private theorem sp14001 : smallValid 14001 61 := by unfold smallValid; decide +kernel

private theorem sp14062 : smallValid 14062 61 := by unfold smallValid; decide +kernel

private theorem sp14123 : smallValid 14123 62 := by unfold smallValid; decide +kernel

private theorem sp14185 : smallValid 14185 61 := by unfold smallValid; decide +kernel

private theorem sp14246 : smallValid 14246 61 := by unfold smallValid; decide +kernel

private theorem sp14307 : smallValid 14307 61 := by unfold smallValid; decide +kernel

private theorem sp14368 : smallValid 14368 61 := by unfold smallValid; decide +kernel

private theorem sp14429 : smallValid 14429 61 := by unfold smallValid; decide +kernel

private theorem sp14490 : smallValid 14490 61 := by unfold smallValid; decide +kernel

private theorem sp14551 : smallValid 14551 61 := by unfold smallValid; decide +kernel

private theorem sp14612 : smallValid 14612 62 := by unfold smallValid; decide +kernel

private theorem sp14674 : smallValid 14674 61 := by unfold smallValid; decide +kernel

private theorem sp14735 : smallValid 14735 61 := by unfold smallValid; decide +kernel

private theorem sp14796 : smallValid 14796 61 := by unfold smallValid; decide +kernel

private theorem sp14857 : smallValid 14857 61 := by unfold smallValid; decide +kernel

private theorem sp14918 : smallValid 14918 61 := by unfold smallValid; decide +kernel

private theorem sp14979 : smallValid 14979 61 := by unfold smallValid; decide +kernel

private theorem sp15040 : smallValid 15040 61 := by unfold smallValid; decide +kernel

private theorem sp15101 : smallValid 15101 62 := by unfold smallValid; decide +kernel

private theorem sp15163 : smallValid 15163 61 := by unfold smallValid; decide +kernel

private theorem sp15224 : smallValid 15224 61 := by unfold smallValid; decide +kernel

private theorem sp15285 : smallValid 15285 61 := by unfold smallValid; decide +kernel

private theorem sp15346 : smallValid 15346 62 := by unfold smallValid; decide +kernel

private theorem sp15408 : smallValid 15408 61 := by unfold smallValid; decide +kernel

private theorem sp15469 : smallValid 15469 61 := by unfold smallValid; decide +kernel

private theorem sp15530 : smallValid 15530 61 := by unfold smallValid; decide +kernel

private theorem sp15591 : smallValid 15591 62 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤15652) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 15653 := (joinSmall (lo:=0) (a:=7826) (b:=7827) (joinSmall (lo:=0) (a:=3913) (b:=3913) (joinSmall (lo:=0) (a:=1956) (b:=1957) (joinSmall (lo:=0) (a:=978) (b:=978) (joinSmall (lo:=0) (a:=489) (b:=489) (joinSmall (lo:=0) (a:=244) (b:=245) (joinSmall (lo:=0) (a:=122) (b:=122) (joinSmall (lo:=0) (a:=61) (b:=61) sp0 sp61) (joinSmall (lo:=122) (a:=61) (b:=61) sp122 sp183)) (joinSmall (lo:=244) (a:=122) (b:=123) (joinSmall (lo:=244) (a:=61) (b:=61) sp244 sp305) (joinSmall (lo:=366) (a:=61) (b:=62) sp366 sp427))) (joinSmall (lo:=489) (a:=244) (b:=245) (joinSmall (lo:=489) (a:=122) (b:=122) (joinSmall (lo:=489) (a:=61) (b:=61) sp489 sp550) (joinSmall (lo:=611) (a:=61) (b:=61) sp611 sp672)) (joinSmall (lo:=733) (a:=122) (b:=123) (joinSmall (lo:=733) (a:=61) (b:=61) sp733 sp794) (joinSmall (lo:=855) (a:=61) (b:=62) sp855 sp916)))) (joinSmall (lo:=978) (a:=489) (b:=489) (joinSmall (lo:=978) (a:=244) (b:=245) (joinSmall (lo:=978) (a:=122) (b:=122) (joinSmall (lo:=978) (a:=61) (b:=61) sp978 sp1039) (joinSmall (lo:=1100) (a:=61) (b:=61) sp1100 sp1161)) (joinSmall (lo:=1222) (a:=122) (b:=123) (joinSmall (lo:=1222) (a:=61) (b:=61) sp1222 sp1283) (joinSmall (lo:=1344) (a:=61) (b:=62) sp1344 sp1405))) (joinSmall (lo:=1467) (a:=244) (b:=245) (joinSmall (lo:=1467) (a:=122) (b:=122) (joinSmall (lo:=1467) (a:=61) (b:=61) sp1467 sp1528) (joinSmall (lo:=1589) (a:=61) (b:=61) sp1589 sp1650)) (joinSmall (lo:=1711) (a:=122) (b:=123) (joinSmall (lo:=1711) (a:=61) (b:=61) sp1711 sp1772) (joinSmall (lo:=1833) (a:=61) (b:=62) sp1833 sp1894))))) (joinSmall (lo:=1956) (a:=978) (b:=979) (joinSmall (lo:=1956) (a:=489) (b:=489) (joinSmall (lo:=1956) (a:=244) (b:=245) (joinSmall (lo:=1956) (a:=122) (b:=122) (joinSmall (lo:=1956) (a:=61) (b:=61) sp1956 sp2017) (joinSmall (lo:=2078) (a:=61) (b:=61) sp2078 sp2139)) (joinSmall (lo:=2200) (a:=122) (b:=123) (joinSmall (lo:=2200) (a:=61) (b:=61) sp2200 sp2261) (joinSmall (lo:=2322) (a:=61) (b:=62) sp2322 sp2383))) (joinSmall (lo:=2445) (a:=244) (b:=245) (joinSmall (lo:=2445) (a:=122) (b:=122) (joinSmall (lo:=2445) (a:=61) (b:=61) sp2445 sp2506) (joinSmall (lo:=2567) (a:=61) (b:=61) sp2567 sp2628)) (joinSmall (lo:=2689) (a:=122) (b:=123) (joinSmall (lo:=2689) (a:=61) (b:=61) sp2689 sp2750) (joinSmall (lo:=2811) (a:=61) (b:=62) sp2811 sp2872)))) (joinSmall (lo:=2934) (a:=489) (b:=490) (joinSmall (lo:=2934) (a:=244) (b:=245) (joinSmall (lo:=2934) (a:=122) (b:=122) (joinSmall (lo:=2934) (a:=61) (b:=61) sp2934 sp2995) (joinSmall (lo:=3056) (a:=61) (b:=61) sp3056 sp3117)) (joinSmall (lo:=3178) (a:=122) (b:=123) (joinSmall (lo:=3178) (a:=61) (b:=61) sp3178 sp3239) (joinSmall (lo:=3300) (a:=61) (b:=62) sp3300 sp3361))) (joinSmall (lo:=3423) (a:=245) (b:=245) (joinSmall (lo:=3423) (a:=122) (b:=123) (joinSmall (lo:=3423) (a:=61) (b:=61) sp3423 sp3484) (joinSmall (lo:=3545) (a:=61) (b:=62) sp3545 sp3606)) (joinSmall (lo:=3668) (a:=122) (b:=123) (joinSmall (lo:=3668) (a:=61) (b:=61) sp3668 sp3729) (joinSmall (lo:=3790) (a:=61) (b:=62) sp3790 sp3851)))))) (joinSmall (lo:=3913) (a:=1956) (b:=1957) (joinSmall (lo:=3913) (a:=978) (b:=978) (joinSmall (lo:=3913) (a:=489) (b:=489) (joinSmall (lo:=3913) (a:=244) (b:=245) (joinSmall (lo:=3913) (a:=122) (b:=122) (joinSmall (lo:=3913) (a:=61) (b:=61) sp3913 sp3974) (joinSmall (lo:=4035) (a:=61) (b:=61) sp4035 sp4096)) (joinSmall (lo:=4157) (a:=122) (b:=123) (joinSmall (lo:=4157) (a:=61) (b:=61) sp4157 sp4218) (joinSmall (lo:=4279) (a:=61) (b:=62) sp4279 sp4340))) (joinSmall (lo:=4402) (a:=244) (b:=245) (joinSmall (lo:=4402) (a:=122) (b:=122) (joinSmall (lo:=4402) (a:=61) (b:=61) sp4402 sp4463) (joinSmall (lo:=4524) (a:=61) (b:=61) sp4524 sp4585)) (joinSmall (lo:=4646) (a:=122) (b:=123) (joinSmall (lo:=4646) (a:=61) (b:=61) sp4646 sp4707) (joinSmall (lo:=4768) (a:=61) (b:=62) sp4768 sp4829)))) (joinSmall (lo:=4891) (a:=489) (b:=489) (joinSmall (lo:=4891) (a:=244) (b:=245) (joinSmall (lo:=4891) (a:=122) (b:=122) (joinSmall (lo:=4891) (a:=61) (b:=61) sp4891 sp4952) (joinSmall (lo:=5013) (a:=61) (b:=61) sp5013 sp5074)) (joinSmall (lo:=5135) (a:=122) (b:=123) (joinSmall (lo:=5135) (a:=61) (b:=61) sp5135 sp5196) (joinSmall (lo:=5257) (a:=61) (b:=62) sp5257 sp5318))) (joinSmall (lo:=5380) (a:=244) (b:=245) (joinSmall (lo:=5380) (a:=122) (b:=122) (joinSmall (lo:=5380) (a:=61) (b:=61) sp5380 sp5441) (joinSmall (lo:=5502) (a:=61) (b:=61) sp5502 sp5563)) (joinSmall (lo:=5624) (a:=122) (b:=123) (joinSmall (lo:=5624) (a:=61) (b:=61) sp5624 sp5685) (joinSmall (lo:=5746) (a:=61) (b:=62) sp5746 sp5807))))) (joinSmall (lo:=5869) (a:=978) (b:=979) (joinSmall (lo:=5869) (a:=489) (b:=489) (joinSmall (lo:=5869) (a:=244) (b:=245) (joinSmall (lo:=5869) (a:=122) (b:=122) (joinSmall (lo:=5869) (a:=61) (b:=61) sp5869 sp5930) (joinSmall (lo:=5991) (a:=61) (b:=61) sp5991 sp6052)) (joinSmall (lo:=6113) (a:=122) (b:=123) (joinSmall (lo:=6113) (a:=61) (b:=61) sp6113 sp6174) (joinSmall (lo:=6235) (a:=61) (b:=62) sp6235 sp6296))) (joinSmall (lo:=6358) (a:=244) (b:=245) (joinSmall (lo:=6358) (a:=122) (b:=122) (joinSmall (lo:=6358) (a:=61) (b:=61) sp6358 sp6419) (joinSmall (lo:=6480) (a:=61) (b:=61) sp6480 sp6541)) (joinSmall (lo:=6602) (a:=122) (b:=123) (joinSmall (lo:=6602) (a:=61) (b:=61) sp6602 sp6663) (joinSmall (lo:=6724) (a:=61) (b:=62) sp6724 sp6785)))) (joinSmall (lo:=6847) (a:=489) (b:=490) (joinSmall (lo:=6847) (a:=244) (b:=245) (joinSmall (lo:=6847) (a:=122) (b:=122) (joinSmall (lo:=6847) (a:=61) (b:=61) sp6847 sp6908) (joinSmall (lo:=6969) (a:=61) (b:=61) sp6969 sp7030)) (joinSmall (lo:=7091) (a:=122) (b:=123) (joinSmall (lo:=7091) (a:=61) (b:=61) sp7091 sp7152) (joinSmall (lo:=7213) (a:=61) (b:=62) sp7213 sp7274))) (joinSmall (lo:=7336) (a:=245) (b:=245) (joinSmall (lo:=7336) (a:=122) (b:=123) (joinSmall (lo:=7336) (a:=61) (b:=61) sp7336 sp7397) (joinSmall (lo:=7458) (a:=61) (b:=62) sp7458 sp7519)) (joinSmall (lo:=7581) (a:=122) (b:=123) (joinSmall (lo:=7581) (a:=61) (b:=61) sp7581 sp7642) (joinSmall (lo:=7703) (a:=61) (b:=62) sp7703 sp7764))))))) (joinSmall (lo:=7826) (a:=3913) (b:=3914) (joinSmall (lo:=7826) (a:=1956) (b:=1957) (joinSmall (lo:=7826) (a:=978) (b:=978) (joinSmall (lo:=7826) (a:=489) (b:=489) (joinSmall (lo:=7826) (a:=244) (b:=245) (joinSmall (lo:=7826) (a:=122) (b:=122) (joinSmall (lo:=7826) (a:=61) (b:=61) sp7826 sp7887) (joinSmall (lo:=7948) (a:=61) (b:=61) sp7948 sp8009)) (joinSmall (lo:=8070) (a:=122) (b:=123) (joinSmall (lo:=8070) (a:=61) (b:=61) sp8070 sp8131) (joinSmall (lo:=8192) (a:=61) (b:=62) sp8192 sp8253))) (joinSmall (lo:=8315) (a:=244) (b:=245) (joinSmall (lo:=8315) (a:=122) (b:=122) (joinSmall (lo:=8315) (a:=61) (b:=61) sp8315 sp8376) (joinSmall (lo:=8437) (a:=61) (b:=61) sp8437 sp8498)) (joinSmall (lo:=8559) (a:=122) (b:=123) (joinSmall (lo:=8559) (a:=61) (b:=61) sp8559 sp8620) (joinSmall (lo:=8681) (a:=61) (b:=62) sp8681 sp8742)))) (joinSmall (lo:=8804) (a:=489) (b:=489) (joinSmall (lo:=8804) (a:=244) (b:=245) (joinSmall (lo:=8804) (a:=122) (b:=122) (joinSmall (lo:=8804) (a:=61) (b:=61) sp8804 sp8865) (joinSmall (lo:=8926) (a:=61) (b:=61) sp8926 sp8987)) (joinSmall (lo:=9048) (a:=122) (b:=123) (joinSmall (lo:=9048) (a:=61) (b:=61) sp9048 sp9109) (joinSmall (lo:=9170) (a:=61) (b:=62) sp9170 sp9231))) (joinSmall (lo:=9293) (a:=244) (b:=245) (joinSmall (lo:=9293) (a:=122) (b:=122) (joinSmall (lo:=9293) (a:=61) (b:=61) sp9293 sp9354) (joinSmall (lo:=9415) (a:=61) (b:=61) sp9415 sp9476)) (joinSmall (lo:=9537) (a:=122) (b:=123) (joinSmall (lo:=9537) (a:=61) (b:=61) sp9537 sp9598) (joinSmall (lo:=9659) (a:=61) (b:=62) sp9659 sp9720))))) (joinSmall (lo:=9782) (a:=978) (b:=979) (joinSmall (lo:=9782) (a:=489) (b:=489) (joinSmall (lo:=9782) (a:=244) (b:=245) (joinSmall (lo:=9782) (a:=122) (b:=122) (joinSmall (lo:=9782) (a:=61) (b:=61) sp9782 sp9843) (joinSmall (lo:=9904) (a:=61) (b:=61) sp9904 sp9965)) (joinSmall (lo:=10026) (a:=122) (b:=123) (joinSmall (lo:=10026) (a:=61) (b:=61) sp10026 sp10087) (joinSmall (lo:=10148) (a:=61) (b:=62) sp10148 sp10209))) (joinSmall (lo:=10271) (a:=244) (b:=245) (joinSmall (lo:=10271) (a:=122) (b:=122) (joinSmall (lo:=10271) (a:=61) (b:=61) sp10271 sp10332) (joinSmall (lo:=10393) (a:=61) (b:=61) sp10393 sp10454)) (joinSmall (lo:=10515) (a:=122) (b:=123) (joinSmall (lo:=10515) (a:=61) (b:=61) sp10515 sp10576) (joinSmall (lo:=10637) (a:=61) (b:=62) sp10637 sp10698)))) (joinSmall (lo:=10760) (a:=489) (b:=490) (joinSmall (lo:=10760) (a:=244) (b:=245) (joinSmall (lo:=10760) (a:=122) (b:=122) (joinSmall (lo:=10760) (a:=61) (b:=61) sp10760 sp10821) (joinSmall (lo:=10882) (a:=61) (b:=61) sp10882 sp10943)) (joinSmall (lo:=11004) (a:=122) (b:=123) (joinSmall (lo:=11004) (a:=61) (b:=61) sp11004 sp11065) (joinSmall (lo:=11126) (a:=61) (b:=62) sp11126 sp11187))) (joinSmall (lo:=11249) (a:=245) (b:=245) (joinSmall (lo:=11249) (a:=122) (b:=123) (joinSmall (lo:=11249) (a:=61) (b:=61) sp11249 sp11310) (joinSmall (lo:=11371) (a:=61) (b:=62) sp11371 sp11432)) (joinSmall (lo:=11494) (a:=122) (b:=123) (joinSmall (lo:=11494) (a:=61) (b:=61) sp11494 sp11555) (joinSmall (lo:=11616) (a:=61) (b:=62) sp11616 sp11677)))))) (joinSmall (lo:=11739) (a:=1957) (b:=1957) (joinSmall (lo:=11739) (a:=978) (b:=979) (joinSmall (lo:=11739) (a:=489) (b:=489) (joinSmall (lo:=11739) (a:=244) (b:=245) (joinSmall (lo:=11739) (a:=122) (b:=122) (joinSmall (lo:=11739) (a:=61) (b:=61) sp11739 sp11800) (joinSmall (lo:=11861) (a:=61) (b:=61) sp11861 sp11922)) (joinSmall (lo:=11983) (a:=122) (b:=123) (joinSmall (lo:=11983) (a:=61) (b:=61) sp11983 sp12044) (joinSmall (lo:=12105) (a:=61) (b:=62) sp12105 sp12166))) (joinSmall (lo:=12228) (a:=244) (b:=245) (joinSmall (lo:=12228) (a:=122) (b:=122) (joinSmall (lo:=12228) (a:=61) (b:=61) sp12228 sp12289) (joinSmall (lo:=12350) (a:=61) (b:=61) sp12350 sp12411)) (joinSmall (lo:=12472) (a:=122) (b:=123) (joinSmall (lo:=12472) (a:=61) (b:=61) sp12472 sp12533) (joinSmall (lo:=12594) (a:=61) (b:=62) sp12594 sp12655)))) (joinSmall (lo:=12717) (a:=489) (b:=490) (joinSmall (lo:=12717) (a:=244) (b:=245) (joinSmall (lo:=12717) (a:=122) (b:=122) (joinSmall (lo:=12717) (a:=61) (b:=61) sp12717 sp12778) (joinSmall (lo:=12839) (a:=61) (b:=61) sp12839 sp12900)) (joinSmall (lo:=12961) (a:=122) (b:=123) (joinSmall (lo:=12961) (a:=61) (b:=61) sp12961 sp13022) (joinSmall (lo:=13083) (a:=61) (b:=62) sp13083 sp13144))) (joinSmall (lo:=13206) (a:=245) (b:=245) (joinSmall (lo:=13206) (a:=122) (b:=123) (joinSmall (lo:=13206) (a:=61) (b:=61) sp13206 sp13267) (joinSmall (lo:=13328) (a:=61) (b:=62) sp13328 sp13389)) (joinSmall (lo:=13451) (a:=122) (b:=123) (joinSmall (lo:=13451) (a:=61) (b:=61) sp13451 sp13512) (joinSmall (lo:=13573) (a:=61) (b:=62) sp13573 sp13634))))) (joinSmall (lo:=13696) (a:=978) (b:=979) (joinSmall (lo:=13696) (a:=489) (b:=489) (joinSmall (lo:=13696) (a:=244) (b:=245) (joinSmall (lo:=13696) (a:=122) (b:=122) (joinSmall (lo:=13696) (a:=61) (b:=61) sp13696 sp13757) (joinSmall (lo:=13818) (a:=61) (b:=61) sp13818 sp13879)) (joinSmall (lo:=13940) (a:=122) (b:=123) (joinSmall (lo:=13940) (a:=61) (b:=61) sp13940 sp14001) (joinSmall (lo:=14062) (a:=61) (b:=62) sp14062 sp14123))) (joinSmall (lo:=14185) (a:=244) (b:=245) (joinSmall (lo:=14185) (a:=122) (b:=122) (joinSmall (lo:=14185) (a:=61) (b:=61) sp14185 sp14246) (joinSmall (lo:=14307) (a:=61) (b:=61) sp14307 sp14368)) (joinSmall (lo:=14429) (a:=122) (b:=123) (joinSmall (lo:=14429) (a:=61) (b:=61) sp14429 sp14490) (joinSmall (lo:=14551) (a:=61) (b:=62) sp14551 sp14612)))) (joinSmall (lo:=14674) (a:=489) (b:=490) (joinSmall (lo:=14674) (a:=244) (b:=245) (joinSmall (lo:=14674) (a:=122) (b:=122) (joinSmall (lo:=14674) (a:=61) (b:=61) sp14674 sp14735) (joinSmall (lo:=14796) (a:=61) (b:=61) sp14796 sp14857)) (joinSmall (lo:=14918) (a:=122) (b:=123) (joinSmall (lo:=14918) (a:=61) (b:=61) sp14918 sp14979) (joinSmall (lo:=15040) (a:=61) (b:=62) sp15040 sp15101))) (joinSmall (lo:=15163) (a:=245) (b:=245) (joinSmall (lo:=15163) (a:=122) (b:=123) (joinSmall (lo:=15163) (a:=61) (b:=61) sp15163 sp15224) (joinSmall (lo:=15285) (a:=61) (b:=62) sp15285 sp15346)) (joinSmall (lo:=15408) (a:=122) (b:=123) (joinSmall (lo:=15408) (a:=61) (b:=61) sp15408 sp15469) (joinSmall (lo:=15530) (a:=61) (b:=62) sp15530 sp15591))))))))
  have good : (List.range 15653).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 245000000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 15652 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 15652 := by
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


private def packet (i : ℕ) : ℕ := (if i < 62 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 5 then (if i < 4 then 0 else 0) else (if i < 6 then 0 else 0))) else (if i < 11 then (if i < 9 then (if i < 8 then 0 else 0) else (if i < 10 then 0 else 0)) else (if i < 13 then (if i < 12 then 0 else 0) else (if i < 14 then 0 else 0)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0 else 0) else (if i < 18 then 0 else 0)) else (if i < 21 then (if i < 20 then 0 else 0) else (if i < 22 then 0 else 0))) else (if i < 27 then (if i < 25 then (if i < 24 then 0 else 0) else (if i < 26 then 0 else 0)) else (if i < 29 then (if i < 28 then 0 else 0) else (if i < 30 then 0 else 0))))) else (if i < 46 then (if i < 38 then (if i < 34 then (if i < 32 then 0 else (if i < 33 then 0 else 0)) else (if i < 36 then (if i < 35 then 0 else 0) else (if i < 37 then 0 else 0))) else (if i < 42 then (if i < 40 then (if i < 39 then 0 else 0) else (if i < 41 then 0 else 0)) else (if i < 44 then (if i < 43 then 0 else 0) else (if i < 45 then 0 else 0)))) else (if i < 54 then (if i < 50 then (if i < 48 then (if i < 47 then 0 else 0) else (if i < 49 then 0 else 0)) else (if i < 52 then (if i < 51 then 0 else 0) else (if i < 53 then 0 else 0))) else (if i < 58 then (if i < 56 then (if i < 55 then 0 else 0) else (if i < 57 then 0 else 0)) else (if i < 60 then (if i < 59 then 0 else 0) else (if i < 61 then 0 else 0)))))) else (if i < 93 then (if i < 77 then (if i < 69 then (if i < 65 then (if i < 63 then 0 else (if i < 64 then 0 else 0)) else (if i < 67 then (if i < 66 then 0 else 0) else (if i < 68 then 0 else 0))) else (if i < 73 then (if i < 71 then (if i < 70 then 0 else 0) else (if i < 72 then 0 else 0)) else (if i < 75 then (if i < 74 then 0 else 0) else (if i < 76 then 0 else 0)))) else (if i < 85 then (if i < 81 then (if i < 79 then (if i < 78 then 0 else 0) else (if i < 80 then 0 else 0)) else (if i < 83 then (if i < 82 then 0 else 0) else (if i < 84 then 0 else 0))) else (if i < 89 then (if i < 87 then (if i < 86 then 0 else 0) else (if i < 88 then 0 else 0)) else (if i < 91 then (if i < 90 then 0 else 0) else (if i < 92 then 0 else 0))))) else (if i < 109 then (if i < 101 then (if i < 97 then (if i < 95 then (if i < 94 then 0 else 0) else (if i < 96 then 0 else 0)) else (if i < 99 then (if i < 98 then 0 else 0) else (if i < 100 then 0 else 0))) else (if i < 105 then (if i < 103 then (if i < 102 then 0 else 0) else (if i < 104 then 0 else 0)) else (if i < 107 then (if i < 106 then 0 else 0) else (if i < 108 then 0 else 0)))) else (if i < 117 then (if i < 113 then (if i < 111 then (if i < 110 then 0 else 0) else (if i < 112 then 0xb91c3f2eb15d0a1e4ab2200f746ee30f15609443e619009182dc0ba000b915f42f015a8a164a721f8f8070031616009883fe19c09b83640d2000b90f9c2f41634a484c02270f7c6fe31f16289843f419109082c40b0000b9096f2e395689fe49521a0f446d830815308ec3ae17d08d02f00ae000b903442ec15c4a0e4a321d0f546e631715a897c3fe19a09e03500d2000b8fd152e815989ea4a321e8f7c6f630c154091c3e418509303340de000b8f69b30d96cca9c4e823c906878234d17409ec41619f09f836c0d8000b8f06b2ec95e4a1a4a22268fcc71032416409503d218608d02fc0ba000b8ea1d2f71670a6e4ce2340ff873433016489a040a19e09b832c0c6000b8e3f52e195bca224b622c0fb870c32415f897c3f419009302fc0d6000b8dd9a2fe966ca6c4d3236901874233616589bc40219b09703200bc000b8d77b2dc1568a024982200f9471832415f89643f018d09483180bc000b8d1602dd1574a084a521f0f5470230a15008cc3bc17c08d02e00ae000b8cb292ec95cca0c4b12290fac71c32b16889a84121a209983500d8000b8c5092df9588a144a72258f9471832c162098040a19a09803080c8000b8bec72ec95d8a224b12250fc070632616109703fc18e09783380d2000b8b8832f7962ca524be2270f7c6ee30815589183d618709282f00c2000b8b2392f49608a284ae2270fbc6ee30615609383da18909082e00be000b8abf22f11610a2c4ae2268fb870a32415f09743e018e08f02dc0ba000b8a5c42e915c0a204a92230fa86fa31e15809283d818709283040b6000b89f862eb95d8a2c4a82258fbc70232516309743da18609003200ca000b899472ed15d8a2a4aa2248f9871631f15f09503f218e08982d00c0000b893152e715b0a0449d2208f706e030e15108e03bc18209183200b8000b88cb030216a0a6e4e123d101472a32616209843e618d09703340c4000b886892e2958ca0c49c21f0f546f031415689183d417e08e82fc0c4000b880452e5158c9f649221a0f406e8312155893c3dc19109a03340c6000b87a292e015689f449c21e8f786f431c15c09203d018608f031c0ca000b873f62ed15c0a184a12240f906fa31815609243d217208b03080c6000b86dbe2e995c0a304b82290fac72432e15f098c3f618f09303400cc000b867772f095f8a3c4ac2220f8071432a16389944041a409c036c0be000b861202f895e0a264b12268f986e431a15b89483d618609983380d4000b85ae12f39608a3a4c022e100072c33216709d041e1ac0a103600da000b854942f59610a464b82310fa471632916009783e618408f03000ba000b84e652e315949f249821a0f846f432916289843fe18d09503240ac000b8483a2e3157c9fa4a22200f646e830e15609403d418809583200d8000b841f02f31610a444c222d0fec73633816609843f619d09b03180c6000b83ba42ef95e8a144ad2298fc870431f15609103ac16408602f00b8000b8354b2f9162ca3a4c522d0fd872c32f165098c3ee18b09683340de000b82f172e895b4a0449b21e8f706d630f15c09303e618e09303080cc000b8290b2d6152c9d447e20d8f0c6cc312156892c3ca18509283140bc000b822bf2f615fca324ac2218fa070a328163895c3ea18e08e03140c2000b81c513011658a684d12348fec72c33116309883f4192096833c0da000b8161f2ea95a0a0a4a22220f8070831a15b093c3ce17d09083080be000b80fef2e695a0a0e4a221d8f246cc2fb15008f03b217608982f00c6000b809962fa963ca4c4c7234902473234216c09d041e1a109c83440c8000b803522e895bca324b52270fb072032c16489843f419e09b03140ce000b7fcf32f99604a404b92228fb8714323162897c3e619708f83080c8000b7f6c72e495a49f24962160f646ce30214f08f43c418209283240cc000b7f0862ed95aca0049721f8f686fc31d15609243ce18209383200e4000b7ea4c2eb15cca264a62250fa46fe31515b89503ec19309603200ce000b7e4022f1961ca5c4c622d8fe072c33716809a44161a809b83240c2000b7ddcd2e795b8a1a4a72220f7c6ee31815989303d819109683100c0000b7d7762fb9640a4a4c62338fe072a33316809b04081a009e832c0d2000b7d1332ef15eca344b12298fa06f632115e89603f818b09503340dc000b7cb1e2da15489fe4a22228f9870832916309ac41019f09b03480d6000b7c4ea2ed95cca204a221e0f6c6f030d15789383e619009583380d0000b7bea32eb95dca2a4b02278fac70431e15e09503ec19109802f80bc000b7b8812de155c9e248c20f0ec06a82f715008d839a17208502c00a4000b7b24f2eb95f8a144a32218fa071031d15e09383d018909683200d4000b7ac022f81630a5e4c322b8fd072433016589984121a509d034c0d4000b7a5e32d9151c9c64782158f446da30015589603f019909983200c8000b79fbe2e415e0a3c4bb2258f9070232415e093c3d618308e02dc0a6000b7998e2e69594a144b12218f9c70431315789343da18408f82f40b4000b793462ec15bca204a721f8fa070631e157094c3f219809903440d4000 else 0xbaabf52f0961ca504c522c900474233916b89d041a1a509f83240b8000baa5b42ec95d0a2c4b12268fb470e31e15f89683d018709283000ca000ba9f782ec960ca3c4b62298f846fe31315d89543de191099033c0cc000ba991e2fb1668a644c9233901c73033216609583da19409583400cc000ba92ce2f61620a424b62268fcc72032c15f896c3e418a09303080be000ba8c692ff966ca5e4c7231900472e34016b09bc40219a09a835c0e0000ba86592d815349d24862130efc6d430d14e89003ba18909082dc0c0000ba80162f11608a464c6232101073c33316909e441019909b83240ba000ba79c92f595fca204a32200f746e231415989083ca18e09602f80ba000ba737a2f29620a444b62278f746ee31215409043b217c08e03280d8000ba6d342ec95e4a2e4ad2260ff474433f166899040419f09783300d8000ba67042e995d4a104a521a0f346d230615609183bc18209383200c6000ba60a43021638a604d1233102873633e16d09bc4181ac0a583540c4000ba5a9f2d194cc9a846f2080ed86a22e714108b839817008782c80c2000ba54472f615f4a384bf22e0fcc72c32f16489903e818b09283300ba000ba4df82f89604a3e4b92280fcc71632816089843fe198098033c0c0000ba47cd2e69584a0a4a92250fb471c32815e89643d418208c82f40bc000ba41792f61644a764d823c105876e3581778a0c43c1ac0a483800e4000ba3b492ea15a49f849b21b8f586ec31015389043be17c09203180b8000ba35042ef9608a3a4b622a0f886fe31515a89383ee18b09483340be000ba2ecb2e695c8a1e4a72200f546f231015b09643e418e097831c0de000ba28922ea15d0a244aa2268f906f831115a09203de19209683180c0000ba22742dc15589dc48b2170f386d630415509243c617f09003100bc000ba1c2d2e895c4a184b12260f846ec31e15c89703fc18b09503380d4000ba15ff2e995e4a4a4bf22d8fcc70e32a15d093c3ca18a09083100c0000ba0fbd2f115d8a1a4a72240fa071633016209a440819809803180d2000ba09932e515a4a124ad2240fb071632515d894c3e618408c03180c6000ba03412f4961ca4a4b922c0fd873a33216a099c3fa199097034c0d2000b9fd1b2e595cca124b322b8fa46f831615388e03aa17208682b40aa000b9f6a73059690a744c7238103476034116a09c840619c09903340e0000b9f0353079698a9a4ea23f105475234816c89ec4261a309b83440e2000b9ea1b2d615349e04862130ef46b42f815488e03b417208d83180d4000b9e3df2ee15e8a0e49a2248f806ec31215c09443e419609483200c2000b9dd872fb9620a4e4c722e0fcc72633116209743f219209a03440e2000b9d7572e81580a144ab2210f806fa32f163095c3e8190097831c0c8000b9d1462dd9578a104a82260fd471a32716009a04121a209e83380ec000b9cae72fb163ca5c4c6233100c73834516b89c04141a90a203680fc000b9c47730916cca9e4e6240905c76c35217109c440e19d09f03440c6000b9be512da95789f449c21b0f2c6cc30215909383c818108d82e00a4000b9b7ff2f89640a624cf232900072e33616889783de19409702f40d4000b9b1d72e1156c9ec48f21d8f3c6ec31215309003b618009103140c4000b9ab862f79630a444b92260f9872632a163096040019a09d833c0ce000b9a5432f4160ca4e4c62300fb470432015b09383dc19209303200ce000b99eee2f59618a3e4c1232100471832415a894c3de19309182d00bc000b998de2d615449da47a2108f0c6be30b15789443ec18309203180cc000b992892fb960ca424c222d0fe872832a16089803e618c091831c0cc000b98c732d91544a064a821d0f7c6e631515008f03a617e093031c0c2000b986242fc1644a5a4ce2331020730333166898c3f419609a83300d4000b980082e015609fc4932198f3c6ec30f15d09503de18a093832c0da000b979b33041638a464cb22d0fd871232215c09403d018109603300ca000b9737f2e595aca104a12220f9070431915a09303be18809183180c2000b96d2b2f71624a384b12240fa06f430715408f03ba17708c82f40ac000b966e12f49654a684c722c0fc471833216589ec41219c09783280d4000b960bb2e295589d648920f0ef46c62fa14d89043ce18e09182f00d0000b95a682f415f8a404b822b8ff4732337168899c3f018c093031c0c4000b954262ee15e0a264a92258fa870e32d161099c3fe19a09383240d0000b94dfc2e395bca264b522b100872c32815f09683ee19009303340d2000b947ba2ef95fca2e4b02238f7c6f431d15d89583f419009703200d6000b9417a2ea9604a2a4bb230901874c33616809b84181a709a83540c8000b93b382ef15b49fa4a121f8f786f631215289383d618b09303080ca000b934f92ef95d8a1e4ab2200f7c6dc30915408ec3c018509203100cc000b92eca2e415c8a124ac2258fa870e32416009703f619209683080c2000b9289d2e095949f64902140f406dc2fc14a08ec3b618708e83040c2000b922842dd155c9f249d21e0f486f030f15909483d218608f03000c2000)) else (if i < 115 then (if i < 114 then 0xbc3c1a2e59578a144a92228f786f431815809403e418d09503100d2000bc35d22f8961ca524c022c8ff072632c16309983fa19709903200ce000bc2f962ee15eca3c4b822f0fcc71c32f163899c40619f09903240c6000bc293a2fd9630a584cf2328fd871632f16789b040819a09a834c0d4000bc22e82f595e4a244ac2228fa070832415989283d618509283080dc000bc1cdd2d715609fc49a21e8f546e631014f09083d818609202e80c4000bc16dd2ce15089a847a20f8ee06b230314888e43a817908d82fc0c6000bc109c2ec15cca304c022a8fe872032716209843f618e09503100c4000bc0a532f495cca2e4b02220f806f230714c88e83c618008f83100c4000bc04392dc956c9f249c21c8f546e031615609103ca18c08d02f40ac000bbfe092e295b0a144a921e8f506f431e15e09543f219509a033c0d2000bbf7d62e795bca1049321d0f446d830815008f83ac17508a02cc0ba000bbf1a92e995c8a1c4a62200f9870232215c09703ec18909383040c2000bbeb652ec1608a3e4c222d8fe071c32b16789ac40c19f09983340ca000bbe53d2e3959ca124a82228f9070e32816409983fa19009583280c4000bbdefa2f115f8a2c4b12258f8470031616109643f219309482fc0be000bbd8a82f81644a684d82320ff873c33016509503da19009483140b8000bbd2632ef15c0a2a4be22e100471832c160898840019809d03340d2000bbcc4c2d895549f448c2140f246d030315209003c218b09102e80b8000bbc5ee2fc1610a384b622b8fd870e31d15c89483ee18c09303080c2000bbbf7330996b4a804d6235904875234516f09cc40819909f83840dc000bbb9133019674a7a4e4242105475233f16d09c440619609883500d0000bbb2cd2f21608a3e4c522d8fcc71432816189c841c1a009783480d2000bbac7d2f89614a4a4c8233100071c32015b092c3f019709403180c8000bba6472e8159ca044a621a0f306da30515409103b418309003040c2000bba00b2ea95b4a0649d21b8f9071032115c094c3de18a09582fc0bc000bb99e32e795b8a2c4be234101c73833116889a03f819309283200c2000bb93802fc162ca2e4ab21f8f8871432515f896c3f819a0a0033c0c6000bb8d442f31620a404cb235901872832815c89203c617e09083080ce000bb86e33039674a6e4c7231101873633116489803fa195095034c0b6000bb80aa2ec95d8a104a82218f706f830d15489103d418209102e80c0000bb7a422fb1664a764d8237102073c33115f89703fa19909683300c6000bb73dc3019658a764cb22f8fe4720329162099840c19709603140d0000bb6db72e595a0a124a42258fa471231b15f896c3e418708f02f80d6000bb67742f095eca324aa2268fc071e32e16009883e819a09c03380cc000bb613a2ea15d8a164aa2258f906f831b16009803e619409a03340ba000bb5af62f115fca284b52268fb872032216289503e418b09c03540b8000bb549d2f89620a424c622d100074233416809ac3fe19b09e834c0de000bb4e562ee15d4a2a4b12220fb472c32115e09543fa19b09903380cc000bb48002f5161ca564c622f100872a332165097440219e09c83400d8000bb41d82e015549d04812130f086c430715789143d219809a83380ca000bb3ba52e915c8a2e4b62248f7870831a15b894c3e018809403100b6000bb355c2f995e4a244b12238f9470a32416409a03f619b09903640d4000bb2f4a2dc95549ea4992200f6c6f8321160898c3f4197096033c0c4000bb29252e8959ca264aa21e0f306d030215209203cc18108d02e80b6000bb22d82f395d0a2c4a921c0f546f631715889243dc18a09383240d4000bb1cab2e695a09fa49a21c0f4c6f631715f09683e818d097831c0cc000bb16642f395fca344b622a0f946fe31515a89643f019609c033c0c8000bb0ff92fe163ca6a4bb2270fc870c32716209743e619509a033c0ce000bb09ca2e915cca3c4b52268fa86fc31d15c89683ee18c09403180b8000bb03752f89618a3c4bd22a8fdc716338161897c40419a09783280c6000bafd103049690a764cf234901872e33816689643f219009903400da000baf6c52f515f0a264b42228f8c70432215f897c3fa19609683180bc000baf08a2ea15c0a1e4b922c0fb873c33d16b09b841a19f09a83300d2000baea3c2f61600a324bb2248fd071e327160098441019509703240e0000bae4002ef95e8a404b422d8fd873e33a16509803fe19b09803200d6000baddeb2dc95449d249521a0f486de30614c08e03a617c08d83100c4000bad7c52e115749ee4962180f106be30a155090c3be16d08a82ec0b6000bad16c2fd9644a3e4b722f0fd073233616909a041c1a909d03680dc000bacb6d2cd15209dc48b2178f306ce30815389343c818a09883340d4000bac5332ee15b8a284b82280fbc716332165098c3f618c08f82ec0ac000babef32ef15eca2c4b622b8fb871432416609903fa19a09883400dc000bab8a82f91620a584c322f901873e337168898440018809683140b4000bab23c30716a0a7c4cf237901474633916c89d442e1b50a603740dc000 else 0xbdcb322ea15c09fc49421f0f9c6f432415f09503da18409383040da000bdc4e82f195e8a3a4c222f0fd871432b161897c3ec18d09382f40c8000bdbe9b2f59640a544c52310ff872c32815c09683ee18e094030c0c4000bdb86a2df155c9fc4a02220f8871031f15e89583e018a098832c0ce000bdb22d2eb15c0a284b42248f9870432115c897c3e419609203340de000bdabf62ec1594a0649e21e0f5470832815f89643f819d09803240c2000bda5a32f49624a564c4232904c74c34716c09d441e1a409683180ce000bd9f622ed15c4a144a12228f986ea30d15809583de18608e83140c0000bd98f93041678a644d2234902874c3431780a2c4481ba0a5836c0de000bd92a32fb9648a6e4d623a103875034616f89f442e1a80a083800e2000bd8c962d315289d848f2118f246cc30a14f88f03b217809082f80cc000bd86422fc9640a524b722b0fbc71c32516189984101a109b83640cc000bd7ffe2f015dca1a4ae2288fa071c322159891c3d618c09683140ba000bd79b82ec95c4a264b52240f9c6f431516109603f019f09e03280b4000bd739a2e51580a0849a21a0f3c6e431515789083ba17308c02c40ae000bd6d772df95449e848c2198f606e831e15f897c3de18909482fc0ba000bd67382ed95e4a2a4b02260fc471232715f895c3fe19309a03040c2000bd60dc2fd9690a8c4e723d103c75a34716b09a840819f09c033c0cc000bd5aa92ed95d8a404b522c8fc870a32c161095c3e418609003000ce000bd54872e19574a024942168f246cc30715408fc3cc18808a82f40b4000bd4e522f095c89f44942168f0c6c830515008d43a017308882c40a8000bd48292e415aca204a92258f686f831d15f89883ea19609783180cc000bd41f52ea15d8a284ba22b8fbc70c315158892c3f419509683200bc000bd3bce2e51580a0449b21c0f346ee31b15c89583e819109683580d8000bd35912eb95a89ec4912188f346c631015489003cc186091832c0d0000bd2f582ea15b09fc49d2210f846f631a15a895c3ec19309c03080ce000bd29092f395e8a3e4bd2278f9070c322163099440819d09e83440de000bd22e32e4158ca044aa2218f706fc32415e09a841419a09883240c8000bd1cd02d6953c9ee48f2140f186d630214b09183c218209103280c0000bd16832f79608a4c4c622f0fe472e32c16489743ec18e092830c0d4000bd10652da95489fa49521e0f506d830e15389143b617608b83000bc000bd0a3b2e315a4a084a921d8f606f231415008fc3c818a09282f40c8000bd03fd2e7159ca184a32268fb471431c15a09203d818e09703200c6000bcfdc32ec95f0a204b02268fb471a323163096c3ea19509583040ce000bcf7832ee95dca364ba2280fb471a32015f09843fe1a009d03440c8000bcf1352f61628a404b52270f9c70631c15f897440619a09a03480da000bceaeb2f195f0a324b92280fc072633716489944241b60a4034c0d0000bce4932f59608a344af2220f9470032a16489883ee19c09f03340ca000bcde542ef95d4a1e4af2230f846f431415b89203be17d08f03000c2000bcd7ee3069690a824d6241905476634c16f09a440e19a09403080b6000bcd19e2fa9610a504b622a8fbc70232315f09803e419109403080b2000bccb8f2d395249e649721d8f186d030a15409083d218e093830c0c2000bcc56b2dc95689dc48c2160f306e830e15709243da187090032c0d2000bcbf3a2de15809fa4a721e8f646f231515b89403d618509283240da000bcb9212df1580a084a02198f406f231715a09103ce17e09103100cc000bcb2f62e395849f64922178f4c6c22fe15008cc39817208903140b8000bcacc22e7158c9f24972198f406dc313154090c3de18709603140c6000bca6792fb166ca604ca236100073e33716009743c617608902f40ae000bca0522df15549e04902188f546e231915d09403e219409a83240d6000bc9a0d2f515f8a484be22c8fd871832516089783ee19609603080ca000bc93c52ed15cca124b22260fb871c32f16389d44221a009c83400cc000bc8d8e2ec95c8a324b02260f986fa31215a09383cc18c092030c0bc000bc87492ea15cca0849d2250f986f431315b89703f819909a83540ca000bc810e2e815bca0e4ad2228f8c6ee31215a09403d418909603400c8000bc7ae72df9574a024a02238f546de30414d08cc39617008502c40b6000bc749b2f49648a604cf236900473232e16709d84161ac09f03180c0000bc6e4c2f91638a564c322e0fd072032415f89503da18609383100c6000bc68132ef95e8a404bc2288fe071832915d09243e818b09503300d6000bc61be2fc1644a4a4b822a8fd071232c15d09683f0191098834c0e0000bc5b972e215aca0e4a321d0f506e031115609103c618609403040ac000bc552a30796a8a784da234102c75834d17309c84161a209f03200c4000bc4eda2f115e8a224a92228f9c6fa31a15909503be18709403200bc000bc48982ef15bca204a82268fd070c32315d892c3c817e09283040c8000bc42402f59614a3e4b9233103c75634317289e040c1a50a403a0102000) else (if i < 116 then 0xbf597a2fb1644a444bd22e8fd872632b164096c3ec19809983400d4000bf53732d415109ca4822150f146b42f214b08c43ba17d08c82f00ba000bf4d5f2d9951c9ce47e2120f386ec30b15489343d418208f82d80b4000bf470d2fb161ca544cd2320fd473032d166899440619509703200c0000bf40f22d9158ca0c4a921d8f446f430b15b89603f619609783280c6000bf3ab72e495a8a1a49621a0f246d830315089083d417b09482fc0ca000bf34822ed15dca0c4a221f8f846f631f162897c3ee19c09b83540d0000bf2e702da95609ee48e2178f246d4311155093c3ee18f098833c0d0000bf28152f595fca424b822e0ffc73c32d16109683f419309b83500dc000bf21d62ee95a8a2e4a72218f886ee316154091c3ce18409382fc0c6000bf1b8c2f49604a364b52298fbc70e31a15c894c3e619a099032c0d6000bf156e2e215709e848f2168f486de30a15409343d218408e83080b6000bf0f3d2e795a8a124a521e0f6870631b15a09583f819109983180ba000bf09282dc957ca184a62258f9c70232416209843ea18c09603200ca000bf03172da157c9fc49a2240f786fc32016189a441019e09e834c0c4000befcd12f115f4a284b42288f9c70c32715c893c3cc18508e82e40b4000bef6ae2e215589f04912158f186be2f714708d03ae17c08e83040d8000bef0982d815549ca4822110f186c430a15a09643e218a09683200ba000beea802d495409d84882138f086bc30314d890c3ca18f09203000c0000bee42c2f7960ca444bb22b8fd872a32315f09703e018908f031c0ca000bedde22f095f0a284ac2210f946e830f15a895c3fe19709703600dc000bed7b62ed15bca2c4a62248f9870a32a16209403fc199099032c0be000bed1692ec15e4a424c222b0fb871632615f09643d818c098832c0c8000becb2f2ea15e0a1c4aa2260fd071c32d162896c3d618409803000c2000bec4e42f395fca1c4a72220f9871432a15e89883f619909983400c6000bebea62eb15c8a124a221a0f346dc30c15489143b617f09002d80a4000beb8682ed9614a3e4ba2268f986fe31715f89643f819b09e036c0d6000beb2222f11608a504c12310fe071e32f163098c3da18f09403280c6000beabf52e715d4a124aa2218f9470231515a893c3dc18508f031c0c2000bea5c92dc156c9f849321d8f6c6d430514e88fc3ba17f091830c0b2000be9f6f2f99630a504c322e0fc871431c15609183d618a09202fc0c4000be992b2f2960ca3c4b52288fac71231d16289803fc19409683340c8000be930b2e115749f44892198f746f832016189883f619809b03480da000be8cab2f59634a4e4c022e8fec72c33216509b440e197099034c0cc000be865d2ef15eca224a721b8f646f031815a89683ea18c09583240da000be80222ee1600a4a4bc22a0fa070e32a16409ac41219e09e03300d8000be79fd2e1956c9dc48a2128f186b6301153091c3d818a09603280c0000be73db2e815b0a0a49d2208f8871232015f09643e018a09403080d4000be6d7c2fa1634a464c422c8fdc72833716609944121a609a83380c6000be672f2f615f8a2a4ba22b8f9c71a31e161898c3fe19509683180d0000be610d2de95409e24942150f3c6dc30314f08c03ae18008d02fc0ba000be5ae02e215589fc4962210f8c70431815d09643f619609883200d2000be548a2f99638a604bf2278f806fc31f15989483ce186093831c0c0000be4e462ee15eca364b12290fb470031615609203ce18f09602f40b8000be47e53011684a604d22350fec72232915e89843f219409803140ca000be41af2e795aca1649c21e8f5470232415f096c3e019609a03500d0000be3b722eb15c4a084a32208f706ee315156894c3e819809903400d6000be35302ec95d8a1849f21d8f4c6de30615689103b418008b82e00ac000be2ef92e815a4a124a121a8f446da311156891c3da18c098030c0c0000be28c92e915b4a264b32220fa870c328163898840219209683180bc000be227b2f71600a2e4b12268f8c6f832015d09743f419a09403140ac000be1c542e515d4a224b12238fb471432316009783e419009883480bc000be160e2ef1608a444b82258fa870432b164096c3f819109303240ce000be0fc72ee9604a3a4af2230f8071632516009383b817a08d82c40a6000be098e2ec15c0a184a521e0f386d630415289383e818a09483300c2000be03722da9580a0049f21a0f006c22f714b08f03be18809102e00da000bdfd242f11638a4c4b72260f9c6ee31715d09843ee19609d034c0ce000bdf6d32f295f8a364bb22c8f9870e32016289483d619609483180b4000bdf0a62de958c9e849b21d0f546da31115809543ee196096833c0d4000bdea842e495a49fe4a121b0f4c6ec31715c09443f019509a033c0b2000bde4322f895fca344c32300fac70c31715c895c3e618f09283180d0000bdde082e1159c9ea49321d8f6870231c160097c3f419809503000b8000bdd7e72df156c9e449f21f8f4c6e630e15409183c4181092830c0c8000bdd16d30a96a0a664c822f8ffc74433716609a03f819609782e40b4000 else 0xc0e9253059680a644c22300fe873a33316509a840e19809883500d2000c0e2d82f89608a3c4b72278fdc73433816809983f219f094030c0cc000c0dc842f81600a404ce2310fe072632615d09503ec19309583200d2000c0d6202fd162ca484c02318ffc73033516289a03f619509683040d6000c0cfeb2e895dca124a221c8f646e030b15689283ca18a092032c0c2000c0c9b92ef15c8a144a521c0f6c6f832b15f098c40419d0a003400c4000c0c3a72d715349d248c2168f246cc30f15409203d418809503180ba000c0bd6a2ec95f4a424b62268fa870a32415d89543d419209683240ba000c0b6fe2ff1680a584c7236101c73c33d167098c3e819709b83240d0000c0b0ba2f115e4a1a4a52200f9c710328164898c3e018c09b83380c8000c0aa982dc95a4a1e4a92248f786ea315159896440419f099831c0cc000c0a4303019674a6c4d12318ffc73633416b89a840e19f09803080b4000c09def2f1961ca504c222e8fcc710327166096c3de18109002f80bc000c097c92df157c9ea4982218f6c6f031115708f83c818309082e40bc000c091982ee15dca3c4b42270fc071c32b16709c841619b097032c0d4000c08b422fb962ca544c12310fa470431f15c092c3d218c09503180ce000c0852e2d715409ec4912188f306c0304153094c3dc19209703380dc000c07ede2f8964ca4a4c422e0fd471432e16389883f819109603040de000c078b12e595949fe4a52210f606f030414d08fc3c818509583240c4000c0726d2ed95d4a344c122f8fdc72632f16109943f819409c03600c8000c06c362e715dca184b222a8fb870a31015589083ba17708e82f40ba000c065f42e815e8a2c4c12280fbc70231d15c094c3d4187092031c0c0000c05fb52f315f0a3c4c122f0fc470831715909683da193091831c0cc000c059802e9958ca004a52258fac6f632115f89843ee18d09303300d0000c053542e895a49fa49a21d8f7070031515709103de18709603180ca000c04d4a2d195289d448c2160f346d230215589343de19509582fc0b4000c0473a2d6155c9f848f2160ef86d230615209243c4182091030c0ca000c041062e515649e24892180f506ce30314b08f83c018109283180b2000c03aa42fb964ca444c22278f806fc31a15809543e4186092030c0bc000c034712eb95dca1e4a82268fc472a32f16b89e04121a809b83480ce000c02e442e415609f049921c0f6470031015489543ea18c09103200d4000c028202dc95689fc49d21d0f7870831a161099040c19f09903480da000c021ee2e415aca124a121c8f486f031415909403dc19c09783400d4000c01b962f495f0a304a52218f8c6f8313159895c3e419609a03680ca000c0151a30716b0a7a4d8232100874233d16e09a04001a309a83200c6000c00ef42e195789fe49d21f0f7470231e15e09583dc18c08d82f00b6000c0088330796b8a6e4ce2320ff074a336161099440219a098832c0d2000c002602e3159ca0249a21a8f5c6f831b16189883ea19509983440d8000bffc422dd1584a164a821b8f706e630b15789203e218e09282fc0c6000bff6272d995689da4832178f406e031315609143be18e09203080c0000bfefeb2ef95b8a044a22228f6c6f230f15609543f619809b03340c8000bfe9a32f4160ca424c122a8fc871432816109a040c1a209f83380c4000bfe36e2e595b0a324b02210f906f631a15b89303d018409182d00b6000bfdd1b2f61638a4c4c2230901874434416f89e042c1a009e03540d0000bfd6dc2f095b4a0a4a721c0f546ca30014e88d83b617908f82f80be000bfd05031016d0aac4eb246907c76434616c09b03fa18d095832c0be000bfca272e6959ca264b22250fac71832415c89983f419809582f40b8000bfc3e62f41610a444b822c8fc471c32716409a840c1a1099834c0cc000bfbdbc2de957c9ea4972178f306e230b159092c3d818409283140cc000bfb7772ef95d4a184a12210f786fa31115809443d217c09383240d6000bfb1512e315a0a004922210f9471432616009683fc19609083200be000bfab002f39608a404c322e8fbc72633116009743ee18a09302fc0d4000bfa4c82e415c4a1e4a92220f8c6e8315154093c3da18e09703100c4000bf9e672fb1638a3c4b62270f7c70c31b15b098440819509a03500e4000bf984e2dc15389d04892188f3c6c430914f08d43b418409403240da000bf922a2e195909fc49521e0f6c6e630214c08d83b417d09183000bc000bf8bc62fb1620a484be22d0ff071632215e89643ea19509603500b8000bf85ad2d995449f049c21b8f8871631515d89283d818b09182f80ba000bf7f5d2f7161ca544c8235900c73a32e15e09343cc19009b03400da000bf79322e495b4a104b22260fc871231915f09583ce18109583000c2000bf72db2fe9664a5c4d923b103c75033816b89c84221aa0a503700da000bf6c7f2fe1670a704cc2300fec74a34116f09bc41619f0a103580c8000bf662d2f79638a504bc2290fd472232815f898040219a09583280c4000bf5fd72f91634a4a4be2290f706f431715d092c3c418609503200c2000))) else (if i < 121 then (if i < 119 then (if i < 118 then 0xc278992db955c9e64902148ef46c4305151890439e16e08c82d80ae000c272312f7162ca4e4c1230900474c34316d09cc4081a009e03500ea000c26bff2e395789f049d21f0f346cc2fb14c08d83ac17708f02e80be000c2659d300967ca8a4dc238102074233e16a09c842c1a40a283800d4000c25f532f215f8a264ba2320fc472a32c164896c3f418e09583000c0000c2592c2e715809ec48b2120f006cc30e15709303de18609282e40de000c252fa2e715bca1e4b322c0ffc720329167899440019809883340c4000c24cdd2db157ca0849f2250f606e831415f09643ec18d09603440d0000c2468d2ef160ca584c6230901475c34516809bc4141aa0a1836c0ee000c240592e895f4a1e4ad2298fb8720336165898440219809b03480c8000c23a462dd95809ea49621a8f546e031215709643f819909d83340c2000c233e42fe1674a8e4e7244909877234c1738a044301a709a033c0c2000c22d902f69608a384be22f0fa0722322165099040e1a809f03480d0000c227562ed95f0a344b622a0fa071632816189983fa19809903240c2000c221322de154c9e64912168f006d2314159894c3da188093830c0c2000c21b1e2dc15509f24962170f4c6f231d15d897c3f819609903300c0000c214de2f015dca384b32280f9471c32c16009583e018d09202d40ae000c20ebe2dd95749f64a82228f806ee31415689103b017508a82e80b2000c208842e39598a0e4a321d8f406ea31e15d09803ec184096831c0e0000c202153029678a724c722d0fe473632915d897440219b09b033c0d6000c1fbe02e715d4a1649d21c0f546ee30815389143be18108b83040d4000c1f5902ee95d0a224b122b0f8c70831e15c89383de18509002fc0c2000c1ef3c2f615eca304b72278fac71631b15d89443ee193091831c0ca000c1e9132e315549e649321a0f5c6e630f15989443e418e09983140ca000c1e2d02eb15c0a2a4b32238fb06fe31d15589543e419209483000c4000c1dc62300164ca5e4d423a900c74232716609e441c1a50a083700d0000c1d6542d515189de4942190f2c6da30515388f03bc17808682cc0b8000c1d01a2f015b4a164a72280f8c6e830d15709443d8188094832c0ba000c1c9cf2f79630a4e4c722e0fd070031715c09543ee19709603280cc000c1c3852f1961ca404b522c8fc471c33416889a83fe19a09a832c0c0000c1bd722d8954c9e84892130f346d431615889243d818908e82ec0b4000c1b7282f61604a324be2288fd06fe31b160897840419109983500e8000c1b0f52e89588a0a4a621a8f3c704323159891c3e018b09183000c6000c1aaca2e095909fe48e2178f106de30515309283d218508b830c0c2000c1a47e2f415d8a1e4ac2230f9870832815f893c3e818e093032c0d0000c19e1a2fd1650a604d4235100c74033016d89e44281a809c83600d4000c198102d314f89ae47220c8f046c030615c895c3f619809883440d0000c191be2f69618a584bc22e8fbc71a32415f09383d218c09582f80ba000c18ba22db158ca0049f21b8f3c6ca30715709543e618809682f80d2000c1853130d16b8a944e2241909878c35617a8a384361a80a283680d0000c17ee02fa963ca5c4ca237903874c34f17189dc4301a50a203600de000c178c92dd956c9f249021b0f606e830915609243ce18408f02fc0ae000c1728d2ee15dca344b52260fa870631b15d09403e819209103400e4000c16c452f19608a324b32290fd471c32b15f09683f819309503040b6000c165d93051690a724d523c102c74833616709a03f819909d03340d4000c15f9e2ea95e4a524c622b8fd872e32d16709b840c1ad0a203640da000c1593f2fa1654a784d4239902475834a17509dc42819f09783280b6000c152fa2ed95d0a384b72248fcc71832b164099440e19a09682ec0ba000c14cb32f71618a3c4ac2268f9c71832716009543e219009783040be000c146892e595d4a264ac2248fc4726330163098c40019f09e836c0e6000c140372f69600a3a4c3234103874633116509b03f619a09503240d6000c139ed2f59628a404b822c8fa86fc32415b894c3dc18f09b03340c4000c133ac2ec1608a2e4a52210f886fa32315c09483e818609003100c2000c12d942d895349e848b2140f306da30315209083b818608f830c0b4000c127502ee95d0a3a4b82238fb871432315e89683e219209883180ce000c121342e495b4a0449d2238f8c6f831415d09703fa19709703000b6000c11adb2f59634a404c32338ff871e32b16189784181ab0a2833c0e0000c114c12df155c9fa4a42260f9c706316156094c3f018c09183180c8000c10e822ef95eca324bf2310fe872832a15d89603d618f09883540d8000c1085c2e195749f249521f0f4c6d8309152893c3be17508e03040be000c102272ed15c8a284ab2240f906f631d16309843ea18f09483240c6000c0fbdb2f79620a544cc236901c74a33f17109ec42c1b60a2035c0da000c0f5b32e215a4a024a22190f406de30314c88f03ba17709083000b2000c0ef8b2e515b8a044a02218f94708314159094c3ce18c09402f40c6000 else 0xc405bf2e195749ea4892150f006b82fd152892c3de18108e83040c6000c3ff722f015e4a364af22c8fe872832a15989483ca17508a83000be000c3f96a2cd14b49ac47920a0ef06a42f714f88e03ac17809102fc0b0000c3f3332ee95d4a164af2270fb070031715f89683e218208b82e80c0000c3ed072e89604a304b02290fac70a32f165098840219f09c035c0e6000c3e7012d295109c848521f8f886f831215a89483d418f09102e80be000c3e0bd2f215e8a364be230100c72a32d16989783fa18a09203000be000c3da882eb15cca0c49d2208f746f231b15589403c018208d02e40c6000c3d4952c994d49a04692058ee069e2e9140089438c17208a82fc0ac000c3ce542eb958ca0c49e21b0f506e231415989383da18509603040c2000c3c82d2e595c8a124a121c8f9c70a32515d09643fc19f09f834c0d0000c3c1d72fe9628a4c4c4230900072c32416189a040c196099832c0c2000c3bb7f2fe1650a484c9234100c73233416b89c44121a509b83440da000c3b5332f295f4a2e4a72220fa871a32816589a03ea18c094832c0d0000c3aef82ed95b0a0049b2180f346d831315a094c3e018809003040d6000c3a8b62f69634a3c4ba2280fa870432115f89703ec19109a03480d4000c3a29a2dd15689fa48e2180f586e030615289183cc17f09383300ea000c39c562ea95a4a144b62258fd071632c15f09583e419409683100c8000c396172eb95c8a124ae2228fb070833316589ac4081a409f035c0d2000c3900c2d915389e84892120f1c6d030314f88f43b617c08f02ec0bc000c389c42f015eca2a4b12270fb872232615c89543fe19509503340c4000c3839f2e415849e048b2188f2c6dc31215509143c218609383440c4000c37d832e415949f84962180f586e030815a09583ee18c09603280c0000c3773f2f115f8a1e4a521d0f546ea31815388f43b617208602c40ae000c371212dd156ca0049f2210fc470a325162897c3f019709b034c0cc000c36aed2e4957ca024a32218f7070232616089343f219409803340c8000c364b92e995d4a384b02220fa06fe30f15689083d819709e03240da000c35e822ec95dca1c49e21e0f6c6e8319161896c3d218c098830c0be000c358462eb95d0a264a62288fbc706327167899c40819709383280d0000c352092ee960ca404c02278fb071432015e09283c617d08e83140dc000c34c0a2d4951c9da48f2160f1c6ce30d151090c3ce18809103340ca000c345ed2dc957c9fa4a42218f8870031f15f89803f419d09b83500d4000c33fa82f41604a364c7236102876834416c89bc40e1a009b834c0e4000c3396e2ee15cca344ab2210f7c6fa31215509183d018109183080bc000c3332b2f29608a464c02310fe872433216689a440e19d09b033c0c4000c32cca2fc966ca7a4e2239100c73633416289ac40e19c09983440c2000c326972ea15bca1e4a22228f886ee31315789543dc19709803140c8000c320622e615b4a124a92208fac72632b15f09803ea19009603200c6000c31a0b2f49630a424ba22d8fe872032c16509583e818509402ec0c2000c313d22ec15b8a1a4b32298fe471c32716389ac41019e09b83400ce000c30d6130d96e0a7a4d2237101474233a16709a840818f09503380c6000c3072d2ea95b4a044a321b8f746f2313157091c3d018809282f00b2000c301132dd95809fe49921f0f686ec31d16089343e619309b83380da000c2fad92e71588a0c49f2258f9c70631915709183c818609183140ca000c2f4972ea95d0a264b622b8fb46fa31815a09603fe187090830c0b4000c2ee6d2e315b4a124a62248f8c6fc32b164897040419709a03480dc000c2e82d2f21608a484b822b8fb472232915c89503e418b09503280d4000c2e2042e2956c9e648e2140ef46ce305155093c3d619009483340cc000c2dbf02d995649e84962160f406d830315109243ce18609303100c0000c2d58f2fb1624a3e4be2290f8c702315158894c3d218009483100cc000c2cf602e315aca064a72238f606e831215288f03ce19109783580d4000c2c9212f015fca2e4b12250fcc72e33116089783ea18c09a83740e4000c2c2fe2dd958c9fe4992200f606de31315809343da19409603040b2000c2bcaf2f69630a644d02350ff4740333165899040e1a109b03580c6000c2b6912e39590a084a321d8f6c70632015709343f018a09603200bc000c2b06d2dd9598a004972158f446d030715309183d818908f83000b2000c2aa292f39614a5c4d723a100873632e162898c41019e09d836c0d4000c2a40c2da155c9da49221a0f606d430915308ec3c817f08e830c0b2000c29dc42f41604a284a92210fa871832c16589784041a30a083640de000c297862ee15dca1c4ac2280f9870231e16009583f019909482fc0c4000c291442eb15c8a284a42278fac6fe31a15b096c3f019a09c03480d4000c28afd2f99614a204ae22a8fd071232815f89783e819809583180d4000c284d62e695d0a364b322a0fec72632a16909743fa19709d03040da000c27eac2da95589da4962178f386d230b15909343ec1a50a483380c4000) else (if i < 120 then 0xc594a92ea95f0a3c4a92210fb86f631315188fc3a217708982cc09c000c58e682ee95dca2c4aa2220fb871a31d16409643f619e09c83640e6000c5881b2f89638a4e4c622c101073c33216689bc41a1af0a583780f2000c581fd2dc95549ea49321d0f5c6d030315288fc3be17808d83000da000c57be62de95689e44882150efc6b02fe15389143d419009702f00c0000c5758b2fa1638a3c4bc22a8fc8714328162097c40019b09e03140c6000c56f6e2d915449ea48c2140f586e431615c09483dc18609603100cc000c569462e49584a164a52208f5c6e231915d09503d618609002f80cc000c563342d414f49c647e20c8ee86c630e15809283ca18509103300c4000c55d142df95849fc49c21b8f306d830715189243c417e09182f40ca000c556d32eb1614a4a4c522a8fc871432e15f895c3f019209503140ca000c550ac2e6958c9f64922170f486e631715709043b818109102f40c0000c54a622f095f8a3a4c02280f746e831a15b89343c418308a82d80ba000c544062f99630a3a4ab2268f7c6e8312154891c3b416e08d82f80bc000c53dc92eb9604a284b622c0ff0720330165898840a199099834c0de000c537862f0160ca484b522f0ff472632715e09683e418c09a83340be000c531602df95709e049221b0f606ec31615188e43c218308d82d80b0000c52b3a2e215709e24892148f346e230e15789403f219809983500ec000c524f22f015e8a264bf22b8fc86fc31e15e89503e019209703180d2000c51eb22ee15eca2a4af2288fa06f632015a89243d819409803480d2000c5185130516c8a984ed23c104c75834116809ac41a19e0a003680d0000c511e530896aca924dc23a102074634117089d04101a20a183700ce000c50baf2f115f0a384bd2300fe073032d16089743f21a6099032c0c2000c5055d2f395fca364b422a8fe872c33616d09bc40019209783200be000c4ff472d7153c9e448520c8ef46b830314b88e43a8179088828c0ac000c4f9222df1584a044a22208f506cc30f15289103c218c09503180c4000c4f2f42e31590a0e4a52210f646f831815d895c3f619709c03440d6000c4ec9b2fc962ca504c22300fac70632516809944141a209b831c0c6000c4e6512f5960ca3e4c422c0fc472a32c164097c3ea19909d034c0de000c4e0112f295dca1e4a721f8f746f831a15c09603fa19809982fc0c4000c4d9e52e51580a084a72258fa871032816109883e819009403180c2000c4d3952f415e0a1a4b52288ff072032f165899840c19709303380e0000c4cd542f115e0a264b02288fa871a32d163097c3f219409203140c2000c4c7462db95649fc49e2228f886fc30f15888f83c218809083000b0000c4c0fc2f415f0a2a4ba2300fe473033516f0a1c4301a909d03700d6000c4baa22f8960ca564c622e8fc4706319158091c3e2181090830c0d0000c4b4462fa9614a304b722d0fd473232b15e096c3e8189091030c0c4000c4ae132ec15d4a2c4a82238f646ee31c15788fc3e018c09383100c2000c4a7b62f79674a5e4cb230900c74433616a09a03fa19809583340dc000c4a1692f395fca3a4ae21c0f8071e33416289a840c1a009a03140b6000c49b06301965ca644c72350fc872432116489643f819a09902f80c8000c494e82df95649ec49f21d8f686de30e15a89503e218f09483180c6000c48ebe2e695b4a1849f2178f186ce30415009083ae18609102ec0c4000c4885e3019664a564d22320fe072e32d163898c3e8186092830c0c8000c4822c2e695a09fc4a92200f8070431915c09443e0192099835c0d8000c47bed2f015f4a204ad2218f6870231415d89603e819909282d00a6000c475bd2e795c4a164a72230f8470831c15889283d019008c03100d2000c46f9c2de15609f44972148ef86b830015509083c818b092832c0da000c469692e4957ca0049421d8f686de30615589183dc18a09403200b0000c463082fd163ca5e4c422a0fa470a32e16889883fa19709983140c6000c45cd12e69588a0e4a62278fa071832215b89303de18209003080c0000c456af2de15909f449921b8f546d030115309343e019309102f00b8000c450792e89610a2c4ad2248f8870232316109603f218d09303300be000c44a592dc957ca104a72250f946fa31c15c09383dc18809383280ba000c444212e51598a0a4a72240f8471633016989cc4261a70a083680e0000c43def2e895a4a1e4b02238f9c6fa32816089643ea18b09603240cc000c437992f51600a264a52200f746f2313155891c3e019509403100ca000c4315c2e915cca364c222e8fe072632716189883f219409583200c2000c42b1b2e995b4a1249d2240f4c6ee31f15d897440219509883280ba000c424ea2e69578a0c49f2218f686fa32715f098c3f6192094830c0ce000c41ea12fa161ca504c02288f74704317160897c3f2190099833c0d6000c418702e495c0a124a92228f406e631015889283d018d09583000be000c4122f2ed95f8a424b82290fa470231b15e093c3e219b09c03380dc000c40bea2f295d0a284aa2228fa06f631215b892c3a017508c82fc0bc000 else 0xc723b63041664a7c4d3233101074433d16f09d04161aa0a283700d6000c71d852e715c0a064a72230f7470231815c89603ee19509703500d0000c717292f79614a2e4b622d0fd470e31915909643e819609b03440c6000c7110a2e495aca1a49f21e8f5c6f231315c09503ce18e09683200d8000c70ae52df956ca024a82240fb871e32516189543fc1a609c83640de000c704c62e1958ca1e4a62240f7c70c31e15b89583ee19809783300d6000c6fe8d2e815aca0e4a521e8f886f231215709403ea19109402dc0c4000c6f86e2da9574a104a621f0f7c6de31115509283e418a090832c0d4000c6f2202f71600a284b72258f9870231e15b096c3e819609602f40be000c6ebbe3019650a5e4c922e8fa070c32515f89783f819109b03640d4000c6e57b2ed15c4a064a22200f8871a32816c09d441c19e099830c0ac000c6df262fb9658a624c92328fdc73633816b0990404197099831c0d0000c6d8df2f31618a484b92270fb46fc31815e09483d818809282e80b6000c6d2a52eb95cca284a521c8f486d830e15b89603f018d09602e80b4000c6cc802d995649fe4942188f386d831015a09303de18309503280ae000c6c63c2ed95d4a344b622b0fc8714327162099840e19b09e83400d2000c6c00c2e415a0a164a52220f446cc307150890c3ac16b08502d40c8000c6b9bc2f8163ca4e4cb238905874233016989b841a19f09a03280d0000c6b3962e415aca0e49b21c0f606fc31b15c89683d618a09503240c0000c6ad692ec15909f84972188f486de30a157091c3c818308b830c0bc000c6a73d2e71588a0849b21d8f3c6d4308158893c3c418809403200d4000c6a0ed2f5960ca484bf22e8fdc72633216709b840619e095031c0b8000c69aa82ea15c8a204a921f8f506fa32315c095c3ec19b099031c0b4000c6946e2f215f4a2c4af21f8f786fa31615a89383d218509503400e2000c68e092fe966ca6e4d7235902475834916e89b04141b00a603580d2000c687e22e39590a0649d21f8f806f231a15a093c3d018809403240be000c681d02d2151c9bc4852128f086b82fe153090c3da19209202d00ae000c67b752f5962ca484c422b8fd472031b15989503ce18109283040c4000c6753b2e615b8a344b42220fa870e32315c893c3d218a09683380d0000c66f122e715a8a044a22150f386e030b15909443d818c09583240bc000c668aa3071678a784d823b904875033d16a09d44241ac09f83380d6000c662552f215fca244b22280f9c70c32d163097c3f619409883180be000c65c0e2ef9628a744d52328ff871a33516709c04001a2096833c0ce000c655f52de955c9f249121b8f446de30d15288e83c017008782cc0b6000c64fa12f495f0a5a4c822e8fe871032a16809883fc1a509f83280d6000c649632ea1598a1249b2168f286dc30e15509283cc190093831c0c6000c643013001670a664c32320fd8722323163099841419d09783440d6000c63cda2de95809dc48320f8f286da31515b095c3d818a09583040b8000c636982f01604a304ba2290fb471631d15d89603e819509883140d4000c630952d615189d04892110f1c6ce30115208d43bc17508c02e40b2000c62a502f29600a244b62270f8c6e82fb15208d43b018209282fc0c8000c6240a2f41628a4e4c022e8fcc71431815c094c3f418a096830c0c6000c61dbb2ef9604a484c522d0ffc74634016d09c84221a709c83600e4000c61761303169ca864dd23a103874833f16a89c43f019009803340d4000c6111e2eb15d8a3e4c42328fec72e335161095c3e819009783240d6000c60b1c2d115189cc4872120f146e030915709403d818d09603380be000c604ce2f4962ca504c42308ff072832d16309643de18608e82fc0b8000c5febf2d695289e44842138f306d630a15089103bc17e08f83200b2000c5f8852e8158ca0249c21d8f6c6f631b15a89443ce18909002cc0b2000c5f2612e195789e649d21e8f6c70432d15e09483ce18809303000b6000c5ec262e815b4a0e4a321b8f406d831615a89603ea1990a0035c0e4000c5e5f12e595b8a104ac2260fb071432d16289903f219109503080c2000c5dfcb2e3956ca0049b21d8f546e830c14f08b039a17508e03000c4000c5d9932ea95d8a044a121a0f146c630715609103c818d09783380b6000c5d3492ee15e0a204a121e0f6c6f031d16389883ee19009983340ce000c5ccde30416aca9a4f0249905c76e34c16e89c84281a30a483680c4000c5c68b2f59628a504c022d0fbc70a323159893c3e219809a83240ca000c5c03b2f51618a4c4c1233101073832f16709a43ea19309483200c0000c5ba252d795249d249521e0f4c6d22fe14f891c3d818809082e80ac000c5b3e52ea15e8a324ba2288fb871433016989a840419209703200d4000c5ada52ed15d8a1c4ad2270fb070432515e895c3da18a097033c0e2000c5a7532f81638a504c92328ff0736330164098c400190091831c0b6000c5a12b2eb95b8a0e49f21e0f746fc32015b891c3ca18d098033c0da000c59ade2f5962ca484bc22d0fdc724326162897c3ea18a09383080c0000)) else (if i < 123 then (if i < 122 then 0xc8b2352e715a8a124b02208f786de31015889583f218008d83240c8000c8ac092e995b4a1249e21c8f586f031b159093c3d618509583240c6000c8a5ae2ff962ca484be2288f646da306154890c3d618508d82f00c2000c89fa02d315049c247a2090ed06a42ef14808d43ae17508902d80b6000c899662ee9604a304ae2260f8c70431815a89603de18408e83080b6000c893292eb15cca4a4bb22c8fb870831e16209603ae17e09083000bc000c88ced2ee15d4a204a72238f8071631a15709283d618909283000c2000c8869b2f595dca384b52270f9870831f15b89483ec19309983480c6000c880672ed1604a244ab2248fb470432a16609a83fc19b09e03600c8000c87a392e495b0a0c49f21e0f5c6f231f15e89883d018809003300d0000c8741d2dd95709ee49921b8f5c6f231a15c89603ea19e09683240ca000c86db830896b8a824dd23b903075033816409783fc19f09c83500ee000c867712ec1608a2c4b12238f9071031e160095c3ea18c09083040c0000c8611a2fe1678a784cf2328fd871a32c163097c40619909b83380c8000c85ae32e915d4a1c4ab2260f746f630f15a09543ea19309783340bc000c854b82e515889f248d2150f006be2f714e091c3c818a09002ec0d4000c84e902e615a09f64942160f2c6ca318157894c3de18909103180ce000c848602e39590a104a42238fb472e32316209803e018c09483380ca000c8422c2ec95e0a244a92238f8871a32416009843f619b09b83180be000c83c032e395909fe49d21e0f746ec312154890c3c818008f02e40b6000c835cd2e715c8a264a82208f806ec31715a097c40c1aa09f03640e4000c82f902ea15d8a244a92208f5c6ee31015a094c3e218909302fc0b4000c829522ef161ca344c622a8fd473c33b16f89dc41e19909883100c2000c8231a2eb95a0a024a12218fa870c32b16089903ea19109803300ca000c81cfc2de95689ee49521b8f586e430b155090c3c017e08b02e00bc000c816ce2e495a09f449121b0f306c830214d08f43c018009102f80c4000c8109f2e415989fe4a32218f446d4314156891c3d018509583440b8000c80a952ce94dc9b24842118f046d230915889003c418008c83040c8000c8045b2e715f4a404bc2298f7c70631a15f09683e018e092031c0c6000c7fe2f2e0155c9e64862170f0c69c2ed14a88c039c15f08202b00a6000c7f7d32fc1634a444bc2280fb870c32615d89543f019209483400d2000c7f1b92dd95649e048f2198f546f231615e89883fa19f09e833c0c0000c7eb9e2e1157c9f449a21c0f686ea311157090c3be18508f02dc0b0000c7e5592ed95f8a404bc22d8fa871632f16589a03fa18d09502f80ce000c7df062f81610a2e4b92298fd874033a16c09c440619809a83500d4000c7d8df2e015649f249a2240f706f631415e89543d017c09582f80c6000c7d2ad2e695d0a364b422b8fdc71c32315c094c3e219309b83240c2000c7cc662f215e8a0649e2200fb072432a160899c40a19d09903240ce000c7c6192f41618a3c4b82320ff872433516d89a04181a40a1833c0d6000c7bfd12f61600a384b32280f886ee31615709483d4189096031c0be000c7b9872f41624a524d1233101c73a336167099840219909b03440d8000c7b3782dc15709fa49f2200f806f831c15d09103cc17f08d82dc0aa000c7ad1d2ff165ca704d92331058756339162097c3f81a509e83440c6000c7a6fc2db15409ce47e2118ee86c430615088fc3b418309602f80b8000c7a0b72ef15dca244b32240fa06fe31f15b897c40019e09b833c0ca000c79a7d2ed95d4a1e4ad2210f586de308156093c3dc18c09783300d4000c7946b2df95689ec49d21d8f546f430d15909283a817e08d03040c6000c78e202f215f8a2a4ab2248f8c70a31e15f89543c618708b02f00be000c787f72e51590a1a4a92230f6c6ea31115289083c218b09583400cc000c781b72f315f0a3a4ab2240f946fc31c15d89603e419009b03680ce000c77b722f295f4a2c4ac2268f906ee311157895c3d619209783300ce000c7752b2f115d4a0a4aa2210f586ec31515b09643e818d09603140ca000c76ee02f71630a464bd2290fec71831e16109583ea19209b03380ce000c768c72de95709e448a2110f006c6303152893c3d819209482ec0c4000c762812f215f4a244af2240f9870431a15a09543e618b08d82fc0b0000c75c272ff1630a584cb235902074c33a16a89a43f418e09883440ce000c755fd2e31570a0a4a22210f606dc31c15f89683e419209403280ba000c74fcb2e695c8a104ab21f0f606e831715609343b416d08502c00ac000c749682f89648a6a4d023990287443401730a044281a80a083680dc000c7433f2e415889fc4992190f286de31515e09443e819b09603300c6000c73cf62f715dca144ae21f8f7c70032415b89343e219609383340c6000c736b02ee95c4a304ac2220f506e230315108e43b217608b82e80b8000c7304b3009670a5a4c222a8fa071a32b15c89443de18f09503280cc000c72a202e1957ca0c49c2178f446e8311153892c3d218909082e80ae000 else 0xca40982e515989f44922158f106c630315589343fe19009b83200ba000ca3a672eb158ca2e4af2240f9c6fa30f15189043b218509102d00c0000ca340c2f99604a464cb232100873033516889683f019509903480e4000ca2dc42f315eca2e4b72278fa871c328164097440019409783280b4000ca279e2de15789f24a62238fa070832915c093c3d218108d82f00b0000ca21822e095ac9fa4922198f6c6ec310156091c3d818309983480e2000ca1b602e115589f249821e0f6870032416109c840c19709703140c4000ca154a2dd95649e849c2168f386e430c15409303e4196097830c0ba000ca0f032ef95c8a3a4c322a0fcc70632616089903f418f09383440d0000ca08c92ea95eca2c4b122b8fc472433316789a43f019009483300c6000ca027a2f21604a4c4c62298ff473033316a89bc4181a309d03640d8000c9fc402f215b4a084a42210f806f231816109803ec18e092030c0c0000c9f5f82f11640a4e4ba22f0fd470e31b15b09683ee19409203100c2000c9efd52e015689e24882130f286e430d154092c3b817e08f83200d6000c9e9a32e71588a004a32260fa070232a16789c040e1a209e83240cc000c9e3892de95749e448620e8ee469e2f914f08e03c618509202e00ba000c9dd562e715c0a204b622b8fec73a331163899040419f09b833c0c4000c9d72f2e495889ea4912188f1c6c22fa14a88f43b817908d030c0c8000c9d0e52eb95aca0c4a42220f786f231515c098440219309a83140ce000c9cac02e795b4a104aa2260f9870a31d15d092c3da19209b03400b8000c9c48e2ea15d0a284ad22a8fc0724333167098c40419c09a83580d2000c9be452ef95d4a1e49c21e0f786f031a15d09483de19209a03300d2000c9b7f92f59628a3e4c22310fe473033816509b440219809c03280c4000c9b1bd2eb95cca1c4a02200f686ec31615c09643ee19509b832c0d0000c9ab8a2e595d8a184ac2208fb872232315c89383c418309503280c4000c9a5502e615a8a164a92260f9070632216109643f61a40a203340d8000c99f552cd95409e048c2160f706fa30f15609543ce18509002e40d0000c999182ea95dca324b22278f746f830f15c09283c417808f82fc0c2000c992d52f295d4a2e4b52268fa470e32415e096c3f418f099030c0c0000c98cb72e415a0a0249721f0f946f6313155892c3dc18a09302e80ae000c986932e795c4a0c4a82238f6c6f430f15308f43c417a09003180c0000c980612de958ca184ad2240fb071c32616489643dc18f09303040ba000c979ec30896b0a9c4d923b905876234917309cc41a1a709f03440de000c973a52ec15dca1a4a42220f706f831715389003c018b09383200d6000c96d702e895b4a0849e21b8f546ea31415a09483d818309a83580f2000c9674e2e215889e04832188f286d830c15509343c018209083200d4000c961132ef15f8a304a82210fac71c33316609783f219d09983440de000c95ab62f59618a3a4b12248fc071632115c09603f219909783140d0000c954622f2161ca464bf22e0fdc72c33716a89b43f0199096034c0d6000c94e472da15389e248d21a8f546ea31015509483d8187092031c0c0000c9481f2e395989f649b2190f346d230314a88dc3a817508d02e00be000c941f62e2156c9f849a21c8f346de30714c09343d218509402fc0c6000c93bba2ea95dca1a4c1236102473a33716509a840e19809903240c2000c935493061694a784de23c103c74633516589783e218f09583300d2000c92ee33031690a8c4dd23b903474032e167099c40019709d03700e6000c928c32e09570a004a52238f9070630615589143b217a08d02f80c4000c922762ef9610a2e4bc2228f6c6de31515809683e018709603440d2000c91c572db15509d648c2150f386c430315288fc3c417f09083180c2000c9160d2f115f4a224b922c0fc072032d160095c3e418e09803380c6000c90fc02fb9614a424c92318fe073a33e169096c3fc19b098832c0da000c9099b2e2158c9f649621a0f306cc30215188f03b418609202e00c6000c9033e2f91638a484b322d8fec72432115f09243c217f08d83040bc000c8fce92f99640a664ca22e0fe072833416009603ee19b09d032c0d2000c8f6982fc9664a5a4c3237102475a34216d099440019509d036c0e6000c8f0562f21604a464c02318fd072833816809b44181ac09d03380dc000c8ea342e295a4a224a82250fa870832515f89843fe19e098033c0ce000c8e4042ee95f8a2c4af2220fac71232415f09643cc19309383280c8000c8dddc2e595c4a0c4ac21e8f646ea31215609283de18509503540ce000c8d768307169ca8e4cc2338fec72433716d09b840e1a309c03200d0000c8d13f2da15249ea48d2158f246de30614f89403ca17708b02f80b2000c8cafb2f3960ca2a4c022a8fb470e31a15c89683ec18b09302e40c6000c8c4df2dd15309c848320f0f086c430215109043a417308d03240d2000c8beae2e495809f24932178f2c6c430b15389283de18a09382fc0c4000c8b86e2ee15c4a304b422d8fe472233216709ac40a19d09c834c0d2000) else (if i < 124 then 0xcbcd752dd155c9de48a2118ecc6ac2f814e08e43aa1710858294096000cbc73a2e5958ca124a32200f4470030f155095c3e419009202f40b8000cbc1042e495549e649b21a0f486dc30e15009043ba18409302f80c6000cbbaef2db95309ca47f20c0ed06ac2f814e08cc3a416e08c83040b0000cbb4a12f4960ca444ca2308fe070a31515888f43b817b08f830c0be000cbae762ec95bca0c49821b0f446d030815789303ea19009102f80c4000cba83f2e4958ca0649921f0f706f031115b09283c218809183200d2000cba1f42f595fca2a4b02250f9870832015d89704161a209e83740d2000cb9bda2e215949ee4902178f246da30815a09483e419009683340c6000cb95792ff966ca764d2235900c74033a16989e84021a309d83480d8000cb8f5c2e2956c9fc4a12208f6c6f432415d89443e419409982e00bc000cb89132ef95c0a344b22228f746f0312158093c3ce18809082e40be000cb83202cd150c9c848120e8ee86be2fe14708bc39c17a08982f40b6000cb7ce62e61594a124942160f006d430314f89143c018309b03380da000cb769f2ee95b8a1a4ac2248fa470432216089783e418b09483080c0000cb708c2d615389d649421b8f486d630215309083d018209583240c2000cb6a512ee95e8a3c4bd22d0fe071e32816309783fe197096030c0c6000cb63da30b16a0a8c4e0241102473c33f16d89f44301c00a703800e0000cb5d942f21604a404c722e8fc4722339167899c40a19909983380cc000cb57502ec95fca2c4ad2260f9470a32916189743fc18f096032c0b2000cb514a2d415409e848a2180f546ec30b15209083c418508f02e40bc000cb4b0c2ec159c9fa4a321f0f806fc31615a892c3dc19209403140d2000cb44d92e915b0a0c4a221c0f8c70a33416b09dc42e1b30a103640e4000cb3e852fa9648a5c4c42300fec72c33516a89843d8187091030c0d0000cb38572e99598a044962178f086ae30115088e03b217e08e82fc0ce000cb32422db95589f24a52210f7c6e630e15809383dc18109182e00c8000cb2bf02fc9634a4e4be235900c72832615f89543f019d09a83480d2000cb25ae2ee15e0a404bb2280fb471432b160096c3fa18809203400d8000cb1f842e715d0a344bc2298f9c6f432315c093c3c417a08c82e40ac000cb19572e3158ca0c4a52200f8470431f16689743da18f09302d40b0000cb13222e915bca204aa2238f5c6f0316159090c3cc17b08d03000be000cb0cbf2fd9638a364bc2290fc872032915a89383e4189098032c0bc000cb06aa2de955c9f649b2180f306e631315289203b417908f82f40bc000cb006d2ea15b4a1e4b022b8fbc70a32616209883fe19909c033c0d6000cafa402e815a09fe48f2148f546d6315158894c3ea18408d02e80b2000caf3fe2e915909f049521a0f6c6f231f15d89443d018a09703180dc000caedda2de15709fe4ad2270f80702325161098c3fe19a0a0033c0c0000cae7932f395eca2a4ae2280fb06fe32515c09503e818009202f00ac000cae1a22c994cc9ae4782088edc6b42fe154892c3d418a09382e00cc000cadb732e395689e648b2140f186e831415309183b618408e82e80b6000cad5552de1584a0c49e2220f7c6f232015f097c3ea18f09683100c6000cacf292e715bc9fa4932170f386ce31215509283d019109a83680c0000cac8cb2fb1634a4a4bd22c0fb471e32e162095440019209b03200c4000cac2a42dc954c9f24a321a0f946de307155891c3c817b08e83000bc000cabc7d2e3157ca004962170f406d830d15489243c817c08e83080b6000cab6282f8962ca364ba2238fa8714326165098c4041a109b83600d8000caaffc2e31574a044a82200f6c6f631f15a090c3d819109783180c4000caa9f52d815589ea49521b0f746f632415b894c3e019409603280b4000caa3cb2e095789f049e2218f746d02f6142886c38016608b02e80b4000ca9d9c2e115709ee4982148f406d830614d08f03b417908802c80ae000ca97692e995b4a1849d21b8f486ec31e15a09543d8189097030c0b6000ca91572d415209d648c2160f3c6dc30014d08e03c618a09283240ba000ca8b012fb1640a504b62290fd873433916909c04061a709c03340cc000ca84d52e195c8a164a72290f9870632315e89503e619309383400dc000ca7e992e895a4a124a321c8f7c6e630914b08e439c17108c83100c2000ca78602e895aca204b42298fbc70a32a16489683f219309c03240ce000ca72292ed1604a304a52238f586da30a15209183d418909603140be000ca6bec2ea95bca0649a2170f306e831715b09583dc19209503000c2000ca65bd2e595a0a0a4a92218fb070c31e15f097840019e09b03300e4000ca5f8b2ec95c8a1a4a72200f486e231715b09283ca18709403300da000ca595f2e095889fc49b2218f5c6ec31215909643e818b096832c0c2000ca530a2fb1654a624c92330ffc74433f16a89dc42019e09983140c4000ca4cf22d995689fe49d2168f186da30e14f88e03a617708902b40b4000ca46be2e1957c9f449a21d8f4c6e230a15c09343de18a09202f00aa000 else 0xccc6e40000000000000000000000000000000003c817c09183080be000ccc09a2f295f8a2c4b12290fbc70c32015c09343d018109182fc0c4000ccba472f81634a604ce2278fa86fe314153891c3ac17308a02e40b4000ccb40d2eb15e4a2c49f21b0f1c6ce30a15209143c218009103340bc000ccadb0300965ca7e4d02359010718317161094c3e218808f82fc0c2000cca7982de15609fe49c21a8efc6c430815409543e819709903400cc000cca10b31a9704abc4fc24890a477034f16e0a1c4301b10a303540e2000cc9ac92ee95dca164a32208f346d230d154094c3da19009d83500dc000cc94772f6963ca584c82308fec72e324162098040419a09d83480d0000cc8e552e41580a0449c21a0f546de30d15088fc3c618b09283000c2000cc87eb30a16c0a844d72310fe874c34616c89e442e1b00a403680cc000cc818f2fa1634a504cd2370ff072032916389703ea18c09503180c8000cc7b4c2ee15d0a2e4b02278f8471e32b16309743fc19209b83340de000cc75192ed95e8a1c4ac2268fb072832916189803f2197097831c0c8000cc6edf2e915bca244b92278f9070432c16589843f419209403340c6000cc68982f195dca304a72228f846f031415e09643e418909182ec0c4000cc62762e1958c9ce4832108ef86c830d15b09743f219409983340c8000cc5c083019640a564c622c100473c33616c09f44261b70a403640e6000cc55e22e495909ec4982198f586ec30e15389203da18309483080c0000cc4fc72da953c9de48a2120ef86ca2f214988e03be17808882b00ba000cc49872ed95f0a164972200f346f232215d095c3e219709603180c6000cc435e2e295709e049121a0f206ce30b15889303b817909002dc0b2000cc3d092f71600a384ad2258f946fc31915909883f619309903340d8000cc36c32f89644a4c4bd2280fbc72c339164099440a1a109c032c0cc000cc30a32dd956ca224a321f8f906fa32415e09703e4198095031c0c6000cc2a812e195489dc48e20e0ed86982eb14988a839c17008d02f40b0000cc24163019698a7e4d723c103474c34416f89f04221a609a83480d6000cc1ddd2e895c4a124b022a0f8c6f031715789403d418909503080b0000cc17b32e115a8a0849c2120efc6b82fc15208f83c418d09282f80c6000cc11612f7162ca364c122a0fb870e31715a89403ca18909603100c8000cc0b2b2ea95b0a0249c21a8f2c6c030815809403e4190096031c0c2000cc05182d895589f44932168f0c6c630b14e88f43bc17608e02f40a2000cbfee32e815dca224a62208f6c6f631215789483f019509482fc0a8000cbf8e32d3152c9d048a2168f2c6be30115108f83ac17d09182f80b6000cbf2ca2db95649f44992178f446dc31715909543fe18b09202f00c0000cbec952e895d8a204b02220f7c6f431616209743dc18808e02d00c2000cbe65b2ed95d0a224ab2220f806f032216409643e218e08f83100c0000cbe0022f79630a604d22300fec73833e16f09cc4381ab09f83740f0000cbd9b12ee15d0a244b62288fac70c31615789043d418408a82d40b0000cbd38e2e415b4a0e49b2168f486e830a15589403ce17f08e02e40c8000)))))))

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



private theorem b114519 : covered 114519 114644 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b114644 : covered 114644 114768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b114768 : covered 114768 114893 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b114893 : covered 114893 115017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b115017 : covered 115017 115142 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b115142 : covered 115142 115266 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b115266 : covered 115266 115391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b115391 : covered 115391 115516 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b115516 : covered 115516 115641 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b115641 : covered 115641 115765 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b115765 : covered 115765 115890 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b115890 : covered 115890 116014 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b116014 : covered 116014 116139 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b116139 : covered 116139 116263 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b116263 : covered 116263 116388 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b116388 : covered 116388 116513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b116513 : covered 116513 116638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b116638 : covered 116638 116762 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b116762 : covered 116762 116887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b116887 : covered 116887 117011 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b117011 : covered 117011 117136 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b117136 : covered 117136 117260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b117260 : covered 117260 117385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b117385 : covered 117385 117510 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b117510 : covered 117510 117635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b117635 : covered 117635 117759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b117759 : covered 117759 117884 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b117884 : covered 117884 118008 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b118008 : covered 118008 118133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b118133 : covered 118133 118257 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b118257 : covered 118257 118382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b118382 : covered 118382 118507 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b118507 : covered 118507 118632 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b118632 : covered 118632 118756 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b118756 : covered 118756 118881 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b118881 : covered 118881 119005 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b119005 : covered 119005 119130 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b119130 : covered 119130 119254 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b119254 : covered 119254 119379 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b119379 : covered 119379 119504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b119504 : covered 119504 119629 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b119629 : covered 119629 119753 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b119753 : covered 119753 119878 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b119878 : covered 119878 120002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120002 : covered 120002 120127 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120127 : covered 120127 120251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120251 : covered 120251 120376 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120376 : covered 120376 120501 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120501 : covered 120501 120626 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120626 : covered 120626 120750 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120750 : covered 120750 120875 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120875 : covered 120875 120999 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b120999 : covered 120999 121124 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b121124 : covered 121124 121248 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b121248 : covered 121248 121373 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b121373 : covered 121373 121498 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b121498 : covered 121498 121623 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b121623 : covered 121623 121747 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b121747 : covered 121747 121872 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b121872 : covered 121872 121996 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b121996 : covered 121996 122121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b122121 : covered 122121 122245 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b122245 : covered 122245 122370 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b122370 : covered 122370 122495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b122495 : covered 122495 122620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b122620 : covered 122620 122744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b122744 : covered 122744 122869 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b122869 : covered 122869 122993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b122993 : covered 122993 123118 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b123118 : covered 123118 123242 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b123242 : covered 123242 123367 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b123367 : covered 123367 123492 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b123492 : covered 123492 123617 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b123617 : covered 123617 123741 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b123741 : covered 123741 123866 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b123866 : covered 123866 123990 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b123990 : covered 123990 124115 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b124115 : covered 124115 124239 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b124239 : covered 124239 124364 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b124364 : covered 124364 124489 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b124489 : covered 124489 124614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b124614 : covered 124614 124738 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b124738 : covered 124738 124863 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b124863 : covered 124863 124987 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b124987 : covered 124987 125112 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b125112 : covered 125112 125236 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b125236 : covered 125236 125361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b125361 : covered 125361 125486 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b125486 : covered 125486 125611 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b125611 : covered 125611 125735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b125735 : covered 125735 125860 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b125860 : covered 125860 125984 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b125984 : covered 125984 126109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b126109 : covered 126109 126233 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b126233 : covered 126233 126358 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b126358 : covered 126358 126483 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b126483 : covered 126483 126608 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b126608 : covered 126608 126732 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b126732 : covered 126732 126857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b126857 : covered 126857 126981 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b126981 : covered 126981 127106 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127106 : covered 127106 127230 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127230 : covered 127230 127355 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127355 : covered 127355 127480 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b127480 : covered 127480 127605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 114519 127605 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b114519 (joinCoverage b114644 b114768)) (joinCoverage b114893 (joinCoverage b115017 b115142))) (joinCoverage (joinCoverage b115266 (joinCoverage b115391 b115516)) (joinCoverage (joinCoverage b115641 b115765) (joinCoverage b115890 b116014)))) (joinCoverage (joinCoverage (joinCoverage b116139 (joinCoverage b116263 b116388)) (joinCoverage b116513 (joinCoverage b116638 b116762))) (joinCoverage (joinCoverage b116887 (joinCoverage b117011 b117136)) (joinCoverage (joinCoverage b117260 b117385) (joinCoverage b117510 b117635))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b117759 (joinCoverage b117884 b118008)) (joinCoverage b118133 (joinCoverage b118257 b118382))) (joinCoverage (joinCoverage b118507 (joinCoverage b118632 b118756)) (joinCoverage (joinCoverage b118881 b119005) (joinCoverage b119130 b119254)))) (joinCoverage (joinCoverage (joinCoverage b119379 (joinCoverage b119504 b119629)) (joinCoverage b119753 (joinCoverage b119878 b120002))) (joinCoverage (joinCoverage b120127 (joinCoverage b120251 b120376)) (joinCoverage (joinCoverage b120501 b120626) (joinCoverage b120750 b120875)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b120999 (joinCoverage b121124 b121248)) (joinCoverage b121373 (joinCoverage b121498 b121623))) (joinCoverage (joinCoverage b121747 (joinCoverage b121872 b121996)) (joinCoverage (joinCoverage b122121 b122245) (joinCoverage b122370 b122495)))) (joinCoverage (joinCoverage (joinCoverage b122620 (joinCoverage b122744 b122869)) (joinCoverage b122993 (joinCoverage b123118 b123242))) (joinCoverage (joinCoverage b123367 (joinCoverage b123492 b123617)) (joinCoverage (joinCoverage b123741 b123866) (joinCoverage b123990 b124115))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b124239 (joinCoverage b124364 b124489)) (joinCoverage b124614 (joinCoverage b124738 b124863))) (joinCoverage (joinCoverage b124987 (joinCoverage b125112 b125236)) (joinCoverage (joinCoverage b125361 b125486) (joinCoverage b125611 b125735)))) (joinCoverage (joinCoverage (joinCoverage b125860 (joinCoverage b125984 b126109)) (joinCoverage (joinCoverage b126233 b126358) (joinCoverage b126483 b126608))) (joinCoverage (joinCoverage b126732 (joinCoverage b126857 b126981)) (joinCoverage (joinCoverage b127106 b127230) (joinCoverage b127355 b127480)))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 114519 ≤ index 220000000/512 := by decide +kernel
private theorem starting_value : fast 220000000=12122540 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 220000000=12122540) (n : ℕ) (low : 220000000≤n) (bound : n≤245000000) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=220000000
    · rw [first,anchor]
      exact starting_value
    · have past : 220000000≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤245000000 by omega)
        have within : index n / 512 < 127605 := by omega
        have lower : index 220000000/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤245000000) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ220000000To245000000
