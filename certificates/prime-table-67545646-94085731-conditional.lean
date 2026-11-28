import FormalConjectures.OEIS.«247824»

/-! Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeQ67545646To94085731

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




private def radical : ℕ := 0x15b3f58835a10d3270da9d382d903709fcf2ceec253427fee484a5c99928cddf8a82beb478e71096586636c95652a5b96ef5387323298ab5b7b600a5443b3491cd643b48bc3bf1a59ca7830df8c2437785a87f9208e6a2dc3e0c5c4a7aabc2285508745740e9b7ab0a19291b430de59aa0b6ea70b8dbbbe062fc4e96dd580de02a0ec3865e40fcd98431618384717a432270bbf8aa9f9527122ecdd72be813f5ca5fe976b6e1d12f3e64dc36ef191d36dce5876922c00815739d630ace76aa716b658851ed23cccf551b1045f58dc390c3ca52f68b84ffac7459fcac95c74b51b68312cdba156ea889d3516c9cd9c2dfe32ed327f3b07acc9973311feea0baacaeb4f8b22f3e921e69b1d1db076947250392b4cbc130da686fdcde267ae3f179986647632bdade6bcb51a9f133530fae66af69e67c692a7fb9aa052835ff9b68e0b8431b45f175a5035ec9249a0e85154412f8e29a0f395f967e9ab7089a868ef6667f2a1ccb35b193ec8d1e81ea9b1bed8196f34e6dfad9f89ed3c37c7ce04fe36ac54af18e4d26705b4605fd879c7990d5784d783f1799a9adb285e16947cf840bf11e8207d9917c4a9797e778c4f2b4864fcb2332689875a9a97b7e6726a8293303769ae19ad1048c1fdd367ccc19d7253e12d225bec2ecab1791123a1d21fd404c67fd6a82d541602b46d5623fb3d4cc0a13ae1a4092c264ae19a2e803127424812d281355a8b8289a8a0db2f008295c7c8a6861f752e939137e62554a033f1cc7c07ff00de457f30faa29d65acf2b8774b366418ffcca51b94aa31d64aec246b6c9c52ed08ad48a0d1945b118d3b91573f5528830eb24856b04b2bb38696c3358ddaadf20d11317173e3dd9e059aa01d16568d65794b6bfec3fef367d840d537d36e606058c4694ac8f4a9a9ad374c32f1ef216097251db1bee6db15fa14e55b72638ed9531e05031f1bb3b074cdad4c5e7787fb17e6649f06241c6f809ad4ccb06c7bc6a269b1c344a2429e2711f7494eb2d73694cb6571d360fa664ef706cd30f123b3b0ff679eb038d984106a227ac54c52a748f032bed17c016e54afd8fd8e3294c75a4d5b343a1031e5f1064e4b0d099be0b50e2d0c958b19cf789cd63444da03efc0de444ecc3db824beeac136b33af252beaa2f1c8a2e9d3ce9ba5ca61127c571f97c6299fe0c814f2a6eeee891a07fa2252df1351379b38ae1bf54c004d5cb7025a0fe9d1dd76892442e5aebe8f0e05737f0354bd1acf2fc2eca73a53b11ab79a9253c1035baee0ae058065bb158a0dca258ba5fcc691cd07290c676068d6658a9d67a0fabec99c1f65be22728c18e6f5e151fcd76e5ea994eff7180153e3926f11802e83dfece9684b028c37d99b1deb43120fc600c067df4abbf034538f64f545f6e608c20ad226fb64f8626107a70d564388fc27ab8a6d8e353ffb78e0e767b3e3664504785391d140cd52ed73afe6644715e6caa1217f6850ec8662c06db71d21b909d5c2716b2f83a5c63d11b0ba056a02387d2032d5ab0eec6f2f01bd5334eaf383d47f61c06055331ae47783c9237638471b1842b6c375f10c1938380571fb78fca8d6c906ac4d9c5e1d96a839f4d003785d54747d12bda1a5d8287234289a5cd8191f0b1a3c865fcefec2b58e5c8d51a301bc1ba71c4560b4ceecf2bc394d0a84dc67fbaa2931af97ea57366045bcf2884c37783b4dc3ad9f9ac0a690605d23951ebad0f5ec13261d5df8a5b7fc62a83f2cea08a433b83e5a987ca07fa015ceee3f64ea740b3e2a135cae76c8f9c9630dfc64c21d9d501ef2b65234874a7cc1528c062fc02d1fc9dfa50e7b5c674a5c3daa6bfcf4d7b930111386ef4c9379ef29bf2ea8287ff467f7bbcd9c6ae1a079827c1deefba16e02c5c1893028af3e37350b1eb4d3569a70c460ca656b09fd52bbd8736e6c70d03a75e45b62496766cd26b8f16470f1e79185898834cbb8d842e668972e277e802240b6b0f71024acc49f3f40d1f548019ba33aaf595e04e5916ace0c539cecbfc708ec937e19bf8931645e853b98e7318f54e8b850da56d48e2ce7e98e0ec0e9b8dc302955bd4cbe902fd8d0d9fe3d63e6208c97c1088b5d5c2b4ff455ca3991af698bf746789b5e7f576609b9217273d52e4a942f5fd926dc41b9107f2cfc6e1be6c86e9303226647f4b5ca50e20a347c024f1679b98996c2e811ab5a437aa5c056b2f8e63a71a62adfee5bdbc43b42f9de0e5dfe925e8b4c985e50ce84f3502124b2ff6be8eb6d55638f85d6505ebe39998fcb8b87cb0861265fe392327ba7e8b6c99fc4a839587d4483c1b5c35a308fe814f711cbaf283353e44401798501bda67f1ace2602611861dca3c46b2b8d79fe8a019186e795fdece9439d26afa7a255efc9f538fb5df354c7e623d7a35d505778d51e5e60c54c8ce86df6527687335ac6

private def light (n : ℕ) : Bool :=
  if n≤98 then decide n.Prime else n.gcd 9426890448883247745626185743057242473809693764078951663494238777294707070023223798882976159207729119823605850588608460429412647567360000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤9699) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 98 = 9426890448883247745626185743057242473809693764078951663494238777294707070023223798882976159207729119823605850588608460429412647567360000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 98 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤9699 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 37 := by unfold smallValid; decide +kernel

private theorem sp37 : smallValid 37 38 := by unfold smallValid; decide +kernel

private theorem sp75 : smallValid 75 38 := by unfold smallValid; decide +kernel

private theorem sp113 : smallValid 113 38 := by unfold smallValid; decide +kernel

private theorem sp151 : smallValid 151 38 := by unfold smallValid; decide +kernel

private theorem sp189 : smallValid 189 38 := by unfold smallValid; decide +kernel

private theorem sp227 : smallValid 227 38 := by unfold smallValid; decide +kernel

private theorem sp265 : smallValid 265 38 := by unfold smallValid; decide +kernel

private theorem sp303 : smallValid 303 37 := by unfold smallValid; decide +kernel

private theorem sp340 : smallValid 340 38 := by unfold smallValid; decide +kernel

private theorem sp378 : smallValid 378 38 := by unfold smallValid; decide +kernel

private theorem sp416 : smallValid 416 38 := by unfold smallValid; decide +kernel

private theorem sp454 : smallValid 454 38 := by unfold smallValid; decide +kernel

private theorem sp492 : smallValid 492 38 := by unfold smallValid; decide +kernel

private theorem sp530 : smallValid 530 38 := by unfold smallValid; decide +kernel

private theorem sp568 : smallValid 568 38 := by unfold smallValid; decide +kernel

private theorem sp606 : smallValid 606 37 := by unfold smallValid; decide +kernel

private theorem sp643 : smallValid 643 38 := by unfold smallValid; decide +kernel

private theorem sp681 : smallValid 681 38 := by unfold smallValid; decide +kernel

private theorem sp719 : smallValid 719 38 := by unfold smallValid; decide +kernel

private theorem sp757 : smallValid 757 38 := by unfold smallValid; decide +kernel

private theorem sp795 : smallValid 795 38 := by unfold smallValid; decide +kernel

private theorem sp833 : smallValid 833 38 := by unfold smallValid; decide +kernel

private theorem sp871 : smallValid 871 38 := by unfold smallValid; decide +kernel

private theorem sp909 : smallValid 909 37 := by unfold smallValid; decide +kernel

private theorem sp946 : smallValid 946 38 := by unfold smallValid; decide +kernel

private theorem sp984 : smallValid 984 38 := by unfold smallValid; decide +kernel

private theorem sp1022 : smallValid 1022 38 := by unfold smallValid; decide +kernel

private theorem sp1060 : smallValid 1060 38 := by unfold smallValid; decide +kernel

private theorem sp1098 : smallValid 1098 38 := by unfold smallValid; decide +kernel

private theorem sp1136 : smallValid 1136 38 := by unfold smallValid; decide +kernel

private theorem sp1174 : smallValid 1174 38 := by unfold smallValid; decide +kernel

private theorem sp1212 : smallValid 1212 37 := by unfold smallValid; decide +kernel

private theorem sp1249 : smallValid 1249 38 := by unfold smallValid; decide +kernel

private theorem sp1287 : smallValid 1287 38 := by unfold smallValid; decide +kernel

private theorem sp1325 : smallValid 1325 38 := by unfold smallValid; decide +kernel

private theorem sp1363 : smallValid 1363 38 := by unfold smallValid; decide +kernel

private theorem sp1401 : smallValid 1401 38 := by unfold smallValid; decide +kernel

private theorem sp1439 : smallValid 1439 38 := by unfold smallValid; decide +kernel

private theorem sp1477 : smallValid 1477 38 := by unfold smallValid; decide +kernel

private theorem sp1515 : smallValid 1515 37 := by unfold smallValid; decide +kernel

private theorem sp1552 : smallValid 1552 38 := by unfold smallValid; decide +kernel

private theorem sp1590 : smallValid 1590 38 := by unfold smallValid; decide +kernel

private theorem sp1628 : smallValid 1628 38 := by unfold smallValid; decide +kernel

private theorem sp1666 : smallValid 1666 38 := by unfold smallValid; decide +kernel

private theorem sp1704 : smallValid 1704 38 := by unfold smallValid; decide +kernel

private theorem sp1742 : smallValid 1742 38 := by unfold smallValid; decide +kernel

private theorem sp1780 : smallValid 1780 38 := by unfold smallValid; decide +kernel

private theorem sp1818 : smallValid 1818 37 := by unfold smallValid; decide +kernel

private theorem sp1855 : smallValid 1855 38 := by unfold smallValid; decide +kernel

private theorem sp1893 : smallValid 1893 38 := by unfold smallValid; decide +kernel

private theorem sp1931 : smallValid 1931 38 := by unfold smallValid; decide +kernel

private theorem sp1969 : smallValid 1969 38 := by unfold smallValid; decide +kernel

private theorem sp2007 : smallValid 2007 38 := by unfold smallValid; decide +kernel

private theorem sp2045 : smallValid 2045 38 := by unfold smallValid; decide +kernel

private theorem sp2083 : smallValid 2083 38 := by unfold smallValid; decide +kernel

private theorem sp2121 : smallValid 2121 38 := by unfold smallValid; decide +kernel

private theorem sp2159 : smallValid 2159 38 := by unfold smallValid; decide +kernel

private theorem sp2197 : smallValid 2197 38 := by unfold smallValid; decide +kernel

private theorem sp2235 : smallValid 2235 38 := by unfold smallValid; decide +kernel

private theorem sp2273 : smallValid 2273 38 := by unfold smallValid; decide +kernel

private theorem sp2311 : smallValid 2311 38 := by unfold smallValid; decide +kernel

private theorem sp2349 : smallValid 2349 38 := by unfold smallValid; decide +kernel

private theorem sp2387 : smallValid 2387 38 := by unfold smallValid; decide +kernel

private theorem sp2425 : smallValid 2425 37 := by unfold smallValid; decide +kernel

private theorem sp2462 : smallValid 2462 38 := by unfold smallValid; decide +kernel

private theorem sp2500 : smallValid 2500 38 := by unfold smallValid; decide +kernel

private theorem sp2538 : smallValid 2538 38 := by unfold smallValid; decide +kernel

private theorem sp2576 : smallValid 2576 38 := by unfold smallValid; decide +kernel

private theorem sp2614 : smallValid 2614 38 := by unfold smallValid; decide +kernel

private theorem sp2652 : smallValid 2652 38 := by unfold smallValid; decide +kernel

private theorem sp2690 : smallValid 2690 38 := by unfold smallValid; decide +kernel

private theorem sp2728 : smallValid 2728 37 := by unfold smallValid; decide +kernel

private theorem sp2765 : smallValid 2765 38 := by unfold smallValid; decide +kernel

private theorem sp2803 : smallValid 2803 38 := by unfold smallValid; decide +kernel

private theorem sp2841 : smallValid 2841 38 := by unfold smallValid; decide +kernel

private theorem sp2879 : smallValid 2879 38 := by unfold smallValid; decide +kernel

private theorem sp2917 : smallValid 2917 38 := by unfold smallValid; decide +kernel

private theorem sp2955 : smallValid 2955 38 := by unfold smallValid; decide +kernel

private theorem sp2993 : smallValid 2993 38 := by unfold smallValid; decide +kernel

private theorem sp3031 : smallValid 3031 37 := by unfold smallValid; decide +kernel

private theorem sp3068 : smallValid 3068 38 := by unfold smallValid; decide +kernel

private theorem sp3106 : smallValid 3106 38 := by unfold smallValid; decide +kernel

private theorem sp3144 : smallValid 3144 38 := by unfold smallValid; decide +kernel

private theorem sp3182 : smallValid 3182 38 := by unfold smallValid; decide +kernel

private theorem sp3220 : smallValid 3220 38 := by unfold smallValid; decide +kernel

private theorem sp3258 : smallValid 3258 38 := by unfold smallValid; decide +kernel

private theorem sp3296 : smallValid 3296 38 := by unfold smallValid; decide +kernel

private theorem sp3334 : smallValid 3334 37 := by unfold smallValid; decide +kernel

private theorem sp3371 : smallValid 3371 38 := by unfold smallValid; decide +kernel

private theorem sp3409 : smallValid 3409 38 := by unfold smallValid; decide +kernel

private theorem sp3447 : smallValid 3447 38 := by unfold smallValid; decide +kernel

private theorem sp3485 : smallValid 3485 38 := by unfold smallValid; decide +kernel

private theorem sp3523 : smallValid 3523 38 := by unfold smallValid; decide +kernel

private theorem sp3561 : smallValid 3561 38 := by unfold smallValid; decide +kernel

private theorem sp3599 : smallValid 3599 38 := by unfold smallValid; decide +kernel

private theorem sp3637 : smallValid 3637 37 := by unfold smallValid; decide +kernel

private theorem sp3674 : smallValid 3674 38 := by unfold smallValid; decide +kernel

private theorem sp3712 : smallValid 3712 38 := by unfold smallValid; decide +kernel

private theorem sp3750 : smallValid 3750 38 := by unfold smallValid; decide +kernel

private theorem sp3788 : smallValid 3788 38 := by unfold smallValid; decide +kernel

private theorem sp3826 : smallValid 3826 38 := by unfold smallValid; decide +kernel

private theorem sp3864 : smallValid 3864 38 := by unfold smallValid; decide +kernel

private theorem sp3902 : smallValid 3902 38 := by unfold smallValid; decide +kernel

private theorem sp3940 : smallValid 3940 37 := by unfold smallValid; decide +kernel

private theorem sp3977 : smallValid 3977 38 := by unfold smallValid; decide +kernel

private theorem sp4015 : smallValid 4015 38 := by unfold smallValid; decide +kernel

private theorem sp4053 : smallValid 4053 38 := by unfold smallValid; decide +kernel

private theorem sp4091 : smallValid 4091 38 := by unfold smallValid; decide +kernel

private theorem sp4129 : smallValid 4129 38 := by unfold smallValid; decide +kernel

private theorem sp4167 : smallValid 4167 38 := by unfold smallValid; decide +kernel

private theorem sp4205 : smallValid 4205 38 := by unfold smallValid; decide +kernel

private theorem sp4243 : smallValid 4243 37 := by unfold smallValid; decide +kernel

private theorem sp4280 : smallValid 4280 38 := by unfold smallValid; decide +kernel

private theorem sp4318 : smallValid 4318 38 := by unfold smallValid; decide +kernel

private theorem sp4356 : smallValid 4356 38 := by unfold smallValid; decide +kernel

private theorem sp4394 : smallValid 4394 38 := by unfold smallValid; decide +kernel

private theorem sp4432 : smallValid 4432 38 := by unfold smallValid; decide +kernel

private theorem sp4470 : smallValid 4470 38 := by unfold smallValid; decide +kernel

private theorem sp4508 : smallValid 4508 38 := by unfold smallValid; decide +kernel

private theorem sp4546 : smallValid 4546 38 := by unfold smallValid; decide +kernel

private theorem sp4584 : smallValid 4584 38 := by unfold smallValid; decide +kernel

private theorem sp4622 : smallValid 4622 38 := by unfold smallValid; decide +kernel

private theorem sp4660 : smallValid 4660 38 := by unfold smallValid; decide +kernel

private theorem sp4698 : smallValid 4698 38 := by unfold smallValid; decide +kernel

private theorem sp4736 : smallValid 4736 38 := by unfold smallValid; decide +kernel

private theorem sp4774 : smallValid 4774 38 := by unfold smallValid; decide +kernel

private theorem sp4812 : smallValid 4812 38 := by unfold smallValid; decide +kernel

private theorem sp4850 : smallValid 4850 37 := by unfold smallValid; decide +kernel

private theorem sp4887 : smallValid 4887 38 := by unfold smallValid; decide +kernel

private theorem sp4925 : smallValid 4925 38 := by unfold smallValid; decide +kernel

private theorem sp4963 : smallValid 4963 38 := by unfold smallValid; decide +kernel

private theorem sp5001 : smallValid 5001 38 := by unfold smallValid; decide +kernel

private theorem sp5039 : smallValid 5039 38 := by unfold smallValid; decide +kernel

private theorem sp5077 : smallValid 5077 38 := by unfold smallValid; decide +kernel

private theorem sp5115 : smallValid 5115 38 := by unfold smallValid; decide +kernel

private theorem sp5153 : smallValid 5153 37 := by unfold smallValid; decide +kernel

private theorem sp5190 : smallValid 5190 38 := by unfold smallValid; decide +kernel

private theorem sp5228 : smallValid 5228 38 := by unfold smallValid; decide +kernel

private theorem sp5266 : smallValid 5266 38 := by unfold smallValid; decide +kernel

private theorem sp5304 : smallValid 5304 38 := by unfold smallValid; decide +kernel

private theorem sp5342 : smallValid 5342 38 := by unfold smallValid; decide +kernel

private theorem sp5380 : smallValid 5380 38 := by unfold smallValid; decide +kernel

private theorem sp5418 : smallValid 5418 38 := by unfold smallValid; decide +kernel

private theorem sp5456 : smallValid 5456 37 := by unfold smallValid; decide +kernel

private theorem sp5493 : smallValid 5493 38 := by unfold smallValid; decide +kernel

private theorem sp5531 : smallValid 5531 38 := by unfold smallValid; decide +kernel

private theorem sp5569 : smallValid 5569 38 := by unfold smallValid; decide +kernel

private theorem sp5607 : smallValid 5607 38 := by unfold smallValid; decide +kernel

private theorem sp5645 : smallValid 5645 38 := by unfold smallValid; decide +kernel

private theorem sp5683 : smallValid 5683 38 := by unfold smallValid; decide +kernel

private theorem sp5721 : smallValid 5721 38 := by unfold smallValid; decide +kernel

private theorem sp5759 : smallValid 5759 37 := by unfold smallValid; decide +kernel

private theorem sp5796 : smallValid 5796 38 := by unfold smallValid; decide +kernel

private theorem sp5834 : smallValid 5834 38 := by unfold smallValid; decide +kernel

private theorem sp5872 : smallValid 5872 38 := by unfold smallValid; decide +kernel

private theorem sp5910 : smallValid 5910 38 := by unfold smallValid; decide +kernel

private theorem sp5948 : smallValid 5948 38 := by unfold smallValid; decide +kernel

private theorem sp5986 : smallValid 5986 38 := by unfold smallValid; decide +kernel

private theorem sp6024 : smallValid 6024 38 := by unfold smallValid; decide +kernel

private theorem sp6062 : smallValid 6062 37 := by unfold smallValid; decide +kernel

private theorem sp6099 : smallValid 6099 38 := by unfold smallValid; decide +kernel

private theorem sp6137 : smallValid 6137 38 := by unfold smallValid; decide +kernel

private theorem sp6175 : smallValid 6175 38 := by unfold smallValid; decide +kernel

private theorem sp6213 : smallValid 6213 38 := by unfold smallValid; decide +kernel

private theorem sp6251 : smallValid 6251 38 := by unfold smallValid; decide +kernel

private theorem sp6289 : smallValid 6289 38 := by unfold smallValid; decide +kernel

private theorem sp6327 : smallValid 6327 38 := by unfold smallValid; decide +kernel

private theorem sp6365 : smallValid 6365 37 := by unfold smallValid; decide +kernel

private theorem sp6402 : smallValid 6402 38 := by unfold smallValid; decide +kernel

private theorem sp6440 : smallValid 6440 38 := by unfold smallValid; decide +kernel

private theorem sp6478 : smallValid 6478 38 := by unfold smallValid; decide +kernel

private theorem sp6516 : smallValid 6516 38 := by unfold smallValid; decide +kernel

private theorem sp6554 : smallValid 6554 38 := by unfold smallValid; decide +kernel

private theorem sp6592 : smallValid 6592 38 := by unfold smallValid; decide +kernel

private theorem sp6630 : smallValid 6630 38 := by unfold smallValid; decide +kernel

private theorem sp6668 : smallValid 6668 37 := by unfold smallValid; decide +kernel

private theorem sp6705 : smallValid 6705 38 := by unfold smallValid; decide +kernel

private theorem sp6743 : smallValid 6743 38 := by unfold smallValid; decide +kernel

private theorem sp6781 : smallValid 6781 38 := by unfold smallValid; decide +kernel

private theorem sp6819 : smallValid 6819 38 := by unfold smallValid; decide +kernel

private theorem sp6857 : smallValid 6857 38 := by unfold smallValid; decide +kernel

private theorem sp6895 : smallValid 6895 38 := by unfold smallValid; decide +kernel

private theorem sp6933 : smallValid 6933 38 := by unfold smallValid; decide +kernel

private theorem sp6971 : smallValid 6971 38 := by unfold smallValid; decide +kernel

private theorem sp7009 : smallValid 7009 38 := by unfold smallValid; decide +kernel

private theorem sp7047 : smallValid 7047 38 := by unfold smallValid; decide +kernel

private theorem sp7085 : smallValid 7085 38 := by unfold smallValid; decide +kernel

private theorem sp7123 : smallValid 7123 38 := by unfold smallValid; decide +kernel

private theorem sp7161 : smallValid 7161 38 := by unfold smallValid; decide +kernel

private theorem sp7199 : smallValid 7199 38 := by unfold smallValid; decide +kernel

private theorem sp7237 : smallValid 7237 38 := by unfold smallValid; decide +kernel

private theorem sp7275 : smallValid 7275 37 := by unfold smallValid; decide +kernel

private theorem sp7312 : smallValid 7312 38 := by unfold smallValid; decide +kernel

private theorem sp7350 : smallValid 7350 38 := by unfold smallValid; decide +kernel

private theorem sp7388 : smallValid 7388 38 := by unfold smallValid; decide +kernel

private theorem sp7426 : smallValid 7426 38 := by unfold smallValid; decide +kernel

private theorem sp7464 : smallValid 7464 38 := by unfold smallValid; decide +kernel

private theorem sp7502 : smallValid 7502 38 := by unfold smallValid; decide +kernel

private theorem sp7540 : smallValid 7540 38 := by unfold smallValid; decide +kernel

private theorem sp7578 : smallValid 7578 37 := by unfold smallValid; decide +kernel

private theorem sp7615 : smallValid 7615 38 := by unfold smallValid; decide +kernel

private theorem sp7653 : smallValid 7653 38 := by unfold smallValid; decide +kernel

private theorem sp7691 : smallValid 7691 38 := by unfold smallValid; decide +kernel

private theorem sp7729 : smallValid 7729 38 := by unfold smallValid; decide +kernel

private theorem sp7767 : smallValid 7767 38 := by unfold smallValid; decide +kernel

private theorem sp7805 : smallValid 7805 38 := by unfold smallValid; decide +kernel

private theorem sp7843 : smallValid 7843 38 := by unfold smallValid; decide +kernel

private theorem sp7881 : smallValid 7881 37 := by unfold smallValid; decide +kernel

private theorem sp7918 : smallValid 7918 38 := by unfold smallValid; decide +kernel

private theorem sp7956 : smallValid 7956 38 := by unfold smallValid; decide +kernel

private theorem sp7994 : smallValid 7994 38 := by unfold smallValid; decide +kernel

private theorem sp8032 : smallValid 8032 38 := by unfold smallValid; decide +kernel

private theorem sp8070 : smallValid 8070 38 := by unfold smallValid; decide +kernel

private theorem sp8108 : smallValid 8108 38 := by unfold smallValid; decide +kernel

private theorem sp8146 : smallValid 8146 38 := by unfold smallValid; decide +kernel

private theorem sp8184 : smallValid 8184 37 := by unfold smallValid; decide +kernel

private theorem sp8221 : smallValid 8221 38 := by unfold smallValid; decide +kernel

private theorem sp8259 : smallValid 8259 38 := by unfold smallValid; decide +kernel

private theorem sp8297 : smallValid 8297 38 := by unfold smallValid; decide +kernel

private theorem sp8335 : smallValid 8335 38 := by unfold smallValid; decide +kernel

private theorem sp8373 : smallValid 8373 38 := by unfold smallValid; decide +kernel

private theorem sp8411 : smallValid 8411 38 := by unfold smallValid; decide +kernel

private theorem sp8449 : smallValid 8449 38 := by unfold smallValid; decide +kernel

private theorem sp8487 : smallValid 8487 37 := by unfold smallValid; decide +kernel

private theorem sp8524 : smallValid 8524 38 := by unfold smallValid; decide +kernel

private theorem sp8562 : smallValid 8562 38 := by unfold smallValid; decide +kernel

private theorem sp8600 : smallValid 8600 38 := by unfold smallValid; decide +kernel

private theorem sp8638 : smallValid 8638 38 := by unfold smallValid; decide +kernel

private theorem sp8676 : smallValid 8676 38 := by unfold smallValid; decide +kernel

private theorem sp8714 : smallValid 8714 38 := by unfold smallValid; decide +kernel

private theorem sp8752 : smallValid 8752 38 := by unfold smallValid; decide +kernel

private theorem sp8790 : smallValid 8790 37 := by unfold smallValid; decide +kernel

private theorem sp8827 : smallValid 8827 38 := by unfold smallValid; decide +kernel

private theorem sp8865 : smallValid 8865 38 := by unfold smallValid; decide +kernel

private theorem sp8903 : smallValid 8903 38 := by unfold smallValid; decide +kernel

private theorem sp8941 : smallValid 8941 38 := by unfold smallValid; decide +kernel

private theorem sp8979 : smallValid 8979 38 := by unfold smallValid; decide +kernel

private theorem sp9017 : smallValid 9017 38 := by unfold smallValid; decide +kernel

private theorem sp9055 : smallValid 9055 38 := by unfold smallValid; decide +kernel

private theorem sp9093 : smallValid 9093 37 := by unfold smallValid; decide +kernel

private theorem sp9130 : smallValid 9130 38 := by unfold smallValid; decide +kernel

private theorem sp9168 : smallValid 9168 38 := by unfold smallValid; decide +kernel

private theorem sp9206 : smallValid 9206 38 := by unfold smallValid; decide +kernel

private theorem sp9244 : smallValid 9244 38 := by unfold smallValid; decide +kernel

private theorem sp9282 : smallValid 9282 38 := by unfold smallValid; decide +kernel

private theorem sp9320 : smallValid 9320 38 := by unfold smallValid; decide +kernel

private theorem sp9358 : smallValid 9358 38 := by unfold smallValid; decide +kernel

private theorem sp9396 : smallValid 9396 38 := by unfold smallValid; decide +kernel

private theorem sp9434 : smallValid 9434 38 := by unfold smallValid; decide +kernel

private theorem sp9472 : smallValid 9472 38 := by unfold smallValid; decide +kernel

private theorem sp9510 : smallValid 9510 38 := by unfold smallValid; decide +kernel

private theorem sp9548 : smallValid 9548 38 := by unfold smallValid; decide +kernel

private theorem sp9586 : smallValid 9586 38 := by unfold smallValid; decide +kernel

private theorem sp9624 : smallValid 9624 38 := by unfold smallValid; decide +kernel

private theorem sp9662 : smallValid 9662 38 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤9699) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 9700 := (joinSmall (lo:=0) (a:=4850) (b:=4850) (joinSmall (lo:=0) (a:=2425) (b:=2425) (joinSmall (lo:=0) (a:=1212) (b:=1213) (joinSmall (lo:=0) (a:=606) (b:=606) (joinSmall (lo:=0) (a:=303) (b:=303) (joinSmall (lo:=0) (a:=151) (b:=152) (joinSmall (lo:=0) (a:=75) (b:=76) (joinSmall (lo:=0) (a:=37) (b:=38) sp0 sp37) (joinSmall (lo:=75) (a:=38) (b:=38) sp75 sp113)) (joinSmall (lo:=151) (a:=76) (b:=76) (joinSmall (lo:=151) (a:=38) (b:=38) sp151 sp189) (joinSmall (lo:=227) (a:=38) (b:=38) sp227 sp265))) (joinSmall (lo:=303) (a:=151) (b:=152) (joinSmall (lo:=303) (a:=75) (b:=76) (joinSmall (lo:=303) (a:=37) (b:=38) sp303 sp340) (joinSmall (lo:=378) (a:=38) (b:=38) sp378 sp416)) (joinSmall (lo:=454) (a:=76) (b:=76) (joinSmall (lo:=454) (a:=38) (b:=38) sp454 sp492) (joinSmall (lo:=530) (a:=38) (b:=38) sp530 sp568)))) (joinSmall (lo:=606) (a:=303) (b:=303) (joinSmall (lo:=606) (a:=151) (b:=152) (joinSmall (lo:=606) (a:=75) (b:=76) (joinSmall (lo:=606) (a:=37) (b:=38) sp606 sp643) (joinSmall (lo:=681) (a:=38) (b:=38) sp681 sp719)) (joinSmall (lo:=757) (a:=76) (b:=76) (joinSmall (lo:=757) (a:=38) (b:=38) sp757 sp795) (joinSmall (lo:=833) (a:=38) (b:=38) sp833 sp871))) (joinSmall (lo:=909) (a:=151) (b:=152) (joinSmall (lo:=909) (a:=75) (b:=76) (joinSmall (lo:=909) (a:=37) (b:=38) sp909 sp946) (joinSmall (lo:=984) (a:=38) (b:=38) sp984 sp1022)) (joinSmall (lo:=1060) (a:=76) (b:=76) (joinSmall (lo:=1060) (a:=38) (b:=38) sp1060 sp1098) (joinSmall (lo:=1136) (a:=38) (b:=38) sp1136 sp1174))))) (joinSmall (lo:=1212) (a:=606) (b:=607) (joinSmall (lo:=1212) (a:=303) (b:=303) (joinSmall (lo:=1212) (a:=151) (b:=152) (joinSmall (lo:=1212) (a:=75) (b:=76) (joinSmall (lo:=1212) (a:=37) (b:=38) sp1212 sp1249) (joinSmall (lo:=1287) (a:=38) (b:=38) sp1287 sp1325)) (joinSmall (lo:=1363) (a:=76) (b:=76) (joinSmall (lo:=1363) (a:=38) (b:=38) sp1363 sp1401) (joinSmall (lo:=1439) (a:=38) (b:=38) sp1439 sp1477))) (joinSmall (lo:=1515) (a:=151) (b:=152) (joinSmall (lo:=1515) (a:=75) (b:=76) (joinSmall (lo:=1515) (a:=37) (b:=38) sp1515 sp1552) (joinSmall (lo:=1590) (a:=38) (b:=38) sp1590 sp1628)) (joinSmall (lo:=1666) (a:=76) (b:=76) (joinSmall (lo:=1666) (a:=38) (b:=38) sp1666 sp1704) (joinSmall (lo:=1742) (a:=38) (b:=38) sp1742 sp1780)))) (joinSmall (lo:=1818) (a:=303) (b:=304) (joinSmall (lo:=1818) (a:=151) (b:=152) (joinSmall (lo:=1818) (a:=75) (b:=76) (joinSmall (lo:=1818) (a:=37) (b:=38) sp1818 sp1855) (joinSmall (lo:=1893) (a:=38) (b:=38) sp1893 sp1931)) (joinSmall (lo:=1969) (a:=76) (b:=76) (joinSmall (lo:=1969) (a:=38) (b:=38) sp1969 sp2007) (joinSmall (lo:=2045) (a:=38) (b:=38) sp2045 sp2083))) (joinSmall (lo:=2121) (a:=152) (b:=152) (joinSmall (lo:=2121) (a:=76) (b:=76) (joinSmall (lo:=2121) (a:=38) (b:=38) sp2121 sp2159) (joinSmall (lo:=2197) (a:=38) (b:=38) sp2197 sp2235)) (joinSmall (lo:=2273) (a:=76) (b:=76) (joinSmall (lo:=2273) (a:=38) (b:=38) sp2273 sp2311) (joinSmall (lo:=2349) (a:=38) (b:=38) sp2349 sp2387)))))) (joinSmall (lo:=2425) (a:=1212) (b:=1213) (joinSmall (lo:=2425) (a:=606) (b:=606) (joinSmall (lo:=2425) (a:=303) (b:=303) (joinSmall (lo:=2425) (a:=151) (b:=152) (joinSmall (lo:=2425) (a:=75) (b:=76) (joinSmall (lo:=2425) (a:=37) (b:=38) sp2425 sp2462) (joinSmall (lo:=2500) (a:=38) (b:=38) sp2500 sp2538)) (joinSmall (lo:=2576) (a:=76) (b:=76) (joinSmall (lo:=2576) (a:=38) (b:=38) sp2576 sp2614) (joinSmall (lo:=2652) (a:=38) (b:=38) sp2652 sp2690))) (joinSmall (lo:=2728) (a:=151) (b:=152) (joinSmall (lo:=2728) (a:=75) (b:=76) (joinSmall (lo:=2728) (a:=37) (b:=38) sp2728 sp2765) (joinSmall (lo:=2803) (a:=38) (b:=38) sp2803 sp2841)) (joinSmall (lo:=2879) (a:=76) (b:=76) (joinSmall (lo:=2879) (a:=38) (b:=38) sp2879 sp2917) (joinSmall (lo:=2955) (a:=38) (b:=38) sp2955 sp2993)))) (joinSmall (lo:=3031) (a:=303) (b:=303) (joinSmall (lo:=3031) (a:=151) (b:=152) (joinSmall (lo:=3031) (a:=75) (b:=76) (joinSmall (lo:=3031) (a:=37) (b:=38) sp3031 sp3068) (joinSmall (lo:=3106) (a:=38) (b:=38) sp3106 sp3144)) (joinSmall (lo:=3182) (a:=76) (b:=76) (joinSmall (lo:=3182) (a:=38) (b:=38) sp3182 sp3220) (joinSmall (lo:=3258) (a:=38) (b:=38) sp3258 sp3296))) (joinSmall (lo:=3334) (a:=151) (b:=152) (joinSmall (lo:=3334) (a:=75) (b:=76) (joinSmall (lo:=3334) (a:=37) (b:=38) sp3334 sp3371) (joinSmall (lo:=3409) (a:=38) (b:=38) sp3409 sp3447)) (joinSmall (lo:=3485) (a:=76) (b:=76) (joinSmall (lo:=3485) (a:=38) (b:=38) sp3485 sp3523) (joinSmall (lo:=3561) (a:=38) (b:=38) sp3561 sp3599))))) (joinSmall (lo:=3637) (a:=606) (b:=607) (joinSmall (lo:=3637) (a:=303) (b:=303) (joinSmall (lo:=3637) (a:=151) (b:=152) (joinSmall (lo:=3637) (a:=75) (b:=76) (joinSmall (lo:=3637) (a:=37) (b:=38) sp3637 sp3674) (joinSmall (lo:=3712) (a:=38) (b:=38) sp3712 sp3750)) (joinSmall (lo:=3788) (a:=76) (b:=76) (joinSmall (lo:=3788) (a:=38) (b:=38) sp3788 sp3826) (joinSmall (lo:=3864) (a:=38) (b:=38) sp3864 sp3902))) (joinSmall (lo:=3940) (a:=151) (b:=152) (joinSmall (lo:=3940) (a:=75) (b:=76) (joinSmall (lo:=3940) (a:=37) (b:=38) sp3940 sp3977) (joinSmall (lo:=4015) (a:=38) (b:=38) sp4015 sp4053)) (joinSmall (lo:=4091) (a:=76) (b:=76) (joinSmall (lo:=4091) (a:=38) (b:=38) sp4091 sp4129) (joinSmall (lo:=4167) (a:=38) (b:=38) sp4167 sp4205)))) (joinSmall (lo:=4243) (a:=303) (b:=304) (joinSmall (lo:=4243) (a:=151) (b:=152) (joinSmall (lo:=4243) (a:=75) (b:=76) (joinSmall (lo:=4243) (a:=37) (b:=38) sp4243 sp4280) (joinSmall (lo:=4318) (a:=38) (b:=38) sp4318 sp4356)) (joinSmall (lo:=4394) (a:=76) (b:=76) (joinSmall (lo:=4394) (a:=38) (b:=38) sp4394 sp4432) (joinSmall (lo:=4470) (a:=38) (b:=38) sp4470 sp4508))) (joinSmall (lo:=4546) (a:=152) (b:=152) (joinSmall (lo:=4546) (a:=76) (b:=76) (joinSmall (lo:=4546) (a:=38) (b:=38) sp4546 sp4584) (joinSmall (lo:=4622) (a:=38) (b:=38) sp4622 sp4660)) (joinSmall (lo:=4698) (a:=76) (b:=76) (joinSmall (lo:=4698) (a:=38) (b:=38) sp4698 sp4736) (joinSmall (lo:=4774) (a:=38) (b:=38) sp4774 sp4812))))))) (joinSmall (lo:=4850) (a:=2425) (b:=2425) (joinSmall (lo:=4850) (a:=1212) (b:=1213) (joinSmall (lo:=4850) (a:=606) (b:=606) (joinSmall (lo:=4850) (a:=303) (b:=303) (joinSmall (lo:=4850) (a:=151) (b:=152) (joinSmall (lo:=4850) (a:=75) (b:=76) (joinSmall (lo:=4850) (a:=37) (b:=38) sp4850 sp4887) (joinSmall (lo:=4925) (a:=38) (b:=38) sp4925 sp4963)) (joinSmall (lo:=5001) (a:=76) (b:=76) (joinSmall (lo:=5001) (a:=38) (b:=38) sp5001 sp5039) (joinSmall (lo:=5077) (a:=38) (b:=38) sp5077 sp5115))) (joinSmall (lo:=5153) (a:=151) (b:=152) (joinSmall (lo:=5153) (a:=75) (b:=76) (joinSmall (lo:=5153) (a:=37) (b:=38) sp5153 sp5190) (joinSmall (lo:=5228) (a:=38) (b:=38) sp5228 sp5266)) (joinSmall (lo:=5304) (a:=76) (b:=76) (joinSmall (lo:=5304) (a:=38) (b:=38) sp5304 sp5342) (joinSmall (lo:=5380) (a:=38) (b:=38) sp5380 sp5418)))) (joinSmall (lo:=5456) (a:=303) (b:=303) (joinSmall (lo:=5456) (a:=151) (b:=152) (joinSmall (lo:=5456) (a:=75) (b:=76) (joinSmall (lo:=5456) (a:=37) (b:=38) sp5456 sp5493) (joinSmall (lo:=5531) (a:=38) (b:=38) sp5531 sp5569)) (joinSmall (lo:=5607) (a:=76) (b:=76) (joinSmall (lo:=5607) (a:=38) (b:=38) sp5607 sp5645) (joinSmall (lo:=5683) (a:=38) (b:=38) sp5683 sp5721))) (joinSmall (lo:=5759) (a:=151) (b:=152) (joinSmall (lo:=5759) (a:=75) (b:=76) (joinSmall (lo:=5759) (a:=37) (b:=38) sp5759 sp5796) (joinSmall (lo:=5834) (a:=38) (b:=38) sp5834 sp5872)) (joinSmall (lo:=5910) (a:=76) (b:=76) (joinSmall (lo:=5910) (a:=38) (b:=38) sp5910 sp5948) (joinSmall (lo:=5986) (a:=38) (b:=38) sp5986 sp6024))))) (joinSmall (lo:=6062) (a:=606) (b:=607) (joinSmall (lo:=6062) (a:=303) (b:=303) (joinSmall (lo:=6062) (a:=151) (b:=152) (joinSmall (lo:=6062) (a:=75) (b:=76) (joinSmall (lo:=6062) (a:=37) (b:=38) sp6062 sp6099) (joinSmall (lo:=6137) (a:=38) (b:=38) sp6137 sp6175)) (joinSmall (lo:=6213) (a:=76) (b:=76) (joinSmall (lo:=6213) (a:=38) (b:=38) sp6213 sp6251) (joinSmall (lo:=6289) (a:=38) (b:=38) sp6289 sp6327))) (joinSmall (lo:=6365) (a:=151) (b:=152) (joinSmall (lo:=6365) (a:=75) (b:=76) (joinSmall (lo:=6365) (a:=37) (b:=38) sp6365 sp6402) (joinSmall (lo:=6440) (a:=38) (b:=38) sp6440 sp6478)) (joinSmall (lo:=6516) (a:=76) (b:=76) (joinSmall (lo:=6516) (a:=38) (b:=38) sp6516 sp6554) (joinSmall (lo:=6592) (a:=38) (b:=38) sp6592 sp6630)))) (joinSmall (lo:=6668) (a:=303) (b:=304) (joinSmall (lo:=6668) (a:=151) (b:=152) (joinSmall (lo:=6668) (a:=75) (b:=76) (joinSmall (lo:=6668) (a:=37) (b:=38) sp6668 sp6705) (joinSmall (lo:=6743) (a:=38) (b:=38) sp6743 sp6781)) (joinSmall (lo:=6819) (a:=76) (b:=76) (joinSmall (lo:=6819) (a:=38) (b:=38) sp6819 sp6857) (joinSmall (lo:=6895) (a:=38) (b:=38) sp6895 sp6933))) (joinSmall (lo:=6971) (a:=152) (b:=152) (joinSmall (lo:=6971) (a:=76) (b:=76) (joinSmall (lo:=6971) (a:=38) (b:=38) sp6971 sp7009) (joinSmall (lo:=7047) (a:=38) (b:=38) sp7047 sp7085)) (joinSmall (lo:=7123) (a:=76) (b:=76) (joinSmall (lo:=7123) (a:=38) (b:=38) sp7123 sp7161) (joinSmall (lo:=7199) (a:=38) (b:=38) sp7199 sp7237)))))) (joinSmall (lo:=7275) (a:=1212) (b:=1213) (joinSmall (lo:=7275) (a:=606) (b:=606) (joinSmall (lo:=7275) (a:=303) (b:=303) (joinSmall (lo:=7275) (a:=151) (b:=152) (joinSmall (lo:=7275) (a:=75) (b:=76) (joinSmall (lo:=7275) (a:=37) (b:=38) sp7275 sp7312) (joinSmall (lo:=7350) (a:=38) (b:=38) sp7350 sp7388)) (joinSmall (lo:=7426) (a:=76) (b:=76) (joinSmall (lo:=7426) (a:=38) (b:=38) sp7426 sp7464) (joinSmall (lo:=7502) (a:=38) (b:=38) sp7502 sp7540))) (joinSmall (lo:=7578) (a:=151) (b:=152) (joinSmall (lo:=7578) (a:=75) (b:=76) (joinSmall (lo:=7578) (a:=37) (b:=38) sp7578 sp7615) (joinSmall (lo:=7653) (a:=38) (b:=38) sp7653 sp7691)) (joinSmall (lo:=7729) (a:=76) (b:=76) (joinSmall (lo:=7729) (a:=38) (b:=38) sp7729 sp7767) (joinSmall (lo:=7805) (a:=38) (b:=38) sp7805 sp7843)))) (joinSmall (lo:=7881) (a:=303) (b:=303) (joinSmall (lo:=7881) (a:=151) (b:=152) (joinSmall (lo:=7881) (a:=75) (b:=76) (joinSmall (lo:=7881) (a:=37) (b:=38) sp7881 sp7918) (joinSmall (lo:=7956) (a:=38) (b:=38) sp7956 sp7994)) (joinSmall (lo:=8032) (a:=76) (b:=76) (joinSmall (lo:=8032) (a:=38) (b:=38) sp8032 sp8070) (joinSmall (lo:=8108) (a:=38) (b:=38) sp8108 sp8146))) (joinSmall (lo:=8184) (a:=151) (b:=152) (joinSmall (lo:=8184) (a:=75) (b:=76) (joinSmall (lo:=8184) (a:=37) (b:=38) sp8184 sp8221) (joinSmall (lo:=8259) (a:=38) (b:=38) sp8259 sp8297)) (joinSmall (lo:=8335) (a:=76) (b:=76) (joinSmall (lo:=8335) (a:=38) (b:=38) sp8335 sp8373) (joinSmall (lo:=8411) (a:=38) (b:=38) sp8411 sp8449))))) (joinSmall (lo:=8487) (a:=606) (b:=607) (joinSmall (lo:=8487) (a:=303) (b:=303) (joinSmall (lo:=8487) (a:=151) (b:=152) (joinSmall (lo:=8487) (a:=75) (b:=76) (joinSmall (lo:=8487) (a:=37) (b:=38) sp8487 sp8524) (joinSmall (lo:=8562) (a:=38) (b:=38) sp8562 sp8600)) (joinSmall (lo:=8638) (a:=76) (b:=76) (joinSmall (lo:=8638) (a:=38) (b:=38) sp8638 sp8676) (joinSmall (lo:=8714) (a:=38) (b:=38) sp8714 sp8752))) (joinSmall (lo:=8790) (a:=151) (b:=152) (joinSmall (lo:=8790) (a:=75) (b:=76) (joinSmall (lo:=8790) (a:=37) (b:=38) sp8790 sp8827) (joinSmall (lo:=8865) (a:=38) (b:=38) sp8865 sp8903)) (joinSmall (lo:=8941) (a:=76) (b:=76) (joinSmall (lo:=8941) (a:=38) (b:=38) sp8941 sp8979) (joinSmall (lo:=9017) (a:=38) (b:=38) sp9017 sp9055)))) (joinSmall (lo:=9093) (a:=303) (b:=304) (joinSmall (lo:=9093) (a:=151) (b:=152) (joinSmall (lo:=9093) (a:=75) (b:=76) (joinSmall (lo:=9093) (a:=37) (b:=38) sp9093 sp9130) (joinSmall (lo:=9168) (a:=38) (b:=38) sp9168 sp9206)) (joinSmall (lo:=9244) (a:=76) (b:=76) (joinSmall (lo:=9244) (a:=38) (b:=38) sp9244 sp9282) (joinSmall (lo:=9320) (a:=38) (b:=38) sp9320 sp9358))) (joinSmall (lo:=9396) (a:=152) (b:=152) (joinSmall (lo:=9396) (a:=76) (b:=76) (joinSmall (lo:=9396) (a:=38) (b:=38) sp9396 sp9434) (joinSmall (lo:=9472) (a:=38) (b:=38) sp9472 sp9510)) (joinSmall (lo:=9548) (a:=76) (b:=76) (joinSmall (lo:=9548) (a:=38) (b:=38) sp9548 sp9586) (joinSmall (lo:=9624) (a:=38) (b:=38) sp9624 sp9662))))))))
  have good : (List.range 9700).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 94085731) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 9699 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 9699 := by
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


private def packet (i : ℕ) : ℕ := (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 0)) else (if i < 4 then 0 else (if i < 5 then 0 else 0))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 0 else 0)) else (if i < 10 then 0 else (if i < 11 then 0 else 0)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0 else (if i < 14 then 0 else 0)) else (if i < 16 then 0 else (if i < 17 then 0 else 0))) else (if i < 21 then (if i < 19 then 0 else (if i < 20 then 0 else 0)) else (if i < 22 then 0 else (if i < 23 then 0 else 0))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0 else (if i < 26 then 0 else 0)) else (if i < 28 then 0 else (if i < 29 then 0 else 0))) else (if i < 33 then (if i < 31 then 0 else (if i < 32 then 0 else 0)) else (if i < 34 then 0 else (if i < 35 then 0x3dceae31196f4ac04f024710987a236b17909f841e19f09b83580d20003dc8023259788af650c25210e479836117909fc42619c09b03480ca0003dc17a3109708ab04e724190707703481728a104201ab09d833c0d20003dbab532e17f4b2252425b10ec78435e17b0a3c4541b50a7837c0d00003db4253189744acc4fa245908077435917d8a444501b80a383580d20003dad733221750ad04fa243909477435c17e0a084401b809f03580e00003da6ec31216b8a924ee23f903874a34c17389d841e19d09a03300d00003da0343269768ad850325110e478c35e17e0a344401ad0a4036c0f60003d99953171718ab04ec23c107476e34017189d841219c09b03200aa0003d930c3159710aba4f2245109875c34516d09d04141a40a703600dc0003d8c523281790afc51825990e079236717c0a3c4361aa0a303700ce0003d859932697a0af050c24f90c877e35617989dc40c19109382ec0c80003d7f013151714ab84f124310a47883571778a0042a1b30a703980f20003d784f329975cae650924e90b87a035717209f040e19c09783280c80003d71bf31096d8a8c4e823d103875634c1730a1442c1a70a083400ee0003d6b1831f1758ac44f724590a07763571738a0443e1bb09e835c0e20003d64863179728ace4fb24a90a47803601778a004401ac0a003400d00003d5ddd31d9744ace508249909477434a1770a304521b80aa037c0e20003d572d324978cafc51625510e87b035a17a8a244481b90a903800ec0003d507b3259788aee50f25410c878a3591778a004461a909f03600e00003d49d731b176cae24f123f90707583501718a0443e1b00a403640e00003d43453181720ab44f4242906076634917109b441419f0a103480d60003d3c9132817a8af050925310ec78e35217a8a1442e1a109f83380d00003d35f431d971cab84f424910e47bc36617a8a404301b40a283800d80003d2f4d31b9748af451025911387a83651790a044261ae0ab03880dc0003d28ba31796ecaaa4eb243109076034916d09d440e19c09c03100d40003d220a3249760ae04f624b10bc78435c1758a184441b70a583800f00003d1b6e31b1730ac04fc24e90ec7b236917d8a3043e1b50a583900ee0003d14c431d1724ad650024990ac77a34816d89d44221a909c83180c00003d0e0332c17a4aec50324f10bc78a35517309e841c1a309d03200d80003d076131c173caae4e9240907c75034116d09d44261a609a83640e40003d00a9325977cad64f724a109077234d16c09c04221a709f834c0c40003cfa0431c1744abc4fc247109479035d17589d042e1af09b833c0d20003cf38330a968ca7a4da23a0ff472e33215d09283d618108e83380e00003ceccb323175cad250824e90b878e35b1808a504561c30a883800da0003ce60a32b17b0b0251b25191087a836d17d0a344381b50a983640ce0003cdf72317970caa64f0243906c76e34716c89ac40a1a609b034c0e40003cd8cb31e9754ac04f2246907475433f16a89a040019509502f80b40003cd2293169720aa04de2390ffc73433116189803f419409d83600d60003ccb8431e1754aae4ec245907477c35e1840a5c44c1b00a083700d20003cc4c9328177cb0451325010b477634916e89fc4141a209d83440d00003cbe1f31b9748ad250b24f10f077c34917309bc4181a60a5038c0dc0003cb77831d1740ac84fb24c90d47963531718a004361af0a0034c0d20003cb0d0321176cad04fb24b90b878635416e89f44481aa09c034c0e40003caa1232417a8afa502249908877235017209e441c1ad09983440be0003ca3503269778ae250625310d47aa3731828a4c4561bf0a303740da0003c9ca631d9770ad850024890a077835617389d041e1a309d03440d20003c9612317971cac24ee246907c75634016989683de19709b834c0c60003c8f5732c97e4b0250f25190d87a036717e0a344561c00a983ac0dc0003c887f32f97e8b0e52125491107c03731890ab047a1ce0ae83980e40003c81d03219770ae650724f90e079a36417e8a504661c30a883700ce0003c7b3c31116f4a9c4f223f106075034616a09a03fa19809803040c40003c748232c17c4afa50c24c90b077834016d89e84161a909b833c0d60003c6dbb32c1790af650a25410cc77a3541728a1c4241ad0a183540ce0003c672b30b96c8a9e4ef243907077e3561780a104341b209e83500c40003c608431e177cb0c51e25a11187ba36a1800a444401af0a003600d80003c59e131c174cad450024a90b877a35317489f442e1b00a683740ea0003c533b31c175caea51725490ec78e3501770a0441c1a109a83280c60003c4ca33199734acc504243908477835617589e84201aa09e83440c40003c45e632d97ccb0850424a90ac78c36b1760a2c4361ac09f83700d80003c3f57316172cac44f1243907076a35017189f44261a609f83340ca0003c38b131c1740aca4fa248908c76434d17389c440419b09983140be0003c321c31b172cac850825290e479e3641788a084261a30a103440ce0003c2b4133c1810b2c52b25b91247b837517e8a544601cc0a983740d8000 else 0x3f780a30b16cca924e223b904c76235b17c0a284481c00a983880e40003f7155321177caec50c25891107b436a1800a3c43e1ab0a183440d00003f6ac231096f0aa04e123c902c74a33a168898c40819709a833c0d80003f64183219768ada50424c10a476434716f89dc41a1a909f836c0d20003f5dad2f99618a3c4b62278f8871232516109843d019209803440ce0003f56ff3291798afe51e25511147c237d18a0a8c4661bb0a503940d40003f505a31e1768aee50424d10d079c36a17d8a3c4381a909e83380d00003f49b431e176caf850f25510c079035e17889f842819f09883240c00003f432c31196e8a824d32351038736326161898840a1a909b03340c40003f3c5e33017ecb2651925810fc7943541770a0842c1a50a203500d60003f35bf31396dca7e4d2239104875834d17109bc4181aa0a303600da0003f2eff32a17c4b1250f24b90cc79435817b8a184321ac09e83400cc0003f284d3261754ad24f8245908475234216e89ec40c19709882fc0c20003f21aa3199724ac84ff24910b07743511770a1c42e1af09e833c0b60003f1b0531f171cab04f024610a477835617589e04241b20a303440da0003f144e32e17d4b0851b25610fc7a437117e8a444461b20a2037c0d00003f0dae317972cab04ea242908c77e35b1740a104301b20a103800ce0003f06df33197f8b2a52f25991207a435f17d0a2444c1bd0aa03900da0003f006e3099668a564b922d8fdc71032716689a03fa19a09f03500c80003ef99d32b97b8b0c51f25611147c23781858a744521b50a483640dc0003ef30d31116d0a984e1242106876034617089f041a19c09a03040d80003eec6e31616f8a9e4f124410b077835716d89e44201a609e03640d00003ee5c831c9754acc4f2241904875434216409703e019209182fc0c00003edf20322973cad64fa245909477e35c17509f04421af0a283700e60003ed8733259764aca50224e90dc79236217d8a344461bb0a803880ce0003ed1e130e1708ac24f724710a077434516a09b841c19d09e82e80ba0003ecb733079690a764d3230900473433216509b03de192095833c0cc0003ec4c33249758ac44f6245106877234d1738a1c4201a509d03440d00003ebe2a3189740ac24f923f106c76433e16689c441219e09c03600da0003eb793314970cab04ee244906c77435216b09d440819b09883200c80003eb0eb32317acb0051b25510ec79235a1818a6044a1b80aa83800e80003eaa5c31016cca7e4d8237902073433c16e89c440c19d09783280d20003ea3c23189718ab24ee244908076c34116b89c441819d09d03200be0003e9cfa32997a4af851425890d077e34116e89e04161a109c031c0c00003e965e317974cabc4f2247109077834c16989c44201a209f03740da0003e8fa73251764ad64fa24590907763581770a4043a1a609d030c0c60003e88e332c97c8b0851325090b079c35d17b8a4043a1b20a4838c0de0003e824231e973cad04f5241908078235417589dc41a1ab09a832c0de0003e7bbc31116d0a964e4239102874833817009b04121a60a4838c0f00003e74ed33297e4b1a52625e11407c236c17d8a2c4481bc0a483640d60003e6e3a323977caea51025710ec79436317b0a144301ab0a103680dc0003e679731b9740ad050624f90c079435317709fc4161a209e03700dc0003e60f83179710aba50424a90ac77c3501768a304281a009803280d20003e5a343271790af451a25510ec7923611780a0841e19e09783080b20003e5388321177caf050f25611147aa36017e8a5c4541bd0a9035c0ce0003e4ccf328977cacc4f6244908075c34616b89d040619c09903480c60003e460932817b4af651024f10cc79834e16e89d840e1a30a1835c0d40003e3f5e3201730ac24eb240106c76a34317009a840c19909703340c20003e38973249788ae250b25490e07a036017b0a5843e1bb0a3833c0d60003e321b307167ca624d5238903074a34016f09a43f419109382fc0c00003e2b9a307969ca7c4d2237903c75035016f09dc42619b09a83300e60003e24eb31d1758aca4fd249909c76635317289f04221ae09f83580e20003e1e5a31d174cac44f7241906075633b16b89a03fe19b09603240c20003e17b131d976caea50d25491047b237317e8a404461b10a0034c0d00003e111b31396fcaa44e523b902475234b1718a10410198096034c0ce0003e0a7631a972cac44f924b10ac78035117789e841019e09f836c0cc0003e03ce31f973cad44fb242107c76034417089b441a19d09903300d00003dfd3131c9754af051325811047b03721800a484381ab0a383580d60003df66233017a8b0451325291147a836817b0a384481b009d03500ca0003defc931e1710abc4f8245107876a34817189c841219e09503100c00003de93a31a1724aba4ef240905475633e16f09dc41c19e09783280d80003de29332217a4afe50b25110a878836317a8a2042e1a709d03580c40003ddbdf3231778ac850424e90b477234e17089d84141a409e03480dc0003dd533320976cabc4ef244106c75634016c89b44141a109d03340de000)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0x4120e43119700a944e124290547583491750a004261a309f83540e4000411a1132d97c0b0651f25190d07a036a1848a7046a1cd0a7835c0e40004113863151718a9e4ea23c908476c34516f89e041819909c034c0c2000410cfa31216d8aa04e1239102474e34817089cc4301a60a0833c0dc00041066330f96e8aac4e623f905c76233916a098440019b0a083600d600040fff530796b4a824df238902073e32816689743e218c09803500d600040f90833997e0af450b25291187b63701840a984701d60ad83a80f000040f26431f174caba4fb24910a078c34e17109dc42c1b20a4836c0ee00040ebdb3169728abc4fa247109076834f16f09cc40c1a209f83680ec00040e54f31296c8a864e023a105076234d17309fc4221a909703380d800040deb731316fcab04e8240904875e34b1788a1443a1a309d03600f400040d80731f9760ae850824b10947883531748a2c4441b00a283840ec00040d17e30d16dca9e4f1245109877c35617089c84001a309b03400d400040cacd3231774adc50924e10cc79c3621788a2044a1cb0ac83a40e400040c41e3211794af4519253911c7c036e17f8a3043a1b40a103640ce00040bd69323976caf650524d10c078a3591778a3042e1aa09f83340d600040b6e231196cca824e323b101075233c16c89cc4161a509b83440c400040b00433297e0b24521259112c7b03621800a444501ae09e03240c600040a93c33297d8b0851e25290e87ac36817b0a1441c1b20a103600ca00040a29f3229748acc50525110a477435417409c04061a109f036c0de000409bf73239764acc4f5248907476434a17309cc40a1ac0a003300be00040953e32717a4b0050d24c10b477234e1750a0440e19d09e83580e8000408e763261780aee50d25711287d43771820a544541c30a603840d20004087db31f9728ac84f4241104c75434d17589e44301a80a003380b800040815430d96aca784db2328fec72433316409ac40e19c09a83280c4000407aab31e9760ac84f123f90447603511750a204341ab0a383780e4000407412315971cad050325390d07aa36617e0a2c42a1ac0a503680d6000406d7031b174cad04f724a10a477234916c89d44201a209d035c0d00004066c831b173cae04ff24d10a877634c16b09e040c19e09f83600d8000406019326176cae24ff248909076434116b09cc41a1ab0a4038c0e20004059633271768ade4fe24e109c7763561778a2443e1a909c03380ce0004053082f81604a2c4b12220f786e430f155893c3e219109a832c0d8000404c643211744ad851225790ec79235a17509f841a1a909b83380ce0004045e93089670a6e4c42300ff071a327160896040419809703140c2000403f483189740ad84fa24b10bc77e35617489d841619e09a03380ce0004038a1321975cad650225190c477e3541788a184441ab0a1036c0c000040320d3151718aca50224890ac79236717a8a0842c1b30a603740d6000402b4732f97b4b0651d256111c7a03631780a2043a1a50a303640d400040249b323176caec51025090f47ae36a17f8a4044a1bf0aa83940e8000401e0e3151700a944ee24890a876a3571750a1041c1a309c032c0e800040176f31996e8aa64e62398ff0724336168098840419709983700ee0004010c2323174cacc4f8245908878035c17209ec42e1b30a083740de0004009ef33397d0b0451825890f479e3631808a5c4381b60a3833c0b800040032533197ccb0851025090d479a36017b09fc41e1a1094831c0d20003ffc783259794aea50c25490cc79835c17b0a5045a1b30a5837c0dc0003ff5eb3171730abe4f7246906475c34016d09b03f818d09402ec0c00003fef4d3191758ac84f824d90987883501750a004301a709f03540e00003fe8ac31b971cac04fd24690907783561780a344461b00a3035c0e00003fe21931396dca924ea23d104875034616a09a440219809d83340d60003fdb5132f97b0af851925590e47943611778a044341af0a003600d40003fd4ba3191734abc4f8243107876234716c09b040419409302f80a60003fce3c30916c8aa84e423e101074233b16889b44101a20a283580ea0003fc76933697f0b1452325b910c7c636817d0a344401b20a003500ce0003fc0d43189754ae44fc24d90b878635a17609f841c1af0a783600ea0003fba163259780ade50424e10b079c3591748a184421b40a383700e60003fb39c3081698a6a4d22308ffc75233e16909d84181a509f03580d60003facf43221760adc502247909c76c34716b09bc3fc1a309883340cc0003fa6503219748ac84f924710a07823531760a304201af0a483500e00003f9f983249768adc50b25490e87a03631820a4c44e1b70a683880e40003f990331296fcab44ed2401060770348169898c41619c09883000d20003f926531e1748aaa4e5241107075234216a09dc42c1ad09f83440dc0003f8bb63209758aec4fe247909476e34d17409d440619509803340c20003f85103211770ad44f824690a878035e1728a044281ac0a4038c0ee0003f7e7931b1710ad04f6244908c77e3541768a1042e1aa0a283740e2000 else (if i < 38 then 0x42c8343221778aec50525110d479c35d1788a144481b40a583740dc00042c1b230c16d0aa24ee245909c77035417a8a144361ac0a603840e200042bb373059680a6a4d02358fd072632c16189883f0193094833c0ce00042b46933297f0b2652425e91387ac3761850a5442c1b70a4035c0c600042add131896d8a8e4e62401068752334168097c3dc18409003100cc00042a73131e1774ae650924910b478a36817e8a0c4341b80a0032c0d800042a0923211764ada50525110bc79e3571790a4443c1b70a5835c0ce000429a213021678a6c4d523a104c76c35117009c44141a209e03380b600042936a32a17a0b0050a25110cc7ac36d1890a9c4641c00a303600d0000428cf0307969ca784d7236101872c33216709b840418b09503240ca00042863f31e9758adc4ff246908076834717109d441e1a409c836c0da000427f903229730ab24f2246107476e34d17089e84201a409f03200c40004278de323175cacc50624c90c879235c17a8a2044a1b309d03340d600042725730f16e8a984e5241105875033416d09b442c1a609c03380b6000426bc03181720aba4e9240905473e33f16d09d841a1a709d03300d000042653c30a96c8aa24e5243909475a34016809984161a30a203600da000425e8d32617acaea50b24b908c76a34d17109b03fc197098031c0c20004257fa31396d0a8e4d923a100874e34616489283d819309803300dc0004251453241770adc50424a10e079e3691810a804561b10a403680da000424a9a32697bcb1252625911147b43701800a904541be0a183740e60004244382fe1630a4e4be2288fe071c32615c092c3e818b09403000c0000423db230e96e4aaa4e6240908476a3421708a004461b00a283540de00042372a30e16e8a9e4e9243107c78234516d89d04101a509e83300dc0004230953129710ab44f124510c477a35517109b841419a099832c0c20004229e4325978cb0251f25711147cc37b1840a084301a809d03500ca00042235031a1708abe4fe25290ec79e35c1798a2c4501c20aa83740e8000421ca731f9774ae450325190f47a035d1770a2843e1ad0a083240c40004215ec3261790ae851025191007ae3691818a544641c50ab839c0e6000420f583181714ac44f424990b478636017e0a4843c1be0ac03800e40004208cf31016fcaa84ea23d906075434817109bc3f819609c03600d400042023231396f0ab24ef240105c74a34416909c440019709b03700e200041fba531216dca924da242106074a33a16889bc41019609a03500e000041f4fe31e1770ae450924b90ac77a3561798a2844e1ad0a283680c800041ee443259774ad04fc24a90e879636317c8a2443e1ba0a503880ea00041e79132197a4ae850c24f10b077c35317b0a0843c1b60aa03c80ea00041e10731296fcaa24df23d1014742331167099440c1a40a0036c0d000041da6b3181750ad84fd24b10ac78e35f17609fc4141a409603280da00041d3a132f979caee50b25290ec7aa3671778a1440e1a609b03300ce00041ccf13241758aea50a24d90b476e35e17289d840e1a109983440ca00041c64e31f1730aa04e623e907875c34716f89ec42a1ad09d831c0ce00041bfc231096d8a824de23a903c72c32716389643ce18a09383240c000041b9153219728ad050324710a077234e1770a084221a10a0035c0e000041b2b42fe9670a6e4c7232902073e33716789c03f6190095032c0d800041abf132f1790aec50024910c879e35f17c0a3c44e1bb0a2836c0da00041a55d316973cad84fe24990a078635a17289f841819b0a003440c2000419ea83229778af250f25310e079435f17c0a1c44c1b60a303840de00041980d3151718ac44ef23f905075434916f89d44241aa0a583840ea00041916f31696fcaae4f4248907c76634b16c89b04181a009b83440ce000418acc31d972cac44f7246107076e34c16f09d841e1a709c83380d800041842a31a9728acc4fc24b90bc78c35417189e441019a0a1036c0d6000417dbc3049694a784dd23d105c76234e16f09bc41419f0a1034c0c800041772f30c16b8a964df23c903874033916509843fa196099832c0c200041708f3189738abe4f5246907c75c34517089f043619f09f83700e0000416a0131396dcaa84e423e903474433816a89c44101a309903480d400041634532597a8af650d24f90f078e35d17409e84141a009c83740f0000415ca031f1704ab64fe24890bc78a35a1788a3445a1b30a283480d40004155ed3259784ae050324e90e078a3501720a1043e1b30a503780da000414f51318973cac450724f10d07843581778a0c4241a90a083580d00004148ae315173cac84f3249108878a3531768a044321a909c83680d60004142093189700aba4fd24c10c878234f17089bc40619909b832c0c6000413b573201760ae051b25711207aa36317f8a2443a1af0a103700de00041349e326977cafe50a25511107b436b17d8a504521b30a783840e8000412df431b9724aac4ed23f105475033816989b43fc19709b033c0d80004127793019670a584ca235900874434716d09f04441ba0a403900d4000 else 0x446fcb30896bca8e4dc23f106877235917a8a0843e1b40a383540e400044692931e175cad250b25310f87ae36a17d0a1c4321ae09d836c0d60004462a430b16e8ab44f1245107476a34116d89f042619509383400ce000445c223111700ac44f924a10dc78e3651798a2443a1ad09e03480e000044556b3259774aea50c25010d877e3591780a0041819b09903400d0000444eea30796aca744ca2318fc070631b15c093c3d218809703300d200044486330d16b0a804d6235903874e34217009e442c1a209703140bc0004441d331096d8ab64fa247107875c34b1710a204321ae0a2835c0de000443b3331d9718ac6505245908877034b17089bc40819709783040ae00044349431b9728ac24fb24b10d879636a17f0a3c4461ad0a083580d6000442dd73239750ae050724d10c078435217509f44261aa0a2036c0e200044275a30696a8a8e4e323a903c76234a17289c04221a509f83740e00004420c930c96e0aae4e923c104475c34116a09a44141a609b835c0d4000441a36315970caca4f624b90cc79836417609d84181a70a383580d00004413c2302964ca744c922c8fd871e334165899840019b0a4035c0ce000440d25319971cab04f3242107476834717289f04061a109c83440de00044068b31196fcab04ee24910c879034f17089f042419e09d833c0d800043ffe431c1724ac850424d10b477835017309f04341af09f036c0cc00043f94931a9718aba50224a109c77a34616c09b84201a809d83680e000043f2c131396f4aa24e623f905475e34a16a89c040619809903340da00043ec2931396f4aa04f0245109476034517089c041c19c09a83380d400043e5923141714ac24fd24b10bc78035317689d44161aa09f03640ca00043dedd3221788af050224e10cc78635c1780a184321a40a183540e200043d81732b9784af050f254111479635717b89dc40a1a309d03580c600043d19430b96b0a9e4e724190987743581768a104301af09b83640ca00043caf231b171cab84f324690b077835217189ec40e19c0a103580ea00043c449321977cac84f9248107874c33916d89bc40219809a83300d400043bd9b31e9768ae6504247908476c34816b09ac3f618e09683400c800043b6d932f17dcb1851f257111079a35d1798a544621c50b183dc0ea00043b05a30f9694a964e023c103474233015d09943f619809982f40ca00043a9ab31f1760ab64e3234901072632d16089843e418a09883280be00043a2fe3219760ade50925390d879235a1780a284341b90a603780e2000439c6d3131704aac4e723d104075a33f17109e042e1ad0a6037c0d60004395c83219738acc4fa24b90b478035317409e041a1a409e83400d2000438f1831f9730ac04f424390a077c34c17089c440c1a109e034c0ca0004388863119718aca50525090dc79635417909f84321b20a303680c40004381f53149718aae4fa24a90c078035317109dc42219a09d03340d6000437b7630a96e0aae4ea241907478435817a0a0c4241aa0a383500d20004374d031d975cad04fd247904876234116f89a840619b09983340cc000436e363151714ab04ee248108077c35717489e041e1a209e03240ba0004367863249794af450c24e10b47963601778a084241a709c830c0ae0004360c632c179cb1051d25e11347cc36a17c8a504421b70a903740d8000435a2a31896f0aa44ea241109078235417509f84321a80a6837c0da0004353903161704ab04ef245108c76c35a17089f842c1ab0a1836c0e0000434ce13221770ae450825290e87a43631768a0042c1a709f83680e000043464b316171caac4e923d90807783551760a144261a109c834c0c4000433fa23199738ade4f9248108c77034e17509ec4261b10a203500d20004338f0328979cafe50b259111c7ba36917b8a184201a009d834c0d400043324531e974cac64fd246107475e34616d8a0c41419f09c03240c8000432b893281780afe50c24c10cc7903601758a0841e1a409d03080c600043250031416fcaa24e324390a875e34e1768a084421b909e834c0c4000431e4d32997a4ade50a24e10c87a43691798a004401b409f035c0dc0004317a331d9734ac050424990a075c3401710a0c42a1a509e03240c800043111c3031680a804dd2369034742330161096c3d818b09403080c6000430a9131096d8a9c4f624c90ac79235817289e84161a009d03680de0004303fd30d16cca8e4e823e105c77235517209b841a19b09683140e200042fd6631b9730abe4e8240109078435417189f84321b10a1036c0d000042f6b93211738ace4f324c90a879235a17b0a3044e1bd0aa83a00dc00042f0013231750ac24df23c106075a34116e89dc3f4196097030c0be00042e98c2fd9684a784da23b0ffc73633116609d04201a109803480dc00042e2da3251760ada50324790ac7843571758a1843a1b60a703700e400042dc3931b9740ae050c24a90cc79235817309dc4241a109c83440c600042d58d3229770ae0513252109877834017009cc3f8194096030c0b800042cedd3261794af250b24d10f479c35f17a8a2c4441b709d033c0ce000)) else (if i < 40 then 0x46161430a16a8a8e4e3238102c74834316f89c842e1a709c035c0ca000460f8331096c0a8a4dd24210ac78635c17509e44101a009e83600de0004608d032817a8ae44fe242108c76835717189dc4281aa09f036c0e20004602233239780ad650124a90b477e35516c09ec41c1a109903400da00045fb7731b1760ae250c24d10a878c34317089e440c1a209903240d600045f4f930796d0a884de23d904873433d16a09a83f419109e83540c400045ee5e31596fca9a4f2241908078035116e09e04201a609c03380d000045e8012ff962ca484be2320ff873833016789a83f819609203140c800045e155322174caca50124510b076c35017209e04261a809e034c0d000045daaa3209770ae050224c90c078235016f89d842e1ab09e834c0d000045d43b3041678a5e4cf238905475a34016a89ac40619e09f03580d000045cdb131196a4a7a4de2389004728335164096c3d619109c03200ca00045c72b30f16f4a904d8239902c74c34016e09c441a1aa09b032c0d600045c09d3171754ad24f924c10947803581750a2c4261a809b83380ca00045ba193089688a7a4d7230101c74633e168899041019d09a033c0cc00045b35b32817bcaf650c25390dc78435417409f44221a709c83540d000045accc31e9748acc4f324390847823501788a2c4381b40a503700f400045a61e3209758ae450824c90b878c35017009c440a19f099831c0c8000459fa031116d0a884d823b902472e33816589903f819209703400da0004598e43269764af450c253910479a3511758a0c4481b60a383580cc00045924d316170caae4ff24e10cc79a3581780a284281a909b03480d0000458bbe31316e4aa04f5244107c76e35517289e84301aa09d83580d200045852f3159730ac24f2249108877034816a09a840619b09983300c0000457e87325177caf650624b10a47883551790a284261b20a903900d60004577cc3261798af650624c90c079835617409fc4221ab0a403800e40004571233241790af450e25190f47a835e1788a104361a509e832c0c8000456aa730a16f8a9c4e0237903474233416b89c441a19f09b03480e60004564103161700abc4ea241908475834016909ac3fe1a109d033c0b6000455d7c30e96c8a964df241906475233d16989d440618a09483300d40004556c93259798ada50725290fc7b23701818a3c44e1ba0aa037c0d800045502c317970ca9a4de23b902c74a34216b09a44161a409d03340d2000454985322176cae050124490887703571748a0c4401b10a2834c0d600045430330e16c8aa84ec245108878a35917c8a0443c1b60a6837c0da000453c8c30f96dca804ed243904874833f17009ec41a19509b83180c40004535ee322977cae04fc244105875234317009a03ee19e09a832c0ca000452f5331a16f4a9a4e9243105477634516e09e04261a709d03480c60004528ae31f9760ac84f924b909077635017109d04101aa09e83440dc00045221231a171cac24f4244907879035117909d841c1a309d83540da000451b9830a16a4a724ce2360fe872c33216709bc4261a509903240cc0004514f231b1718abe4fe246106c7723491700a0c4281a309a034c0d0000450e603181760ad04ef24790cc78c35b17a0a0842c1aa09b83500c00004507cf31496f8ab24e624010a877435517989f84201af0a103740f0000450112330979caf651024f909878435b1758a0442a1ab0a403900e000044fa8131796f4ab44fb24790cc79036317809f441e1a309d83680e000044f3fa31096f4ab84f524990a878635216f89a840618f09683480ca00044ed6f31296d8aaa4f3241908478635817b0a044201b30a403680de00044e6d331b9738ae44f3249108c78c35b1728a20418194098033c0e400044e03c3171710ac24eb23e106475e3441720a044321ad0a183580ca00044d98a31e1740adc4fa244907c77034e16f89d04141a809f83400d400044d2ee3159734aaa4ea23f105874a34816c89b04021a009883280d000044cc4531e1754aea50424710b077e35617189f042c1a509f03580d000044c5ae3199704aaa4f0242908477e3561730a2444e1bf0a4836c0d800044bf2f30816bcaa84e7240907075e34616f8a244321ad0a2836c0ce00044b85d336180cb2852225890f47b23691790a404521b20a003740e000044b1cc3169728ace4f4243107c76834617289ec43c1a709f83400ce00044ab1e31b1724aac4ef242104c74633c16a09a840219c09703240c200044a487319972cab84eb242106c76434d1760a0842a19f0a2835c0d8000449dde31e9750ad64fb23f907076e34f17409f44201a80a083340d000044975831116e8a984e5239905075a33416789e041419e09d035c0d60004490943299798b0a51724c90e079435917609f041c1a40a103680d60004489e7325179caf450a25611207ba3761850a504501b50a283600e000044835d31416e8ab24f4243906076434b17009f842e1b20a703600da000447cf030696aca7e4e623f103874633516709c041219d09a033c0d400044764431d9748ac64f924b10b879235b17689e842e1b209b830c0ce000 else (if i < 41 then 0x47bc1e30716a0a744d1235100874233316409803ea18c09503000b800047b56d3241734ac04ee23e105875e34e1778a184341a709d833c0d600047aefc302967ca644de236101c74e34216a09c44301af0a503340c800047a84b325177caee51025490d07a23601798a3443c1aa0a583780d400047a1c430916fcaaa4e6241105c75633d16b09c040a1a309903440e0000479b2131a96e8a9a4e0237901074633016389803f2197095031c0b200047946832d97b8afc508254110879a3621790a384441b809f83500d4000478dcc3169708abe4f5248108875633716689983f819a09483340ce00047874a30916fcac24ea239904c75c33d16f09e441a1a209e03440d00004780ad319173cace4f6244106076e3551768a004301ae09f836c0e40004779f532b97a4ae650724f10e479e3651790a3c4361b20a783740de0004773463269780ada51425110b47b036b17d8a484301b10a303540cc000476ca831196c0a904e023a902474433316689a440e19409503240ce00047661931116e4aae4ea23a902873233716b89b04141a209d03480c8000475f9c30b96d0aa04e823e901474a34116d09d84181a50a0032c0c400047590931516f0aa64f4245905c75a34d16e09ec42a1a70a883ac0de00047525e3191750ad250024d90cc77e35e1798a384421b20a403800dc000474baf31f175cac24f9242104475a34716a09a04101a209a03180c800047451831a9748ac44f324810ac77235016e09ac3fe19d09a832c0ce000473ead3031660a604cb22b8fc871a32215b895840219209b036c0e600047383d300968ca884e623f108876235317409e841c1a50a283780f400047318c3249794b0451325590c877e35017409f44261b409f83280c6000472b0530f16f8ab24f4241107475c34817389bc41e1a7096833c0d600047247c313971cab84fa24a10a078834916e89c040a19509603180d4000471dd83199704ac04f6247906076633d16689743ec19709b83380d400047174531496c8a844d923a901c73a33516409bc40419209583300ca00047109e31f972cab650124c10c479034e16e09d84261b60a983840e2000470a2530a16a0a764d82380fe872032615c89383ea18d09883380e200047038531b9780ae44fd24d90c079e3671830a684461b80a783600d800046fcf930e96b8aa44dc23b103c73033216509783da18308d02f00b400046f6803021680a7a4db237902872832b161895c3e818e09603300c000046efae33017b4b06516253912c7c436e1800a744581c00a683600e600046e9123149708aba4ec241105c76c35116e09b040218d08f82f80d000046e27431d9748ace4f524910cc7a236517b8a2044e1b509f83340d800046dbe23199718ab64fa24610a07823561760a1c4321ac0a483640d200046d55731116eca9a4ed23e106476034e1758a144521ba0a903980e800046cece30b96a8a9c4d923b902c73633616989b44021a609a83380bc00046c82c320974caba4f2243105075c34416e09cc40e1a209a03140b800046c1823241764aec51625411047b636e17b89f842c1aa0a283500e200046bad2325177caca4fb245908c77035a17009d842a1b10a283600d200046b4253221744aba4f724990a477e35a17b0a244361a509e834c0cc00046adb230a16a4a884dd239902873c33516509643e618508e03000c200046a72331296e4a8c4d4233903873c33716009503d019409a03340c600046a08f3149710a9c4e424090707803571758a184221b60a283480d40004699f931a9774ae250f25290d879636117b0a304541b70aa039c0ee00046937b30a96d8aa64f7240103475834516d89d441019809703180c2000468cce31d972cabc4f6247909076634f1720a1043c1ad09f03500dc00046863e30e96b0a8e4e4245109878a3541740a004301ae0a103540ca000467fba3099688a804de235901473834616909b04101a70a383900f40004678ff3289750ad451225010e878c36117b8a304381aa0a383740d200046725d31f9728ab64f2244908477c35317509f440a19a096832c0da000466baa3229758ade50625210f079a35717709d041a1b00a183580d800046652830d16aca924df23c90407583471728a084421b60a403800ec000465e8b31a175cada4fd24f10cc79836217b0a444461b60a803740d8000465808304966ca664c8237100472c32d16289883fe199095830c0b800046516c31b1710a924e923e104474c34716c89f04121a309b03600d2000464ac031e9734ac850324790a076c34516d09f84321a809a030c0d20004644573009684a7c4e223d908076234b17109cc41019609403100ca000463dcc31016e4a864d923b103876034316e0a0c4261ad0a383840dc00046372f31c1730ac84fd241104c75e34416609983e618b09183240c400046307e3231768af04fd24590a87a636c17c0a304381aa09e83300d00004629c43251738acc4fa24890b478635e1790a104141a809d834c0d200046234e30b9690a764cf233901073833e16989743f218c09703280c4000461c8e327974cad64ff24f90d879635e17a0a4c4341af0a083400ce000 else 0x49620e31e1754ad64ff241908476634616f0a184381ab09e03580d4000495b7831c1720ab84f1246106474233516789a040a1a00a3834c0e20004954fa3081670a564c72330ff071232015d89703fa192097832c0ba000494e6631c1778ad44fc243105c75c33a16809743fc185092031c0c60004947c0323175cad8506250906c76c34916f09d041a1a109d033c0d000049412f31516dca984e223c901c74234217089cc41e19e095031c0d6000493aa530e16bca824d5238103875633e16709943fc19109183200c40004934033199744ac250024a10c077234717209f84141a509b83380ca000492d623179714ac04f3244909c76634616e89c840619a09b03600e40004926d830a16b8a8e4dc23f904075033b16989ac4121a00a303740d20004920782f69634a4c4c522b8fc473033115f09483cc18709082f80c80004919da31c1720ab04df23b101872433916b099040219709c83200d800049136230796a8a864d6237907078e35d1790a144321b50a383340c6000490d022fc965ca4a4b72270f8c6fa31815e89683d819509302f00ba00049064132b17acaf050c24d10c879235317689e040c19a09c03440c200048ffcd30d16c0aa44e923d103c74c33716909d84101a90a2036c0d200048f90b32a1788aca4fd24790807743491730a204361ae0a403780d800048f285314171cad24f1243907076634417089e04081a209a83380da00048ebbd32c97bcb0050b25211107a836117d0a5845c1c10a803640da00048e524314972cab64f6247107876a34a16f09c440c1a909f83580ec00048de8931f1738ac44ef243907c78035f1750a1c4401b70a903940e600048d80230f96d4a924dc239101074c34016a09bc40419a09d834c0e200048d15731e973cada50924a907476834816e89c44161a209b03400d400048cabd31d1724ac04f924a90a478c3721830a3844e1ba0a803980ce00048c41a3229754ada4f724c10c07783481768a144401b20a703940d600048bd9731016cca744e223b101474234417189dc4201b00a283640f200048b71930d96a4a824dc242902875033a16889b84061a40a403680d400048b08a31696f8a884dc237101873233716589643f819409983340b800048aa023129718ab84f9240904073e33916d89c44181af0a0836c0de00048a34e323177cad84f8246106076034617389f04261b20a283680dc000489cc530d16d4aa04f024710ac7a436917a8a4844a1b50a483740e200048963830c96e4aa04ea23d902073033016709b44081a309a034c0da000488f903249778abc4f8241106476234716b89d841419809503180bc00048890331816f4ab64ed241106c74c34516c09b840219d09b032c0c200048829e2fc9650a504cb2328fcc72032c16589903e418409182e40ca000487c023191724ace4f3242908477835517789e041a1a5099833c0ce00048755431d973cad84fd24b10c478a35417809ec4201aa0a103800ea000486e9f31f1778ad450a25010f079435d17d0a3444c1b60a4036c0e200048680231596f0aaa4e924310747643531778a304481c10a203680de00048616831716f4aa44f0242908477834916c89703fc19709783300c6000485ac73241750adc50024b108476e34917289f84221a70a503700d800048545e2ff1658a5e4c7231900c73e33b167098c400192098030c0d6000484dcd31316e8aae4ed243107877c3521790a084201ac0a483780e000048471b321177caf051224e90ac76033f16d09e04181ab09d835c0dc00048409131196e8ab24f1246108c78834f1770a004361b10a283580e0000483a0e30a96c8a964e423f906074433c16c89d04321af0a703880de00048336e319972cabe4f6249908877834a16d09c040e1a50a003440c4000482cbb3271788ade50425210d07843551740a044341a809f03540d80004826083261794af250d24990b078c35b17f8a4444e1be0a5036c0d2000481f5c320177cade4ff24890a478a35817209cc4181a20a083480de00048189e32d17fcb3253a266913c7de3781868aa04781d10b403cc0fa0004811fe31a972caba4f3243909078035517589f042419d09e83600ce000480b53312971cab44ef246908877835817809dc41e1a209f03340d80004804c131296cca9a4e723f906476633b16a89b84201ad0a103640be00047fe2f31696f4aa64e423c904475834616c09c04121a209c83500d400047f77132b979cb0451125611447ba36b1818a704501c90ab83980ee00047f0de3151708ab64ea2350ffc72c33516309884061a30a003640d600047ea3031d9714ac44fa24710bc77a34c17089f842e1b60ab037c0ea00047e3a830f1704ab04ee243907075633e16989b041219f09883340c200047dcda33397ccb0a51825290d478835b17e0a2043a1b30a103700e000047d65d303968ca824de23a900472433216289983fa19c09882f40ba00047cfbe31996fca904e323c9018740338164897c3f619809a034c0ce00047c92631a1708aba4f3249909876434d17109f04181a309a03540de00047c29031416eca984e523d104475c34216a09a441219709a03200ce000))) else (if i < 45 then (if i < 43 then 0x4b073630c9688a824d9233902873833016409843e819509203240ca0004b007f3241790b0251d25991147c237e1828a404541bc0aa039c0f00004af9c83271780af451324e90c07963661810a7045a1cb0ac83940ee0004af3353141700aa44e8243105c74433516889c440419d09e03100be0004aecb730c16a4a824d22320fdc72832c166899c3f419609603100d00004ae6163209760ad44fa249109478035e17b0a1043c1b909f83600ea0004adf9a3071694a764d3237904075a34e16b89d040419a09603140ca0004ad8e63299778acc50724a10b078c35b17909fc4241a609c83400ca0004ad27030716c0a9c4e02390ff472432b16089703de18308e02ec0b00004acbd131a9728ab44ee23d904c75033916709ac3f219409282f80b20004ac54d30c1678a604c322f8ffc738333165098c3e618a09202fc0c40004abec631296dca8c4d9236902c74c33d16809b440219e09c83380cc0004ab84f3031684a6c4d7235100473833916889c042619f09683200b00004ab1aa31d175cade50624c109c77c35317489d84101a60a003380ca0004aab2730a16a0a724c8232102073632f16909d041a1a109b035c0d00004aa4c32fc1654a624db237103075433b1738a0c42a1ad0a103600d40004a9e3b30d16dca9a4f224710b07a636217a8a304401bb0a803840e40004a97b630d96e0aae4f8243906076834a17609e84181ac0a203700d00004a912230d16fcaa44ed243107876434917109dc4321ad0a403600cc0004a8a4c33097e0b1852425b91187b635b1790a204341b20a203640d40004a83a931f9758ac24f9242907c76a34c173899c3f419009683180d20004a7d0131b9720ad24fd24c90ac77435017209ec4281a309c83340c20004a766831c172cac64fa24990c477e34e1730a2442e1a70a383680e20004a6fa7326176cae650d24e10d079436117b0a384421c30a8838c0e40004a69343011644a564d0232100c75233f16d89ac40819f09c83580da0004a62873219774ada50224990d079a3651788a1c44e1c30a883580ce0004a5bc532f17f4b1c51f25a911c7b236d17e0a3443e1b70a603580dc0004a55533011674a864df238900c74233a16889b43ee19f09c830c0ca0004a4eac317972caba4f5248909877835117189d04261b10a283500e00004a485b2f81614a484c5230901475034116e89d04221ad09d83680e20004a41af3209770adc50924a90d079035f17909fc4481c00aa83880e20004a3b2e30d16c0a8a4e323f907475433f16d89c440219409b03500ca0004a34903191704a9c4df23d906075c34016c89a43f619809a033c0cc0004a2e07318170caac4e5242106875e34816e89ec42c1a609a035c0d60004a276031f975cad8500243107075834917009bc4061aa09e03400d20004a20da30d96eca9a4eb23f908076434316d09b440419709903300da0004a1a3d3141700aac4f124910b078835717209ec4201a60a0833c0dc0004a13a931016dca9c4ea23d902c75634917289f042c1a009583280d80004a0d2930a16a4a944d5235102873e33916909743e619409c83380c40004a069031a9714acc4fe24b10a876e34d16f09c442019d09883240c400049fffc3181708ab84fa24d90e47aa3621760a204341b309f83380c600049f95f31a9734abe4fd24a10b077034f16e89c841c1a809f03780e400049f2de3099694a7e4dd23e905075e34116f09943f4196098833c0cc00049ec5e30b1690a804e2239902c73433516a096840219a09f03700e400049e5da31016c4aa64e9241108876234716e8a204201a20a183580cc00049df4931496f0ab64fd247909077034916e89ec4221b20a683580d600049d8c930f16aca9a4e7244106c75e33a16909c04161a80a2037c0c200049d24c30a96c0aa84ec23e903c74a34316e89d04181ac0a383680e200049cbe32fd962ca4c4c322f900072c33416989883f619b09b03300d000049c535322978cae6501248908076434016b09cc4141a009c83280c800049be8d31b9738ad450124c10bc78234b1738a084321ae0a003480cc00049b8013171720aca50724990b47823551728a0842c1ad0a1834c0d400049b16f317171cac64f2240905476034116c09b44121a609e032c0de00049aaf230c16cca8c4d7239103073c336165098c408197098031c0b400049a4423241790ade50724a109c79235c1798a184301aa09c83480ca000499d8c3219754ad24ff24910b477c35f17f8a4c4501bd0a803980ee0004996e131d9768ac84fd24710a878e36617e0a2c4461c00a903800e200049902d322974cac64f8244107c75a33816909cc4161a709d83780da0004989bb3021698a8c4c92358ff074233b16609c04221b00a003340da0004983343149708ac84ef247107076635017009e440819a09a83400d2000497c7132b1788adc50825290d877e35017009c84201a309883380cc0004975cf3219730ad84fe24790a076c34b1770a2443e1ad0a003440d4000496f4931296dca844d9237101872e32b16009903f819709d83380ce0004968b33159744ad450424d10b477c34c17a0a304461ae0a203480d4000 else (if i < 44 then 0x4cab3431216e0aa04e123c107077a3501718a0042e1a709d83540da0004ca49a3179720ac64fe24c108c77e35a1758a2043a1a909d035c0da0004c9de932597acaf450824a10b078a36517b8a204401ae09e83180c20004c976930f96c4a9a4e8241905c76235317289c84141aa0a283740e00004c90c231e1720aba4ee249109c7963601798a144301ba0a383540d60004c8a4d30896d0a884da23d901072232916289b041819e09d03440ca0004c83be31316f0ab24ef243908c77635a17909ec40e19509603100ca0004c7d173219748ad84f9247908477a34b16c09bc41619f09603380cc0004c76853141734ad44f324e10ac78235017309f04081a009783340c40004c701230c16cca9a4e123a104875e34a17789ec4201a809f03300c80004c698b30b96aca8c4e9243106476433b165098040219209383000b80004c631030996c8a824d6238100471231e16289683ec19a09d03440d00004c5c763169700a9e4f424510a879035e17b0a2c4581bc0a483940fe0004c55ee31616f0aa24f124910d07943641828a784541c30a703740ce0004c4f5831616cca804d7233901873033e16c09c440e1970a0032c0c40004c48a63201734ac84e7241906876c34f17009e04221a709983480d20004c42353061668a644ca235101474033a16809a04181a409d83240cc0004c3b8e31a1714aca4f3243909c7703571780a2044e1bb0a503840d40004c3516306965ca7c4db23a102c74433416d09ac40619109a03340d40004c2e8431396e0ab04ea23d907877035116f89c840219e099832c0ca0004c27d03201750ac84f724d90ec7823571738a104181a60a303580d40004c213e3179718abe4f924990ac7723501768a184401b40a603600e40004c1ac130a16eca9e4d72370ff873c33816989b040a1a509d83580e20004c142731716fcaa64e623c102474233316b099c41a1a309d03340e00004c0d8e3189704aac4f0245907875a34b16a09c44121a90a003480d60004c06eb31d9728abe4f1242107075034116b89b840019909283040be0004c007830816c0a8e4e623c104074c33d17089f44261ae0a203400de0004bf9eb31516f8aac4f3242107c76e35917609cc42a19a09983200ca0004bf3463181728ab44ec246108878435f17689f04261ac0a083480c60004becbb30e16ccaa04db23d104475e34216c89e44321b30a303640da0004be6593009650a5a4c922d0fb471c32116589903e418409683040d40004bdfc23151730ac04f0240104c76c3431750a0841c1a60a2034c0de0004bd907328979cae250a24e10b076a3521790a1c41a1ad09f83300da0004bd2793109700ab04f724c10d07a23611790a3042c1a70a903640e40004bcbdd31e973cabc50c25310f87aa36c1800a7845e1c40a8837c0de0004bc5313261784af450f24e10c077436517f8a3043a1b80a683700ee0004bbe96317170cab84f8248909c77834817189e441e1a309803240ba0004bb8212ff1660a6c4bf22c0fe075634316f8a004221a309a03480be0004bb15632f97d0aea50425010d479c36817d0a1841a19809c03440da0004baad130a96c0a8c4e1236101874033a16989943e618f09482dc0b80004ba42a31d1768ae650425290e87a23711850a6c4521be0a983900de0004b9db030b1698a804d4235900873e33415f89703fa19209a03500de0004b97113111710ac24f324890b878c35d17c8a1842e1a509d03640d20004b909530b96e4aa84e6243907476e35717889f84181a409c03700de0004b89f43159734ada50925090d47783531788a2443c1ae0a003580dc0004b838f2fb1620a3c4be22f8fe472a32f167098c400196098832c0c60004b7cdc321971caae4f7242905c75c33f16a89b04221a50a083500c80004b763f31416e0a964dd23c904474a34416c09d440a1a80a783900d40004b6fee2ef9620a5a4bf22e0fe072c33516989bc41819d09a83280c40004b696f30c16d4a864d3235100c71c32415e09443e018608e02e00b40004b62b93251758ad250024a107875034a17509ec41e1a809e033c0dc0004b5c2e30d96a4a684d023d902874834316a09d841a1a209f031c0c20004b55b53051694a864dc2349000724322161099c41419c09f83500ce0004b4f27314171cab64f9247909477835817689fc4361ae0a503840de0004b488531d9724acc4f4244909878c36517a0a2c4441bd0a2834c0ea0004b421e30416a8a8c4dc23c903073834216d09d84401ae09d836c0e00004b3b873179708aa84e5238104074e337167898040c1a009f035c0d80004b34e03211750abe4f8244108876835517509e44321a909e03680c80004b2e3f31a174cacc4f2247908c78c36417d8a5844e1bd0a803480ca0004b27b331196e0aae4e9241104877034c17489e842e1a609e03240c20004b2128319972cab24ec242907c76c35017109f44281a509d83740dc0004b1ac62f89628a504c422b8fb070a33016409983fe19d09783240e00004b143b308168ca5c4d0234900872632b161899c3fa19e09e03780d60004b0dae30e96e4aa64de2370ff472a33016209903f419309c03200ca000 else 0x4e4f7d302168ca924d9238100c74033a16e89c440c19c09b83400cc0004e48d73209774ada50924d10a879836b17f8a2c44a1b80a983740c60004e42383179720abe4f223d905c7703521748a0841e1a909e03480d80004e3bcc30616b4a8e4dd242906475a34a17089d4414198099033c0d80004e353e30e96c8a8c4e323d104c76e34b17189c041c1a309f83840ec0004e2eaf31216f0a9c4e624010707723541750a084341b00a883780d60004e282d3099694a884d423a101072c33016309b83ec18d09603340d40004e215633117c8afe52025d112c7b836817c8a6c46c1ce0ae838c0e00004e1aa53209764ad04ff246108077635617689e04201b00a2038c0d40004e141930e96cca924d9240106c76a34b16e09f043e1ba0aa83980ee0004e0d8d3139710a944da236101c72a32716289583e818909903380de0004e071430c16a0a864da237104c77034f17509f44241b30a303600e40004e009330d96c0a964df23f909476434e16e09b440619309583240d00004df9d132c17c0afe50f25090c078e34e16f89dc40c1a309f03340c20004df33131a1744ade502246909077634b17109d4412196094032c0e40004dec9431a1750ac850124a109c77a35217a8a5845c1c50a8837c0e20004de5f43181708a964df23f108877034d1738a0c4281a409b83580f00004ddf693159714ac64f2242108877834a17209f842c1a409e83440d40004dd8de30d96d8ab64f623f905476434316d89d44201af09f83740e00004dd23d31a972cab04ef24b10c477c35616e09a83e819009683180c40004dcba7314171cac64f123f906076435517589e44061a009b83500d00004dc51830c16c4a964eb242107876634417289c04121a309b83200c80004dbe77322175cadc50324a109c7763571790a1c43e1ba0a4835c0da0004db7fc30e16d0a9e4e223f107476234116f89f84321a709f83140d20004db1942ff966ca5c4c822c0fb471e32415e897c41019d09c03340c60004daafc31116f8aa04e223e105c76234d17009c43fc19309403000d20004da47730c96b0aac4f023f10487563461730a004241a609c83180ce0004d9de331416f4aa04eb243909877c3561738a244481b20a283740de0004d975c31316d8a944e0238901474433816509903e018c09282f00c00004d90c93179700aa04e623f105074834016989c041419b09983640cc0004d8a353161710aae4eb241106c77a34c16c09cc41a198098830c0c40004d83873211764ada4fc249107476435017a0a0442019609683040c00004d7cff31016e4a9a4ef245108c78a34e17289e040819b09d03240be0004d76653139704ab24f423f105c76c34f17509dc42a1ae09e03540bc0004d70092fb9628a404b82230f6c6da318158092c3ce18d092032c0c80004d698f30896b0a8c4e223d107075e33b16989a44021a40a003380d80004d631131016c0a844e6241107075e34316b898840219209803000c40004d5c733199728ae050824d10d079035117609e841e1ab0a483880e80004d55e131a9730ac24fc24c10d07a03671790a304561b60a303480ca0004d4f6d30796b8a984e323c906475833b16b097c3ea18e09903500d60004d48d131796e4aa84e6240107877c34d16f89fc41219b09d03200c80004d421c32917acaee51225790c078434f17589e841a1a609d834c0d20004d3b913179754ac44f024c90b878234d16f09d042a1ae0a003480d60004d350430d96bca924db23b103074e33416609a440019b09803200ba0004d2ea12fe9660a644cf2330fec73433216a09b84201aa09a033c0dc0004d28083179724ac84f624b109077635317889f44121a009c03100c80004d217c31116cca924d6237104874833916b89b440c19809883300da0004d1ac632817a8af451224f90b47843561788a1441c1ab09f034c0ce0004d143231816fcabc4f624490a076e34f1750a0c42c1af0a283500c80004d0dc32fe9668a564d1234901473433216509743f219809803140d20004d07483081690a664ca22f8fc073832d16609a43ec18b094830c0d20004d00953231770ae850a24f10b478235017a0a244361b80aa83940ea0004cf9f731b9740ada4fa242107c76834917189dc40c1a509983000b80004cf37f30896a4a924e1237100474433f16d89c44161a60a103540c60004cecf33161710aac4e8246905c75c33b16b89cc41c1a309a83640e00004ce6513199700a964dd23a106075e34a1760a1442a1a909603180cc0004cdfc130e96e8a904db239904075834716f09c44101a509c03380d80004cd9313139708aa84e7241906c76a34816c09ac40a19f09e03800e80004cd2a530f96cca824e6240106c77635517209d840019e09a83440d20004ccc2c3051684a804da240106877a3571770a144341b90a683940ce0004cc58431e1738abc4f123e904873833515f89683f6193095031c0d40004cbf0130b96b4a6c4db239101075234016a89b04061a309d83680e00004cb88131016e4aa04f1243103c742333166898c40219c09703080c00004cb1c032a97ccb1852025b91407ca3711820a9446c1c00ad83980f2000)) else (if i < 46 then 0x4ff2753071694a744db23c101c74034516989d44221ac09d033c0d20004febe131c1764ace4e6238904474a34016e89e041a1a209683200ce0004fe5633121708ac44ff245108075a3471740a0042a1aa0a503680ce0004fdec7319972cacc4f9248108476634316d09c44081a909903300d40004fd8043251774ae250f25410ec79a36a1800a684601c30a7835c0e20004fd18030c16f4aa04e52421074766340168897c40c1a309f03480d60004fcae8315174cace50624f10b077834e17289d040619e09a83400ca0004fc4763031678a824db23e904073833d16709a04241b10a183640dc0004fbdc63219784af651425710dc7a636617d8a3c4421b50a303780e20004fb734316973cac24f9247109876634a16c89b84101a5097031c0c20004fb09c31a1724ac24f423e103c77635116c89983f018f09783280b80004faa053161728ac44fa24990d878e34216b09b040e1ad0a503980ea0004fa37031416e4aaa4ed23a8ffc736338161099c3e618809683080bc0004f9cc43239768ae650825290dc7aa36517c0a344381ab09e03640d80004f9631315171caaa4e5243106c76a34c17509ec4141a009c03440dc0004f8fa431096bcaa84e0239101c73c34317189c84141a209f035c0de0004f893e2fd1638a544c32300fdc714324167099040019909e03500de0004f829431a9748ad850224990ac78235a1758a3844c1b90a603780ce0004f7c2630296a4a6a4d523a104075433e166899840e19e09f833c0d00004f756132b179cae651025310ec7943541778a344361af0a783ac0ea0004f6ee53039698a764da23c904c76634716f89ec4221ac09e033c0d80004f68882fe9628a504bc22a0fcc71432315c09883f019109803380de0004f620a3049674a6a4d8237902074433f16909a83f418e097830c0d00004f5b8d30a16c0a984e623e103074c336163098040419509c03540dc0004f551730716a0a8c4e923a103075434416a09f041a1aa0a483800e40004f4eb22f81618a344b42288fbc70c31c16009843e418d09382f00ce0004f482431516f0aaa4eb24510b078a34f1738a2c43c1ae0a4035c0d80004f419f31316eca8e4e6237902073c33e16989b840419e09a03380c20004f3b1230c96bca9c4e7240907476c34516d89dc41419509582e80ba0004f34903101724ac44f224790647763541758a144441b30a503540da0004f2e1330596a4a7a4e0237902475634716f09c040419c09683200c80004f2789314970caa84ee242905075234b17209f04101b20a683900fa0004f21163069690a6c4d0233103875c34e17709e442a1ab09e83300ba0004f1a7c318171caaa4fc24510b477a35616e89ec4101a009783380be0004f14053051688a6a4de23b102c734331160898c3f618d09683480da0004f0d9d3049688a7c4d9235101473634316d89b840019809e03440c40004f070d31416c8a964e12358fec71c33116709ac41019b09e83580da0004f00883119718a964ec241106075633a16489803f019309183000c00004ef9df3219748ace4f824710b477c35717a0a244401b80a003500da0004ef34f3131714aa24e723f106075233a16b89b440c19d09d03300d40004eecb131396fcaa84ee245109876634116f89e84401ad09e83540b60004ee5fe3249778afa51f25810f07ac37117c0a4c44e1b80a303740d80004edf8a307169ca784cc2338fec73032d16009803fe19a09983400c80004ed8e2321977cadc4fc246907475a34517009e441a1a109e03280d40004ed24931b9758ada4fa24690a077434c16d89d44141a809e034c0d40004ecbc13119714abe4ed24990c479a35917889b842619909883240d20004ec5572fb1668a584d2237902873e33216789c042a1a409b836c0e80004ebecd31316e8aae4f4242904c74a34816f09dc4281a809f03640c20004eb84b30b16dca9a4de24090747623421728a044241a0098031c0ca0004eb1993251788af64fd243106875c34d16d09f441c19e09883340de0004eaaf33209768ad44f924990a877835a17b0a3443e19e09b03200ca0004ea469315970caa84ed243908878035b17489d440c19809683000be0004e9dc0318171cab64fa24a109076a35717709f04221b009f032c0c20004e971a3199704ab84f924610a078035016e09dc41c1a309e835c0dc0004e909431216f4a904e323b105876834d17009fc41a19a09803340b80004e8a0c30c96b8a8c4f2241105475a34117109e84361af0a8034c0d60004e837530f16dcaa04e4236900474e33a16989a440a19409683480be0004e7d003111700aae4e9241905872e33316709a840419a09c03200d00004e765b3199730af050c24f10d479036517a8a384401bc0a9839c0e20004e6f9b327979cb0e51525410e87ac3741838a6444c1be0a803900ea0004e692a30616a4a7a4dd23d906c76a35717289b03f019609e034c0ce0004e62bc2fe965ca624c622d0fc471832c16909e04161a109d033c0e20004e5c6e2f81618a484ba22b8fcc71232616189403d418e08d02e00b60004e55e631016d0a844db23a902475234616c89b841c1ad0a283340da000 else (if i < 47 then 0x51953531b9728ad250624d10b478a35a17689fc4321a609c83400ce000518ebc30916b8a804d62338fec71e33416309883f419309683400bc00051883b30f16e0a904e0243906476234516e09f84241a009e83340d00005181bb30d16f4aca4ed23f906c76a35316d09e84321ae0a203780f4000517b3d30e16a4a964e7243107475e34816f09e042019e09e03540b80005174c630716a0a724d62308fe873c33d16b89e04201a209b83580ce000516e313179740ab84f524c908c77e34d1728a1044a1bb09f83380cc0005167b030a16a8a824da237101c74232a16209643e2190094030c0b600051612a31216f8a9c4e2240105475234e1778a184161a709f83580d8000515a9f31016fca904e72429058744338168897c3e018b095030c0cc0005153fa3249754aea50724d10bc7723501770a344381b50a703780d2000514d7930a16c0a824df23b103074034117089c040e19e09783480e20005146ec30b96b4a744cd2308ff073232f16909bc41419a0a003540d800051407130616c4a864e223e105473832c16b099040a1a60a2034c0cc0005139b332817acb1052325811047a236017c0a484501b70ac83940e0000513332309166ca564c322c8fbc71c32f162896c3d818309703300d4000512caa31596f8aaa4e9242105c74033116609d04101a80a0034c0ce00051262d30916c4a964da23a103875e33f166897840619e09c83400c4000511fc72fe164ca3e4bb2290fb470431615c092c3c018909382f80bc00051194b303969ca884db23e107077035016c09dc4241a509b034c0f00005112dd3029680a7c4df237101c73633216989b8410194095834c0cc000510c5b30a16aca6c4da235901474a33916a09a83fa19f09c833c0d00005105b93221770ac64f824810a478e34416909bc40a19d09c03400c000050fef732c9798b0251a25290fc7b436d17f8a484561b40a503700e000050f8663169714ab44ed24b90dc79e3591780a244281a809e032c0be00050f1ea3111708aba4f3245106075c34516e89e042a1a309f03400d400050eb4c31796f4a9a4e223a9058748335166898c40819109703100bc00050e4e62f91630a544c522b8fc873834016a09903f018d09182fc0b600050de3e31c9744ad44ff247908875a34616f09d440e19b09783280be00050d7b13121728ac450124b10b878c36717d0a3c4441b00a4835c0ce00050d12630f96dcaac4e6241103c76034517309dc4181ab09c83440e000050caaa30f96b8a8e4e023a902073832e16309a041219109883540d000050c43330896c0a884de23c102475a33e16d89d442c1a909d83580d400050bdb830a16a0a8a4e7237101c73a33816a89c441e1b20a6035c0cc00050b71e31496fcaa64db23b102874c34116b09a841c19c09e832c0d400050b0ab302968ca884e1240107876a35017589e043c1b10a503800d200050a9f3329178caea50624b90e078236517c8a4c44e1c10a683780d800050a36131616e4a9a4e7244109075c3481750a204201a609d03700d4000509cbe31d9724ab64f824690a078235217189fc4281ac0a103640d80005096183201768ae04f9248909477434717489ec4281a309c833c0cc000508f8231396e8a964e223d103c75e34116c89b842c1aa0a303340de0005088f83139714ac44ef247907876434516f09c041219909783200d200050827e30816aca724ce2389030746337164898040619a09c037c0e0000507bf230d96c8a8e4dc241904474e34816d89bc40e19c09a83600da0005075663129704ac84fd24d90d078635617709e442a1a409d834c0e2000506edf30e16cca8a4d6236906076034f16d09a03f819609d03580cc0005068932f295f8a384bc22f0fb0706324162096c3e218308b82c00b00005061d932a1784afc50c25010f07923651800a3443a1a809d036c0dc000505b233259764ad44f924a909876e34816609903f21a009b03200d8000505493315170cab04ef244908076634416d89d04121a409f03580d8000504e2f2ff9658a564bd2280fbc6fe31b15989643f219d09983400d4000504788319170cab64f324b109477635117009b440e1a309b03540d00005040ff3119700aae4eb23e107875434c17209b44161a109e03540e0000503a4732917b4b0651525490f479236617e0a604561c70ab03940ea0005033db303167ca6c4cc238103474234817109f842c1ad0a303600e2000502d3631e176cae250624b90c878235517a0a404421b20a5037c0ce0005026c53021678a724c422e8fd871831d15e09303c618a09a83600d800050204b30316a8a7c4d5238902474433a16b09cc41e19f099834c0e60005019b131e1704a8e4dc2328fec72e33f16a09d442019f09d83440ce00050133f3091694a7a4d223a101c73632a16609a040c19f0a083840ee000500ccd302966ca524ba2250f846fa31715809383d018409003040be00050062d3189734ac84fb24810c079435d17b8a4443a1b70a203300bc0004fff9e314971caba4f4248109877234717009e841a1b10a283440d20004ff8e332c97bcaf651725490f87b636517e8a1843c1a809f034c0ea000 else 0x52fcef00000000004e223c104877034616e89bc41a1a10a003380c000052f65431b170ca9c4e0239902073433d16c099c40019f09a83540dc00052ef9a325977cade50a249105c75a34116789a040419509c03500e400052e91b3079688a664d4238901c73a333165897c3f819309403000b600052e2a33081698a884db237900873232b15e094c3ce18609383100ae00052dc0631b1710ac24f8249909077c35b17589f84301b40a403780d200052d55d3221770ae450a24b10c878a3521788a104341a309b83540d400052cecf31496f8aa84ef23b905c75434316c09a440419a09c03580b600052c85130996aca924e323a903475034716c89c040419d09a033c0da00052c1b031b172cab64e223b900474233a16589a03e8194095032c0d800052bb403019660a744cf23590287563421720a1842c1a50a003440e400052b4a631a96f8ac44f724610a477834b17289cc4241a70a203680e200052ae392fe1670a684cb2280fa46fc32815d89603de18709082e40bc00052a7b530e96e0a9e4e9242107475234316f89fc4201aa0a003340c800052a12d3141720ac04ea23e109477e35617209cc4301ae09e835c0e4000529aa23199724ab24ed24890bc79635917009e84141a809f03580d400052943a301967ca644ca230102075433e16809ac3fa19d09e03300d0000528daa3139700a964ea242108c76034c1718a0043a1af0a183340c800052873c3099690a8a4e023a104076c3531758a004221a909a835c0dc0005280b331496c8a824d82380fe874032c16589783de19e09d035c0d60005279fe3279788afc51625310e07a635f17e0a484561b509d83600e6000527392301967ca5c4ba22c0ff073032c166898c4001a409e03640cc000526d0b30d16a4a7a4d9235900474833316a09e441e1a609c03580d000052667b3189704ac24ff24910d879635717809d842c1af0a103540e2000525fd231e9744ad44f0246106c76a34316f09f441e1a30a083840dc00052593531716e8abc4fb243906c76634616e8a1c4361b90a9836c0e40005252c4304166ca5e4c222b8fe473c33a16689984101a30a083640d8000524c4b3099698a8a4ce234901073032215f89ac3fe18509383000bc0005245c330c16b0a804d7235100871833216a09c04101a309e83580d6000523f183219778ae851325891007b636c1820a7045a1bf0a603740e000052388a3141714abc4f1245908076a3501700a0841e1a709f83700d000052320b304966ca6a4d4239903474634817089f844a1ac0a0835c0d6000522b723141728ad44fa245109077a34e17309d041a1a40a003380c60005224f530896c0a864e3238103476834c17209e441e1a809d835c0e0000521e833019654a524cd2330ff073433016709ac41619909b03500d000052181b3011648a624cb23a101073a33716689803fc19409603200d80005211bb301966ca764d5238901c74033f16e09e842a1b009a03680d6000520b4c303965ca744db236900c73632d16689843fc19f09b03480d00005204c130f170cac64fa240106075834116a89bc4101a009d03340d200051fe143219728ab04f324e90a077034d17309dc41e19b0a083480d400051f7a830696a0a9a4e8244108878a35b17709f84201a309c03400d200051f0f83269784aec51225711287b036717d0a684521b20a2835c0e000051ea6a3131704aba4f2247908476e35017789fc4441b00a403700ce00051e3e830d96f0ab04e423e107c77c35817a0a1843c1bd0a803900de00051dd5c3119708aa64f8245106475c35117389f441a1a909f03440cc00051d6b1322178cada50725190d47983691820a6844a1ba0a103a40dc00051d03030b16b8a864d0238102072e33816b89c040a19909f83580be00051c99c31e176cad44fc24690a077a34f16c89c84001a40a403680e800051c2f331d1744abe4f9246908076634d17289fc41c1a709883440da00051bc8f30796b0a9c4e223a903c7643491748a084421b10a583740e200051b5f63199728aca4fa249906c75c34217109d03fe197097832c0c200051af7f30816a4a904e223c104474e34a16f09f843019b09d03580e000051a8f031416e4aa84e623d904c76634716e09c04281a70a0036c0c800051a25831c1748ab64ff24890a076234f17409f042e1ab09f83340c4000519bd131116d4a884da236102473633115f89943ee19709f83540d6000))))))

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



private theorem b35125 : covered 35125 35221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35221 : covered 35221 35316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35316 : covered 35316 35412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35412 : covered 35412 35508 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35508 : covered 35508 35604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35604 : covered 35604 35699 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35699 : covered 35699 35795 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35795 : covered 35795 35891 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35891 : covered 35891 35987 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35987 : covered 35987 36082 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36082 : covered 36082 36178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36178 : covered 36178 36274 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36274 : covered 36274 36370 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36370 : covered 36370 36465 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36465 : covered 36465 36561 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36561 : covered 36561 36657 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36657 : covered 36657 36753 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36753 : covered 36753 36848 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36848 : covered 36848 36944 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b36944 : covered 36944 37039 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37039 : covered 37039 37135 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37135 : covered 37135 37230 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37230 : covered 37230 37326 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37326 : covered 37326 37422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37422 : covered 37422 37518 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37518 : covered 37518 37613 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37613 : covered 37613 37709 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37709 : covered 37709 37805 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37805 : covered 37805 37901 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37901 : covered 37901 37996 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b37996 : covered 37996 38092 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38092 : covered 38092 38188 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38188 : covered 38188 38284 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38284 : covered 38284 38379 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38379 : covered 38379 38475 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38475 : covered 38475 38570 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38570 : covered 38570 38666 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38666 : covered 38666 38761 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38761 : covered 38761 38857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38857 : covered 38857 38953 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b38953 : covered 38953 39049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39049 : covered 39049 39144 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39144 : covered 39144 39240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39240 : covered 39240 39336 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39336 : covered 39336 39432 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39432 : covered 39432 39527 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39527 : covered 39527 39623 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39623 : covered 39623 39719 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39719 : covered 39719 39815 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39815 : covered 39815 39910 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b39910 : covered 39910 40006 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40006 : covered 40006 40101 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40101 : covered 40101 40197 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40197 : covered 40197 40292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40292 : covered 40292 40388 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40388 : covered 40388 40484 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40484 : covered 40484 40580 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40580 : covered 40580 40675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40675 : covered 40675 40771 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40771 : covered 40771 40867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40867 : covered 40867 40963 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b40963 : covered 40963 41058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41058 : covered 41058 41154 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41154 : covered 41154 41250 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41250 : covered 41250 41346 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41346 : covered 41346 41441 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41441 : covered 41441 41537 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41537 : covered 41537 41633 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41633 : covered 41633 41729 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41729 : covered 41729 41824 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41824 : covered 41824 41920 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b41920 : covered 41920 42016 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42016 : covered 42016 42112 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42112 : covered 42112 42207 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42207 : covered 42207 42303 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42303 : covered 42303 42399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42399 : covered 42399 42495 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42495 : covered 42495 42590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42590 : covered 42590 42686 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42686 : covered 42686 42782 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42782 : covered 42782 42878 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42878 : covered 42878 42973 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b42973 : covered 42973 43069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43069 : covered 43069 43164 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43164 : covered 43164 43260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43260 : covered 43260 43355 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43355 : covered 43355 43451 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43451 : covered 43451 43547 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43547 : covered 43547 43643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43643 : covered 43643 43738 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43738 : covered 43738 43834 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43834 : covered 43834 43930 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b43930 : covered 43930 44026 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44026 : covered 44026 44121 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44121 : covered 44121 44217 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44217 : covered 44217 44313 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44313 : covered 44313 44409 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44409 : covered 44409 44504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44504 : covered 44504 44600 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44600 : covered 44600 44696 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44696 : covered 44696 44792 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44792 : covered 44792 44887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44887 : covered 44887 44983 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b44983 : covered 44983 45079 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45079 : covered 45079 45175 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45175 : covered 45175 45270 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45270 : covered 45270 45366 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45366 : covered 45366 45462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45462 : covered 45462 45558 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45558 : covered 45558 45653 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45653 : covered 45653 45749 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45749 : covered 45749 45845 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45845 : covered 45845 45941 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b45941 : covered 45941 46036 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46036 : covered 46036 46132 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46132 : covered 46132 46227 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46227 : covered 46227 46323 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46323 : covered 46323 46418 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46418 : covered 46418 46514 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46514 : covered 46514 46610 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46610 : covered 46610 46706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46706 : covered 46706 46801 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46801 : covered 46801 46897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46897 : covered 46897 46993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b46993 : covered 46993 47089 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47089 : covered 47089 47184 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47184 : covered 47184 47280 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47280 : covered 47280 47376 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47376 : covered 47376 47472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47472 : covered 47472 47567 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47567 : covered 47567 47663 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47663 : covered 47663 47759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47759 : covered 47759 47855 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47855 : covered 47855 47950 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b47950 : covered 47950 48046 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48046 : covered 48046 48142 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48142 : covered 48142 48238 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48238 : covered 48238 48333 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48333 : covered 48333 48429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48429 : covered 48429 48525 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48525 : covered 48525 48621 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48621 : covered 48621 48716 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48716 : covered 48716 48812 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48812 : covered 48812 48908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b48908 : covered 48908 49004 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 35125 49004 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b35125 b35221) (joinCoverage b35316 b35412)) (joinCoverage (joinCoverage b35508 b35604) (joinCoverage b35699 (joinCoverage b35795 b35891)))) (joinCoverage (joinCoverage (joinCoverage b35987 b36082) (joinCoverage b36178 b36274)) (joinCoverage (joinCoverage b36370 b36465) (joinCoverage b36561 (joinCoverage b36657 b36753))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b36848 b36944) (joinCoverage b37039 b37135)) (joinCoverage (joinCoverage b37230 b37326) (joinCoverage b37422 (joinCoverage b37518 b37613)))) (joinCoverage (joinCoverage (joinCoverage b37709 b37805) (joinCoverage b37901 b37996)) (joinCoverage (joinCoverage b38092 b38188) (joinCoverage b38284 (joinCoverage b38379 b38475)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b38570 b38666) (joinCoverage b38761 b38857)) (joinCoverage (joinCoverage b38953 b39049) (joinCoverage b39144 (joinCoverage b39240 b39336)))) (joinCoverage (joinCoverage (joinCoverage b39432 b39527) (joinCoverage b39623 b39719)) (joinCoverage (joinCoverage b39815 b39910) (joinCoverage b40006 (joinCoverage b40101 b40197))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b40292 b40388) (joinCoverage b40484 b40580)) (joinCoverage (joinCoverage b40675 b40771) (joinCoverage b40867 (joinCoverage b40963 b41058)))) (joinCoverage (joinCoverage (joinCoverage b41154 b41250) (joinCoverage b41346 b41441)) (joinCoverage (joinCoverage b41537 b41633) (joinCoverage b41729 (joinCoverage b41824 b41920))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b42016 b42112) (joinCoverage b42207 b42303)) (joinCoverage (joinCoverage b42399 b42495) (joinCoverage b42590 (joinCoverage b42686 b42782)))) (joinCoverage (joinCoverage (joinCoverage b42878 b42973) (joinCoverage b43069 b43164)) (joinCoverage (joinCoverage b43260 b43355) (joinCoverage b43451 (joinCoverage b43547 b43643))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b43738 b43834) (joinCoverage b43930 b44026)) (joinCoverage (joinCoverage b44121 b44217) (joinCoverage b44313 (joinCoverage b44409 b44504)))) (joinCoverage (joinCoverage (joinCoverage b44600 b44696) (joinCoverage b44792 b44887)) (joinCoverage (joinCoverage b44983 b45079) (joinCoverage b45175 (joinCoverage b45270 b45366)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b45462 b45558) (joinCoverage b45653 b45749)) (joinCoverage (joinCoverage b45845 b45941) (joinCoverage b46036 (joinCoverage b46132 b46227)))) (joinCoverage (joinCoverage (joinCoverage b46323 b46418) (joinCoverage b46514 b46610)) (joinCoverage (joinCoverage b46706 b46801) (joinCoverage b46897 (joinCoverage b46993 b47089))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b47184 b47280) (joinCoverage b47376 b47472)) (joinCoverage (joinCoverage b47567 b47663) (joinCoverage b47759 (joinCoverage b47855 b47950)))) (joinCoverage (joinCoverage (joinCoverage b48046 b48142) (joinCoverage b48238 (joinCoverage b48333 b48429))) (joinCoverage (joinCoverage b48525 b48621) (joinCoverage b48716 (joinCoverage b48812 b48908))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 35125 ≤ index 67545646/512 := by decide +kernel
private theorem starting_value : fast 67545646=3982129 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 67545646=3982129) (n : ℕ) (low : 67545646≤n) (bound : n≤94085731) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=67545646
    · rw [first,anchor]
      exact starting_value
    · have past : 67545646≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤94085731 by omega)
        have within : index n / 512 < 49004 := by omega
        have lower : index 67545646/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤94085731) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeQ67545646To94085731
