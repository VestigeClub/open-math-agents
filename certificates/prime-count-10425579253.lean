import FormalConjectures.OEIS.«247824»

/-!
# A certified value of the prime-counting function at 10,425,579,253

Credit: @VestigeClub. A wheel sieve verifies a table of prime counts. Legendre's
recurrence stops when the remaining interval contains no composite with two
surviving prime factors. Meissel's semiprime correction gives the exact count.
Blocks of 2,310 count survivors of the first five primes, and a smaller bitmap
supplies the frequently used initial prime counts.

The Meissel identity comes from Physbuzz's published reduction for A247824.
The Legendre recursion adapts Daniel Veljjanoski's Palomar proof as formalized
by rleshner in OeisA100475.conjecture (Apache-2.0).
Palomar source: https://github.com/veljjanoski/oeis100475-palomar/tree/0968200356e449a24a023264821d4ea966091cf0
Reference: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9315
-/

namespace ShortPeriod

open Finset

def cop (n : ℕ) : Bool := decide (n%2≠0 ∧ n%3≠0 ∧ n%5≠0 ∧ n%7≠0 ∧ n%11≠0)

private def pop (x : ℕ) : ℕ :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b+(b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c*0x0101010101010101) >>> 56)%256

private def withinPeriod (n : ℕ) : ℕ :=
  let word := (0x1df000000000000002001d10228828228820a0801c4a08820228a20008801b628028208a20a00a201aa8008028a20a08820019c828228220808a208018f08200a20a082288201828228200a00a288200176228800a08a088200016828a2020882882820015a0a20a08a28028028014c820a082208282282013f20808a08808220a201330808228028228a000124a00a28808228820a011808808820228a2020010a8820828208a20a0800fba28028028220a08a00ef20820228200808a200e38808020a2020822800d5828220a00a00a28800c728228820a082088200ba0228a2020880882800ad208a20808a280280009f28a20a00a2080822009382208088288082200084a20a08220828208a007700a00a2882822802006a0a08a08820228a00005d208828828008a202005008a28028020a20a000438a208282280208080035228808220a20a082002808828228a00800a2001b8028228820a00a08000e800228a202088288000028208a20a08a2002 >>> (80*(n/64)))%(2^80)
  (word >>> 64)+pop (word%(2^(n%64+1)))

def wheel (n : ℕ) : ℕ := (n/2310)*480+withinPeriod (n%2310)

private def check (r : ℕ) : Bool :=
  wheel (r+1) == wheel r + (if cop (r+1) then 1 else 0)

private def valid (lo len : ℕ) : Prop := (List.range' lo len).all check=true
private theorem glue {lo a b : ℕ} (u : valid lo a) (v : valid (lo+a) b) : valid lo (a+b) := by
  unfold valid at *
  rw [← List.range'_append_1,List.all_append,u,v]
  rfl

private theorem b0 : valid 0 72 := by unfold valid; decide +kernel

private theorem b72 : valid 72 72 := by unfold valid; decide +kernel

private theorem b144 : valid 144 72 := by unfold valid; decide +kernel

private theorem b216 : valid 216 72 := by unfold valid; decide +kernel

private theorem b288 : valid 288 72 := by unfold valid; decide +kernel

private theorem b360 : valid 360 72 := by unfold valid; decide +kernel

private theorem b432 : valid 432 72 := by unfold valid; decide +kernel

private theorem b504 : valid 504 73 := by unfold valid; decide +kernel

private theorem b577 : valid 577 72 := by unfold valid; decide +kernel

private theorem b649 : valid 649 72 := by unfold valid; decide +kernel

private theorem b721 : valid 721 72 := by unfold valid; decide +kernel

private theorem b793 : valid 793 73 := by unfold valid; decide +kernel

private theorem b866 : valid 866 72 := by unfold valid; decide +kernel

private theorem b938 : valid 938 72 := by unfold valid; decide +kernel

private theorem b1010 : valid 1010 72 := by unfold valid; decide +kernel

private theorem b1082 : valid 1082 73 := by unfold valid; decide +kernel

private theorem b1155 : valid 1155 72 := by unfold valid; decide +kernel

private theorem b1227 : valid 1227 72 := by unfold valid; decide +kernel

private theorem b1299 : valid 1299 72 := by unfold valid; decide +kernel

private theorem b1371 : valid 1371 72 := by unfold valid; decide +kernel

private theorem b1443 : valid 1443 72 := by unfold valid; decide +kernel

private theorem b1515 : valid 1515 72 := by unfold valid; decide +kernel

private theorem b1587 : valid 1587 72 := by unfold valid; decide +kernel

private theorem b1659 : valid 1659 73 := by unfold valid; decide +kernel

private theorem b1732 : valid 1732 72 := by unfold valid; decide +kernel

private theorem b1804 : valid 1804 72 := by unfold valid; decide +kernel

private theorem b1876 : valid 1876 72 := by unfold valid; decide +kernel

private theorem b1948 : valid 1948 73 := by unfold valid; decide +kernel

private theorem b2021 : valid 2021 72 := by unfold valid; decide +kernel

private theorem b2093 : valid 2093 72 := by unfold valid; decide +kernel

private theorem b2165 : valid 2165 72 := by unfold valid; decide +kernel

private theorem b2237 : valid 2237 73 := by unfold valid; decide +kernel

private theorem allrows : valid 0 2310 := (glue (lo:=0) (a:=1155) (b:=1155) (glue (lo:=0) (a:=577) (b:=578) (glue (lo:=0) (a:=288) (b:=289) (glue (lo:=0) (a:=144) (b:=144) (glue (lo:=0) (a:=72) (b:=72) b0 b72) (glue (lo:=144) (a:=72) (b:=72) b144 b216)) (glue (lo:=288) (a:=144) (b:=145) (glue (lo:=288) (a:=72) (b:=72) b288 b360) (glue (lo:=432) (a:=72) (b:=73) b432 b504))) (glue (lo:=577) (a:=289) (b:=289) (glue (lo:=577) (a:=144) (b:=145) (glue (lo:=577) (a:=72) (b:=72) b577 b649) (glue (lo:=721) (a:=72) (b:=73) b721 b793)) (glue (lo:=866) (a:=144) (b:=145) (glue (lo:=866) (a:=72) (b:=72) b866 b938) (glue (lo:=1010) (a:=72) (b:=73) b1010 b1082)))) (glue (lo:=1155) (a:=577) (b:=578) (glue (lo:=1155) (a:=288) (b:=289) (glue (lo:=1155) (a:=144) (b:=144) (glue (lo:=1155) (a:=72) (b:=72) b1155 b1227) (glue (lo:=1299) (a:=72) (b:=72) b1299 b1371)) (glue (lo:=1443) (a:=144) (b:=145) (glue (lo:=1443) (a:=72) (b:=72) b1443 b1515) (glue (lo:=1587) (a:=72) (b:=73) b1587 b1659))) (glue (lo:=1732) (a:=289) (b:=289) (glue (lo:=1732) (a:=144) (b:=145) (glue (lo:=1732) (a:=72) (b:=72) b1732 b1804) (glue (lo:=1876) (a:=72) (b:=73) b1876 b1948)) (glue (lo:=2021) (a:=144) (b:=145) (glue (lo:=2021) (a:=72) (b:=72) b2021 b2093) (glue (lo:=2165) (a:=72) (b:=73) b2165 b2237)))))

private theorem wheel_shift (q r : ℕ) : wheel (2310*q+r)=q*480+wheel r := by
  simp [wheel,Nat.mul_add_div (by decide : 0<2310),Nat.add_mul,Nat.add_assoc]

private theorem cop_shift (q r : ℕ) : cop (2310*q+r)=cop r := by
  have m2 : (2310*q+r)%2 = r%2 := by rw [show 2310*q=2*(1155*q) by ring,Nat.mul_add_mod]
  have m3 : (2310*q+r)%3 = r%3 := by rw [show 2310*q=3*(770*q) by ring,Nat.mul_add_mod]
  have m5 : (2310*q+r)%5 = r%5 := by rw [show 2310*q=5*(462*q) by ring,Nat.mul_add_mod]
  have m7 : (2310*q+r)%7 = r%7 := by rw [show 2310*q=7*(330*q) by ring,Nat.mul_add_mod]
  have m11 : (2310*q+r)%11 = r%11 := by rw [show 2310*q=11*(210*q) by ring,Nat.mul_add_mod]
  simp only [cop,m2,m3,m5,m7,m11]

theorem wheel_succ (t : ℕ) :
    wheel (t+1)=wheel t+(if cop (t+1) then 1 else 0) := by
  let r := t%2310
  let q := t/2310
  have split : t=2310*q+r := (Nat.div_add_mod t 2310).symm
  have h : (List.range 2310).all check=true := by rw [List.range_eq_range'];exact allrows
  have item := List.all_eq_true.mp h r (List.mem_range.mpr (Nat.mod_lt t (by decide)))
  have step : wheel (r+1)=wheel r+(if cop (r+1) then 1 else 0) := beq_iff_eq.mp item
  rw [split,Nat.add_assoc,wheel_shift,wheel_shift,cop_shift,step,Nat.add_assoc]

private theorem cop_iff (n : ℕ) : cop n=true ↔ ∀ p ∈ Nat.primesLE 11, ¬ p ∣ n := by
  have ps : Nat.primesLE 11 = ({2,3,5,7,11} : Finset ℕ) := by decide +kernel
  rw [ps]
  simp [cop,Nat.dvd_iff_mod_eq_zero]

theorem count_rough (t : ℕ) :
    ((Icc 1 t).filter (fun n => ∀ p ∈ Nat.primesLE 11, ¬ p ∣ n)).card = wheel t := by
  induction t with
  | zero => decide +kernel
  | succ n ih =>
    have interval : Icc 1 (n+1) = insert (n+1) (Icc 1 n) := by
      ext k
      simp only [mem_Icc,mem_insert]
      omega
    have fresh : n+1 ∉ Icc 1 n := by simp
    rw [interval,Finset.filter_insert,wheel_succ,←ih]
    by_cases hp : ∀ p ∈ Nat.primesLE 11, ¬p ∣ n+1
    · rw [if_pos hp,(cop_iff _).mpr hp]
      exact Finset.card_insert_of_notMem (fun mem => fresh (Finset.mem_filter.mp mem).1)
    · have no : cop (n+1)=false := Bool.eq_false_iff.mpr (mt (cop_iff _).mp hp)
      rw [if_neg hp,no]
      simp

end ShortPeriod


/- Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace WheelTableA94

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


private def packet (i : ℕ) : ℕ := (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x3ab60e119d9b6d2b63403944308218d32405aae037a522434c0a262c7570360b01689d1784d8c180345ada9c22287ce24050328618302abcad593d2030c2770494d45aa5a8602f214089851b7e3556002d62e1568bf88056a0702b99c742f3ad40648d102a0c41e22a6502b962402838dea735ca89501190266f8246c44cbf10b43024b307a4c570c944ab2022f02cdcdb50238f12c0211c383dc8219f6264e01f44c58b42aa71c8b5a01d64d33f3243e88518d01b999eb813c26c73811019ea0e3266581d892d2017b87588f9265aefb720162468c83e5081a96540142ef17c19b7171582101224f8cbcc8b37ac18c010454bf11453a2b4cb800e13a13f666e944fd2e00c1f8a154039ff0a3d9009f554c2ade2dade356007d56a61e78bd92676a0059a559dd3bd3d30ce600319eeda6eaf31e4fd50000f93ddbb67eefdffe else (if i < 2 then 0x6e2a1aab3e1522a44b506cc155941180896a81606b0b1474266d75888980693f40c0fd888a13367068030831c4901c11218066ae8021d1461b0180d064c5c788582a4742d9f0635a08ac312424892d5061f073110366302a4b006041b6614e808d83c6a05ebc476e0092ca50a6105ce4a84d62d2a8b935605b3c319653818c126cd059b91500ec0f60c2e06057e15a9d8d2182f54f0056a0931a610461a818205518bc61a44c88c27220536c760421da13859b20520104ac2b029c3d3000506a508e9861b26568204ee818992787024225d04d24c8ed84446e5c16c04bbb430300a25c31934049de34730e982b129e904831006c514dc3dcb1404672e644e1194e3471a044f2902ac8f81c5680a04301cb59861572ae6c3041838b14873440319e003fc32c8231e685da12703e5105574a88388099a03ca947a44d060391a67 else 0x9f0b7484c511415c01609d61a8596b4a171c00e09c12d050c8b409530c009a8197c9080613a698c098ed9364b110a8445650976866253324449301d095ab2f02e6f10089770094214780a82150eaae109291483817d0c62a4720913c280308cf932444108fe912809c930700d0608e5e0bb5812248c845908c938db21462d1ccc9208afc1834c29426c92b3089804002a54cd032bd3087d7e47c008a48aa32e08690c518403e11464280856903c80a0805a42c40841c525021058098e490827076a4626448f309c080d6b2520cf8291bc0807f33730adc5093211c107dd328a0cb018b1e12007bfa3d629317a25562c07aa022439c28252c20b0790750b88570ce409c407791063206c478c980b076250a0560e57012ca8074c840a61d07801915607347e08150c826b362007170ad654be00673ca306ff0ca5111855624559)) else (if i < 4 then 0xcd75a952b004238a29c0cc230860982146a41a90caa09532438eb84908c0c9728221601d91888810c81c45009c1612370160c6a04484ac5b842d1520c542145352a53c102600c3d5e80848b24268a1a0c20612c29522ec79b2c0c0ab618c242e1ca01800bf3b2f000a50c4409b30bdd230686435c3148060bc11aecd9f8078851140bac0c05b083829632030b9b02808f29811480420b81391b8914542e144d0b658ca9445083dddc830b515014462046a0a3520b37d11286981d9228d50b20442e88092671216c0b0ac88a3421c16342480af1d2692cf1064001da0ada898452e13c015aa00ac229ca1712421c40b60aad4872222704a918880a9923548144410652a10a866061d12c829004060a69a851a1197b5528e30a4f471023aae20ec48b0a335c2033c078e91eb40a20220891108190d51c0a08a1022e8a89109579 else (if i < 5 then 0xfb843047663443486d20fa66028088a811e1b000f9312a5510c8c02022c0f770ac891af329768430f620890ae31701848510f4da5208a1206a1ca280f3219e99312448f94a10f1963544a82996538180f02f30800c84c2ac2c50eed22860514324b021e0ed5cac44930a9342e040ec1d1800300025c605f0eab3101326344489b050e9393030404e496acac0e8018010ca0c2543c220e690472a44ad18459c00e512a2d9990a44135120e39ce4bc11c093338000e25062c8203074461540e0b319473a1482016f90df3b6c2644aa60269100ddcf9953002096585800dc1d14c62c8d991c3820dac206c0ee4203a500a0d9145c2ec1c1b220ccd0d7707e91cf0071849c80d608c30aaf430c54a000d4c1148b010c1853c220d361ac2144a1d1c26800d1f001e821b9016f3600d066e2e8c05a928c0540cef270445ada2c14a02 else 0x1289458300a4e80050c912745e009b10131a8508125fb0994855002a489112470eb264624015843712348051400a1968928a121c9160a29c4485981712074e0288dc9740601011f12d140009fa811ca411d681e5312936166d4811c4418240017e28070411ad258a73380c109415119b11740005c14502431187222442481990c8a311704ac18069a41a51521159aed22c04239040a6113e5f583b28a342cc1011259c9ba22404cd0878110b8cbb115a89c0641510f382a014a717d880e110dfd122480cb415402110c42a4f4cf12d18061610ab8b0844aa0a6274e91099116480b800322350108489a2d92078020740106e00d0470862cc392a1058083460e442811ad31041b424a48aa8268162102c04c505e00560a24e10148c594005f2a50e280ffddaa01c6043284e440fe35529094232cec38c0fd1a1c836400401f100))) else (if i < 9 then (if i < 7 then 0x154b8130c418eb9c2182153818204627062818a1151fb02c068d30997286150902615b108ce1821a14f3089255945026206714e14c9520184006ac0114cb4582e2412e4a144114b53303211c248ac1a8149eb2523081c168930a1483c6448743c4b7d041146b3c821851a278231c1458200599016194288c144552a9009a444209061431102f01e24a018454141d1a6165064c0710101401d1e5528e4c2c027313eb811449473813911113d5382a4a00b3c0866413be638c382c1231404713a5c3908ec1225ca988138d500229b20ea3970c1377003930646141d8171362c8907244460c8522134f841a8a05a12820d0133806c6c3412250b330131f0e1d8438a8a5284b130757008532344c82da12f1a11110813ae4503512df02180208849341b612c80196184788e8858a12b3a046a31781210192129c342d02a09d0b406c else (if i < 8 then 0x180d02c18a6c0341414417fd008d24240346140117e54a79b0a00508ce1a17cf88a1b3572000949817bc02c242484b10613417a60a8034aa1dd0069817968514240288082324177f58c2c1e4370116201767620e5c32d2b54001174d4869b242a46a4acc17392d9498517680010017233151512a86044c2a170d2a04060d934cb81116f760040b96e18e21a016e156c641181851842a16c8a0cf4116e2a2660116b55130304a120242ca169d318119a50c4cc8e4168392989600e8552d9c166c4243706a130d156016526134204eacba4b11163e4aa0412038b0322616282149d40980d2108f160f0e842afad040471515f95c2da8a01485109115e38121417c4100a8bb15d0014212c0c781246815bca43206846022d10315a3602a11d10e638678158b20d1ec17116452841579020919290540a20d156250249a370684c158 else 0x1ab8a00b01a5404212f51aa48801c1162a8c98a01a8fc111106515d83a001a7ea10421018422f0051a68140c9129080a966e1a52054248a32a7548a01a3b810494b29344e60a1a2475a420e0108d113c1a0e3499a440c6c9081819f6b9602a4d049409a919e146404891518968a419cf1a8448599a01410019bc8404e41038c6168019a64c54342111762091198a01bb921662a38b7119768220326a4518188a195f3220486e14e5a148194a715021138534601419344c4202889c0b653219254008a80cc061400a19118c640350311c088518ff1818d210208b005918e388e94452ab86b09718c9b221542a5861a39318b6531c86030130808618a14a2a81803d80b450188e65028509494118281877d25508a8165a80511865080619704008d584184c0fa0851a8347948a183b20250a2804142a43182053566841d82659c1)) else (if i < 11 then (if i < 10 then 0x1d6807184210d1841a211d530e2655410c42b0481d3e08c1e90a007228651d2c80240fe2070808881d14441b504538e0c4b41cfe0b19d54080141d921ce752c222889b8934881cd52060069c002168561cbe6647022591ba90081ca8099255073084642c1c900e580b1a8204ae931c7ca901c306162045601c681252b060091414a91c51c15072c550d00b281c3f4602ad0629108a001c2c240154048c70e2181c15e34769a00a10182a1bfe94ad3858022640591beb34050062460a138c1bd53d0074202d9859201bbbd94342a394d130911ba8042ec142401829921b8d086c4aacb06bf20a1b790e98210758a024a01b5f8935a391c5326c401b4b488822821a2390cc1b3622833434a809c1031b1d628426c38e518f201b089520af00858482321af674809c30231140401ae14010803d5a260ce41acd06180072c45c09c2 else 0x20121ad51590303a80421ffbad2588570083d0141fe81880c544624841191fd50231204986948e101fc10214ab53a81181201faa724f9810021163621f9a08d1082049c0120c1f83d4703c200308e5071f6ea182d9d0040a45a01f59142307726949a0001f3f5135780e4ba1888a1f29822064921c9632a41f1700ee52800a21240c1f02e902cc00c8714a041ee886543d7920486b901ecf088ca8f132091f941ebc35601212418c30821ea510c32282c92d311a1e92740603048432d0601e7a1c8b1cdd0290003e1e67220f64a1a30044041e4f59389298a46885811e3c542ec142086400b01e2704a1721888d780111e11530068424b8983921e009032040214170a211deb604cda310420a5121dd88a84602818a046491dbc196cb42307066bc31da761b411300aa68a041d90bcf04506460144831d7b2a440cc0d04c13a1) else (if i < 12 then 0x22ab48260a0540d037612299200a064f0518414422874025015c0488c0782272491b70042b406a80225bc86db4318008a2942249111710434c4a008422342a30953088027921222160301e2cc0082542220692764883108ec17721ef2a608ab410a9a26221d9c00025b851741c0b21c4c510a918d540224821ac64166880426b1995219406d821108a4b483f2181e10324011f40318021701048c1c01910803321630481864402802208214ea0109d198914168821364158116187642dc8211f383b8b85404b184021098258c61c0d03818920f69844260c44a4b80020e42750404648a4620020d03022c42c2513444820b4a59d091e2ae0266520a30b1c0a803324000c209028805bb0440443442079346396142158108e2064b1012c0c4a009ac9204dc02244cf04932133203d102801b0118a05142028c708e18020244ce1 else 0x2551ea8a1409f0a30846253c0764381220242716252930102235480540bc250fa8e04458c44ab1ba24fb70903428039c20c124e594104c48912ac8a624d232821e302303502024c008c104130382544624ad8065bc88330021022497418070757045806924862813f0020c408508247113b4124140211ea8245ac10640161c32aab424490a0708013418121a2434a744841043c064e024214d2192900220c819240a31322b056200cdc823f4135b0004665124a623e010670ca94880930223c6d62cc9904907794023b114e8058818883664239d6702188a01814a4923849d880a43d43081c72372310940a3008c07a0235a8a883266264d7104234b11820c208c40028323360478285f88029054231f02e21c5da022a12c230b4ad0d0015035142822ef1e8525a34252cd9322db9809330018a3812922c09eda4310215b88b8)))) else (if i < 20 then (if i < 16 then (if i < 14 then 0x27eb300a64000216888027d5e14226440261a39827c144088e911817c04127a91c2e94692e93810027930f01100d53145a85277b9b39083a34402cc22769000cc256488a894027562200350a054a602b2740005172e4109016ab272c876002ccb1205050271b12040360912a43042701a1860ca988d74e2426ef881885d2412c801026d9cc821993006c106926c1306a302a44ddb90026afc8820e0d10800863269b2340c15b60840914268a0cae02889180031026780b01082eb0c014422667418c072121182c002650043a58065066c871263d051832028291c02d2623627504a11c358969260e9250a604e838128425f7366144491161441e25e04cd220a48a63480b25c9d0013a49a43e244425b614a30256500050c525a69083406860816100258db27548a2034c8e48257b4326020a688c20c0256922c0898500c30720 else (if i < 15 then 0x2a71084c5a209601c60a2a5e0409282250b166c02a4941a5ac19c30a000a2a38d100901408a486a02a222678164040da0d092a0d28d244e40050a27129fda17008120c04123029eb468242100d71300229d0800a609ff9546c4529ba9f109123e410890229a7913100060a410cdc29978803042020500cb6297e0ba1764a8448a552296b34048218e02841d229557425d10d0202c6442942c600c49e10662008292e165101c8330600c32917a90069802286dea129058881d0146184040728ec28d37a4a0d30872028dc00208d056519004128ce00a008e48a02045028b8cb48bda26005060028a04c21a2e21632058d288c48169a054a224085287681a3c55048904507285cb8d25ec0146c2522284a30102b001119627028370e21443098017142281f4b4e842630a1064e280a850518515272011927f91438d10304e10800 else 0x2d0b34aa80914c21404c2cf701b0860a2e9468012ce0f0421c20d904bc0a2cc73110848df51819952cb920c24800304015122ca1041d3134d143508b2c8c8440b3cb614680802c78259488011c21d6102c5d1eb2a3466b0098b12c486195146212d481402c37400647442120ca022c2248a91a010b3234142c0b4d482c0521a6624c2bf39241b33853042b882be3488010b02060053c2bce105a01688183b8922bbbd00050065f0909212ba690168287640988c42b942880415829a264402b820218f02c21c210092b6c075801b88214ae052b54c192cb072c2c88302b400341a3700056408d2b2c41a204a588cc180a2b15a4044e5064a879412b02108a8b80152234502af0800880bc11451a442add15252008e26005922acb850ba0031083880c2aae0d79e3464fd550082a9a8a144e85504881a02a8524200c57ac20a245)) else (if i < 18 then (if i < 17 then 0x2f9851582a9289a0b8d02f851823c445890214222f70e3430806c23150092f6000482a9890040d822f477408f2b426e08c212f34140876402c9a20032f1dc2c122455da588402f08c61cc00330104af02ef224640981a0db230c2edbe207950642314c882ecad02c800a4410c1052eb3401aaa320442d3c52e9caad037602482540a2e8708604845079534322e772050c841811c00832e6628480034980107682e51c940450d0807022f2e3f46490200a65601112e27792041461222176d2e1600617432080149902dff4b1658a5961401222deb320444c29908a1622dd624459640253b40482dc622478100b20050602daecfa88668e04804132d9a0c886322700019f02d832f103108cd0acc122d73100106e8454410482d5c6646021e941343212d434c0e126c82aa96382d32044620a0a2c420432d1f4150a1130158a406 else 0x322680958a605434c4023212c81351807086091432010a4a8028c81a501031eb91505a08d8e9844031d7c120a7505930320031c2202ec9c002e1a40c31af028cd18c03811c08319197650d4a2678c55a317da81912526240c128316a324a4030028cd0253154202302478605325b313de5204110bc8e2982312870a10f110599410431148490a8b2a0060e8231025330109045028e8030f2809f000058840a1130d981e9d00e2a42d11530c64080762ac029988030b48018490d04804b9430a2628c02448c20c406308c82468193887544093077189806d26128408730637084507442000fa1304a36a3136620037924303520312847118898533024602063106804b021301000a3d0ac04b002742ffda90f1101930504402fe696b03708055007582fd411854804288d01612fc30983620200088c962fb01880202b03ed80a0) else (if i < 19 then 0x34a40a2100e283380cc3348c84580c90391d1365347a4a25048018c2c02a34674200c4842855304b34540510b802a204cb143441a40680846ac18111342b852270602446a12b341c08407c20080d03083409870a0081c00f532033f508a4928c2288711233e0ecd308291010600733cf0ee00210860e404833be0009e8a01a0e060433aab13041304200b58a3398da8100885445220233858204035468b40930337016a491058712014c335561487404b2b662e933451004a1b104604a04332ec0270ad14ca18605331d142b04402a00a09c33063836422985902e6032edb34a038b0018687732d80444c6112893131632c68844019800a7306132b115450309102aa4d1329f0c02a384120558303288a89a34686f0a0401327992804c849009001232658250e8c12438082632500061169097e20318323a258a1c8c22642807 else 0x373620506da222d330243725ca2817a2000401183711509e8001642b80b036fb8379a15240d0051136e5aa30182c84018cf236d26640011a10a4cac036c010444e41b240303036a92e4434189980624b369051543a2963528b04367a6815827008a85e09366521d90404038271a3365180a36c825014b041363f1200a01639244a50362d4026547808c1900236158fd8210413d344053601418885a85432090635eda19c200038408d4d35d68b808474c705489235be23a04249c82d92b835a85514068f410bc09035944c421d0c382a2028357f23190990a1631424356d0c202883c11e8804355ecc014210222004683547112ae462288d109a3534091702430380a710351d5524e84835908930350912c811843a09460c34f602d8941228210e8234e482c10863c010225234ce2ca20ab440a14b0934b80410c2744d86388c))) else (if i < 23 then (if i < 21 then 0x39b118190402a640512a399dc29130081871049a3984241c899329b38960397344028c0908d252403960e000491308e1020f394ec08ca430030481983935c12ee831164e01d0391f21c984646a151881390c3224500058acb60038fbc22880584421188138ea18c00915b100805238d547155912908028a238c141752048244e248138b10c88030222e4010c389e16920748c182c400388bb0b2002588682a10387071080983193cd9b6385b264150c10790d026384b0c0990014a31008a3834997485616200850e38241011800550a200b9381232000326a085842638020000040e0d89265837e81572e15814a9a23137d4240948489f00526437c12104ad0742201c8237ae12c5005a025c24423797b08a58253041c1ac3786084150208a82612937714932188c0c381113375bd6420700748c3301374c02000ae884802446 else (if i < 22 then 0x3c1c0a09d0c4004124543c09c2180991802158253bf70b882100514046ca3be61118014220c60ac83bd511080326cc0024343bc390840a415d1800513bb001442eca4401a3803b9934814318a03a97063b81ce82d084a0077c423b698c018848b246ee073b5b0400111022e80b803b488e889222289600213b380847404115011a103b2463208081fc0a40153b0d30ad5900aad003623afc291c5002614144083aeb08e0b601904801093adb0035208608830a483ac71e232004481439a83ab1135104a491ac25483a9d30186114891fc0023a8a2445d424250960103a76c45b440b08101e803a6343c819133000a8443a4ec58632800c038a8c3a381213242aac0681a63a20695424c542583a283a0e4320c180880072d43a0124800040a120c01639eb8b920d01e024106d39d54d90082191246c4739c31805c0061241c8c1 else 0x3e9b21b443953a8381393e83289a7660045355213e6cc0c0344f0e0c8cb03e56a308ca840c3818a63e45488d04080860c44a3e34414c048a291300843e2700012041b42049803e128993422424205c913dff0828e318898050073dea324450821384a4713dd6041022d1053730323dc146804a94152290783dab0c8a99a6222044e43d9d074801800032009c3d8a5880b1d0260094283d768c2b60080056e0833d5f102506834ac89ac93d4b44322001dd2043453d3652608878859a10183d23a087240012d026c43d0c19680e08d22cc6903cf90929a20570a20c403ce80490c14c4040bc043cd5093078c2011814233cbe4352641ba40720833cad50c083302a4814083c9269cf102898e652a23c7f04458452244603583c69e1808b502a8c408d3c5516aa1142414169103c4110a06463d040ac303c2d86242118b880b910)) else (if i < 25 then (if i < 24 then 0x411b212c8504b418430341074264582ca832070040f828900c007341020440de578019f2c53002d940cd28b3a8620044110040b8818296408498742a40a4132148a8100d1439408d926a8490a88e4950407b3009c09084682432406285c7a03331911246404cc98c02083274a708403c3020b80062498030402984b204000e58482d401ac81108030c248c00400ba00209020138c1843ffa042210d000c3c1543fe44810c125131634633fd3c5018410021c48433fbba49e8af0008bd4203fa32a307134484dc88a3f8c826546864c9416033f782448680b0826a8153f606402412d3a98c13a3f4bc418001d00636e073f36830934838258058a3f221481b1421885124c3f0e30310422689a78013efe89160c60013010413eed2008c10b500f20603edc126108908b8050063ec86500082e2a045c623eb50280b3b0540c8205 else 0x439982882160041e0d4843843012e39014208d1c4370b30bf40800098031435e019600890e60a112434bd410800165840ac6433358e803a032a8517843230ac2010000c632254313464528020422241842fe090602d33089162c42eb0a3012484705483842d2c8222a8cd839159142be7206011ca82221a242ad00030c348819d10442962e4e052240a75608428344c0880a81488b13427020a44b65448002a442609a02000027024907424f3255084050440522423c253c0208910a03c142274a8ad4b00818027442106741f90570c2280041fd90102ba100284e4a41eb34a470a11c84000141d8a11083300815892a41c1b1060e80da04266a41aa51360a58608dc28241907246ce050428336e417e8152048101e018e44168104900d36340a3d44155143832804c208bc041410208554a218e3016412fc054324302802119) else (if i < 26 then 0x460ee2110c428041b81a45fc2360c2514083100645ec440c00c100b9021645d7ce818025fb00240845c484889648e108604445acac32631032490635459a0c18c02223481918458601f2548e0014182a4570c40caa0704b07121455d102044602da381384547e649180192512a60453548cc0402942c43104521818492a30e40426145112c618228a002801444fd1934100157a0830344e741680b1e01aa58c044d60287057c2310800044c4c4019118a242548044accca4072920580e174499089478c02640432444813c22e00620da1d2a4473008520431064090844660308088038200a2244512429599012488370443b015d940ce1551840442688809e18a40a40c74415480bd2120441180143ff2c4ac0084344693543e921503a2a432512d043d40212039d1d1aa03043c10c0411581c72016443abe00e44894b005a8a else 0x48580000d8602000800548439858014284d3102e482a88870065c9992b70481440400e86d48d1b904808406012500860044047f00f0a9880e2a25a4947db5e3402229202424d47c711156151284c806847b511581130045d018847a29022044998500783478e04760217c1a58004477d40004d581402906a4766a38a05906241308f4757000800f91204a88447410001a1b05c4d8f884733808b704804100014471e8b23508d10b084504709821e62089433411246f820a0450100cb066246e821900921180034a246d21c8506295266640246b97c973244244b40c446a5a612033c41904c8046938282140641c81921467f94082306390030e5466f344012a40148a110465f8096e00040430a03464a0d552818421605544637c11010416ae0140d46222098412e8a0da412)))))


private def pop (x : ℕ) :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c * 0x0101010101010101) >>> 56) % 256

private def raw (j : ℕ) : ℕ :=
  let entry := ((packet (j/2048)) >>> (80*((j%2048)/64))) % (2^80)
  (entry >>> 64) + pop (entry % (2^(j%64)))

private def small (n : ℕ) : ℕ := if 5≤n then 3 else if 3≤n then 2 else if 2≤n then 1 else 0

def fast (n : ℕ) : ℕ := raw (index n) + small n

private def quick (n : ℕ) : Bool := if n≤454 then decide n.Prime else n.gcd 47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810 == 1

private theorem quick_ok {n : ℕ} (hn : n ≤ 206781) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · simp
  · have hm : 47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810 ∣ Nat.factorial 454 := by decide +kernel
    have allsmall : ∀ p : Fin 455, p.val.Prime → p.val ∣ 47952908052796135760256600170199578387740533448517890811411728517171138658867337095151452769077564443190074989606933241597341551376625294861617115261811011811910212652094403655944384810 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 454 := by
        by_contra! hi
        have hb := Nat.mul_le_mul hi hi
        rw [pow_two] at hsq
        omega
      have hd := Nat.dvd_gcd (Nat.minFac_dvd n) (allsmall ⟨n.minFac,by omega⟩ hpr)
      rw [eq] at hd
      exact hpr.not_dvd_one hd
    · intro hp
      exact Nat.Coprime.of_dvd_right hm (hp.coprime_factorial_of_lt (by omega))

private def step (j : ℕ) : Bool := raw (j+1) == raw j + (if quick (number j) then 1 else 0)
private def valid (lo len : ℕ) : Prop := (List.range' lo len).all step = true
private theorem glue {lo a b : ℕ} (left : valid lo a) (right : valid (lo+a) b) : valid lo (a+b) := by
  unfold valid at *
  rw [←List.range'_append_1,List.all_append,left,right]
  rfl

set_option maxRecDepth 6000 in
private theorem leaf0 : valid 0 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf430 : valid 430 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf861 : valid 861 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf1292 : valid 1292 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf1723 : valid 1723 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf2154 : valid 2154 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf2585 : valid 2585 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf3016 : valid 3016 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf3447 : valid 3447 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf3877 : valid 3877 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf4308 : valid 4308 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf4739 : valid 4739 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf5170 : valid 5170 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf5601 : valid 5601 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf6032 : valid 6032 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf6463 : valid 6463 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf6894 : valid 6894 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf7324 : valid 7324 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf7755 : valid 7755 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf8186 : valid 8186 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf8617 : valid 8617 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf9048 : valid 9048 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf9479 : valid 9479 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf9910 : valid 9910 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf10341 : valid 10341 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf10771 : valid 10771 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf11202 : valid 11202 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf11633 : valid 11633 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf12064 : valid 12064 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf12495 : valid 12495 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf12926 : valid 12926 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf13357 : valid 13357 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf13788 : valid 13788 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf14218 : valid 14218 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf14649 : valid 14649 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf15080 : valid 15080 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf15511 : valid 15511 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf15942 : valid 15942 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf16373 : valid 16373 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf16804 : valid 16804 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf17235 : valid 17235 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf17665 : valid 17665 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf18096 : valid 18096 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf18527 : valid 18527 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf18958 : valid 18958 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf19389 : valid 19389 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf19820 : valid 19820 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf20251 : valid 20251 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf20682 : valid 20682 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf21112 : valid 21112 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf21543 : valid 21543 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf21974 : valid 21974 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf22405 : valid 22405 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf22836 : valid 22836 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf23267 : valid 23267 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf23698 : valid 23698 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf24129 : valid 24129 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf24559 : valid 24559 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf24990 : valid 24990 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf25421 : valid 25421 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf25852 : valid 25852 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf26283 : valid 26283 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf26714 : valid 26714 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf27145 : valid 27145 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf27576 : valid 27576 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf28006 : valid 28006 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf28437 : valid 28437 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf28868 : valid 28868 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf29299 : valid 29299 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf29730 : valid 29730 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf30161 : valid 30161 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf30592 : valid 30592 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf31023 : valid 31023 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf31453 : valid 31453 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf31884 : valid 31884 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf32315 : valid 32315 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf32746 : valid 32746 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf33177 : valid 33177 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf33608 : valid 33608 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf34039 : valid 34039 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf34470 : valid 34470 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf34900 : valid 34900 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf35331 : valid 35331 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf35762 : valid 35762 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf36193 : valid 36193 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf36624 : valid 36624 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf37055 : valid 37055 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf37486 : valid 37486 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf37917 : valid 37917 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf38347 : valid 38347 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf38778 : valid 38778 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf39209 : valid 39209 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf39640 : valid 39640 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf40071 : valid 40071 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf40502 : valid 40502 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf40933 : valid 40933 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf41364 : valid 41364 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf41794 : valid 41794 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf42225 : valid 42225 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf42656 : valid 42656 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf43087 : valid 43087 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf43518 : valid 43518 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf43949 : valid 43949 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf44380 : valid 44380 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf44811 : valid 44811 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf45241 : valid 45241 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf45672 : valid 45672 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf46103 : valid 46103 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf46534 : valid 46534 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf46965 : valid 46965 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf47396 : valid 47396 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf47827 : valid 47827 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf48258 : valid 48258 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf48688 : valid 48688 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf49119 : valid 49119 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf49550 : valid 49550 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf49981 : valid 49981 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf50412 : valid 50412 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf50843 : valid 50843 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf51274 : valid 51274 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf51705 : valid 51705 430 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf52135 : valid 52135 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf52566 : valid 52566 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf52997 : valid 52997 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf53428 : valid 53428 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf53859 : valid 53859 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf54290 : valid 54290 431 := by unfold valid; decide +kernel

set_option maxRecDepth 6000 in
private theorem leaf54721 : valid 54721 431 := by unfold valid; decide +kernel


set_option maxRecDepth 20000 in
private theorem allrows : valid 0 55152 := (glue (lo:=0) (a:=27576) (b:=27576) (glue (lo:=0) (a:=13788) (b:=13788) (glue (lo:=0) (a:=6894) (b:=6894) (glue (lo:=0) (a:=3447) (b:=3447) (glue (lo:=0) (a:=1723) (b:=1724) (glue (lo:=0) (a:=861) (b:=862) (glue (lo:=0) (a:=430) (b:=431) leaf0 leaf430) (glue (lo:=861) (a:=431) (b:=431) leaf861 leaf1292)) (glue (lo:=1723) (a:=862) (b:=862) (glue (lo:=1723) (a:=431) (b:=431) leaf1723 leaf2154) (glue (lo:=2585) (a:=431) (b:=431) leaf2585 leaf3016))) (glue (lo:=3447) (a:=1723) (b:=1724) (glue (lo:=3447) (a:=861) (b:=862) (glue (lo:=3447) (a:=430) (b:=431) leaf3447 leaf3877) (glue (lo:=4308) (a:=431) (b:=431) leaf4308 leaf4739)) (glue (lo:=5170) (a:=862) (b:=862) (glue (lo:=5170) (a:=431) (b:=431) leaf5170 leaf5601) (glue (lo:=6032) (a:=431) (b:=431) leaf6032 leaf6463)))) (glue (lo:=6894) (a:=3447) (b:=3447) (glue (lo:=6894) (a:=1723) (b:=1724) (glue (lo:=6894) (a:=861) (b:=862) (glue (lo:=6894) (a:=430) (b:=431) leaf6894 leaf7324) (glue (lo:=7755) (a:=431) (b:=431) leaf7755 leaf8186)) (glue (lo:=8617) (a:=862) (b:=862) (glue (lo:=8617) (a:=431) (b:=431) leaf8617 leaf9048) (glue (lo:=9479) (a:=431) (b:=431) leaf9479 leaf9910))) (glue (lo:=10341) (a:=1723) (b:=1724) (glue (lo:=10341) (a:=861) (b:=862) (glue (lo:=10341) (a:=430) (b:=431) leaf10341 leaf10771) (glue (lo:=11202) (a:=431) (b:=431) leaf11202 leaf11633)) (glue (lo:=12064) (a:=862) (b:=862) (glue (lo:=12064) (a:=431) (b:=431) leaf12064 leaf12495) (glue (lo:=12926) (a:=431) (b:=431) leaf12926 leaf13357))))) (glue (lo:=13788) (a:=6894) (b:=6894) (glue (lo:=13788) (a:=3447) (b:=3447) (glue (lo:=13788) (a:=1723) (b:=1724) (glue (lo:=13788) (a:=861) (b:=862) (glue (lo:=13788) (a:=430) (b:=431) leaf13788 leaf14218) (glue (lo:=14649) (a:=431) (b:=431) leaf14649 leaf15080)) (glue (lo:=15511) (a:=862) (b:=862) (glue (lo:=15511) (a:=431) (b:=431) leaf15511 leaf15942) (glue (lo:=16373) (a:=431) (b:=431) leaf16373 leaf16804))) (glue (lo:=17235) (a:=1723) (b:=1724) (glue (lo:=17235) (a:=861) (b:=862) (glue (lo:=17235) (a:=430) (b:=431) leaf17235 leaf17665) (glue (lo:=18096) (a:=431) (b:=431) leaf18096 leaf18527)) (glue (lo:=18958) (a:=862) (b:=862) (glue (lo:=18958) (a:=431) (b:=431) leaf18958 leaf19389) (glue (lo:=19820) (a:=431) (b:=431) leaf19820 leaf20251)))) (glue (lo:=20682) (a:=3447) (b:=3447) (glue (lo:=20682) (a:=1723) (b:=1724) (glue (lo:=20682) (a:=861) (b:=862) (glue (lo:=20682) (a:=430) (b:=431) leaf20682 leaf21112) (glue (lo:=21543) (a:=431) (b:=431) leaf21543 leaf21974)) (glue (lo:=22405) (a:=862) (b:=862) (glue (lo:=22405) (a:=431) (b:=431) leaf22405 leaf22836) (glue (lo:=23267) (a:=431) (b:=431) leaf23267 leaf23698))) (glue (lo:=24129) (a:=1723) (b:=1724) (glue (lo:=24129) (a:=861) (b:=862) (glue (lo:=24129) (a:=430) (b:=431) leaf24129 leaf24559) (glue (lo:=24990) (a:=431) (b:=431) leaf24990 leaf25421)) (glue (lo:=25852) (a:=862) (b:=862) (glue (lo:=25852) (a:=431) (b:=431) leaf25852 leaf26283) (glue (lo:=26714) (a:=431) (b:=431) leaf26714 leaf27145)))))) (glue (lo:=27576) (a:=13788) (b:=13788) (glue (lo:=27576) (a:=6894) (b:=6894) (glue (lo:=27576) (a:=3447) (b:=3447) (glue (lo:=27576) (a:=1723) (b:=1724) (glue (lo:=27576) (a:=861) (b:=862) (glue (lo:=27576) (a:=430) (b:=431) leaf27576 leaf28006) (glue (lo:=28437) (a:=431) (b:=431) leaf28437 leaf28868)) (glue (lo:=29299) (a:=862) (b:=862) (glue (lo:=29299) (a:=431) (b:=431) leaf29299 leaf29730) (glue (lo:=30161) (a:=431) (b:=431) leaf30161 leaf30592))) (glue (lo:=31023) (a:=1723) (b:=1724) (glue (lo:=31023) (a:=861) (b:=862) (glue (lo:=31023) (a:=430) (b:=431) leaf31023 leaf31453) (glue (lo:=31884) (a:=431) (b:=431) leaf31884 leaf32315)) (glue (lo:=32746) (a:=862) (b:=862) (glue (lo:=32746) (a:=431) (b:=431) leaf32746 leaf33177) (glue (lo:=33608) (a:=431) (b:=431) leaf33608 leaf34039)))) (glue (lo:=34470) (a:=3447) (b:=3447) (glue (lo:=34470) (a:=1723) (b:=1724) (glue (lo:=34470) (a:=861) (b:=862) (glue (lo:=34470) (a:=430) (b:=431) leaf34470 leaf34900) (glue (lo:=35331) (a:=431) (b:=431) leaf35331 leaf35762)) (glue (lo:=36193) (a:=862) (b:=862) (glue (lo:=36193) (a:=431) (b:=431) leaf36193 leaf36624) (glue (lo:=37055) (a:=431) (b:=431) leaf37055 leaf37486))) (glue (lo:=37917) (a:=1723) (b:=1724) (glue (lo:=37917) (a:=861) (b:=862) (glue (lo:=37917) (a:=430) (b:=431) leaf37917 leaf38347) (glue (lo:=38778) (a:=431) (b:=431) leaf38778 leaf39209)) (glue (lo:=39640) (a:=862) (b:=862) (glue (lo:=39640) (a:=431) (b:=431) leaf39640 leaf40071) (glue (lo:=40502) (a:=431) (b:=431) leaf40502 leaf40933))))) (glue (lo:=41364) (a:=6894) (b:=6894) (glue (lo:=41364) (a:=3447) (b:=3447) (glue (lo:=41364) (a:=1723) (b:=1724) (glue (lo:=41364) (a:=861) (b:=862) (glue (lo:=41364) (a:=430) (b:=431) leaf41364 leaf41794) (glue (lo:=42225) (a:=431) (b:=431) leaf42225 leaf42656)) (glue (lo:=43087) (a:=862) (b:=862) (glue (lo:=43087) (a:=431) (b:=431) leaf43087 leaf43518) (glue (lo:=43949) (a:=431) (b:=431) leaf43949 leaf44380))) (glue (lo:=44811) (a:=1723) (b:=1724) (glue (lo:=44811) (a:=861) (b:=862) (glue (lo:=44811) (a:=430) (b:=431) leaf44811 leaf45241) (glue (lo:=45672) (a:=431) (b:=431) leaf45672 leaf46103)) (glue (lo:=46534) (a:=862) (b:=862) (glue (lo:=46534) (a:=431) (b:=431) leaf46534 leaf46965) (glue (lo:=47396) (a:=431) (b:=431) leaf47396 leaf47827)))) (glue (lo:=48258) (a:=3447) (b:=3447) (glue (lo:=48258) (a:=1723) (b:=1724) (glue (lo:=48258) (a:=861) (b:=862) (glue (lo:=48258) (a:=430) (b:=431) leaf48258 leaf48688) (glue (lo:=49119) (a:=431) (b:=431) leaf49119 leaf49550)) (glue (lo:=49981) (a:=862) (b:=862) (glue (lo:=49981) (a:=431) (b:=431) leaf49981 leaf50412) (glue (lo:=50843) (a:=431) (b:=431) leaf50843 leaf51274))) (glue (lo:=51705) (a:=1723) (b:=1724) (glue (lo:=51705) (a:=861) (b:=862) (glue (lo:=51705) (a:=430) (b:=431) leaf51705 leaf52135) (glue (lo:=52566) (a:=431) (b:=431) leaf52566 leaf52997)) (glue (lo:=53428) (a:=862) (b:=862) (glue (lo:=53428) (a:=431) (b:=431) leaf53428 leaf53859) (glue (lo:=54290) (a:=431) (b:=431) leaf54290 leaf54721)))))))

theorem fast_correct (n : ℕ) (bound : n ≤ 206781) : fast n = Nat.primeCounting n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases smallN : n < 6
    · have tests : ∀ i : Fin 7, fast i.val = Nat.primeCounting i.val := by decide +kernel
      exact tests ⟨n+1,by omega⟩
    · have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤206781 by omega)
        have ok : (List.range 55152).all step=true := by rw [List.range_eq_range']; exact allrows
        have h := beq_iff_eq.mp (List.all_eq_true.mp ok (index n) (List.mem_range.mpr ix))
        change raw (index n+1) = raw (index n) + (if quick (number (index n)) then 1 else 0) at h
        rw [whose] at h
        simp only [fast,e,h,unchanged]
        by_cases hp : (n+1).Prime
        · simp [hp,(quick_ok bound).mpr hp,Nat.add_right_comm]
        · simp [hp,mt (quick_ok bound).mp hp]
end WheelTableA94


/- Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace CheckpointA10425Slim

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



private def light (n : ℕ) : Bool :=
  if n≤46 then decide n.Prime else n.gcd 5502622159812088949850305428800254892961651752960000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤2185) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 46 = 5502622159812088949850305428800254892961651752960000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 46 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤2185 then light n else n.gcd 13786117807745248330297337381285929061651640023451164725055304709664843445926585043282813794781729864835926839784029128350552469509838656771615789041601967434081932401290691593659791420286585844556689823031316386998681933670143607680231320307882231022932389306084258518856832957832613223705542791299021119431533290162726590222867968622117172359908148752641110965685579673773663276246994829705943295092061181740736951486944352951916887371304090654568502636492119638228965093366129229283284991837780042622921191261678787528129582327293323090179843978047734423602898401755600127524554972112263411611349701873802477010407053968400936356066458574794029868841587949072254554381372481797558485927763682733521203877821779565176389893722600563009673230195503137825133555836454284888201311814469338994903526981914940168091947728827182678137649261492993077179996851031630572170217428007566862591462031152733786257410549335720282125110 == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd 13786117807745248330297337381285929061651640023451164725055304709664843445926585043282813794781729864835926839784029128350552469509838656771615789041601967434081932401290691593659791420286585844556689823031316386998681933670143607680231320307882231022932389306084258518856832957832613223705542791299021119431533290162726590222867968622117172359908148752641110965685579673773663276246994829705943295092061181740736951486944352951916887371304090654568502636492119638228965093366129229283284991837780042622921191261678787528129582327293323090179843978047734423602898401755600127524554972112263411611349701873802477010407053968400936356066458574794029868841587949072254554381372481797558485927763682733521203877821779565176389893722600563009673230195503137825133555836454284888201311814469338994903526981914940168091947728827182678137649261492993077179996851031630572170217428007566862591462031152733786257410549335720282125110 == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl

private theorem sm0 : smallValid 0 17 := by unfold smallValid; decide +kernel

private theorem sm17 : smallValid 17 17 := by unfold smallValid; decide +kernel

private theorem sm34 : smallValid 34 17 := by unfold smallValid; decide +kernel

private theorem sm51 : smallValid 51 17 := by unfold smallValid; decide +kernel

private theorem sm68 : smallValid 68 17 := by unfold smallValid; decide +kernel

private theorem sm85 : smallValid 85 17 := by unfold smallValid; decide +kernel

private theorem sm102 : smallValid 102 17 := by unfold smallValid; decide +kernel

private theorem sm119 : smallValid 119 17 := by unfold smallValid; decide +kernel

private theorem sm136 : smallValid 136 17 := by unfold smallValid; decide +kernel

private theorem sm153 : smallValid 153 17 := by unfold smallValid; decide +kernel

private theorem sm170 : smallValid 170 17 := by unfold smallValid; decide +kernel

private theorem sm187 : smallValid 187 17 := by unfold smallValid; decide +kernel

private theorem sm204 : smallValid 204 17 := by unfold smallValid; decide +kernel

private theorem sm221 : smallValid 221 17 := by unfold smallValid; decide +kernel

private theorem sm238 : smallValid 238 17 := by unfold smallValid; decide +kernel

private theorem sm255 : smallValid 255 18 := by unfold smallValid; decide +kernel

private theorem sm273 : smallValid 273 17 := by unfold smallValid; decide +kernel

private theorem sm290 : smallValid 290 17 := by unfold smallValid; decide +kernel

private theorem sm307 : smallValid 307 17 := by unfold smallValid; decide +kernel

private theorem sm324 : smallValid 324 17 := by unfold smallValid; decide +kernel

private theorem sm341 : smallValid 341 17 := by unfold smallValid; decide +kernel

private theorem sm358 : smallValid 358 17 := by unfold smallValid; decide +kernel

private theorem sm375 : smallValid 375 17 := by unfold smallValid; decide +kernel

private theorem sm392 : smallValid 392 17 := by unfold smallValid; decide +kernel

private theorem sm409 : smallValid 409 17 := by unfold smallValid; decide +kernel

private theorem sm426 : smallValid 426 17 := by unfold smallValid; decide +kernel

private theorem sm443 : smallValid 443 17 := by unfold smallValid; decide +kernel

private theorem sm460 : smallValid 460 17 := by unfold smallValid; decide +kernel

private theorem sm477 : smallValid 477 17 := by unfold smallValid; decide +kernel

private theorem sm494 : smallValid 494 17 := by unfold smallValid; decide +kernel

private theorem sm511 : smallValid 511 17 := by unfold smallValid; decide +kernel

private theorem sm528 : smallValid 528 18 := by unfold smallValid; decide +kernel

private theorem sm546 : smallValid 546 17 := by unfold smallValid; decide +kernel

private theorem sm563 : smallValid 563 17 := by unfold smallValid; decide +kernel

private theorem sm580 : smallValid 580 17 := by unfold smallValid; decide +kernel

private theorem sm597 : smallValid 597 17 := by unfold smallValid; decide +kernel

private theorem sm614 : smallValid 614 17 := by unfold smallValid; decide +kernel

private theorem sm631 : smallValid 631 17 := by unfold smallValid; decide +kernel

private theorem sm648 : smallValid 648 17 := by unfold smallValid; decide +kernel

private theorem sm665 : smallValid 665 17 := by unfold smallValid; decide +kernel

private theorem sm682 : smallValid 682 17 := by unfold smallValid; decide +kernel

private theorem sm699 : smallValid 699 17 := by unfold smallValid; decide +kernel

private theorem sm716 : smallValid 716 17 := by unfold smallValid; decide +kernel

private theorem sm733 : smallValid 733 17 := by unfold smallValid; decide +kernel

private theorem sm750 : smallValid 750 17 := by unfold smallValid; decide +kernel

private theorem sm767 : smallValid 767 17 := by unfold smallValid; decide +kernel

private theorem sm784 : smallValid 784 17 := by unfold smallValid; decide +kernel

private theorem sm801 : smallValid 801 18 := by unfold smallValid; decide +kernel

private theorem sm819 : smallValid 819 17 := by unfold smallValid; decide +kernel

private theorem sm836 : smallValid 836 17 := by unfold smallValid; decide +kernel

private theorem sm853 : smallValid 853 17 := by unfold smallValid; decide +kernel

private theorem sm870 : smallValid 870 17 := by unfold smallValid; decide +kernel

private theorem sm887 : smallValid 887 17 := by unfold smallValid; decide +kernel

private theorem sm904 : smallValid 904 17 := by unfold smallValid; decide +kernel

private theorem sm921 : smallValid 921 17 := by unfold smallValid; decide +kernel

private theorem sm938 : smallValid 938 18 := by unfold smallValid; decide +kernel

private theorem sm956 : smallValid 956 17 := by unfold smallValid; decide +kernel

private theorem sm973 : smallValid 973 17 := by unfold smallValid; decide +kernel

private theorem sm990 : smallValid 990 17 := by unfold smallValid; decide +kernel

private theorem sm1007 : smallValid 1007 17 := by unfold smallValid; decide +kernel

private theorem sm1024 : smallValid 1024 17 := by unfold smallValid; decide +kernel

private theorem sm1041 : smallValid 1041 17 := by unfold smallValid; decide +kernel

private theorem sm1058 : smallValid 1058 17 := by unfold smallValid; decide +kernel

private theorem sm1075 : smallValid 1075 18 := by unfold smallValid; decide +kernel

private theorem sm1093 : smallValid 1093 17 := by unfold smallValid; decide +kernel

private theorem sm1110 : smallValid 1110 17 := by unfold smallValid; decide +kernel

private theorem sm1127 : smallValid 1127 17 := by unfold smallValid; decide +kernel

private theorem sm1144 : smallValid 1144 17 := by unfold smallValid; decide +kernel

private theorem sm1161 : smallValid 1161 17 := by unfold smallValid; decide +kernel

private theorem sm1178 : smallValid 1178 17 := by unfold smallValid; decide +kernel

private theorem sm1195 : smallValid 1195 17 := by unfold smallValid; decide +kernel

private theorem sm1212 : smallValid 1212 17 := by unfold smallValid; decide +kernel

private theorem sm1229 : smallValid 1229 17 := by unfold smallValid; decide +kernel

private theorem sm1246 : smallValid 1246 17 := by unfold smallValid; decide +kernel

private theorem sm1263 : smallValid 1263 17 := by unfold smallValid; decide +kernel

private theorem sm1280 : smallValid 1280 17 := by unfold smallValid; decide +kernel

private theorem sm1297 : smallValid 1297 17 := by unfold smallValid; decide +kernel

private theorem sm1314 : smallValid 1314 17 := by unfold smallValid; decide +kernel

private theorem sm1331 : smallValid 1331 17 := by unfold smallValid; decide +kernel

private theorem sm1348 : smallValid 1348 18 := by unfold smallValid; decide +kernel

private theorem sm1366 : smallValid 1366 17 := by unfold smallValid; decide +kernel

private theorem sm1383 : smallValid 1383 17 := by unfold smallValid; decide +kernel

private theorem sm1400 : smallValid 1400 17 := by unfold smallValid; decide +kernel

private theorem sm1417 : smallValid 1417 17 := by unfold smallValid; decide +kernel

private theorem sm1434 : smallValid 1434 17 := by unfold smallValid; decide +kernel

private theorem sm1451 : smallValid 1451 17 := by unfold smallValid; decide +kernel

private theorem sm1468 : smallValid 1468 17 := by unfold smallValid; decide +kernel

private theorem sm1485 : smallValid 1485 17 := by unfold smallValid; decide +kernel

private theorem sm1502 : smallValid 1502 17 := by unfold smallValid; decide +kernel

private theorem sm1519 : smallValid 1519 17 := by unfold smallValid; decide +kernel

private theorem sm1536 : smallValid 1536 17 := by unfold smallValid; decide +kernel

private theorem sm1553 : smallValid 1553 17 := by unfold smallValid; decide +kernel

private theorem sm1570 : smallValid 1570 17 := by unfold smallValid; decide +kernel

private theorem sm1587 : smallValid 1587 17 := by unfold smallValid; decide +kernel

private theorem sm1604 : smallValid 1604 17 := by unfold smallValid; decide +kernel

private theorem sm1621 : smallValid 1621 18 := by unfold smallValid; decide +kernel

private theorem sm1639 : smallValid 1639 17 := by unfold smallValid; decide +kernel

private theorem sm1656 : smallValid 1656 17 := by unfold smallValid; decide +kernel

private theorem sm1673 : smallValid 1673 17 := by unfold smallValid; decide +kernel

private theorem sm1690 : smallValid 1690 17 := by unfold smallValid; decide +kernel

private theorem sm1707 : smallValid 1707 17 := by unfold smallValid; decide +kernel

private theorem sm1724 : smallValid 1724 17 := by unfold smallValid; decide +kernel

private theorem sm1741 : smallValid 1741 17 := by unfold smallValid; decide +kernel

private theorem sm1758 : smallValid 1758 17 := by unfold smallValid; decide +kernel

private theorem sm1775 : smallValid 1775 17 := by unfold smallValid; decide +kernel

private theorem sm1792 : smallValid 1792 17 := by unfold smallValid; decide +kernel

private theorem sm1809 : smallValid 1809 17 := by unfold smallValid; decide +kernel

private theorem sm1826 : smallValid 1826 17 := by unfold smallValid; decide +kernel

private theorem sm1843 : smallValid 1843 17 := by unfold smallValid; decide +kernel

private theorem sm1860 : smallValid 1860 17 := by unfold smallValid; decide +kernel

private theorem sm1877 : smallValid 1877 17 := by unfold smallValid; decide +kernel

private theorem sm1894 : smallValid 1894 18 := by unfold smallValid; decide +kernel

private theorem sm1912 : smallValid 1912 17 := by unfold smallValid; decide +kernel

private theorem sm1929 : smallValid 1929 17 := by unfold smallValid; decide +kernel

private theorem sm1946 : smallValid 1946 17 := by unfold smallValid; decide +kernel

private theorem sm1963 : smallValid 1963 17 := by unfold smallValid; decide +kernel

private theorem sm1980 : smallValid 1980 17 := by unfold smallValid; decide +kernel

private theorem sm1997 : smallValid 1997 17 := by unfold smallValid; decide +kernel

private theorem sm2014 : smallValid 2014 17 := by unfold smallValid; decide +kernel

private theorem sm2031 : smallValid 2031 18 := by unfold smallValid; decide +kernel

private theorem sm2049 : smallValid 2049 17 := by unfold smallValid; decide +kernel

private theorem sm2066 : smallValid 2066 17 := by unfold smallValid; decide +kernel

private theorem sm2083 : smallValid 2083 17 := by unfold smallValid; decide +kernel

private theorem sm2100 : smallValid 2100 17 := by unfold smallValid; decide +kernel

private theorem sm2117 : smallValid 2117 17 := by unfold smallValid; decide +kernel

private theorem sm2134 : smallValid 2134 17 := by unfold smallValid; decide +kernel

private theorem sm2151 : smallValid 2151 17 := by unfold smallValid; decide +kernel

private theorem sm2168 : smallValid 2168 18 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤2185) (hp : p.Prime) : p ∣ 13786117807745248330297337381285929061651640023451164725055304709664843445926585043282813794781729864835926839784029128350552469509838656771615789041601967434081932401290691593659791420286585844556689823031316386998681933670143607680231320307882231022932389306084258518856832957832613223705542791299021119431533290162726590222867968622117172359908148752641110965685579673773663276246994829705943295092061181740736951486944352951916887371304090654568502636492119638228965093366129229283284991837780042622921191261678787528129582327293323090179843978047734423602898401755600127524554972112263411611349701873802477010407053968400936356066458574794029868841587949072254554381372481797558485927763682733521203877821779565176389893722600563009673230195503137825133555836454284888201311814469338994903526981914940168091947728827182678137649261492993077179996851031630572170217428007566862591462031152733786257410549335720282125110 := by
  have all : smallValid 0 2186 := (joinSmall (lo:=0) (a:=1093) (b:=1093) (joinSmall (lo:=0) (a:=546) (b:=547) (joinSmall (lo:=0) (a:=273) (b:=273) (joinSmall (lo:=0) (a:=136) (b:=137) (joinSmall (lo:=0) (a:=68) (b:=68) (joinSmall (lo:=0) (a:=34) (b:=34) (joinSmall (lo:=0) (a:=17) (b:=17) sm0 sm17) (joinSmall (lo:=34) (a:=17) (b:=17) sm34 sm51)) (joinSmall (lo:=68) (a:=34) (b:=34) (joinSmall (lo:=68) (a:=17) (b:=17) sm68 sm85) (joinSmall (lo:=102) (a:=17) (b:=17) sm102 sm119))) (joinSmall (lo:=136) (a:=68) (b:=69) (joinSmall (lo:=136) (a:=34) (b:=34) (joinSmall (lo:=136) (a:=17) (b:=17) sm136 sm153) (joinSmall (lo:=170) (a:=17) (b:=17) sm170 sm187)) (joinSmall (lo:=204) (a:=34) (b:=35) (joinSmall (lo:=204) (a:=17) (b:=17) sm204 sm221) (joinSmall (lo:=238) (a:=17) (b:=18) sm238 sm255)))) (joinSmall (lo:=273) (a:=136) (b:=137) (joinSmall (lo:=273) (a:=68) (b:=68) (joinSmall (lo:=273) (a:=34) (b:=34) (joinSmall (lo:=273) (a:=17) (b:=17) sm273 sm290) (joinSmall (lo:=307) (a:=17) (b:=17) sm307 sm324)) (joinSmall (lo:=341) (a:=34) (b:=34) (joinSmall (lo:=341) (a:=17) (b:=17) sm341 sm358) (joinSmall (lo:=375) (a:=17) (b:=17) sm375 sm392))) (joinSmall (lo:=409) (a:=68) (b:=69) (joinSmall (lo:=409) (a:=34) (b:=34) (joinSmall (lo:=409) (a:=17) (b:=17) sm409 sm426) (joinSmall (lo:=443) (a:=17) (b:=17) sm443 sm460)) (joinSmall (lo:=477) (a:=34) (b:=35) (joinSmall (lo:=477) (a:=17) (b:=17) sm477 sm494) (joinSmall (lo:=511) (a:=17) (b:=18) sm511 sm528))))) (joinSmall (lo:=546) (a:=273) (b:=274) (joinSmall (lo:=546) (a:=136) (b:=137) (joinSmall (lo:=546) (a:=68) (b:=68) (joinSmall (lo:=546) (a:=34) (b:=34) (joinSmall (lo:=546) (a:=17) (b:=17) sm546 sm563) (joinSmall (lo:=580) (a:=17) (b:=17) sm580 sm597)) (joinSmall (lo:=614) (a:=34) (b:=34) (joinSmall (lo:=614) (a:=17) (b:=17) sm614 sm631) (joinSmall (lo:=648) (a:=17) (b:=17) sm648 sm665))) (joinSmall (lo:=682) (a:=68) (b:=69) (joinSmall (lo:=682) (a:=34) (b:=34) (joinSmall (lo:=682) (a:=17) (b:=17) sm682 sm699) (joinSmall (lo:=716) (a:=17) (b:=17) sm716 sm733)) (joinSmall (lo:=750) (a:=34) (b:=35) (joinSmall (lo:=750) (a:=17) (b:=17) sm750 sm767) (joinSmall (lo:=784) (a:=17) (b:=18) sm784 sm801)))) (joinSmall (lo:=819) (a:=137) (b:=137) (joinSmall (lo:=819) (a:=68) (b:=69) (joinSmall (lo:=819) (a:=34) (b:=34) (joinSmall (lo:=819) (a:=17) (b:=17) sm819 sm836) (joinSmall (lo:=853) (a:=17) (b:=17) sm853 sm870)) (joinSmall (lo:=887) (a:=34) (b:=35) (joinSmall (lo:=887) (a:=17) (b:=17) sm887 sm904) (joinSmall (lo:=921) (a:=17) (b:=18) sm921 sm938))) (joinSmall (lo:=956) (a:=68) (b:=69) (joinSmall (lo:=956) (a:=34) (b:=34) (joinSmall (lo:=956) (a:=17) (b:=17) sm956 sm973) (joinSmall (lo:=990) (a:=17) (b:=17) sm990 sm1007)) (joinSmall (lo:=1024) (a:=34) (b:=35) (joinSmall (lo:=1024) (a:=17) (b:=17) sm1024 sm1041) (joinSmall (lo:=1058) (a:=17) (b:=18) sm1058 sm1075)))))) (joinSmall (lo:=1093) (a:=546) (b:=547) (joinSmall (lo:=1093) (a:=273) (b:=273) (joinSmall (lo:=1093) (a:=136) (b:=137) (joinSmall (lo:=1093) (a:=68) (b:=68) (joinSmall (lo:=1093) (a:=34) (b:=34) (joinSmall (lo:=1093) (a:=17) (b:=17) sm1093 sm1110) (joinSmall (lo:=1127) (a:=17) (b:=17) sm1127 sm1144)) (joinSmall (lo:=1161) (a:=34) (b:=34) (joinSmall (lo:=1161) (a:=17) (b:=17) sm1161 sm1178) (joinSmall (lo:=1195) (a:=17) (b:=17) sm1195 sm1212))) (joinSmall (lo:=1229) (a:=68) (b:=69) (joinSmall (lo:=1229) (a:=34) (b:=34) (joinSmall (lo:=1229) (a:=17) (b:=17) sm1229 sm1246) (joinSmall (lo:=1263) (a:=17) (b:=17) sm1263 sm1280)) (joinSmall (lo:=1297) (a:=34) (b:=35) (joinSmall (lo:=1297) (a:=17) (b:=17) sm1297 sm1314) (joinSmall (lo:=1331) (a:=17) (b:=18) sm1331 sm1348)))) (joinSmall (lo:=1366) (a:=136) (b:=137) (joinSmall (lo:=1366) (a:=68) (b:=68) (joinSmall (lo:=1366) (a:=34) (b:=34) (joinSmall (lo:=1366) (a:=17) (b:=17) sm1366 sm1383) (joinSmall (lo:=1400) (a:=17) (b:=17) sm1400 sm1417)) (joinSmall (lo:=1434) (a:=34) (b:=34) (joinSmall (lo:=1434) (a:=17) (b:=17) sm1434 sm1451) (joinSmall (lo:=1468) (a:=17) (b:=17) sm1468 sm1485))) (joinSmall (lo:=1502) (a:=68) (b:=69) (joinSmall (lo:=1502) (a:=34) (b:=34) (joinSmall (lo:=1502) (a:=17) (b:=17) sm1502 sm1519) (joinSmall (lo:=1536) (a:=17) (b:=17) sm1536 sm1553)) (joinSmall (lo:=1570) (a:=34) (b:=35) (joinSmall (lo:=1570) (a:=17) (b:=17) sm1570 sm1587) (joinSmall (lo:=1604) (a:=17) (b:=18) sm1604 sm1621))))) (joinSmall (lo:=1639) (a:=273) (b:=274) (joinSmall (lo:=1639) (a:=136) (b:=137) (joinSmall (lo:=1639) (a:=68) (b:=68) (joinSmall (lo:=1639) (a:=34) (b:=34) (joinSmall (lo:=1639) (a:=17) (b:=17) sm1639 sm1656) (joinSmall (lo:=1673) (a:=17) (b:=17) sm1673 sm1690)) (joinSmall (lo:=1707) (a:=34) (b:=34) (joinSmall (lo:=1707) (a:=17) (b:=17) sm1707 sm1724) (joinSmall (lo:=1741) (a:=17) (b:=17) sm1741 sm1758))) (joinSmall (lo:=1775) (a:=68) (b:=69) (joinSmall (lo:=1775) (a:=34) (b:=34) (joinSmall (lo:=1775) (a:=17) (b:=17) sm1775 sm1792) (joinSmall (lo:=1809) (a:=17) (b:=17) sm1809 sm1826)) (joinSmall (lo:=1843) (a:=34) (b:=35) (joinSmall (lo:=1843) (a:=17) (b:=17) sm1843 sm1860) (joinSmall (lo:=1877) (a:=17) (b:=18) sm1877 sm1894)))) (joinSmall (lo:=1912) (a:=137) (b:=137) (joinSmall (lo:=1912) (a:=68) (b:=69) (joinSmall (lo:=1912) (a:=34) (b:=34) (joinSmall (lo:=1912) (a:=17) (b:=17) sm1912 sm1929) (joinSmall (lo:=1946) (a:=17) (b:=17) sm1946 sm1963)) (joinSmall (lo:=1980) (a:=34) (b:=35) (joinSmall (lo:=1980) (a:=17) (b:=17) sm1980 sm1997) (joinSmall (lo:=2014) (a:=17) (b:=18) sm2014 sm2031))) (joinSmall (lo:=2049) (a:=68) (b:=69) (joinSmall (lo:=2049) (a:=34) (b:=34) (joinSmall (lo:=2049) (a:=17) (b:=17) sm2049 sm2066) (joinSmall (lo:=2083) (a:=17) (b:=17) sm2083 sm2100)) (joinSmall (lo:=2117) (a:=34) (b:=35) (joinSmall (lo:=2117) (a:=17) (b:=17) sm2117 sm2134) (joinSmall (lo:=2151) (a:=17) (b:=18) sm2151 sm2168)))))))
  have good : (List.range 2186).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd 13786117807745248330297337381285929061651640023451164725055304709664843445926585043282813794781729864835926839784029128350552469509838656771615789041601967434081932401290691593659791420286585844556689823031316386998681933670143607680231320307882231022932389306084258518856832957832613223705542791299021119431533290162726590222867968622117172359908148752641110965685579673773663276246994829705943295092061181740736951486944352951916887371304090654568502636492119638228965093366129229283284991837780042622921191261678787528129582327293323090179843978047734423602898401755600127524554972112263411611349701873802477010407053968400936356066458574794029868841587949072254554381372481797558485927763682733521203877821779565176389893722600563009673230195503137825133555836454284888201311814469338994903526981914940168091947728827182678137649261492993077179996851031630572170217428007566862591462031152733786257410549335720282125110 ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd 13786117807745248330297337381285929061651640023451164725055304709664843445926585043282813794781729864835926839784029128350552469509838656771615789041601967434081932401290691593659791420286585844556689823031316386998681933670143607680231320307882231022932389306084258518856832957832613223705542791299021119431533290162726590222867968622117172359908148752641110965685579673773663276246994829705943295092061181740736951486944352951916887371304090654568502636492119638228965093366129229283284991837780042622921191261678787528129582327293323090179843978047734423602898401755600127524554972112263411611349701873802477010407053968400936356066458574794029868841587949072254554381372481797558485927763682733521203877821779565176389893722600563009673230195503137825133555836454284888201311814469338994903526981914940168091947728827182678137649261492993077179996851031630572170217428007566862591462031152733786257410549335720282125110 = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p 13786117807745248330297337381285929061651640023451164725055304709664843445926585043282813794781729864835926839784029128350552469509838656771615789041601967434081932401290691593659791420286585844556689823031316386998681933670143607680231320307882231022932389306084258518856832957832613223705542791299021119431533290162726590222867968622117172359908148752641110965685579673773663276246994829705943295092061181740736951486944352951916887371304090654568502636492119638228965093366129229283284991837780042622921191261678787528129582327293323090179843978047734423602898401755600127524554972112263411611349701873802477010407053968400936356066458574794029868841587949072254554381372481797558485927763682733521203877821779565176389893722600563009673230195503137825133555836454284888201311814469338994903526981914940168091947728827182678137649261492993077179996851031630572170217428007566862591462031152733786257410549335720282125110)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p 13786117807745248330297337381285929061651640023451164725055304709664843445926585043282813794781729864835926839784029128350552469509838656771615789041601967434081932401290691593659791420286585844556689823031316386998681933670143607680231320307882231022932389306084258518856832957832613223705542791299021119431533290162726590222867968622117172359908148752641110965685579673773663276246994829705943295092061181740736951486944352951916887371304090654568502636492119638228965093366129229283284991837780042622921191261678787528129582327293323090179843978047734423602898401755600127524554972112263411611349701873802477010407053968400936356066458574794029868841587949072254554381372481797558485927763682733521203877821779565176389893722600563009673230195503137825133555836454284888201311814469338994903526981914940168091947728827182678137649261492993077179996851031630572170217428007566862591462031152733786257410549335720282125110
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 4775000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : 13786117807745248330297337381285929061651640023451164725055304709664843445926585043282813794781729864835926839784029128350552469509838656771615789041601967434081932401290691593659791420286585844556689823031316386998681933670143607680231320307882231022932389306084258518856832957832613223705542791299021119431533290162726590222867968622117172359908148752641110965685579673773663276246994829705943295092061181740736951486944352951916887371304090654568502636492119638228965093366129229283284991837780042622921191261678787528129582327293323090179843978047734423602898401755600127524554972112263411611349701873802477010407053968400936356066458574794029868841587949072254554381372481797558485927763682733521203877821779565176389893722600563009673230195503137825133555836454284888201311814469338994903526981914940168091947728827182678137649261492993077179996851031630572170217428007566862591462031152733786257410549335720282125110 ∣ Nat.factorial 2185 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 2185 := by
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
  c (j/32) + tally f (32*(j/32)) (j%32)

theorem fromBlocks_succ (c : ℕ → ℕ) (f : ℕ → Bool) (j : ℕ)
    (boundary : c (j/32+1) = c (j/32) + tally f (32*(j/32)) 32) :
    fromBlocks c f (j+1) = fromBlocks c f j + (if f j then 1 else 0) := by
  have split := Nat.div_add_mod j 32
  have hs := tally_succ f (32*(j/32)) (j%32)
  rw [split] at hs
  unfold fromBlocks
  by_cases h : j%32=31
  · have div : (j+1)/32 = j/32+1 := by omega
    have rem : (j+1)%32 = 0 := by omega
    rw [div,rem,boundary]
    rw [show j%32+1=32 by omega] at hs
    simp [tally] at *
    omega
  · have div : (j+1)/32 = j/32 := by omega
    have rem : (j+1)%32 = j%32+1 := by omega
    rw [div,rem,hs]
    omega


private def packet (i : ℕ) : ℕ := (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x2c784e24d147f3a9a0bc4f249046c290e0501600002bce4da3d067a389a4be54248f460250f0541800002b2c4da3d087a391a0bc562590064280e8501400002a854ea410e7d3a9acc658271186c290e85416000029eb48a18fe7333178ac4d210dc56220c84814000029424f239027838194be55238f068290d84c0e000028a04c2390a7737194ac4c228f06a2e0f06018000027f94e24d0e7d3718cb851240f862260e0440c000027564e255147f3a9acba53250f45e250e04c16000026af4e2450c7d3b1b0c05223900662a0f8480e0000260e4aa35067c399a8c05927908742f1185416000025694ca39067736180aa4d220f45e240d84810000024c04ea450c7c399a4bc4f228ec64250d048140000242149a31027636194b450238e464280f04c100000237251a611e823b1b8c054250fc682b0f84810000022c053269268b3f1d8d25f2a92c7a2f1306c1a000022214b229007837998b651210e860280e84c100000217052259147f3b1a4bc54250f066240d84412000020d04c24d107e3a198ae4f218e45e260e05014000020284ca31067b381a0b651238f060250f0541400001f834c23d007837994ba52230f862271005c1600001ecf53a7d268a3e1c0ce5a281207c33118641a00001e274f255187e3a9acb6532390066280e0541600001d7b51a591e853c1c0ce5d279046c2c0f0541800001cd54f24d0e7e399a4bc57260fc66290f8481200001c2c4ea490c7c38190b250230f05e250d04c1800001b79522711c853e9c8d05c27108702f118501200001acd4f249147e399a4ba50228ec6029108501800001a244fa5116803b1acc85a28110742e1205c160000197651a6114803b9acc0592891876301185014000018c95125916813c9acc85c291207e36150681c000018204ea591a813b9b8c45727114722c1206c1c0000177f4b2390c7e38998ae50240f466270f85c14000016c85527d26853c1c4ca5b29114762f11864180000160f57a99348e421d0d05d2910c762f1206416000015625025d18813d1b8c85a2790466291005c14000014b55225918833b9a8c054248f8682c10858160000140154a7520823b9a8c45726110723012070180000134f53a7126863c9bcc456260f86a280e84c120000129c53a7120833c1acc6552810c702c0f85c1a000011f1512611a833b1b8c2562790c6e2b0f8581c0000113e5326124863c1bcce5d2a9247c321286c16000010845628524873e1bcca5b259006a270e8541200000fd155a7526873d9c0cc5b2890c6e2c108480e00000f1955a7d2e8d411e8d85e299247e34130641a00000e695326520843c1b0ca5826908742a1185c1800000dac582952c8d421e4d65f2891c7430118541200000cef57a8926883d1c4d25d2911c7a301105c1400000c3d5326922853d1b4ca5a28110742d1085c1600000b815827d26893e9c8ce5c251006c2b108681a00000ac25a28d368f419d4d65e29920702f118601600000a08572953691429f8e4612a91c782b120601a000009425c2b94094441fce8662b9307e34110601c0000087d5c2b1469645a04e6682d13080321586c1c000007bf5aaa9429747208ea682c9387c34148781e000006ff5b2ad3891439e8de632c9348235128601c000006355d2b54497449ecd85e2992c80351405c180000056a602d54e9a46a04e6642b1247e3111050140000049d602d14e9947a0cec692e9448835158781c000003ca652e5589d48214ee662c13882321306c1c000002f2652e55ea24c220f66e3014c8e361406822000002116831568a84da3cfa72329548c3a1507820000001227134984b45225d127c36964964016880200000000089c11e6e16a305629f479f4d459228c43600 else 0x541b4b228fe783719cbe54248f466260d840120000538448214f46e34974aa4e220ec62250f04c14000052e24aa31007535180b24e210e46027100541a000052434ba31067637194b453250fc682d1186018000051b3421ece66a32178a849200d85a210d8440c0000511d46214f8743597cb452248f064250f04c160000508a421f4e66e3196ca6491f8dc64250e84c1600004ff946208f26f34178a4481d8dc5a240b83c1000004f4a5025d14813c9a0bc54250fc662d0f0501600004eb047a0cf27135994b64d208e05a230f0501600004e1548a21007536190b04e220f060250e0401400004d764aa2902763598cb452259046e26100501200004cdb49229047737188b251220ec60290e84c1c00004c3a4b23d0a79399acc254228e860250e85c1400004b9d4921cf66f34988aa4e238ec662c0e8441200004b0a449f8e86b31970a64a200d85a270e8481000004a6c4ca3d087936190b652228e862291006018000049d945200ec7034174ae4e238f466280f0541a000049334ea4d127f3b1b4c858259046c2a10854180000488e4ba450c7f3b1b4be56249046a2d1206816000047f049a250075361a0be53248e864240e8601c0000475747210f27033978ac4b200dc5e260d83c10000046b94ba20fc7a36994b650248fc6e2f12064140000462245a0cf67134174a84d228f4642810854160000458649220fa7637998b651238f864260f0500e000044e749a25067635980b04e218e8602a11058140000445145214f8733316ca2481e8c052220e85414000043ab4da410c7b381a8c254248f8682910858160000431348218f67131974aa4b220e05a200d0400e000042704ca390c7b38188b04e238f462260f04c0e000041d849a20fe7737190ae4f200e05c250c84c140000412f4fa490c7b36984b24f230e460260e8480e0000408d4ca39067a3a1acba51221006e2b1085c1800003ffa45a04e6682f94896421d8bc4e200d0441400003f4b5326522883c9c0c858261046e2d118541800003eb545a04ee6d329649e49208e060270f04c1200003e124b224f871329689e441e0cc54220f0541400003d7649225007436180ac4b1f0d45c270e0501400003cd54c229067635984b24e220dc5a240d84c1000003c2d4da45108039994b852238f062280f0501600003b994520cf27034978ae4d228f0682a0f85c1a00003afc48a14fa6d3497ca84c220f068280e8441000003a6347a21007837990b44e228e85e270d04c0e000039c34aa2d027534174aa4b238f866280f848140000391f4ea49127e39194ba54259046e2f10858160000388b46a04f0703397ca44a200d85e260d84c12000037e84ca20fc733618caa4c230f0682a13068180000374c4a220fa7535988ac4b228e85e250d83c10000036a94c235007c399a0b452238f066291005c18000036014da3d087938190b250248f8662c10050140000355e4da3d087837180a64a1f8d858210c83c0e000034b84d23d0a7c38194b851238f8682c100581a0000341c4a220fe7034178ae4b218e060250d83c0e0000338547a10f4703116ca64a210e45e250e04c16000032d8512611c7d3a1b4c25627114722e10054180000323a4b231047737194b04e228fc682b1185814000031914fa5516813c9c0cc5a279187631130781e000030f24a22d047837988b24b1f8d856220c840120000304a4da3d0a7c399a8c258269086e2d110641400002fb048214fa7434980aa4d200d85c240d84c1600002f084e2410a7d391a0c058250fc6c2c108541400002e664ca30fe7536190b24d1f8d85c210c8441400002dc64aa2d087937184ae50210e460250d8401000002d1f4c23d0a7b38990b854240f462240e84c1200) else (if i < 3 then 0x7a2c47a1cfe7634994b44f220ec6a28100500e000079924922d007533174ae4f238f05c250e85012000078f649a29007536190b8512390064260e850160000786248218fe7734180aa4c218e462240c03812000077de3d1c4da663015898441f8e460270e84c14000077404a220f67134184a64d2190064250d05012000076b93f9ccda662f1589c471f0d85a240d83408000076174ca250477371a0b44c220e060250d848100000758048214fa723598cb04a200e05e250c84c16000074e945a0cee6c319609e451f8e062250c040120000744f45a14f47335180b250210e462280d04814000073b24aa3902753719cc055258ec6428108601600007322431f8f07033970a449208e8641f0d0440e0000728946a14f46f32978aa4d228f064270e84c14000071f446208f26e32974a6471f0c854200c8440c00007165421e0e26c32164a44c218e864280e03410000070c649225007636180b44f238ec62230e054120000703246a10f27133980ae4b208ec5a250e0401400006f9e45a10f4703316ca0481e8cc58250f0481800006f0648214f67235178aa49200e460260c8501600006e6e46a0cf2703316ca6481e8d05c240e0481a00006dd24a231047836190ae4c1f8dc5e250f0500e00006d354c249087b39190b851250fc6e290f8501400006ca2431fce86a31168a449200dc60260e0501800006c0a47a14f87433980a84b220e45c240d04c1400006b694c2410e7e38194b651240f460280f0541600006ac94aa390a7735994b450228ec62280e8541800006a3146208f47032970a449210e0561f0c04810000069934aa35047939194b84e230f05c270e848100000690044a04ec6d3215c9a411d8d0501e0c8380c0000686946a0cee7032970a649210e8642a0f05010000067d9421e8e26b3095896471d8d858260e050160000673b49a30fc753718cae4d210ec6a2a1185c12000066974f251107c389a8ba51249006a2d12060180000660145a14f26c309689e47208d864280f054120000656648a21007435978a848208dc58240c84c10000064d2451f8ee6e33178a649220e860270e850180000643a48218fe7938198b84f230f06a2a1085c12000063a946218fa7235980ac49210f066240c03c100000631a431fcec703296ca84b208dc56240d848100000627e49a2d027837198b653240f864280f8581a000061e349225007837990ac48200d85c230d040100000615d409d8de683196098401d0d45221090240a000060bd4a23d087837198bc552590c72290f04c180000602b429f8ea6c30960a84e208e05c270e04c1200005f874ea490e7937184b852238fc66280e8481000005ef245a08f07034978a64b228e8642a0f8581200005e5f46204ec7133974a44b220e060280f0481800005dbd4ca390a7935994b650230f066290f8481000005d30429fcea682f9589c441f0e85e270e0401000005c9748220f46c33974a249200d85c240e0441200005bf44c23106783598cb45425104702d100601800005b514ba450c833d1ccd860299106c291004c1e00005ab749214fe7636198ae4e218e462270f0501200005a194aa18fe7738998ba52238f46a2a0f85c140000598a44a04ec6d31960a0441d0d458220c83c0a000058f445a08ee6e31964a648218dc5e250d04410000058564a22d087a36188b04d220e862270f06018000057c344a04f47235980ae50250f864260f85014000057234ca2d007434178b25124900702d108581400005692421fcf07133170a84d218e45a260d84416000055fb45204e6672f1508a411d8d45e280d0400c000055544da3d107d3a9b4c056251006c2b0f85818000054bc47218f47136190b24c200d85e240c0480e00 else 0x9f1a46a08f27132978b04d208f060270f04c1200009e7f49a21007737198bc522490066260f8581a00009ded44a00ee6e33970aa4b1f0cc54200b8340a00009d703a1b8ca5e2b9348e441d8cc56220d0401000009cda44a00ec6d32968aa4e220d85c220c03c1000009c424620cf4733598caa4a210e46a280e0541c00009bab4720d00763618cb253240ec62270f0481400009b253f1d8d2642c94c96451e0d05a220d03c1000009a834c231007334984a84a200ec5e260f04814000099f3439f4e0693116498421c0c854220b84012000099554aa29067637988ae50230f46c2a110601a000098bd47a08f27234178aa4f220e8662c10864160000982747a18f87033178a2451c8c452210d048140000979446210f87434984ae5025108702e10850100000970144200ee6d319649a441e0bc501a0a8440a00009671421e0dc68309609e4a218e862270f05814000095e5421e4e86b31960a24a220e46a2a100601c00009559421f0e06a30964a44b218f0642a0f04c12000094c347214f46e3297cb24f220f066290e0480e00009434429f0e86c3196ca04a1f0d45e220e05418000093b03f1e4e06a2f164a649218e05c230c844120000930f4ca45087837990b04e218e05e260e04816000092843f9d4da612c9489e46200d054220c04012000091fc3f9d4d8622e1549c461e8c854230d84810000091654922d027836190b650238f064290f05016000090c64aa30fe7334978a44a200e45e240d048120000902d48225007736188b44e228f462261005c1a00008fa63e9d0d6652e15094421c0bc4c1c0a0380e00008f17421f4e86c32164a0471f8dc58260e0481600008e794aa2cfe7635980b44d200e062270d8401200008dda4ba39067c38990b650240f8702c110581600008d4545a00ee6e33974a6491f8c8481d0a8380e00008cac48204f06e3015096411d0d858230c0401400008c1a451f0e86a329709e451f8d0521e0a8380e00008b8c431f8ec6932174a648200dc60220c8441000008af248a10f27133980ac4c200d854210b83c0a00008a61431f8de6a31960a0471e8dc56220d03c14000089c847a00f67335988b64e208e460280f84c1000008937451f4ec6d3095c96431c0bc4e1b09030080000889d4920cf6733597cb04e210e0642b0f858180000880b421f0e0662f14498431c8bc52260e03c0e0000877648a0cfa7736984aa4e210dc5a230d84c0c000086de48a18fe733417cae4d200d45c240c844140000864249a2cfc783618cae50230ec62270f84c0e000085b544200f46f32970aa4e228ec64250d04c100000852a409e8e26d33970a646200d056220c848120000849b441f8e8693215ca0451e8cc50200c844140000840c431f8ea6e33174ae4f218ec64280f854120000837548214f6723598cb04d210e45c230e04414000082ea411dce0662e1689a441d8c4521e0b044100000825446210f66f3216ca2471f8dc5c270e84816000081ad4d2410e7d3899cb653259086e2a0e85414000081114a235047938990b85025104682b1105c120000807f449f4ea6d319649e461d8d456250d8380c00007ff0431f4ec6f33974a84b238f064290f0541000007f5847220f67334184aa4c220ec64281004c1400007ec4451fcea6931164a6461f0cc521e0a8340c00007e3244200f06f32964a2491f8d858250f0541400007d9c46a18f67133978a84d200dc5c240d8401000007d0a439fcf46f3416cac4a210e862250d83c0a00007c6d4b231007a391a0ba52240f460240c8300c00007bd745210ee6c3317cac4d220ec62280f8480a00007b49419e0e0682f154a048200c8501e0d8441800007ac43d1c8d8622b1388a3e1c0cc52210b8441000)) else (if i < 6 then (if i < 5 then 0xc379431fce86e32178a6471f8d054220c83c0c0000c2e447214f66e31164a449200e8682a11050120000c254439fcee7035188b450228e860260f04c140000c1bf46a0cee7034170a64b229006e2d0f84c160000c133431ecea6c3396ca248220dc5c270e054160000c0a5421ece86a30178aa441c8c44e200d848140000c00f4720cf47033170a0481e0d05c2810048180000bf82411f0e46c301509a451d8d054210c0340e0000bef2421f0e26a31164a849210e862270e040100000be65441f8e4692f964a4481e0bc52220e8541a0000bdcf449fcec6c321689e451d8d058250f858120000bd3b441f4ea6c3195c9a421c8c454210c840120000bcb63e9d4da652e94c96471e8d052220c840100000bc2346208f27435184b04f239006c2c100601a0000bb8649229047535178ae4b210e86429108480e0000bafa411e8e26c2f15094401b0bc4c200c844100000ba67449f8e86a3095c9e431d8d056260d048140000b9d4449fcee6c3095ca2461d0c454200c044120000b942451fce26a3016ca44b200dc5a210b83c100000b8ad45210f86f3297caa4c230f060260e058140000b81f429f4e2682f1649c441d8d456230d84c140000b7894720cf2733417caa50248fc682a0f04c120000b6f843a04ec6b31174a84b218e85e280e03c060000b663461f4ea692f15498491e0c04e1e0b83c0e0000b5d2441f0e6672f9509a431f0e05e2710050100000b549421e8e46b31974a4451d0bc4e1d0a8400a0000b4b2451fcea6c3196cac4f220f8722d100641a0000b42e3e9c0ca5e2b14090441f0d85e290e850120000b39349a20fe7233178a64b1f0cc5a210c848140000b307431e8e2693015ca2481f0d05a240f85c160000b27b3e9c8d2612a93c8c401c8c454230c854140000b1e5451fcec6f34178ac4d228e85e240e854140000b15a419e4e46831164a6471f0d852210c840120000b0c345a04f26e31974aa4b210ec64260d04c160000b02c46a14f27033970a64b210f4662a0f84c120000afa63f1dcda6a2f15ca0461e8c450210b830080000af1e401dcde642d1509646208d85a210c8300a0000ae8247204f67033980ac4d240f8602610054180000adfb3f1d0d8652f95c98421c0bc461e0c0400c0000ad6a449fcec6b3116c9e471e8d456200c8400e0000acd34822d06793718cae4d228e05e240c83c120000ac47409e4e46a3096ca24c1f8e0622810850100000abb544a0cfc7434180ae4f220e860250e84c120000ab2445204f07635984b453240f0642b108541a0000aa9a419e8e46b311609c421d8cc4e210c044100000aa064520cf87235180ae4c220f062240d84c120000a96e46a0cf47133968a447208c852220e854180000a8e2401e8e66a2f15096451f8e45e250c848100000a8474821cfc733417cac4a200e05a260e84c1c0000a7b744208f06e33174a2491f8dc5a260d844120000a7194ba350078381a4be51238ec64280f058140000a68b411e0d6652e9448e3f1d0c454230f850120000a5f248a20fa7434984ae4e240f8662b0f04c140000a5683e9d8e06b32970a44b210d858220b83c100000a4d346210f67234174aa4b1f8cc58220e850140000a447431f4e66a301609e481f0d456240e050160000a3af47a18f6723397cae52251046c2b1085c180000a31e429f8ea6e3316ca0491f8cc58220d03c0e0000a2983f9dcdc662e1589e471e8d85c240f0581e0000a20146a04f2703517caa49200e062270d0440e0000a16a45200f06d3296ca04a220f066290f050120000a0d745a00f46e33184ae50231046e2e11058180000a0404620cf47235970a24a1f8dc58230c8400e00009fb0441f0de663015c96441d0cc64250f8501600 else 0xe72f411d8d8642e960a647200dc58230d84c1c0000e69e439f0e2682f94c9a421e0c4541f098300e0000e60b431f8e46c3216ca44b230f460280f04c140000e582419ecda6630150963f1b8c456250e84c180000e4f2421ece66b329609a411b8c452220e050180000e463439fcf06c32968a24a1e8d454240d8440e0000e3d5431fcf06b3316ca84c210d850240d84c160000e33f45a18fa71339709e461f8e460280d850120000e2aa47a1cfa7837188aa491f0d858250e848100000e221401e0d8632e95896421d0c454240d834120000e19f3d9d0de672e1549a451e8d058210c0340c0000e110449fce0692f1589c441d0c84a1c0b0280a0000e085419f4e86c32978aa491f0d85a220d048120000dff24620cf87133974a64c228ec66260d858140000df66401e4e86a2f15094411c0b84c200b044160000dece48a18f86f3196098451f0e062280f854140000de3c45a10f06e311689e4a220f46c2c10864120000ddaa439fcec6b3115c9c451f0d058210c04c140000dd17459fcec692f15ca24b210dc54210c850160000dc8d419e0e6682e9509a48200e45e240d8440e0000dc04421f4ea6c31168aa4b220e462260e050160000db74441f4e66a3115ca84a220e860270f048160000dae4439fcf06f3215c9a471f0e058200b83c100000da5145a08f67034178a24a200dc561d0a83c0c0000d9cb3d1d0d8662f95898451f8e45a1f0d044140000d939449f8ec7032968a649208e460290f058180000d8a8439f8e2662e958a2471f8e05a210e84c140000d81644204ee6b32964a64a200dc5e270f044080000d78e3d9c8da632e968a04a208d856260d04c120000d6f348a1cfc7736190b655261046a2c12064160000d66245208ee6d32174a8461e0c44a1f0a0340e0000d5d9411e4e46a319689a441d8d060250e058140000d54c421f4e66c3115c9e481d8b450220d8400e0000d4b946a20f8703296ca2491f8cc5a261085c140000d428419f4ea6d3216ca449200dc5e260d048100000d3a23f1c0d65e2d138883e1b0b8481b070240e0000d318409e0dc652f1488e401b8c4541f0a8340a0000d28147208f47135980b250228e4602b10040100000d1ef459fce46a3196c9a481f0d45a230d044100000d15f431fcec6c31978ae4e228f8642b10854180000d0cc46208f26d32170a4461e8dc5c260e844180000d03f431f0e46830160a64a1f8d85a260e04c180000cfb5419ecde693096ca64d218e460240f0501a0000cf25439f0ec6f3116098441c8c050220d850120000ce92449f4e6672e1589e451d0c858250d8400e0000ce05411fce86d32978b252238ec5e230d84c140000cd7343a0cee7436188b24c220ec5e250e044140000cce7411d8e26831168a0451e8d056210a02c0c0000cc4f4620cf06d319649e471c0c0501f0b0340e0000cbc6409d8d6622e9509a481e0d4581f0d0480c0000cb38431f0e86b31964a44d208e05a240f8480c0000caba3a1b0ca5d2b94494421e0d056271004c160000ca2c421e8e66b3195ca048210d05c250c840100000c995469fcee7134178a6491f8e058210c8480c0000c90246200ee703497cb04f2390064290e854120000c874429dcde662e95c9a471f0cc5c260e858140000c7ee3e1ccd2612d95896431b8c456230c844100000c7663f9d4dc672f15898431d8c44a210c03c120000c6d9421fce86c33174a449228e060260f04c120000c64b419ecda652f94c98471e8dc60240d84c180000c5b944a04f06d34980ac4f228f0662910058160000c532411e4de652d958a2471f8c852260f050180000c49b48a29067835194b651238f0642a0f05c160000c406451fcee7030968a2451e0d85c26100480c00) else (if i < 7 then 0x10a773f9d8da662d14c96421d8c850200c04814000109e545208f07132170a84b218ec60260d054140001095b411dcde652e14498421c0c0521d0c04c14000108d33f1e8da652d14092431e0d45c260d840100001084c401e0d6652f9549a441d8c04a1b098300e000107ba46a00ea6c301649c49200e86428100581200010729431f8ee6f33978ae4e230f06a2b1085010000106ac3c1c4cc5e2b1448a3e1a8c456210b03c100001061b44a00e2693094c9c471e8d458210c840140001058944a10f66e3096096431e0d85e291084c16000105043e1c8d4642f14c92431c0bc521f098300a0001047c3e9d0d65f2b12c903d1a8b44a1c0b0300a000103ed429fcea693196ca4481f0d054230d040100001036c3d9ccd6622c13894411c0cc54230c84812000102d049a39067a36984b24d238f06e2d118541600010244439fcec6d32174a6481e0d058250d84412000101bf419e8e0692f95094441d8e462260e8401200010134419f0ec6f32170a2461f8d05a240c84c140001009e46a0cec6f31960a0441f8d05e270f8581c0001000547a10fa7336190b84f228e864270d84c180000ff7c401f4e2693215c9c481e8cc58200a8340c0000fef0401d4d65d2992c843a1a8b850230a0340e0000fe5e431e8e66d32974a2491d8cc58230e058100000fdd63f9e4e0662d95498451e8d054220c840120000fd47401e8e46b31168a2471e0e0662911060160000fcb9439f8f06c31968a84b200e460291205c120000fc2844a00f06d3216ca2481e0cc58280e04c180000fbad399accc5d2a9388a3a1a0ac4419088340c0000fb114922900773618cbc52248f466280e850160000fa88411e8e2662e15c9c471d8c854220e058160000fa023f1e4e8672f964a448200e05e290f8541e0000f975409d8da652c94090411b0ac481b0a83c100000f8e4441fcee7031968a24b218d45e2510060140000f852439f8ea6c3296ca84b200d056260e848100000f7c6449fcec6d33970a0431e0c04e1c0a83c0c0000f73544a0ce86a311589e431b8b854220d044120000f6a9409e0dc652e14492411b0c0521f0a834100000f61445a00ec703317ca2491f8d85a230e0400e0000f588429ece26b30168a64a210e06428100581c0000f4f9439f4ec6e33178a4471e8c85e2b0e0400e0000f46e409dcde6730960aa4d220ec5c230c84c140000f3d9441f8ea6a301609a481f0e05e28100581a0000f34d44200f27133978a24a200d858220c844100000f2c2431e4e0642d94c96431d8c458210b83c100000f237411e8e66d31970a849200dc642c0f054180000f1ad411e0e068309609c451f0cc58220d848120000f11a4720cf27034180aa4c200e85c260f854140000f08b45204ee6e33970a84b208e4622b0f850100000effe449f8ec6a32164a84b218e0622b0f850120000ef6d449f0e86d32170a2441d0b84e210b044100000eedb441f4e46b2f95898441e8c8501f0d8400c0000ee494620cf8723597ca8491e8d858220e04c0e0000edb345a00f47235174a248208e05e250e848120000ed2e3e9c4ce5f2c13c90401a8ac4a1e0c0480c0000eca5409dcdc6831964a449208d85a240b8400e0000ec1345a00e8682f9609a411c8bc54210d0480e0000eb7c48218fa7335988b04d210ec62260c840140000eaf0411ece8703116ca2481f8f0642a0f8541a0000ea66401d8d8652e1589c441d0d0521e0b840140000e9e03e1ccdc642e9408e3c1b8b0481e0b83c100000e95f3d1bccc5f2b14090421c8c050220f060160000e8d7401e8e0692f95c96441d8c856230d040140000e84a409e0ec6a30968a24a208e062281005c120000e7b8431f0e4693216ca249208e462270e84c1200 else (if i < 8 then 0x12d55411e0dc6530960a2461f0dc60260e8481200012cd63a9acca5c2a128863d198b84c200f0541400012c4e3f9dcdc662e95c9c441c8a4481c0b0380e00012bcb3c9c8d8652f95894451e0c856220d0481200012b40411e8e6672d948923c1b0ac421d0a0300c00012ab3411f0ea693116ca44b210dc58220b8400e00012a1e45a04f06d3015498441e0dc52240d844100001298d441f8ea6e32974aa4c230f064290f050140001290d3d1c4ce602e15094451e8d0541f0a83c1000012881431f8e46b2f9589c451e0d058230b04012000127f3421dce26b301549e471e8d0541e0d048160001275f459fce6683196c963f1d0cc521f0d04810000126d5411e0e069309609a461f0d05c260d0340e000126573a1acc65b29930883c1889c421b0b0440c000125ca429ece26731164a4461e8cc52230d04c14000125453d9d0d6642e15096451e8d452200b83c10000124b4439ece86c33178ac4b218f860290f850180001242f3f1ccda5e2c140863b1a0b04a1b0903010000123a63f1d4dc642e95090421c0b850240d0400e000123243c9c4d6612d13c8a3d1b8b04c1f0d0441400012295421ece66b32174a647200e85e250e0480e0001220245a0cf6733597cac50220f05c270e850140001217a3f1e4dc662d95094431c8c458220d04814000120f43e9e0e06a3015c98431b8bc441b0a038100001206d3f1d4d8612c1448e411e8cc54210c8441000011fdc441f0e6692e95c9c471d0c04e1e0c8440e00011f52419e0de682e94898421d0c04c1b0a0381200011ec83f9e0e26a31160a44a208dc5e270f0481400011e40401d0d8632e14492411c0b84c210c03c0c00011db7419ece66b311649e471f0d458210d0501200011d1d48a24f67035174a44a200e066270d84c1600011c8d429f0e46931974ac4b200e05a280e84c1200011c02419f0ea69309649e44208d85a220e0481200011b7543a08f06f33174a849210e862270e0501a00011ae7421ece66b311549a45200dc58250e8441000011a5e409dcde693095c9c471d0cc501f0a82c0e000119e6399b0cc602b9489a431c8c05a220b844120001195b411dcd8662f950903f1b8c4501e0b85018000118c149a28fc7637194ae51220f060270c83c0e0001182847a20fc7435988ae4c218f466280e8501400011798439f8ec6f32174aa4e218e466270d83c08000117143d9c4d2622e14c9a421d0cc58240d0481200011687421f8ee6d32974ae4b218e86027100581a0001160e3a9acc25928924803c198bc481d0b83c100001157f429f4e0652e9549e451d0c84c1f0a0340e000114f3409e4dc6a31170a4461d8d0561f0b8381000011465431f4e66b2e15096441e0d85a240e0400e000113d14620cf47235180ae4e218e454220d850160001134f3b9bcd2622d95898431d0c856260d84818000112c1431ece46d3015c9e461f0e054200c044120001122f44a08f67233170aa4c200d452240d84814000111a6409e0e26b3296ca2471f8d462260f05c16000111233d1ccd2632d94490401c0b84a210c848100001108e45a08f06d3116ca4481f8dc56240e8340c00011002409e4de682e14490401c8c04a1d088340800010f70431f8ea6f34170a64c230f062250e8541200010ee2419dcd8663015492401c8bc4c1c0a8441400010e5a401dcda682f964a84b208e05c220b0340c00010dd23f1dce66c33174a449208e45e270d8481200010d43439fcec6b3196ca0461e0d054200c0380e00010cb4431ece2662e14892411c8b852210d04c1200010c1948210f67335178ae4d228f4682a118641c00010b90409d8dc6731970ae4f230f86e2d110641600010b01431e8e2692f164a84b1f8cc56230d0480600 else 0x14ff144a0ce86b31968a64d218cc56230d0441000014f65421f4f26b31970a84b200d456250d8501200014edd409dcdc652d93c8e401d8cc50230e84c1600014e573e1ccd8602c12c8239178a04c1f0b0400c00014dcb411ece469301609e47200dc5a230e0541400014d3d44a04f47233180aa4d228f46a291085c1600014cb043204ea6a3115c9a441d8c4501d0982c0800014c1348218fa733719cbc522510466290e0400a00014b9a389a4c258289288e3e1b8b854220d8481400014b123e9c8d8642e14c923f1b0b44a1d0b8440e00014a8b3f1d8da602b93c903d1a8bc4e200e0440c00014a00411e0dc672f15ca0451e0d45e240c04c100001497a419e8de6a3095c9a461f0b852240e04410000148de48a14fc7636980b24d210dc5e260f04c180001485d3b1b4c65f2d13c98411c0c04a1d0b84012000147d143200ec6f34970a84c200e466270e0441000014743411d8d4652c144903f1d8c052200c84012000146bf3d9bcca592a940923e1c8c458230d84c160001462b451f4f0713418cb44f220e466250f05c160001459f431f4e86d32170a2491f8cc5a250e84c14000145183f1d4dc662e95098441f0cc52230e04c120001448b42a00ec7032168a84a220ec62281085812000144093c9b0cc5e2a9287e39188a8441b0b84812000143843d9c4d4612d14092461f0dc5c210b84012000142f5439f8ee7032970a24c210d45a250d84c120001426f3f1dcd8662f95c9e48200e060260e84816000141e83e1ccda652e15096431e0d460250e8440e000141643c1d4d6662c14090431c8c452220c04010000140e33c9c0ce5f2a92c8a3e1b0ac481a0b8481200014057419f0e8683015896461e8c056200b8341000013fce411f0de672f95498441c8bc4c1e0a8340c00013f46401d8dc6931170a6491f8dc58230d8340e00013eb7421e8dc672f95096401c8c44e200d0481200013e254620cf66e33974aa4e220f86426100581000013da93a9b4cc5e28924863d1b8b84a200c03c1400013d233d9c8d8622c93c8e3f1b0bc4a1d0c0380e00013c99401dce0662c94490421d8cc561e0a0381000013c07421f8ec6d31958a049218e864250c8441600013b833d1c0ca5d29928863d1c8cc54200a8341000013af7429ece26b32170a84e208e060290e0501000013a723f1d4da652f160a0461c8c45a1f0c84010000139e6419ece068311649c461e8d056240d84c100001395e3e9c8ca5e2a9348e3b1a8b04a1e0b04412000138d53e9d0d6622d14c98411c8bc4c200b83c0c0001383c47208ee6a30960a2491f8dc62230f8540e000137b33f1d4d6642c93c8c3d1b0c04a200d8481600013727439f4e469301589c471f0dc60280e854120001369c429dcdc6b3095c9e451f0d85e240c048160001360f419e4e46d3217cae51230ec5e240c83c0c000135893e9d0d8652e94c923f1b0b44e1b0a83c12000134f645a18f87334174a64b1f8dc60260d84c100001345d48214ee713417cb04f230f86c2f120681a000133db3d9d4e0662e94c943f1a0b4521d0b8380e0001334745a14f8713498cae50230fc66281005018000132b9439f8ea6d3316ca6471f8d456230e04416000132303f9ccd8642e9549a46200dc5c230d844100001319e45204f47034178a84e220e456200b0441000013113421ece2692f168a0451f8cc58260f048120001308e3e9d4d4622b9388e401d0c4501f0b83c0c00013002419f0e86c3295c9c461e0cc56240e83c0c00012f7a411dcde622d150903d1a0b44a1b0a0381000012ef63d9c4d2622b940883e1c0cc54230f0581400012e68429ece0663015c9a421e0cc541e0b0380e00012ddc401ece86b301509c461f8cc5e270e0501400)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0x172743b9b4c65a2911c7e35188a0441c090280c000171de449fcea6e3196ca44a200dc5a250f05c140001715c3b1c4d6662f95492411c8c854210c8440e000170d93d1c4ce5c2a9408c401c0c852220b830100001704c419e4de6631970a84e2490060240c8401400016fcb3c9d4d8632d95494421c0d452230c04c1200016f3d429dcd8622b9408e3c1c0c456230e84c1600016ead441f8f06d3416ca647208e05e260e0540e00016e1847220fa7333978a64e218e8642a118601600016d90401e0e0693015098461f0c858230c8441000016d123a9b8ca5a2893484391a0b84e1e0b0300e00016c8e401e0dc632d1489e431d8cc54210b0380a00016c0e3a1a8c25c2b13490411c8c450220d8481c00016b873d9ccd8652f1489c481d0dc5e240e04c1200016b073c1c0d4602e14c923f1a8b4481e098300a00016a7d409d8dc632b93c94411c8c45a240e04810000169f3401e0e06932970a0461d0d054230d844100001696e3f1dcdc642e950a0491f8d858210d04812000168e5419f0e6682e95898451d8c8561e0c8441600016855441f0e86e31964a04b210e85a240d84816000167d0401e4e26b2f95c92431e0d456210c8481200016741449f8ea6b3095c9a451d8b84c1e0b03c0e000166bb409e0e66b3095c9e401c0bc4a210c8381000016629459fce86e3115ca2441f0dc5c250d048120001659c429f4e2663096ca24b218e8602a108641c0001650944a08f47134178a0461f8ec60270c8441a0001647a449f4e66e339609c451f0cc561f0d0440e000163f1401e0dc662d95c9a451d8c04c1e0a0380e00016367411e4da652c9488e401b8b84c230b84014000162e33f9d0d8632e14096441e8b84e210c03c1400016258421ecea6b309549c471e8c45a250e05014000161d13f9e8da632d15498421d0d05c240d0380e0001614a3e1ccda662e154903f1c0d0521f0a0280c000160bc431f4e66830160a0451e0e0602810060140001602447a28fe7332970a2461c8c850230d8401000015f97401dcde662d14094441e8c04e1d0b03c0a00015f0c419f0e86b31960a2491e8cc501e0b0401400015e734721900763417cb050230fc6c2c1106c1a00015df13f1bcd4602d94892401d0d052210b8340e00015d6b409dcde652f14c923e1b0b4461d0b8481200015cd845a18f67234178a849208e058220d8481400015c513e9d0da652c94498401d0c0521d0b0400e00015bc5439fcf2723397cac4b208e05c1f0c0380e00015b423f1dce46930968a8461f8d85c240e0501400015ac13b9b8d0612d14894441e8d4501e0a0380e00015a37409dce0672f168a44a210d0561f0a04010000159ae3f9dcd869309589e471f0d45a250e05012000159303b9b4d4622e1408e3f1b8c854200d04412000158a5409e8de692e15892421d8d858220b8340a00015815429f0e66c31168a0461e8d45a250d04c0e00015787439e4dc673096ca8491e0d45e250d04010000157003f1d4d8632d15098451e0c854200c0400e0001566c459fce4662f9589c481f8d860260f0440e000155e3409e0e0662e1489246200d85c280f850180001555643200ee6d32978ac4e220f064290f05414000154e3369a4c45c2a934863c1a0ac4a1f0b8441600015455421f4e6682e144883c190a84c1e0a82c0a000153ca419f8ee6e30164a64c220f86a280f05014000153473e9d0da612c14c96431d8c454250f05418000152bf3f1d4da662e144903f1b0c04a210b8380e00015230431fcf26e33170a8491f8dc58260c03c140001519c46208f070339689e471f8d458220e04c140001510e44a04f06d3217cb050208dc56220c84412000150853e1e4da642f964a0451d0d0561f0d0340c00 else 0x1946743a04f06d3015c9e451e8cc521f0d0380a000193eb391c0d6632e94c94411d8c84c1d0b0440e000193673d9ccd8632d14c96401d8c852220c84c16000192e83d1c0d05d2c93892411c0b44e1d0b03c0e00019259421f8e66c31960a04a210e460260f85814000191cf409d8e0682e9549e471e8d858220d840080001913b45204ee6f3197ca64d218ec66270f85812000190b8401e8e069301589c431e0dc58230f04c10000190363c9b8c65a2a1288a3b190a8481f0d04c1600018fad3e9e8de692f95494431f0d454250e0481400018f253e1d0d8672f9589a411c8b84c1d0a83c0e00018ea13d1d0d4642e9549c431d8cc54230e0481400018e213c1b4cc5a29934883e1b8d056230d84c1400018d9a3d9d0d65f2c1388c3e1c0bc4e210c0401000018d10421d0dc6630960a047200e860270f8501600018c744a22d00773517cae4d228f062270e0400e00018bfa37998c4602b9388a3c1b0b8481f0b0340e00018b6a429e8dc692f96ca44a1f8e05e270e8481000018adf419e4e2672f9589c46210dc5a260e03c1600018a5e3d1ccd6652f9589a481d8d054210c84416000189de3d9d0dc632e94894411d0c454230d04c120001894d439f8e86c32974a64d208e458230c8380c000188cb3c9c4d0612b944903a198a8461c0a83c0a00018840401e4e666309589c471f0cc521f0b84014000187be3b9bcd0602d94898451d8d860240e04c1200018731429ece4682e14c96441e0dc5e260c84812000186a6431ece46a3016098461f0d458250e84414000186283a9b4ce5f2a12c8239180a446200b8400e0001859945a10f26f319609c441f8d45a210d04816000185173e9ccd6612e13c8c3c198bc501d0c044120001848f3e9d0d8672e95496421e8d05a240c04410000184123a1acc65f2c9408c3e1b0b84c230c8400e00018387409e8e66b3115ca048210e85c220c84414000182f645a08e66c301609c451f8d058240c8400c00018267439f4ea6d3115ca446200d456210c04410000181e53c9c0d4642d95096421e0d45e260e0501600018156421ece4692f16098441e0c854210c84c10000180d03f1dcde68301649a461d8c456240b038140001804b3c9d0d0622c14496411c0c454230e0481000017fc83d1c0d2632e1488c3d1a0a8401b0982c0c00017f453e1d8dc682f1649e49208d85e260d8481200017eb7409f4ea7033974a64a210e46029100541400017e2f409e0ea672e94c94411c8b852230d84c1400017da93d1d0d4622c140903f1c0b84a1c0a82c0c00017d1146a24f67136984b04b228e85a230f0481200017c8c3e9c0d45c2b12c8a401c0d054200c8440e00017c01401d8da622e14c923f1b8c44e200b0300c00017b78401e0e069301589c441e0cc54230e0581600017aec44204f46d3196ca2471e8cc521c0a0300e00017a61401e8dc672d13c8a3b188b44c1e0d03c0e000179ca47220fc7433174b04d210e05e270f0440e000179493c9c8d6652f95c9a451e0d860270f8581a000178ce3a9b4cc602c14c94421b8c4541e0c844100001783945a04f4713317ca849200e46428100581c000177a646208f67033174aa4e238fc702e1084c0e000177243d1c8d25e2c1449c461f0dc5a250d040120001769e3e1b8ca5d2a930803c190b44619090380c000176173e9d0d2612d9508e3e1a0bc4a200a03c0e00017586441f8e86c31974a2471f0d85c260e04414000174f9431f4e86b3096caa49208d85c240f848100001747d3a9c0d0652d94496471e0c8521f0c8400a00017404391a4c45c2a93890411a8ac481e0b83c0c00017378421f0e66b33984ae4b218e460220c03c0e000172f1411e8de652e95c9c48208e462260d84c1200) else (if i < 12 then 0x1b65e421f4e4682e9549c471f8d85e290e844100001b5d5401d4de662f1689a461d8c44c1d0b8340c0001b5553d1ccd4632e15c9a441d8bc501f0b0380c0001b4d93a1a4ba582913896421d8d85a270e040100001b449441f4ec6f32970a64b208e860270e850140001b3c63e1c0d6642e13c90421b8b856200c04c0e0001b33047214f87135980b451228f468260f04c120001b2ad3e9c8da622d94898431c0ac461d0b03c100001b22d3b9c4d4662c94c92411c8c04c1c0b04c100001b1aa3d9c8d2632d14c96441e8d05c210c840140001b11247210ee6a311649a451f0d85a240c84c180001b08c3e1dce0652f1509c451d8c44c220d850140001b005429f8ea6b321609e471e0d456240d040140001af86399acc65a2993880391a8b04e1f0d0400c0001aef7439fce6673015498461d0d85c260e83c0c0001ae703e9d8d2612c9408e3d198ac3c1d0a0340a0001adec3e9d0d6612c944923f1c0c04c1f0b03c100001ad65401dcda662d14896411c0bc501d0982c0c0001acde3f9e8dc693115c9c461d0bc481f0c054140001ac55401d8de652f15492411b8c052230d844140001abc443a00f27333974ae4c200e05c250e04c120001ab36429f0ea6d31964a249210dc5a250e8500e0001aaa8439fcf06e32174a849200d458210c0300c0001aa21401dce46d2f95c98431d0c454230c0440e0001a99e3f1e4dc682f1609e461e0c45a270d844100001a90b44a04ec67301549c461e0d85a260e850120001a87f421e0e06932160a449210dc54200b8340e0001a7fa3e9d4da68301589e491f0d056240e854160001a7763e9c8da672e95496461e0c450210b83c0c0001a6f63c1ccd6653015894431d8cc56210c0300e0001a6783a9b4c85e2c950943c1a8b04c200c040100001a6053599cc2592992c843d1b8c052200b038120001a574431fce6683015c96411c0bc501f0a83c100001a4e9411dcde642e95896441d0c458210c840120001a4613f9e0de662e94096431e0d85a260f854120001a3e23a1b4c45b281287e37188ac481d0b8380e0001a35b3f1d4d2622c94094411b8c856270d844120001a2d83c9b8ce602d94894451e8cc56220d058140001a25d3a9b4ce5e2b9388c3e1c0c050220d04c120001a1c049210f06f3396cac4e238f068270e8440e0001a12c47210f67535978a84b210e05a250d8500e0001a09d429ece26a31168a247210d860250f060220001a01c3c1c0cc5e2b1388a3c198ac461c0902c0800019f93401f4ea6a30964a449200d854220c83c1000019f103d9c4d4632c140903b1b0c052210d8480e00019e8c3d1c4ce602c15096431d0cc541f0b0401000019dfc431f8e8673116ca2441e8c84c1c0a0301000019d83389a0c0562611c7c35180a4461a0a83c0c00019cf8439f0ea6a31970ac481f0c454220c8440c00019c68441f0ea6f3296ca84d208e864280f8501600019bd944204f06d2f95c96431d8c0501e0b83c1200019b4d429dce066301589a421c8d058230d0401000019ac63e1c8d4622d94498411e8cc56230d0400c00019a443d9ccd6612d14496421d0c84c220e85012000199bb409e4e0662e95894451e8cc5a250d84c1600019933411dce46b3015092421c8bc54200b84014000198ae3e1c8d45e2912c883c1a8bc50230d84c16000198233f9e0e26b32170a0441f0d456230e850120001979d3d9ccd8672d95c96401c8c854200d0481200019712439ece46a2f15c9e481d0c450200b8400e0001968b3f9e0e6682e954a2471c8b84c200b8400e0001960340a00f6713397ca84b208e862270d8440c00019578409d0da642d9489c451f0d85a270c04412000194f3409e4de672f94c8e421e0d858210d0481000 else (if i < 13 then 0x1d7f93a1c0c65d2c14490421c8c052210d8400c0001d76c429e4e0662f14c96421d0d04c1c0b0380c0001d6ea3c1c4d05e2c1448a3b190b04c1e0a8380c0001d66f3a9b4cc5c2a94090411e0cc56230d844100001d5dc431fcec6a3116ca8471d8d05e2910854120001d563391a0ba57289348e3e1a0b4441d0b03c0e0001d4dd411e8e0622e1489e461e0d056230c044120001d45a3e1bccc602d93c8c3f190b84e1f0b838120001d3d63f1d8e0662f9509c471e0d45c220c8340e0001d3553c9c0ce602a13c883f1b0ac481909038100001d2cd419e4e26b3095c9e441e8d45a250d048100001d24d3d1ccd0642e94894401b0b04c200c044100001d1c5401e0e0612c94492401d0d052220d04c140001d135439ece86b3116098451f0dc5c2a0e844120001d0b53c1bcd05e2b1448e401d0c4481a09820080001d02f3f1d8de662e15ca44c218e862290f8581a0001cfa6429fcf06e31970a649208dc60280e04c100001cf19429f8ee6a3296ca44b220f066270e84c0e0001cea4391b0ca5f2b13884421d8d054210d050120001ce1f3e9d8de67301689c461f8d85a230c8400e0001cd98401c8ce5e2c138823b1b0c454200c8380a0001cd06419f4e86c319649e48218e45e230b840140001cc7e3d1c4d4612e1589a451e8d860280f860180001cbfa401d4d8622e944903e1a8c0541d0b02c0c0001cb74411e8e06a30968a4471e8c854200c8501c0001cae8419f8ea6d30960a448208e05e280e848120001ca613d9dcd6662e15098471f8d4501f0c844100001c9dc3d1bccc5d289288a401c8b850210b8380c0001c95d3d1c4d6632d13c8e44200cc56260f050160001c8d4401ece86730970a6471e0d058270f854100001c84f3e9d0dc662e958a048208f462260f054180001c7c93e1d0dc672e15c9c431f0dc561f0d04c140001c740409d0d8622c934903e1a8b44e1f0b840140001c6bf3c1b8ce5f2a928883b1a8ac4a1d0983c0e0001c646389a0c05927924843d1a0bc4a1e098240e0001c5be3f9d8d8622f15096421c8bc4e200c0380c0001c53f3b9bcca5c291287e3b190a4401b0b0400c0001c4b93e9d4d8632e94c94451e0cc56220d84c100001c42c411e0e2652e1549a401b8ac4c1a0a0400c0001c3ae3a1a8ce612b13c8c3d1a8c050210b840160001c32a3d1c0ce612d15098421c8c4521f0b044120001c2a4401d4de662f9589a461d8c052210b83c120001c2253b9b0cc5b2a1287e38168943e19088340c0001c195441f4e66931170aa4b220f462260e054140001c1143e1d0d6622e94896431b8c44e1e0c0440e0001c089419ecde673014890401b0ac4a200b034100001c0043f1c4ce5b299208239178ac461b0982c080001bf75431f4e8692f95098461e0d05c250c84c100001bedf45a04ee6c3095496441e8d45a230c840140001be53409e8e2662f9589c48210e05e260d854140001bdce3e9d8e26a3014892411b0b0481a0a03c140001bd513b1b8c45c2a1388e3f1c0ac481e0b83c100001bcc8401f4e2662f164a4481f8d45a230d848120001bc473d9c8d2622d95096451c0c44e1c0a8300c0001bbb2431ece4662e15ca448208d85c290f84c120001bb2a401d4d6622f160a0461f8d058260d03c100001ba9b449f8e4693195c9a421c8b84e1f0b84c0a0001ba0e421f0ec6c31974a84a210e45c250f84c180001b9943b9c0ce622c94496441c8cc5e270f850160001b909419e8e8683096ca0471e8d054210d048120001b8823f1d8d2632c94898441e0d45a250e03c100001b7f5419f8ec6c2f96ca04a200d454200b840120001b76246204f06f33174a84b1f8e85e220c0400c0001b6e8389a8be5528120803a1a8ac461d0b8400e00 else 0x1f97f409d8da602d14092441d8cc60291004c1a0001f901399b4c85a2a9448e401b0c050230d04c120001f8763f9d4de652f94c96421b8c054230e848120001f7fa399a4c858281207e37178a4421a0b02c080001f7783c9c4d05e2b934883f1b0b04c210b0400c0001f6ec3f9e8e2672e95894441e0dc5a230c8480c0001f6693e1ccd45f2c94c943d1a8b84819090300c0001f5e13e9d0d6622c14090431a8c454250e050100001f567381a0c057279247c38188a8441c0a0380e0001f4d8439f0e2693196ca84b218e05c240c83c100001f44d409f0e66930164a0481f0dc5e240e050160001f3bb45200ea6e3297cae4e228e462280f860160001f3373e9ccd866309649e461e0cc58250d044100001f2b33d9ccdc672f15ca0481e8c452220d854100001f22d3e9d4dc662e95098461f0e056220e044120001f1a53e9d8d8632e9589a441f0dc56220d844140001f12b3a1b4cc612d13c90411e0d858200b0400e0001f0a13f1dce06c30160a24c208e060270e858180001f01e3e1c8c85f2b130883b190ac481c08024060001efa6391a8c65d2a9448a3f1c0c04a1d0a0380a0001ef1e3e9dcd6662f9549c441e0cc56220c0380e0001ee8d45a08f0703497cb04e230f05e250f848120001ee0a3c1c8d2642d95894411c8bc4c1f0a8340c0001ed7b449f8f06b3016ca44a208d856220c83c100001ecf0419f4e66a2f9609c461e8d454240f058100001ec743c1c8d0653015c9e48200d860280f860140001ebed3f9e8ea6c32968a448200c84e220d044140001eb5b45204f6713416ca0461d8c44e200d0400c0001eacc421e0da672f14c9c441c8cc58220b8440c0001ea51399acce632e9589c421f0d058230d850140001e9ce3c1b0c65c29930863a190ac461c0a8300a0001e94a3c1c8d0612c14090411d0c050210d048120001e8d0391b4ce5b299308c3c1a8bc461e0d04c120001e83f419f0e46832974a4471e0dc60260f858100001e7b63f9d8d8643015c9a451c8c856240d0440c0001e72b401d0ce5f2c13c8c401c8c856230e04c180001e69c45210f4743497cb04f238ec68290f0501a0001e6263719cc25b29934863e1a8c8541c0b83c120001e599429fcea6a32168a64b1f8dc60250d848120001e5113e9e4de69301689c481f8e45e2810048100001e489409e8e069309549a441c8cc50230d848120001e4093c9c0d4652f15c9c451e0d45c250e854120001e39b33984b45224108763516898461c0a0240a0001e3163d1c0d2652e968a4491f0d456210d04c0e0001e288439f8e86f33170a84a1f8e060260f04c100001e1f9431ece66d3296ca0481f0d056230d04c100001e1733e9d0da632e1549a441e8cc5c280e844160001e0ef3f1d8e46b31960a0471d8c856270f05c160001e06042a08ec6c30158a04a200d056220d054160001dfd4409e0de622c948923f1a8c44e210d048160001df4d401dce0662e95ca448208dc5c280e848120001decb3e1d8da673015898431c0c4521f0c044120001de473c9c0d2622c94c8c3d1c8bc4c1e0b0340e0001ddbf3e1ccd25f2a938863d198b0461f0c044100001dd383c9c0d6632e14c94421c0bc4e220d03c0e0001dcba399acbe53269188039188a440190a830080001dc343e1d0dc672f1589e461f8dc60260e048180001dbaf3d1d4d6602b9408e401b0b84a1c0b844100001db2d3f1dcd8632c14496431f0c856230d04c180001daa73f9d4d2632c93c883d1d0c050210c044100001da1842a00f87535180ac4d200e85c250e84c100001d98148218f06e33174a449218e06c2a10048100001d8fc3c9c4d6602b94096411a0b44e1e0c844140001d8783e9dce0672f15c9847210d45e250e8441200))) else (if i < 16 then (if i < 15 then 0x21ac2419ece0662f94c96421c8c050210c0441200021a3c3f1d0d8672f15096451f8e45c240d8481a000219c6379a4ca5c2a130883d1b8bc4c1e0b8340c000219503699cbc5627118823b180a44c1d0a8340e000218cb3f1d4de682f95c9c431e8d058220d05012000218453e9ccd6642e9589e47220f064270e85014000217bd409d8dc672f14c96441e0c4521e0d03814000217353f1c8d0632d9509a471e8c84e1e088300e000216aa3f1e0e26a30158a2461e8d456220d0440c0002161a441fcec6d32174a64c200d858260c038100002158f421f0e2652e15098401b0bc56230b8401000021508401dce0682f960a249218e862250d04810000214883c1c4d05d2a93c8a401d0c056230e04c10000214153618cba542691c82391889c401a0a8380e00021386431f0ec6a31168a0461d0d058250e84812000213073b9c0ce5c2a130863c190ac4c200c03c10000212843c1c0d2612c1448e3f1c0b0501f0b04814000211f6431f4e66e31960a04b1f0d45a1f0c8400c000211713e9d0da683095094411d8c856220c0440c000210e0449f8ec6b3115ca2451e8c858230e84c0c000210603d1ccca5d2a9409245200e054220c03c0800020fe53a99cc45c2b1388a3f1a0a8481c0a8301000020f5b409dcdc642d94c94421d0c4581f0c8541600020ecb429f0e2662e950963e1a8b8481f0c8401000020e4a3d1c8d2632e958a0481f8d458240c8401000020dc43f1ccdc622b938923f1b0bc4a1e0b8401200020d37419e0e06d31970a64a1f8d854220d0441200020cb13f1d8da672f14890401a8b4481c0b0381200020c38389a8c65c2a138883b1a0b4481c0b8440e00020baf401d0d6652c94c94411b0b4481c0b8441200020b2d3d1ccd4652d1449640198bc4e1c0d0501200020aa5409d8da652f15498441d8b44e200b8441600020a19421e8e6673196ca64d230ec60260e850120002098b449f4f07133174ae4e238f4662910854180002090c3b9b4d6602c94c98421e0c454250e84c14000208883e1d4d4602c9448c431d0cc56230c03c0e000207f6439ece6652f15498431e0d45a250d048100002077c3a1b0d2612e14490431c0b8481c0b82c0c000206f13f9dcda6630960a247200dc5e29108581a0002066d3e1dce0642e150923f1c8c04a1f0d0440c000205ed3c1b8ca5c2912c803a198bc4e1f0c0340c0002055f421e8e0662d94c98421b0c854210d04c16000204e6389acc45d2b934863b1a8b450220d84814000204713699cc059289288e421b8b84a1e0b84810000203f13d1d4d6602b1488a3c1b0c050200c84812000203733b1bccc5e2a93494421b0bc421c0a0380e000202f03e9d4d2602b94096421c0c04c1b0a83c1200020261409e4da662f15494411d8cc501d0b03c14000201d1439fcf06e31970aa49208e0682c1186418000201483e1c8d6622e13c94411b8b452210c84816000200b5459f8e86d311649e441d0d45a240c84810000200333e1c8da662f9589a441d0cc5a260e048100001ffb63b1bcce5e2c1348a3b190ac4e220c840140001ff2c409e8e66c3216ca64b218dc5a270f854140001fea2401dcda692e14c963f1d0b8501f0b044140001fe1e3d9c8da6a2f95498421d8d05a210d0500e0001fda03c9bcce602c944943f1c8c052230d0400e0001fd15409e8f06e32968a4451f0e05c230c050180001fc9d399b8c85b2a9388e3d190a8481c0b03c0a0001fc1c3c1acd05f2b934883a198a44a1c0b0340e0001fb89449fcee6d33170a84c1f8dc62250e84c100001fb013f9d8e06a3016ca84a210e462260f0480e0001fa8f36194ba57261147e381a0b04c1e0a8380e0001fa0a3d9c8d2612c13c883d1a8c04a200c0381200 else 0x23c2b3a9acce5c2991c803a1b8b0441e0a0340a00023ba83b9c8d6622e9549c421c8c44e1f0d84c0e00023b20409e0d8652d1488c401c8c44c1c0a0340e00023a95401e0de672e94c9a451e0d056240e0481200023a1d389b0ce602a9388c3e1c0cc56200c840120002399c3e1c8d6632e14496411c8c856230c84c140002390d439e4da632f15c9a461c0c04c210c83c120002388f3a9b4ce5d2a9388a3d1a0a44c200a8340c00023817371a8c057269107833170944018098340e0002378f3e9d0d6652e1488c411d8c050200c04014000236ff439ece26630168a84c210d856220d04814000236783f9d0e0682f9609e47200dc5a250e85012000235f33f9e0dc6a30158a0421c8cc58250d8401000023567419f0ec6d32164a44c200e862270f05014000234e33d1c0d05f2c14094431b8c04a200b0400e000234643c9bcd0622b93c923c1b0b44e1f0a0340c000233df3e1c8d8652e14c94411b0c44e200c03812000233603c9d0d2642d1489a461e8d45c230d84810000232db3f1c4d4622d1549e481f0d858240e84812000232543d1d8da652e9589a461f0d054210e04812000231be4620cee6e3317caa4c208e45c220d848160002313d3d1c4d45e2b1308a3f1c8bc4a1f0b0400e000230bf3a1acd05e2a1247c38170a03e160802c0a00023033409cce06630960a0481f0d456220b8480e00022fbd3799cc05c2991c863d1b0b850220b8401000022f31419e8e46b3015c98441d0c856200b8480e00022ea7429e4e0642e94c96401d0c856220c8340600022e1c421ecde662f9649c47200e05e260f0500a00022d973f1d4da632f9549e491f8dc521e0c0340e00022d0f409e8dc652f1589e481f8d0521e0c0400a00022c81431f8e669301589a421c8bc52210d84c1400022c023b9b4cc5d2b950943f1c0c050210c8401000022b7f3d1bcd6632d9408e411c8bc52210c8401000022b05399bcc65a289247c37180a84419090341000022a853c1c0c65c29928883d1b8b84e210b8440e00022a003e1d4d0622d94c923e1c8b84a200d05012000229783f9e4e26a3116098401d0cc5a200d85414000228f63d9d0d86330964a2491e8d85c280f848160002286e421f0e2662e14c96421e8c854260d84c16000227e2421f4ec6f32968a4471f8d4622c1106418000227623c1b8ca5d2b13c92421c0b44e210c83c10000226d8421e0de662f9549c451f0d45c260e85410000226593b1accc602b1308c3a198ac481c0a84810000225d53d9bcc65c2a14092441e8d458230c8400c0002254a421ece4672f9448e3e1a8b8461c0b83408000224c63e1d0d6652f9609e471f8d85a230d040120002243c411f8ea6c3095c9c4a210ec60270e84812000223ba3d9d8d8622e1448c3c198b0461b0a0380c0002233b3d1c8d4612c9448e401b8bc521f0c0340e000222b2409e0de662d1509c461e8d458220e04812000222353b1c0d2632e14c9a431e0dc5e230c04012000221ac411e0dc612d9609e441f0c450210e050160002211945200ec6f3396c9e461e8cc58210c8440c000220933f9e4e4673015896401b8c84e1d0c04412000220103e9d0dc652e15092421d8d45c230d0441000021f87409e0e0672f960a6471e8d456230e0481400021f033f1e4dc642e9509a441c8c852200d0380c00021e7744a0cf67335164a248200dc60240d84c1000021df03d1ccda612c13c94411b0b4481a0802c0a00021d5e45208f47434980ac4b200dc58220b03c0c00021ce03b9c8d6632e9589c481f0d460291004c1200021c5c3d1d0d8652f9549c471f0cc58240e0380e00021bd5401d8e0662f15498421d8cc56260d04c1800021b523e1ccda622e15092421d0bc4e200b83c1200) else (if i < 17 then 0x25d27429f8e8692f14c98461f8d45a250e8400e00025c9d411e4de672e9489a451d8cc54210d0581800025c203a1a8ca612d14092401c8c4501f0d8481000025b9d3d9c0cc5c29924883f1c0c0521f0d0481400025b1f3b9c8d4622d94494401a8c054220c83c0c00025a93411d8d8622e14492411b0c04e200a8300600025a133c1c8d2612d15094481e0d05e280f848120002599a3a1bcc65d2a1288c411b0ac481b0a83814000259183f9dcd6622c94894421d0c858270f84814000258923e9d4d4642f164a247200e05a240e85c140002580d3d9d0da652e15496431d0cc4e1d0b03c0e0002578c3d1c8d6622e9649e421d8c852200d8440e000257073f1d4d4652e9649c481f0d860250d840100002567d409d0d85f2c13c92431d8bc4e200b0440e000255fe391a8ce5e2b93c8e3b198b84e220c03812000255773e9d4d65f2c944923e1c0cc52200a03808000254e4429f8ea6c31968a647208e85e260e04814000254673a9b4ce632f1549a47200d458220c8480c000253e1409e0de652d94c94451d8cc5a230c84014000253663b1c4d0602c14894441d0c44c1f0c8380e000252e33d1c0ce5f2a1388e3d1a8b44a1d0a8340c000252633c1c8d8632d14494451f0d45c270f85818000251e43b9d0d2612c93c8e3f1a8a84c1c0c04812000251623d1ccd8652f9609c461e8d858240d0480c000250dd3d9d0d6632c134883a198b0461a0a8401200025056411ecea6d30964a0461d0bc52200b8400e00024fdc399acc65c2a934883c1b0c4501f0d0480e00024f5c3b1b4c85d2a1348c3e1a0b4481e0c0440e00024ed3409d8de622e94c9a461d8d45a230e0481400024e42431f4e66a2f948943f1a8ac441d0b8481000024dc33b9b8ce5f2e94896421c0c050210b83c0e00024d38411e8e0672f9649c461f0d856230e04c1400024cb33d9ccd6622e14c90401b8bc541f0d84c1800024c3a37198ba552812c86401b0c0501d0a8400800024bb53e1d0da642c938903f1b0c056210d03c1600024b29409d4dc682f95c9c451e0cc52210c04c1200024aab3a1b4ce602d148883c1a8ac421a090300c00024a273c9bcce5e2c14496421c8d05c240c03c0c00024998449f0ec6d32970a64a208d85c260e85c18000249103f9dcd8642e95892411a8c0501d0c04010000248943a1acc85d2a1388c3e198a0441f0b8440e0002480e3f1d4d25e2b14494411b8c856240d050180002477d431fcea693015092421c0c44a1e0c04416000246f2401e4e66b31960a449200e462250e8400e0002466e3e9d4e0652f95498441e8d85c260d84416000245f13b9b0c45d2b14894401a8a8461c0b03412000245703d1c8c85d2a9388c3f1a8b44e1d0b0340e000244e0439f8e8693095c9e481e0d056250d0381000024452409ece0652c1408e401d0bc4e220c04410000243cf3d9ccd85f2b94c94401e8d0501e0c0300c00024346401dcdc642e9509a461d0c452210c04414000242c63b9bcd4622a93886371709c421b0a040100002423e401e4e4692e960a0421e0d052230e84416000241be3b9b4ca5d2b1348e3e1a8b04c200c03c0c000241393d9d8e0662e15ca0461f0d052200d04c16000240ac43208f26d3096c9c45200e05a250e858140002402b3c9ccd6682e94c92431c0b44e1b0983c0e00023f9c441ece0632f1589c461f8d45e250e0601600023f1c3c1ccd6652f954903c188ac441b098280a00023ea5371a0bc572690876341709c401a0a03c0c00023e1d3f9d4d6602d94c94411d0b852220c0340c00023da13c1c0ce5e2b94092421e8d4581f0c8381200023d253a9bcce5f2d14896401e0c858240e84c1200023caa3a1bccc5e2b93c92421c0a44a1b0b02c0800 else (if i < 18 then 0x27e18401e8e46d32978b24e23908702d0f8501800027d943d9b4c85b2b138923e1b8b4481f0a8341200027d01431fcf87436180a84b208dc5c240c0401400027c853c9ccd6602b94898441c8d0541f0c0441400027bfa421d8de682f9589c491f0d054230d84c1000027b763f1dcde6b31160a249200e460250d0381000027b023699cbc5628920863c1b8a44e220d8481800027a87399bcd4632f14894411b8c856250e0501400027a0b399b8cc5b29930823a1a0a8481d098300e0002797f411e0e26e3316ca6461f8d458230e0501000027903389b0ca5d28124883e1c8b0481f0b0301000027878429e8de662e14c9c461f8d85e220b84414000277f73c1c0d0602b1308439188a8461d0a0340a000277703e1c8ce622c94898431c0c052220b84814000276ea3e9d8d8652f14c94421d8c04e1d0b0300a0002766f3a1acce5d2b94096401c0c05a230e05418000275ef3c9c8d6622c95494431c8bc501e0a8401400027568411e8ec6d311709e471e8e45e291085c12000274e0421f4ea6b319549c431d0c054220b8401000027466399b0c85d2c93c883e1b8bc4c1f0c04412000273d64420cf8703295ca0471f0d85a230d04c16000273563d1ccd8662f95c9e451e0c8501f0c84c18000272cf409e8e86b32978a8451d8cc4c210c83c1000027257391a4be5b29928843d1a8b048210c8440e000271dd38198c25b2b128843a1b8b8481e0b84812000271543f9e0e0672e95896431e0d054240e0400e000270d7391a4c65e2a934863d1a0b450230d0440e00027049421ecea6d3296ca24b228e85c220d0481600026fb944a04e66d309689a431d0dc56210d8500e00026f343e1d0dc662e9549a431c8c04a1c0a8301200026eac401dcd8642f15c9e461f8d05e210d0481400026e253e9d8d8663095c9e471d0cc54240c8381000026dad389accc5e2b13c92431d8d050200c0400e00026d2d3a1b0ca5e2b1388e401c0c44e1d0a83c0c00026ca53f1d8d8642f16ca649220ec62280f8582000026c1f401ccd85e2b138883d1b0a84a1b0982c0c00026b93419e0e2682f95496421b8bc4c210d0441400026b143c1c0ce5f2b1348839190ac441a0a02c0c00026a8d3f1d4da642e148a0431d8d05a240d84c1400026a01431f0ee6e319689a431d8d44c200b8481000026989379a0c45c2b138883f1a8cc541f0c0380c00026901409d8da672f95898431e0cc56230d840120002687f3d1d4da662e9549845200e866260f85414000267f83e1d8de682f95896431c8cc52200b834120002676743204f47132180aa4e228ec64291005418000266ee399b4cc5e2b13c94441d0c852210c0380800026668401e4de652f15c9a471e0cc5c260e04c10000265ed3c1bcd05d2c13c8c411d0d0541f0b0380e000265723699cc459289388e401c8c052200c8300c000264e63f9dcd8653016098441e0b844190b83c0e0002645c409e4e2683095894411c0c458250d84814000263e1399a8c45b281208239188a044190b03c0c0002635c3e1c4d8652d14496431d8c454230c84814000262d83d9c8d2612d1549c481e8d458230c03c0c000262513e9d4d8642e15ca24b210e058230e05c18000261cd3d9d8d4622c95092411c8cc56210c03c1200026144411d8d6652d13c9443200d85a280e05014000260bb419d8de6d30968a649218d858230d04816000260363f1dcda642e95498451e0cc54240e04c0a00025fb33e1d0da652f15c9a431d0c052220d03c0c00025f353b1bcd6632d14496421c8c04c1e0b03c1800025eb83b1c0d4632e1489a421f8e05c220d0441400025e363c9c0d2602c144923e1b8b04819060140600025db53b9c4d4642e1448e3f1b8c8521f0c0401000 else 0x29ebf43200ec6c33170a4451d8d058220c0380c00029e403c1bcca58281288a3d1b0b8521e0b8441400029dc83719cc0592a9348a3e1a8b84c1b0b0340e00029d3d419f0e66b31968a64e218e85a240d8501400029cb93d1ccd2612b93c8c3c1a8bc481c0a03c0e00029c3b3b9c0d4632e1489a451f0dc56220d85c1400029bbe3b1b4cc5f2b93c883d198a43e1a0a8401800029b3e3c9bcca5d2b93c903f1c8c85a220d04c1600029aba3c9ccd8662d15092401b8c852200b0340e00029a42381b0c65b2b944943f1a8b44c1f0b03c0c000299bf3e1d8dc632b938883b1d0cc58220b840140002994b37180b654279107e36178ac481d0c0480e000298c63e9c8d2652e15096401c0b84c1e0b0400e0002983642a00ee6d32978ac4a200dc5a260e85012000297b43f9d4d65f2d1388a3d1c8c850240c84c0e0002973a3a9b4c85f2a14090431e8c856230e04814000296be3a9b4c85828924843b1a0bc4e210c0400c00029631421f0e66c309649e471e0c852200c84816000295ad3d9c4d2602c9308a3f1b0b84a1e090300800029524401ccd2602a1348c3c1b0b84c1b080280a000294a73b9c0ce5f2b93c883c1a0b8461c0882810000294253d1ccd6642c1348a3e1b0bc4c210b840120002939f3d1c4d4632b94492401d0c84e220b83c12000293173f1e4e6692f15494411e8d05c220e05814000292933f1e0e0652f14c9a49200dc60250d840140002920f3e1ccd8682f1609c471e8d85c220b8380e0002919a381a4c259289308639190a43e170983c0e0002911f3b1bcd05f2b1408e421d8c44e240e84414000290a4399bcca5e2a9348c3d1c0c450200b83c14000290223c9c4d2652e96098431d8c44c1c098300a00028fa33b1c0d4612d14c96421c8d85c260e0501600028f1c409ece2693095898421d8cc56240d84c1000028e91419e4e06a32174a0481e8d05a240c8501800028e03419ece46931158a0471f0cc54240b8401400028d7b3f9e0e0652e160a0471f8d054230d8481400028cf2419f0e868301649e461d0d458220c8400e00028c6a401d8e26b33180aa4c1f8e05a230d8541600028bee3b1b0c65a29128843b1a8b8441e0b8401400028b64429e4e46d32970b04f218e45c230d0401200028ae23d1d0d8652f9509e481e8d85a240d0381000028a52431ece6693196ca64d210e45a280e04812000289ca3f9dcdc652e9549a441d0cc50200b0481200028942411e0de672e15092401b8b454210c84816000288c93b1b4c25a29928823b188a8461d0983c0c0002884c3c9c8ce612e1549c461d8d05c260d84410000287cb3c1c0d05b299348a39198ac461c0a8400e0002873b431f8e66c33174a44a210e4602a0f85814000286be3a9b8c8632e94c96431d0c44e200b838060002863d3d9d0d6632f9589e4a208e05c250e05c1a000285bf3b1bcca602b93894401c0cc56200d84418000285433a1b0ca5c29928863d1c0b8461b0b0380e000284b9409e8e46a32168a0461e0c852230c03c1000028430419e8de66309609e441e8cc581f0a8340e000283ae3c1b4d0602d14c94431f8cc56230b83410000283303c9c8d6612c14498411c0c050200a8340a0002829e44a00f4703497cac4f210f86a2d1005c140002821c3e9d8d8642e1488e3e1a0bc56230c8340e00028193401d4d6632e1488e431e0d85c250e85016000281113d9ccd2632f15490431b8b44e1e0a8300a00028095391a8c65a2993892411b8b44c1f0b8340e0002801f3699cc056271108037190a040180882c0a00027f993d1d4d4642c94090401c0cc4c200b8340e00027f1e399a4c2572590c763417098421a0a0340c00027e9d3e1d4d8622d9549c48208e05e250f0481200))))) else (if i < 29 then (if i < 24 then (if i < 21 then (if i < 20 then 0x2bf643c9c0c85e2c14494411b8bc4e220c840120002bee83a9a4c45a29940883d1a8b8501f0b838120002be5844208e66b31168a648200e058210c048160002bdda399acc85a27120863a188b0441f0b044140002bd4d3f1dce068301609a471e8cc52220c850160002bcd5381a8c65628920843c1b0a84a1c0b038100002bc4c401e0da652e94c92421d0b84e1e0b83c0e0002bbc73c1b8ca5a29938883e1b8bc4c200c8380c0002bb403f9e0ea6b3216ca84b210d45a260f048120002babf391b4c45a2a1388c3e1a8b84a1e0c054140002ba46371a8c85d2b938883d1a0b850200c8480c0002b9c23f1e0e0672f95c9e441f8d856230d848120002b9423c1c0ce5d29930863d1b0b8461e0a838140002b8c03c9ccd8632d1549a451e8d054200d048180002b847399a4c85b2a1308a3f1c0c052210c83c100002b7c43d1d0da672e94c92421c8c850200c044120002b73c3f1dcd6662d95096421f8c456210b83c160002b6c93618cba5428120843b1a0a8461b090380e0002b63d419f0e26a2e95496441e8cc54250d83c0a0002b5bc3c1bcc85e2b1408e3f1c8c8521d090300a0002b534411e4e2682f95c9c46208e054210c840120002b4ae3f1d8da642d9549c461c0b84e200e04c120002b426421e8e8672f168a24a218e45e250e854180002b3a53b9b0cc602c938883f1b0b0481a0b03c120002b32a3a9bcc85e289288035170903e17098380c0002b2af3a1a4be53271147c35178a4461b0a03c140002b22d3d9c4d05d29928883a178a8481e0a840120002b1a93e1ccda632d144923f1a8c054220d84c140002b121431f0e2652e15092441d0cc54200b0300e0002b0ab391bcca5a2a12c883e1a8bc50200d848120002b01d42a00ea6a3216ca64b218f4722e108601a0002af91419e8ea6b30160a6481e0c856220c048120002af1e34190b4512691c7c36178a4441c098340e0002ae9f3a1a8c05727120823d1b0c04e220c044100002ae1e3d1c8d0602c95092421e0dc501f0b03c120002ad94421f4e4662e1508e3d1c0bc52200b84c100002ad09419e8e4692f958a64a1f0d856220d04c140002ac863d1d4d461299208238190bc4c1d0c0440e0002ac09391a8c85f2c1408c411a8bc4e200c850120002ab7c421e8e2683016ca047200dc5e240d838100002aaf83d9c4cc5c299388e401b8b84e1f0a8380e0002aa783c1bcd05d2a9308c3f1d8b854220b840140002a9f23f1e0de672e94c92411c0b84c220d0480e0002a98036198c45b299308a3b198ac4c210e854160002a8fc3d1bcca5b299147a38190ac441a08834100002a87a3b1c8d4652d140923f1d0c4541f0d0400e0002a7f43d9ccd8652f1589a421c8c452210c0400e0002a7743b9c0d0632d13c923f1c0c04c1d0c850140002a6ea409d4e46a2f9609a451e8d450200a8340c0002a660411ecdc652e15890401d8d056200c0380e0002a5e23b9b8cc602b13c92411c0c452210d040100002a556431f8e8693015896411d8d458250d850160002a4d43c1bcd2602c144903f1b8bc521d0b0300a0002a4513f1e8e46c3095496431d8d458230f050140002a3d03b9bcc85d2b14896431d8d052200e058180002a34d3e1ccd6652f158a44a220ec60260e850100002a2cf3b1b8cc5f2d15894441d8c854220d848160002a24f3d1c8d25f2c1388a39198a8441809834120002a1d7399c4cc5f2a9388c401c8c04a230c040140002a1573b9c0d0612c1448e421c0bc4e200b038100002a0cd411dce2652d95096431c8c456250e040100002a04e3b1acc85d2a934843a1a8b04e200c0441000029fd3391b0ca5c2b934903f1a8c0521f0a82c0600029f49411d8da662f15498451d0d058220c8481200 else 0x2e0003799cc05c2a134863d1b8b4481f0b0380c0002df72421f0e66b321589e471f0cc54260d054120002dee8401dce0662f15c96431e8d056220c83c120002de6c3a9a4c25a271187e39190ac441a0a028060002dde23f9d8da632d1348a3e1b0c050210c850120002dd643b1acc256269107e36190a0461b098300c0002dcd7429f8e66a2f960a0461f8d458210c02c0a0002dc5d3a1b8cc5a2992c84361609842190b038100002dbdc3b9c8da632d15096451e0c850210d048100002db5a3c1bcd2642c144903f1c0cc5220098300c0002dacb421ece06a3196ca8481f8d45c280e050140002da4c3b9bcce622d14896431e0c858220c044100002d9d3389a4c65c2b13c92411c8d854200c848160002d94e409e8dc642e14c96441d0c8501e0b838100002d8c2411e8e46830964a0461e0d058230d8400e0002d84d38198bc58289147a37178ac481d0b038100002d7be431f4ec6b319649e471f8d054220c8400e0002d74b3698cbc5828928883c1b8b84c230d0380e0002d6c2401d8dc652f95c9e471f8cc58260f8480a0002d6463b1bccc5e2b130883b1a0b04c1c0a038140002d5c43d1bcce602a93c96431d8cc58230c03c140002d5403f9e0ea7233178a44b220f8702b100601a0002d4c93899cc05a28924863c1c8c456210c038100002d4443e1ccd8652f168aa4a210e85c260e850180002d3d037998b8552792086401c0b44c1d0a8300c0002d34c3d9c8d2622d148923f1c0c850210b0440c0002d2b54721cf67133174aa4a200e060230d0440a0002d24234988ba5528114843e1b0b44c1e0c0380c0002d1ba3f1c8d0612c94c9e491f8d85e270d044100002d12347210f67234974aa471f0e458260f84c160002d0a03d1c0d2602b94090401c0b852200c048180002d0203d1d0d2642d94490441d0d058230d854180002cfa3389acc85e2c13c8a3a1b0b44c1e0c044180002cf2c38198c05c2b93490401e0e060270d848100002cea63e9d4d6663015c9a421c0b852230c844140002ce22401d0da642d95094401c0c450210b8400c0002cd9e3c1c0cc5f2b93c883a1a8c44a1d0a040100002cd1b3d9c0d2632e95098441f0d85c1f0b8400c0002cc9f3c1c4d6662d944903e1a8ac481e0a83c100002cc18401e4dc642e15098431c0b4481e0a8340c0002cb8c431f0e26930970ae4d228f064260d848100002cb0d3c9ccd6622d14492411b8bc54230f854180002ca8e3c1bcd05e2c1348c3f1d0bc52240d044140002ca05401e0dc662e1509a441e8cc58230d040140002c9813f1c8de672f15c9e4b208e460280e040120002c90a37994bc58281248038170ac441d0b0340c0002c8893b9bcce602d1408e421d8cc58240c844100002c80e399b4cc5a28928843b1a0b450220c04c160002c77d429f8ee70339689e481f0d85e290f854100002c6f1429ece26830970a248200e060250d850140002c6783b9b4c85b2b13c8239198c458230c83c0c0002c5f73c9c4d4632d14090401d0d45a220c03c140002c57a3a9acc85b299388c3d1909840170902c0e0002c4f73c1bcce5d2c13c8c3f1a8b8541f0b0300c0002c4763b9b8d05d2b13c883d190b04c1e0c048120002c3f93a9a0ba592912c8a3c1b8cc58240d854140002c3733e9d4d8652f15898441e8e05e260f054180002c2f23c9c8d2612e95094411b8b050210d0400c0002c2773b9c0ce612d14892411c0b450220d048120002c1ff3a1a8c25b29924803a1b0b8461d0b8300c0002c16e441fcf06b3115c9a461f8d452200d044140002c0f7389a4c45c29120823a180b04e20098300c0002c06d419ece26a2f95c963f1b8cc52230e8400c0002bfe2411dce26830158a4461e8c052200b0441000) else (if i < 22 then 0x30085371a0c25b2991c883f1c8c44a1d0b0400a000300023d1c4d2642f15098431c8d052200c044100002ff7c3e9c4dc662f9649a441e0e05c250c0440c0002fef73d1c4d8622d1489a441d8d05a250d840120002fe723f1d8e06830968a0491f0d85c260d840100002fdf43b9c8d85f2a9348c3f1a8b0481d0a8300e0002fd6e3f1dcde653095494441f0d85a270e854120002fceb3e1d4d4612b93c8c3e198a0441b09038080002fc673e1bcd45e2c948903e1a8ac481d0a040060002fbe13e9d0de662d9509a441d8b8501e0c044140002fb603c1ccdc622b1348c401b0b44e1f0d040160002fadf3d9c8d2602d14892421c8d4561f0b8380e0002fa5c3e1d0d8632e948903d190a8441c0b8380c0002f9df399b0c45c2a930883e1c8c44c230d048160002f95a3d9c4d0622d1408e411c8c4521d078200c0002f8d83b9b4c25d2a938883b188b042180802c080002f8583b9c0cc5f2c13c8c3f180ac4a1f0a034140002f7e634990ba59299308a3e1b8c8501f0a038120002f7693b9b8d261291248638198ac4c1f0b8380e0002f6e83d9c4d6642e9589e471e8d8622a0f85c1a0002f65e3f9e4e2662e950923b1b0b84e1e0a838100002f5e4391b0c45b2913c923f1d0b84c200b8340e0002f569399bcc85e28924863e1b0bc4e210c8380c0002f4e33f1d4d6622c1408c3c1b8b850210d848160002f451441f4e8683096ca6481f0d85c230d0501c0002f3ca409e0e2692f9549c461e8d85c240d040100002f350391b4cc5f2c14898461c0d458220d84c100002f2cd3b1b4ce5f2b144943f1c8b84e200a8300a0002f2463d1ccd8642e9549e471f0e060230d044140002f1c63c9c4cc612c128863d1b0bc542711054120002f13d3f9ccd4622b938943f1c0c054220f044100002f0bd3c1b4c85d2a134863c190b84a210b03c0c0002f0343f9e4de612b1409040190a8481b0a8340c0002efb5399a8c85d2912882391b0b44a1a0a834080002ef383a9bcce5d2a93c8a3d1b8c04e200c03c100002eebc3a1a4c2592a13490431e0cc56210b83c0e0002ee373f9e4e86e321689a431c8c458230d04c120002eda6441f8e26a3216ca0491f8d854240d04c140002ed1b3f1e0e06a2e9549a411d0c854220f04c140002eca13b9c8d4632c94492431c0c852200c844100002ec28389b4cc622c13c92411a8c850220d040100002eba23e9dcda622d94894431c8c84e1e0903c100002eb203d1ccd05d2a93c883a1b0b850210c848120002eaab3a1acc65c289187a35178a0481c0a03c100002ea2a3a9c0cc602e14c94421e0d454230d83c080002e99b431ece06b32974a84f210d85a250f850140002e9193f9e0da672e948943f1a8bc481809838120002e8953e1c8d4622f14c8e3f1d8c04e200a0300c0002e8123d1bcd05f2a9348e3f198c052240e054140002e7913b9c0d2612c140903f1c0b048210c850100002e71b379a0c257281208639198a44a1b0b0380e0002e6973d9c8d2612d93c8c3d1c0bc4e200c844120002e61a3a9b0ce5e2c14c92421d0c4501f0c0400e0002e59e3a1acc45c2b1388e441d8c44c1f0c848100002e51f399b0cc602a9388a3c1a8ac4c1f0a0440e0002e49a3d9d0d6622e14892411d0b0481c0b0380e0002e40f421ece66c30970a4441d8c04e210d848140002e3943a1a4c65d29928843d1a8b44a1c0b0340c0002e3173b1a4c05928938883c1a8b04c210d038140002e2913f1e0e0652e958983f1b0c052210d84c100002e20d3d1c8d0602d9549e4a1e8cc54210c03c140002e193389b4c45a2a9408e3e1b8bc4a1a0b0380e0002e10e3e1d8dc672e14c96421c8b84a1c0b0300c0002e07747a20fc723518cb050238fc6a2c108681400 else (if i < 23 then 0x320f73b9bcd05d2b144863d1c8bc52210d04018000320703f9d4de692e95498421e0d45e230e8481200031fe8409e4e6672d9509c421e8e060290f0441000031f663d9ccd6622d14c8e401a8b04e1e0a8381400031edd3f1d4da6530164a4471e0c8541f0b83c0e00031e603a1bcd25f2b1348c3f1c0c052210d04c1800031dd9409dce26c31970a64b200e458230d8441600031d4e429e8e46b2f15ca048228e4622c0f8481400031cc3439e8ea6e32164a44b210e05c220d0380e00031c433c1b8c85a2891480351609c4217090340c00031bc23d9ccd8622d1408c3e1b0c4561f0c0441600031b39409dce26a31168a4481e0d45620098380a00031ab13f1c4c45f2c14094421d8c052200c8441000031a2b3f9e4dc68309609e461f8ec60240b84c16000319a1431e0e0642e94894431c8c44c210c044180003192b36188ba55271187e37180b04a1e0a03c12000318aa3b1b4ca5c2a9448e431c8c0441a0a8340c00031823401e4e4672e95c9a45208dc5a240d04012000317a7391a0be5a279187c3b198b84c1e0a0300c0003173536990b854259047635180a84416080300a000316b23e1dcd6612b93c8a3f1c8c8521c098300c00031626411e8de6830964a4471e8e862240f85016000315a53c1c4ce5f2b93c8e411b0c04e1f0d84c1a000315273a9b4ce602c948923f1a0b0461c0b04012000314ac389a8ca5a281208439198b0481c0b03c14000314293d1c0d0612c9348c3d1a8b8461a080280c000313ab3c9ccd4612e14892431c8c452220c03c0e0003132a3b9bccc5e2c1448a411d0b04c180a03c0c0003129e429f8ea6b31960a248200e05c250d048140003122b369a0be582a93896441d0c84e210b8380c000311a33f9c8d45e2c9509e461e0d854220c840120003111f3c9c4dc622d9589c411d8d458210b03c16000310a43a9b4ce622d94490441c8c44e1f0b03c1000031017411ece6693195ca2471f8d45e240f0500e00030f903f1d4d8662e9549e451d8c858270d0440e00030f123b1acce632b9408e3e1b8c052210d84c1600030e8e3f1d8de642b93492411a0b84e200c84c1a00030e163699cba5929128823d1b8b4461c0c0400c00030d923f1dcdc663095c9c471e8d056230c0481400030d17381b0cc5b28120863a18098421d0a8340c00030c9a3b9b4ca5e2c14094431c8c856220d8501800030c183c9bcc65c2a1308a3c1a8b44a1c0a83c0c00030b9a3b1b0ca5d2b14096441c0b44c1f0b8381200030b10409e4ea6e34978a6481f0d85a230d0481000030a8c3e1c4d6632d14892421e8cc52210b8440c00030a01409d4e0652d95094461f0dc602a0f04c140003098d3799cc05b291308437180b04c1d0b8440c00030914389acc45d2b138863c1a8c058230e05016000308963c1c8d0622d94496451d8cc5a270f84c18000308143f1d4d45f2b14090421b8b84c1d09820080003078f3e1d8e068309609a451f8c852200b8400c00030718379a4be5928130903e1b8b84a1d0a03414000306a336990b856269188037178a4461d0b83c120003061c401e4e2682f14c96411d8c0501f0a0280a000305a537998be5a29128823e1c8bc54200b83810000305243d1d4d8632e960a84d228e05c280e8541000030497421ece4672d94c9a461f8d056230d03c0e000304153b1c0ce612b94896401d8c84e1e098340e000303913e9ccd2642e1509a3e1b8cc54220e04014000303103d1d4d6602b1388a3a1a0b04a1f0b83412000302903a1b0ca602c13c903f1c8c44e1e0b0440c00030209401ecde642c944903d1c0c854210d0440c000301883c9b8d0622c14496421d8c04e1d0c03c10000300fa441e8d8612b14492421d8c852220d03c1200 else 0x3410d3a1a8c65c299288436188b04a1f0b8340e0003408d3b1ccd0622d95c98411b0b84e220d85c140003400a3d9d8e2662e95498431d0c854220c83c0e00033f9835984ba5829928863c1a8b44e200b03c0c00033f213899cc65d2a1348c3f1c0c856200c04c1400033e9a419f4de642d9589a431e8cc50220b8481000033e0c421dce46c3196ca2481f8d05c220d8541600033d8f3b9bccc5e2b138883d1a8ac481d0b8380e00033d14371a0c85d2b948923f1b0bc4c1a0a0380a00033c903e9d0da6731960a04a1f0d45c240d8481800033c123c9bcca5d29934883c1b0bc54200c8401200033b9c38998ba5529938903f1c8cc4e1f0c8401400033b10421e8de683115ca6491f0d45c29100601c00033a933d1ccda663095ca04a200d460230d8441200033a113d1c8ce5e2d14098471e0c858240f8641e00033989401e0de68309609e46200e458230d85818000339093a1acc65e2a93c923e1b8b4481e0c844160003388d3a9a4c45a289308a3b190a0401908824080003380b3c1d0d85e2b14490431d0c84c1d0c0380e00033790399a8c45c2b13c8c421e0c84c200a83c120003370f3d1ccdc672e1509a471f8cc56220c03c0e0003368c3d1b4ce5f2c150923c1b0b84e200b03c08000336083e1d4d2612d94c92431e0d056230c8440e000335863d9ccd0602d93c883d1a0c4501f0b84412000335083a1b8cc5f2b9348a3c1c0c854230c844140003347f409ecde67301649a491e8d056200b0340a0003340738190b45125108783b188a03e1a0a03810000333883b1b4ca5d29920843b190a844180883812000333083c1ccce5e2b93c8a3a198a8481f0c040140003328e37990b854261107a38198a04419090380e0003320c3c1c0d0602c94494421c0bc4e1d0b83c0c000331853e9d0d4612c1489a451e0d458230d8481a000331053c1c0d6632e94496431d8c452220c03c0c000330803f9d4e06c2f1609c481d8c0521f0c0340c000330023b9ccd6612e14c92441e0d45e240e0400c00032f7e3e9d8dc662d94c94451d0c450220c0440c00032f073899cbc59281248239188a03a170a02c0a00032e833e9c4d8632e95498431f0d052240c8400c00032e1036998be5a2a138823f1b8b44c1d0b8401400032d8543200ee6e3116ca0471f0d458260d0501800032d053d1c8d2602c1489c451f8d85c27100581800032c9934988b653259047836188a4441b0a0341000032c143e9d8dc622d13c92431d8c054250d8401200032b8a401e4e067301589c421a8b0481d0b8481800032b0b3c1c0d0612b934843a198b44a1d0b8340a00032a883e1bcce612d14896431d0c456220b8301000032a0a3919cc05b2a130843b1a0ac4c1f0b83c0e000329863f9dcde662f958a049200e05c240c8441400032911381accc602b14496441f0d45c281006418000328903c1ccd6622e1448e421c0bc4c1b0a03410000328123b1b4c45b2b1388c411c0c04a1f0b03c0a0003278e3d1ccd8632e9589a431d8d0541d0983c0e0003270a3f9e4e2682e13c8c3e1c0b84a200b0380c000326883b1b0cc5f2891c7c3a188b04c1e0a8401000032611371a0be58291348a421d0c052210c840100003258c409e4de642d1488a3b1a0b44a1c0a038060003250b3b9a8c65c2a13c943f1e8d862220d8380c0003248a3e1c8d4632e15c96441e8d85a260f0481200032402419ece6682f15094451b8b8501e0a83c100003237b411e8e4692f958a04b228d05a220d84410000322ec441f8ea683015c9a401b8c850200c04412000322693e1d4ce602b9388e431c8bc58210c84014000321e0409e0e2672e94c90411c8bc4e220c850120003217631970b0542610c7033180a4441a090340800))) else (if i < 26 then (if i < 25 then 0x361193e9d4d4622d94c903f1b8b44e200a8280e000360903e9c8d6632d14092411c0b44c1f0b838100003600b3d1c8d25f2c9408a3f1c8bc501e0b82c1000035f92391b4c85a281147634180a0441e0c0341400035f2334988ba58289248237198a4461c0a8300c00035e98421ecde652e15c9e471f0d454230d0481600035e133d9d0d4632f164ac4f220e8682a1084c1600035d9c38198c25b2a9348a3a190ac46210c0380e00035d213a1a4be5827124843b198a84219098380c00035c9e3d9c8da672f15498421d0cc58210b83c0a00035c1f3a1a8c2592912c883b198ac421d0c0481000035ba13a1bcce602d144903c1a0b4481d0a8401000035b213d9ccce5e2e9509c47208ec64260e04c1200035aa8391b0ca5827124863e1b8b44a1d0b8401000035a243d9dcd8622d9549e48200dc5e250f854140003599c3f1d8da642d9589a461e0d854200c0441400035925379a8c259269187e36160983e160782c080003589e3d9d4d8622e14c9e4a210d45c230c8380a0003582538998bc58281208839188a84a1f0c8380a000357a9399bcd4622d14894421b0c052210c83c0e000357263d9c8d4642d94894431c8c852210b83c10000356a63c9c8d6652e1509a441e0d858230b83c1200035630389acca5f2c14496411c8bc461b0a03408000355a5409ece8673015ca4451c8d058240e0500e000355293b9b8cc602c13c903f1a8a8421a090380a000354af389b0c25826914803a1a8a0421e0b8440e00035425411e0de682e950a44d220e85a270e85816000353b23799cc057271207c35170a048220b0341000035336399b4cc5e2a1288437178a0441c0902c0a000352bb3a1b4c65b28928823c1a8b8501e0b83c060003523f399a8c0592892c883c1a0b0481d0a04014000351af421f8e6682e95c9e46208e054210b0401200035133379a8c85d2992c8c3c1b0a4421b0a84410000350ad3f1dcde662f15098441e0d056220c8401400035033391b4c85d2c15496451e8cc58220c8441000034fad409ece669301649e49200e05e250d8441000034f273f1d0d8602e14494431d8cc56220e04c1600034eac391a8c45e2c14092411c8b4521f0b8441200034e20421f0ec6e35984aa49210d454220c83c0e00034da23a1bcd0622c1448e401c0bc501e0b0300c00034d1f3c1c4d0612c9488c421e8d854210d0401400034c99409e4e4672e950a0471e0cc58230e0441200034c243819cbe55251107833168983c16098340e00034baa399acca5b2913482391a0ac4c1c0b0300c00034b293a1c4da662f15c9c431d0c050210c8441600034aa53d1c8d4622c14092411a0b84a1c0a8381000034a1d411d4da662e1509a441d0bc50230c8501200034994419f0e468311689c431d0d854230e84c0e000349133c9c0d2602a938883e1c8c856200c03c1200034897399a4c65c2a93c943f1c8c84a1d0c03c0e000348153d9c8d6662f14c92401b0c0501b0902c10000347963c9c0d6652d94896441b8b84a1d0b83c100003471c391acc85e2d14092421b8c454250e050180003469a3b9c8ce5e2b94492431c8cc54210b0400a000346123e1d8d8682f95ca6471c0cc58230c0380a0003458f3f9e8e26b301549c451d8d450200c84014000345103c1b8cc602b14492421c0b8461e0b03406000344873f9d8d6642c9448c3e1a0b852210d85018000344003f9d0d2602d93c92401a8b84e1f0c04c140003438a389a0c2572811c8636178b0461c090380c00034310389b0ca612e14c98411b0c44e1f0c848100003429a379a8c454269208037160a0421b0a8380e00034213409d8da682e94492451f8c8501f0b040120003418b3e1c4d2612d1509a441f8cc5a250d8501400 else 0x3815d3e1dcd6642d95492451f0d85e240d84412000380dc3d9c8d6622d15092411d0d05a210b8340a000380593d1d0da663016ca4471f0e85e280e84c0e00037fd73d1c0cc5e2b128863d1b8c04c1f0a8341000037f573c9c0cc5e2b1408a3e1b0b84a1b0a8340800037ed43c1c0ca602e1549848208dc5a220c0300800037e48401e8e0692f95898421c8c452210c03c0c00037dce389a8c85b291187e341709c421a0982c0a00037d4e3c9ccd6662f14c92431f0c856230d0401a00037cd43a1c0ca5e2b140863d1c0b44e210c0380c00037c5a389acc8622e1448e3e1c8b84e1e0c0380e00037bd2409e8e66931178a6461e0d85c260e8541400037b4b3e1ccd6622c950903f1d0c052230b83c0e00037ad53698cbe552690478321689c3c1a0a8281000037a4c3f9e0e6692f170a44b210ec662a0f85814000379c1419e4e8692f15898441e0c04c1e0b03c140003793a3f1dce4682d93c8c3e1b0c8541f0a83410000378cd3498cbc582892c84391a0b0441c0902c10000378513a9acc458279188438198a44019090380c000377d33c1ccd6642d95898441e0cc501f0c84c1200037756389a4c256281187e371889c4219098380a000376c7449e8e069301549a441c0b8521f0d04c14000376413e9d8e0662d15492401a8b0461e0b04c10000375c03b9c0d25e2b9408a3a1909c4a1e0c04010000375403c9b0c65c2a12c8239198ac4a200c83008000374bd3c9bcce602d14492421c8cc501e0c8480e0003744537994be57279187834180a4441b0a84418000373bf3e1c0cc5f29930843d1c8c458230d84c160003733e3c9ccd6632f15c9e48200ec5e270e05010000372c7391acbc58291147a39190b0481e0b02c0a000372493b9b0ce602e140943e1a0b04e200d04814000371c93d1d0d05f2c14c98441e0d458230c844100003715635180b4532610874331608c3c1a0a0340c000370c3441f0e4692f160a44a200d45a260f05816000370413e1d0dc672f15894401c8d45c281085c1600036fc13b9b8d2602b138923e1c8c854240d0481a00036f4d36198c25b2912c843a1a0ac4e1f0c8480e00036ecc3b9b4c25e2d9348c3b190ac481c0a8340e00036e4a3d1d0d6652e94c94401c0c8501e0a8301000036dc3401dcdc6931970aa4e238ec60240c8480e00036d3e3f1d4d6642c94898441d8d8521f0a83c1000036cb83f1d4dc682e9549a431d0c450220e0441400036c3d3a9c0c45929930863b190a8481c098381000036bbf399a4cc622c94896461d0c854230d03c0c00036b3d3c1c4d6632c94092401b8bc4c210e0441400036ab83e1c8d6622b9348c3e1a0b050210d0481200036a35401dce4692d94c96421c8c850210c84814000369ad3f9d4dc662e964a249220f468291185c180003692a3e1c8d05d2a1348c3f1b0c04e1c098340c000368c331974b254259107637198b84619088240a0003684639194c05627120823b1a0ac501f0e04c12000367bf411f4e66c2f95c98441d8c452200c03c10000367483a9b0c65e2b94494441d0b84e1f0c04c14000366c1401d8e0672e9609c48200e05c260f054120003663e3e1c8da642f15c9c461e8d45a290f85012000365b1429f4ec6b3216ca248210e05a230c84c18000365303e1c4ce5e2c94490431e0d456210f05414000364b33a9b8d4602912c8239180ac461b0a03008000364383a9b0c25b2992c863b190b44c1e0d84c0e000363af409e0e0682f1488e3f1c8c050220c84412000363313c1c0d2602d144943e1b0bc46210a84012000362aa401dcda632e9549e451d8d862220c840120003621947218fe763618cb052248f8662b118641e000361a038198be572a1348e3f1a0c44e210b0440c00) else (if i < 27 then 0x3a18a3b1b0ce642b95092401d8c4461c0a8340c0003a10a3b9c4d45f2b9388a3b1b0b8521d0b83c140003a08a3b1b4c45e2a12c86401c0b84e1d0c058140003a0063b9b8cc5c299388c3c1b0b8461d0b8481200039f7942a00ec6e33174aa4b208cc5a260c8400e00039efc3b1ccd8642d14c96411f0e4602a0f0441000039e753f1e0dc662f1609e471e8d8541e0c8380e00039dfe37198c05b2a128843917094421a090340c00039d823a1a0bc56289208039188b04c1e0982c0c00039d0e379a0b85327920863e1c0c44e200e03c1400039c8a3e9e0e2683115c9c481f8d458250c0501400039c0d3a1b8ca5f2b14098411d0b84a1d0d04c1200039b9b35988b652261147834170a04219088340a00039b1c3b9c0d25e2b948923f1a0a84419080280a00039a933f1c8da662f950923e1b8b4481d0a0340e00039a113c9b4cc5f2a9388e401b8b04e1d0a038140003998f3b9c0ce5c299348a3c1a0b04e1f0c83c120003990f3d9d0d25f2d14c9a45200d452220d8440e0003989537998bc55271147637180ac4c1e0c0480e0003981c3919cc059289187433158943a1a090340c000397973f9e0ec6d30968a44c208e056220d04c120003970b409f0e46530964a246208d45e260c85010000396883b9c4d2602d14090421d8cc501e090340a0003960c3b9c4d4602b9488e3d1b0c04e200c0380c00039591399a0c85f2c94092401b8b84c1f0b0400c00039512399bcce5f2d15098411c0c84e200c04010000394913c1c0d2612e1448e401c8d456230c03c0e0003940d3d1c4c65e299448c3b1a8b04c1e0b84012000393903a1acce612a93c8e3b1a0b04a1f0c8340e0003930f3d9d0d8652e15098431f0d456220c83c0e000392893c1b0cc5e29120863e1b8c450220c83c0a000392053e9c0da652c94c98431c8c450210c04812000391893a9c4ce5e2992884391889c4a200a8340e0003910e389a0be56289248c3b1b0bc4e1e0b83c0e000390893c9c4d4662f14c92451e0d458240f0581a0003900f399b4c85b2992c8c3d1a0b84c1d0b0441000038f913c9c8d4622d94492431c0c04c1e0a83c0c00038f0d3d1c4d25f2b93c8c3d1b0b44c200c0400c00038e8f3a9c0ce602a93c8a3d1a0b44e230d0401200038e19379a4c25b2a1308c39180a848190882c0800038da0389b0c65b2a1308a3d1b0c44c1e0b0381000038d1a3f1d0de652d148943e1a8bc561f0b8340e00038c8b429ecec6c3215c9c431d0d45e220d0401200038c093c9ccd6612a94498441f0dc56220d84c1800038b853f1dcd8652d94c90401c0c852220c0481200038b0f3799cbc59291288439180a042190a0380e00038a83401e0d8642d9489c49200e85c260d8380c00038a08399b8c65e2a93490401a8b84c1e0b8380a000389833f9d8dc612d95896431e8c85c250e05816000389093a9acc85c2b934843a190b44e200a8340c00038880409e4d6642f158a247200d058260e04c1600038809391bcd2602b93896451e0c456220e84c12000387823f1d0e0672e15ca0461f8e85e250f85c1a000386f8409e4e06831964a448218e460280e848120003868b32178aa52269148037188a8461e0b0380e00038600411e4de662f15098431e8d856260d84c1800038577401d4da6730964a2481f0e05e230c85010000384f2409f0e66b30968a849208d8581f0b0380c000384793818cc0582791c823c190ac52200b0380c00038400389a8ca602c9448e3d198b4501b0983c0a00038373419dcd8612c93c8c3e1c0b84e1e0b8380a000382e3439f8e6692f94c98471e0dc5e270f05014000382613c1c8d8622d94c96401b8bc50230d05014000381e23b1c0ce5f2a928883f1b8b44e1e0b8380e00 else (if i < 28 then 0x3c1853b1c4d2632c94c90431a0b84a1b09838160003c0fb409e8e46b31160a24a1e8d85e250d04c140003c0753f9d8da622b13c8e3d1a8b8481b0982c0c0003bff33e9d0e0672e14c90441f0e05e230d844140003bf6e3d9d8de652f1589e431e0cc58250b844100003bef837990be58279107e3a198bc4a1c0a8340c0003be763c9c4d0622d94496441e0d4561f0d04c0e0003bdf43c1c4da642c94088401b0b84e1f0b844100003bd6b411e4e06a2f1549c461e0cc54220e850140003bcf2389a4ca622f15094401d0bc4a1e0a840080003bc743b1ccda642f94c923e1b0b8481b0982c0c0003bbf63a1bccc622c1448c3f1e8d858240d8400c0003bb763b1bccc602b9348e3e1b8b84e210c0380e0003bafb3b1c4cc5f2d9589a48208e860260d03c120003ba7a3d9d0d8662e94c98441e8d058230e848140003b9f1401e0dc672e94c96421b8bc4e1e0b8300a0003b96a411e4e0693115896431d0c054200c0300a0003b8f3379a4c45d2c1388c3b180a4401a098380e0003b8763a9acc2582a13c90411d8d05e250f850140003b7e8419e8e06a3015ca04b200cc58210c84c160003b7673b9c0d05f2b1348c3d1c0b0461a0a8340c0003b6ed37198be552711c803b170a8441d0c844140003b66a3e9dcda662e15092421c8c44e1b0c040100003b5df401e4de682e96498451e8e060240e04c140003b5623b9b8ce602b94492401e0b44c1d0b0380c0003b4ee369a4cc5d2b13888401b0b44a210c0340e0003b46b3c9c4d4652e13c90411c8c04a1e0c8440e0003b3e53f9e4e46b32974a64b210e45c250d858180003b3633d1c4cc612c14896411c0c050220e04c120003b2dd3f9c8d05e2b9408e451e8d860260e850140003b2633a1bcd0632e1448a3a1a8c04e200d048180003b1ec399a4ba562610c8038198b84c1e0c0440e0003b164419e8e46c30964a2471f0d054220e048160003b0df3d1c4ca5e2b9388a3e1a8b04e240c84c120003b0623b1b4cc5e2a9308638178a8461d0a82c100003afed391a0bc57291187e3b198b444190982c0c0003af663e1ccda652d94492401d0cc56220d850140003aedc411dce2662e95898471f0d45e2810858160003ae593e1dcda672d94898461d8d45c271004c180003adc9421dce2662e15898471f0cc501e090300e0003ad593296caa4c240fc6a30168943e1809030080003acd23e9d4da622c14896441e8d050210d054160003ac6433978ae52248fc7636160983e1a0882c0a0003abec381a0bc592992c8239190a0441b0b044120003ab6e3b1c4d0602b93c8e411d0bc58230d844100003aaf5389a0ca5d2c144963f1989c421909838100003aa7b3b1b8d0612d94c9a441e0d45a210c8400e0003a9f93c1c8da672f95496461e8d458210c848160003a97a3b9c4d85f2a934843c198ac441f0b838100003a90435990b856279147e39190a044180982c0e0003a88a38994b45327930883b1a8ac4419098340c0003a7f5451f4ec6c3196caa4c228ec682a100601c0003a7733d9d4da622d948923f1e8cc54220d044160003a6ef3e1d4d2622e960a0441d0d054260d04c120003a6753a1b4c65b2a1348e421d8c8501b0b848120003a5fa399a8ca5e2c14494401e0d456230e848100003a58834988b656289247c3717094421c0a0340c0003a5063b1b0c85c2b13c90401c0d45a260d840120003a4853c9c8d4602b1408c3f1b8bc4e200a834100003a4093a1b0ca5e2b9448e3f1b0c04c1e0a8240a0003a37a421e4e2673096ca0451e8cc501e0b840120003a2fb3e1e8e66b321609c48208d45c240c840120003a282371a0be5828128803a190b8461e0a8340c0003a207381a0c25b29128843e1b0c04e200a8300e00 else 0x3e0e13b9b0ce5f2992c823b1909c441d0b038140003e067399acca5b2a1348e401b8bc50220d03c160003dfe13f1d0d4602c9448a3f1c8d050210e044160003df5f3d9ccd8652e9609c481d8d456220c840120003dedd3c9ccda652f950883c1a0ac461b0b83c0c0003de623b1b4d45f2c1389040198b44a1e0c044120003dde4399b0c85c2993c8c401c8c8481c0b0400c0003dd713719cc2562992c863c198b44e200b83c140003dce8411e0e0662e15096431d8c852230d050120003dc693b1b4ca5c2c1509842198a042190882c080003dbeb3b9b4cc5d29938883c1b0c0501f0a8300c0003db71391b4c65c2a12c8037190a8441b0c048140003daf9379a0be592992480351709442190902c080003da7f399b4cc5f2c134883b1a0bc52210d044120003d9fb3f1d8e26831170a64a200e05c240d840140003d97f3a9c0ca5b2a940903f1b0ac441a0b038100003d8f2419e4dc682e95ca04b220f4662b0f85c140003d87c389a0be5a281288435178ac481f0d044100003d7fa3e1d0dc662f940943f1b8b44e210b840100003d78a33994bc59299388839198ac4a200a830100003d711399a4c45d2a12c8238178a0461d0a83c0a0003d69b36994be5728120863a188a8441d0a038100003d6153f1d0d8622d14890441f0d85e250d050120003d59b3819cc25928920823c1a0b0441a098300e0003d52735988b4562891c843b198b04c1d0c040100003d4aa3a9b8ca5b2a128823c198a4441c0b040120003d41f409d4de682f9589a431e8d056210b83c120003d39d3e1c8d25c2a9388e401a8a0421d0a844100003d320391a8c4592a1308c3e1a8b44a1d0b044100003d2aa3718cb851261147c37188b054240d050160003d2283d9ccd45f2c9408a3f1d0cc54220c048140003d19b3f9d8e2662e948903e1a8c052200d050100003d12a34990b64f259107836188a8421b0b83c120003d0a4411ece4682e95896421d0d456210d048160003d03138198bc58299388e3f1b0c04e200b03c0e0003cfb43a9b0ce5e2b1348c401d0d058230c040120003cf303e9d4d8622e1549c471d0d05a200d044120003cea6421f0ec6b31168a64b208e462240d844100003ce2f389a8ca5c2b9348e3f1a0b44e220b838100003cdb7391b4c65a291288a3d1c0d854210c0380e0003cd3f37198c459269187e37180a4481d0a038120003ccbf3d9c8d8662e148943c1b8b84a1d0a83c0e0003cc4b381a8c45e2b9348e3e1c0c456220d848100003cbd03a1acc05b2a12c883b188a8401a0982c0e0003cb503c9bccc5e2b94490401c0cc52220b840100003cae134180b254281207c3b198b042190a8380c0003ca613d9d4da682f1549a421e0cc56240a030120003c9dd3e9e0d2622d94490401b8cc5a220f048120003c9683619cc65b2b1348e421f8d058210e044120003c8e23f9e4e669309649e441f0cc5a240e04c140003c8633d1c4d064309609c431e8d058260e840100003c7ee36998be5a279207e3b190983a17090380c0003c774381a8c45a291187c37198bc4e1a0a038120003c6f63a1b0d05c2a130863f1b8bc4e1d0a8340e0003c67e389b0ce5f2b94892401c0c454210c0340e0003c6033a1b4d0612b934823b1a0b04c1f0b040140003c57b401e0e86930960a0471f8cc56220d04c160003c508369acbc5528120803918098401a0a0380e0003c48f3a1accc602b14490431e0cc56200c048160003c4033f9dcda662e9508e411d8cc5a210b8300c0003c38e37998be57271187a36168a0421c0a82c100003c30b3d1d8e46a301609e441e8d05c270e848140003c285401dce2652c94c92411c0c854200c0380e0003c2073b9b8d2602d1348a3b1a8b04e1d0982c0600)))) else (if i < 34 then (if i < 31 then (if i < 30 then 0x400ce3a1bcca5d2b938923e1b8bc52220d85012000400523a1b8c85b2a1348c411d0d052200d03c0e0003ffe03518cb854271247e3a178a4461c098300e0003ff59401d8e26c32174a449208ec6c2b1105c140003fecd431ecec6f331609c461e8cc5e230e848140003fe463f9d4da682f14092411c0b04c1d0b03c120003fdcb389acc05b2912c8c3d1c8bc4e200c848100003fd433f9ccd8642d144903d1a8b456220b040100003fcc33a9b8c85a2a9388c401c8c04c200b0400c0003fc443a194bc5727928863a190a8421d0a034100003fbc53c1bcd05f2c94896411c8bc50200d850140003fb453b9b8cc5d2892c8a3d1a0b44c1f0c048120003fabe3f1dcd8602c13484391b0c04a1e0c048100003fa4c35188b859281288239188a0461b0a834100003f9cc3c1b0ca5e2d14092421e8c458210d048140003f93e43a04ea6c31970a64a208e05e260f05c1e0003f8c13a9b4c85b29934883d1b0b8441d0983c120003f84a381b0ca5e29930863c1a8ac42190a0340a0003f7d735990be592a93894441d0c4521f0c83c0c0003f76436998c05929120843c190b0481b0982c0e0003f6ed389a4be5829128843f1b0bc481e0a82c0a0003f670389a8c058279187e371709c441b0a0300a0003f5f33a9b8c45b2891c803a1a0bc54210b040140003f5703f1e4e2652f94c92421c8bc541f0c8400e0003f4f33b9c8cc5d2a93c863c1a8b44a1c0a83c160003f4793a9a4c457261147c3a1a0b8441d0c040160003f3ff381a0c85b2a930883e1c8c84c200d048160003f3813c1d0d2652f1509e451f0d85c240c8440e0003f2fe3d9c8cc5f2e14c943f1d0c8562610854140003f27e3c9d4dc642d15496441f8d85c250e0440e0003f2023a1b0d25f2c138863a198ac50210b040100003f1833c1b8cc5c2a1308639190ac441f0b040120003f1013d9d0d6632b93c8a3d180ac421d0a0340c0003f06f459fcea6c3115c9e461e0c858240d850100003eff53919cbe5527920823b198b0461d0982c0a0003ef713e1d8de673116ca6491f8e0602910050140003eef43c1b4cc5c2b93c8c3c1b8c84a1e0a03c120003ee723d9d0e0632c9489a441f8d054220d0380e0003edec3e9dcdc662f14c92411d8b8441a0a02c0e0003ed673e1b8d2622e1589a461f8d05e240f04c120003ece23d9c4d0632c9448a3e1c0c858210d83c0e0003ec57419e0e0672e14c94401d0c054210d850160003ebd13e1d8e268309549a461d0cc56260e8440e0003eb59389acc85b29940903d1b8b8481f0b83c0e0003ead3401e0e06730160a4471e8cc54200a03c100003ea563a1b0ca612c14c923f1a8b44a1e0b8380a0003e9cb411e4e66d3015c9a411c0c856220c84c140003e9463e9d8de6a2e960a4491f0d458240c848120003e8c93b1b8c85e2b938883b1c8c4521c0c0280a0003e8573499cc05b2a138863f1c8c052210b844100003e7dc391a8be57279107e36190b84e220b0380e0003e7543f9e8e66a321649a471e8d852250f83c0c0003e6d5391acc4592912c863b1b8c048190b03c100003e64f409e8de692e148923f1b0d060250d0481c0003e5d2399b8ce612d94896401a8b04c200c83c120003e55b38198be542610c80371809c3a1a0a8300e0003e4dc3b1b0c65e2d1388a3c1a8bc4c1f0c848120003e45d3c9c4d8662d94490401a0ac4a1b09834120003e3de3c1c0d25e2c94494421d8d856220c040140003e36d36190c05a2b1308a3e1b8b450210d840100003e2e43f1e4e4672f95c9c481f0dc56230e050120003e2633d9d0da662f160a04a210e45e230d048160003e1e6399acc85e2a9308c401c0b450230c83c100003e1623d1ccd0602b93c883b1a0b04c1f0b0340600 else 0x4208536184b8542712c8c401b8bc541e0b8440c00042010371a4c45c2a92c823c1a8b8501d090381000041f81449f8ee71321689e461f8d856220c8481800041f0c3719cc05928128823b190ac4a1d0c0440e00041e893d9c0cc5c2a13c92441d0cc54210c04c1400041e043f9e4e46b3095c98461f0cc50220d0381000041d7e3d9c8d4632e14c98441d8c852210b8441200041d0a389a4b852261208035170a04a200b8440e00041c8e3b1c0d0612d9589e431d8b84e1f0d0480e00041c133a1b4c65f2b134823a178b4421c070240600041b9c391a0bc58289208037180ac4c1f0c8381000041b1c3d1bcd4602d14492401c0d05c270f0441600041a963e9ccd2612d9509a441d8d45a270e8581600041a193b9b8c45a29128863a1b0d054230f0641c0004199d3a1acc45c2912c883c1b8b84e220c838120004191d3b9c8d45f2e14494441d8c04a1f0b84816000418983e9dce06a2f9509a471e8d0581f0b848140004181d389a8ce5e2d14490401a8b848210c84012000417983e9d0ce612c14492401d8c84c1d098280c0004172136194c05a2992884391a0ac4a200d04c14000416a9379a8cc5f2c1448c3f1b0c44c1f0a0300e000416273d1ccd8602d9449a471f0d45c220c85016000415a73c1ccd2632c94892411d8d45e260c8440e0004152a3a9b8cc602e14c8e411d8d054220b84410000414be34178b253249187e37178a040190782c080004144c35990be582993c8a3e1c0c44c1d0a03410000413d3391acc85b2a134883d198b84c1d0a8380c000413513d9d8d4632e94892421c8c04a1a0b8380a000412d23b9c4d25f2c94c8e431f8d85c220e85814000412513c9c4ce5e2c944903d1b0c04e200b85010000411c83f1d4dc632e1549e441f0d05a250d8481200041142409d4e267309649e431d0c44c1f0b8340a000410c7399a4c65d2a94492431d0c452220c0400c0004104e381a4c2552812080391a0b0461e0b0401400040fd33a9c0ca5f2a1308a3d1a8c04e1e0c84c0e00040f57391b4c45c2992c8a3b1a0b448200c8441200040ee43799cbc5a29930843c198a8441d0c0401000040e643b9c0d0602b92c90401c0bc4c1e0b8381000040ddd3d9ccda622d1408c3f1b0b04c1f0c03c1200040d6b3619cbc58299288a3b1a0ac4a1a090340c00040ce33e9dcdc662e9549a421c0cc58240f0500e00040c5b401e8de682f15c9c481e0c856210b0380e00040bd4401d8d6632d950983f1d8cc622a108601e00040b4b411e4dc642d95094451d0d056270e8541400040acc3d9c8d4622b134883c1a0b04c1e0a8400c00040a4f399bcce602d140923e1a0b450220c8400c000409ca3c9d0d8642c94896461e0c44c1e0d03c0c000409473e1c8d6622d94494441e0c854230d8480e000408c93a1b8cc5b291388a3c1b0c44e1b0a030060004084b3b9bcd2602b13c8c3f1c0bc4c200e0480e000407c3401d8e2682f95c9a441d0c054220b83c0c0004075233170aa50240fc6e2e1488c401c0a02c0c000406cb3f1e4e4672c9589a421f0d458230f044100004065835184b4512691480391a0bc521d0c83c0e000405d63e1c8d2622c9509a421d0d45a220c8400e000405593b9c0ce5f2b9388a411d8c454210d03c0e000404d93c1bcd05d2a1348c3a188bc501f0d0401000040453401d8e0672e93c92401b0b050210d8480c000403d23c9c4d8672f164a6481d8c85c260e04c1400040347411f0e46a3015ca046200dc5e230d04c1a000402ce389a8c0562912c82391a0c052210d04814000402483f1e4e0693095ca047208d85c240c83410000401cb3b9b8d05f2c94890411e0d05a250d0400e0004014c3c1b4ca5f2a9409c411d8cc56200d8440e00) else (if i < 32 then 0x4404a3d9ccd8632e94c92411e8dc64280f84c1400043fca3d1d8de682e14490401b0bc4c1e0b0381000043f433f1d4d6632d14898421c8d0501e0c8441000043ec73a9b8cc5d2b1348e411d8c450230c0381000043e413f9ccd45e2a92c883c1a8b84e200b8481400043dc6399a8c45a281188039190b4501d0c0341200043d3e429ecea6a3116ca449200d85c200b83c0c00043cca37990bc53249087e39190b0441f0b0301000043c473f1d4dc642f15c98431d0c4541f0c0401200043bd0379a0c459271107635190ac461c0b8480e00043b5738198c05827930883f1c8c050200c0541400043acd419f4ea703316ca4471e0d456230c8480c00043a4b3d9dcde672e15094451e0c050200b84012000439c63e1c0d05e2912c8038198b04e1f0b0480e0004394b391b4ca5c2b1348a3f1c8cc58210e84812000438d636994be5c291308e3d1b0c056220c048120004385e379a4c25a28124863c1b0ac48220b8300e000437e03b9b4c85d2b13c94421b0b450220c04010000437623c1c8d4612d9449646208e056240e04416000436e23c1c8d0652f1549a4a210e4662d0e83c0800043655421ecea6b2f14c94411d8c456240e84c18000435d23c1c8d8632c9489847200d858260d048100004355a379a4c25b281208036170a8461a0983412000434d0401dcdc642d94898461f8d858240f048140004345a34998b853261147835150903c16090300e000433d73b9bcd4672f9549c411c0c0461c0a02c080004335a3a9b4ce602c94c943f1b8b8501e0c0380c000432d73f1d0d0602a1348a421b0b04c1f0c0380c0004325c3b1b0ca602a1308038180b0521e0b04010000431df3c1b8d4612c14c96411d8bc52200d844100004315b3f1d0d8632f15c96401d0bc4e210d03c0a000430e7371a4be5829134883f1a8b84a200b848100004306f36198bc5927920863d198a84c200c8440c00042fe83f9e8e26c309609e461e8d058250f0441600042f7734184b6562892c8a3a180ac4a1c0a83c1000042efa3b9b8c65b28924823b1b0ac4a1d0a0280200042e7a3c1c4d0632e14c963f1a0ac4a200c0400c00042e00391a8c65c2b1488a3e1b0ac4e200d84c1600042d7b3d9c0ce5c2b9308c3f1c0c454210c0441000042cfc3c9ccd05f2b9388a3d1a8b4441b0a0400e00042c7e3d1b4ce5e2c94092421e8d050200d8400e00042c023a9b8ca5e2b94890401c8bc4e1e0c0300a00042b8f36988bc542590c803a198b0481e0b03c0a00042b0a3e1c8d8632d94892401a0b04a18098340a00042a8b3a1b0ca5d2c14496461d8c8501f098380600042a083d9d0d85e2b9408a3b1b0b050200c844140004298e399b0ce612d140923e1a8b0481e0a8381000042902411e0de692f1488e3f1d0cc54240f04c12000428853a9b8ca5c2a930883f198a44a1d0c04416000428033d9c0d4642e950923d1b8bc4c1f0d84c120004278b399b0c85b2892c8438198a03e1c0a8300a0004271636190ba5927928883c1a0ac441b0b0300e00042699391a8c85b29930883c1b8c454230e0501000042611409e8e0652c14090401b8b4401e0a84010000425913a1b4ce59279248037178a0421b0a84012000425163b1bcd2663115c9e461f8d052210b848160004249e391a8ca5f2b13c8e3d1b8c4561e0a03c1000042413411dcde653015498411c0c856240b84014000423943b9bcca5c2b130863c1a8b84e210c844100004230f3f9dce0692f1589e431d0c054230d0380800042287409e8de672f168a448208dc5e240d84814000422053d9e0d05e2c128843a1a8b450200b0380e0004218b3a1b4ca582792c8638188a84a1e0c04010000420f84420d007336174a84b200e058240c83c1000 else (if i < 33 then 0x45fe13719cbc582913890401b0bc501e0a8300e00045f6639198ba5829118803a188ac461d0a8380a00045ee93c1bcd05d2b1308e3f1a8b8481d0c0441200045e693d9c8d4612c1408a411a8b84a230c8441200045de63c9e0de662e94c9c411a0bc481b098280600045d613e1c8d4652d944903d190a44c200c0480e00045ce2391acc85d2b13c8e3d1b8b44c200b8300a00045c5d3d9c4d85f2b94094411d0b8481d0a0341000045bd3409ecea7034174ae4a1e0d058230e0541600045b543c9bccc5f2c15092441d0d05a260f0440e00045acc3e9d0d8642e15092401c0c854220d84c1600045a4f3b1c0ca5e2c13892401a0ac4a1e0a83c0e000459cd3d9c4d8622e14892421d0c454210c034140004594d3d1c0d05f2c12c8c3e1c0bc52200c85016000458d33b1c8ce5c2b93890401b0bc52240d04816000458553a9b0c2582892c863a198ac481e098300e000457ce409e8dc652e14c9c4a1e0cc56230c040100004574b3d9d0ce5e2b94490401b0b4461b0b0400c000456d537994b8582b130863c198b04a1b0b0340a000456573b1acc85b2a13c903f190a8461c0a8440a000455d23f9e8e2682f95098471f8d85c230c848140004555a371a8c4592691c78361889c3c18090340c000454de3a9b8ca602c9388a3d1a0b04a1f0a8380c0004545d3b9c4c65b2a924803a198b04c1d0a83c12000453d83e9dcd8672f95c98441e0d058220a84010000453563b1bcd05e2a1247c35168983e190a83c0e000452e3379a0be54271208438188a442190a03810000452623d9c0ce5d2b13c96421c8b854200d8340c000451d8401e0d6612d14094451e0d45c250e84c100004515d3a9c0d6642e140883f1c0b04c1d0a04012000450ec36194c0572893094411d0c856230d0501200045074359a0c05c2a1347e3a190b04a1f0d0401000044feb401ece66b3015ca249208e058210b8401200044f7435994c059289247e3a1a0c050210e0441000044efc379b0c85929930883f1a8b4481c098340e00044e7d3a1c4d2642e15498411c8bc4e1d0a0240800044e0b35194ba55269108036188a4481f0b83c0a00044d9b3297cb055259107a35160983e1a0a8300c00044d173e9c0ce5e2a92c8e3c1a8c054220b8380800044ca136998be5b289288a3c198b04c1b0a0381000044c1443a00ec6c3196c9a451f0d056200e8501a00044b963b1b4ca602d94892431d0cc58210d83c1000044b123d1c0d0612d14896421d8bc4c1e0a0300e00044a953c1c4d05e2a9388c3e1b0b84e1d0c8481200044a123e1d0d8622d14c903f1b0b0481d0b0380a000449923b9c0cc5f2c14490431e0c854210a8400e000449203518cbe5827920843b1a8b850200e0601e000448a7391a4c0582791c7e38190ac40190782c0c0004482d391a0bc58291308a3a198b44a1e0a03410000447b1399a8c65c2892c8c401c0bc4c210e8481000044738391a8c45c2a9348c3e1b8b84a1d0c04010000446bb391b0c85b2a938903e1b0bc541f0a840120004463e38198c059281208239198b4501c0a8380c000445cd35994bc5a2a934883c1b0b44a1d0b04c140004454f3a19cc258299308c401b8a8441d0a84012000444c3419e8e2662f15c9a421d8c04c230c84416000444413c1c0d8622c9488e421b8b0421b0a83812000443c53d9d0d6662e15092441d0bc4e1f0d84012000443423c9c0d460299348a3c1b8b444180982c08000442bd3f1e4e46b33974a44d220e460270c03c1200044245369a0c2572892c8e3e1b8bc4a1e0a03c0c000441bf3f9ccd4612c93c883a198a4481c0d0480e00044147391a0c45a28120823c190ac4a1e0a0300c000440ce37998be5f29938903f1b8b04817090340c00 else 0x47f4537990c2582712c86401d8bc52220e04c1200047ec83b1b4cc612b1408c401d0d054210d0441000047e50389a8c05b2a130843b198b44c1c098340e00047dd4389acc65a2b1388c3b198b04c1d0c0441200047d5e38198c25b279147a361709c421c0c8481200047ce93618cbe572791c8034168943e1d0b0380e00047c603f9dcd65c2d95090411c0c450200c8401200047be13c1c0d6632d1448a401c8b44c210c0400a00047b57409dcda642e158943c1a8b44619088240c00047ad33c9c0c65e2a93490401c0b4501a0a0340a00047a553b9b8cc622c93c8c3f1a8bc4a1f0b03410000479cd3f9d8e06931168a4481e0cc54220d0541200047952381a0c25a2912c8a3d1b0bc541d0b0300a000478da37194c25829124883b190b0461e0b8401000047850401dcde6a301609c471d8cc56200c0380e000477ca409d0d6632d94898451c8bc541f0c8440e0004775736184b65629930863e1a8bc521e098340e000476d63c9d4d6632d954a0491f8e05a240f04c140004765a391b0c25a2a12c8a3e1a8c056240c83814000475d83d1bcce5f2b12c843d198c056220c84416000475583c1bcd0612b134883b1a0bc48200c04012000474dd391b8cc5f2b140923b190b042190982808000474683819cc2592a1388a3f198a84217090340c000473f03919cbe5b29930883b1c0bc521f0b8480c0004737c37990be58281388a3c1b8b450230c04014000472fe3d1c8d4632d15498441d8cc58210c84414000472813a1b4ca5d2b9388e411b8c050200b8340c000471fb3e9e4e4672e9509846200dc62280f054140004718b36190b652261107a35168943e1a0782c0e0004710d3c9ccd4602a12c883f1c0b8461c0b02c0a0004709537994bc5226118803c190a43a18090340e000470223799cc25c2a1308a3c1c8b84a1c0b0381000046f9d3e1d0d4622c93892411c8c4541e0c0481000046f2f34994c0562791c7a35170a4481b098280a00046eb3391b4c65a291288039198b0481c0982c0e00046e2643204ee6c31170a44a210ec5c260f8481200046db2381a0ba58281288a3e188ac40160802c1000046d26409dcdc652e14c90401c0d04a1e0b83c0c00046ca83a1b4c85a2892c883b1a0b04a1e0c83c0a00046c3136994ba552791c7e37178a4461f0b83c0800046bbd36194bc552510c7e34180ac441c0b0381000046b3c3d1d0d6622b1248039188a8481b0a8341200046ab83d1c0d2612c9448e401c0c454250e8380c00046a393c9d0d2622d94c8e411d0bc56220a04010000469b33f1ccd8672f95896451e8d05c220d044120004693e399a4c45d2a9308639190b0461b098280c000468bd3d9dcda632d94c90441d0d054210d8440e000468363e1dcdc632e1589e451f8d454230e84812000467b63c1acc65a2992c8c401b8b456260d84c12000467433598cb651259107c38178a040190983810000466c53c1c4d4612c13c92421d0cc5a260e85010000466453d9ccce612c94c96451f8d8541e0b8380a000465c13e9ccd8622c9408e3e1b0c850220d0440e000465443b1bccc602c94496411c0c85a240e05014000464b9429f0e2693015c9a471f0d8541f0c03c0a0004643f389b0ca5f2c94c923e1a8c44e200a8340e000463c3399acc8622e14092421d0cc5a240c840100004633e3f1c4d8652f15c9e431d8d456230d84414000462ca379a8c45d29934883d1a0a8461a090340e0004624c3a9c0d05d2b13c903f1c8c04e210c04410000461ce3b1accc5e2b1488c3e1c0bc52240d048120004615637194c45928124883d1b8c852220e84414000460ca419f8f26e321709e481f0cc4a210b844120004605636990be5727130883f1a8b84e1c0b8341000))) else (if i < 36 then (if i < 35 then 0x49e9b3e1d4d8642c94092411a8b8481c0b0441600049e1c3a9b4cc5a29934883b1a8bc481c0b03c1800049da43919cc05727120883d190b44c1b098341000049d2d37190b2542610878371a0b84a1c0a8380e00049caa3c9c8d8642b9348a3d1889c441c098341000049c2c3a1a8c65d2b94092421d0c04c1d0b0340e00049bb63899cc05a291308c421e0c852210c8401400049b39399a8ca5e2c93c8e411d0c454250e8581200049ac435994ba5527924843c1a8ac4a1c0d0480a00049a4a3a1b4ce622d94892421d8cc5c250d0440e000499cb3c1c0c45c2a93c96471e8d85e270e8440c0004994d3a9b4c65d2b93c8e401b0b84a200b8340c000498dc3598cb656259187834168943a180883c0c0004985b3c9ccda672e9609e451d0c856200d04012000497dd3a1bccc602b94490401b0b04c1e0b8440e00049758409e4e6682f95892441d0bc50230b84814000496dc3b1b4ca5c2993894431d8cc58260d04c1a000496693799cc05a28924823d1b0c054230d03814000495f1391c0ce612c14898451e8c04c190a82c08000495733a1b8ca5c29930843b198a4441c0a0340c000494f43b1a4c458291308a401b0bc481d0c0400a000494723c1bcd05e2c14c8e3f1d0c0501f0c8440e000493f93a1a8ca5b291308c3f1a0bc4e1e0b038100004938338198bc5628118803a1789c401c0982c0c000492fb401d8e2682f154a44a1f8dc5a240d84812000492783c1d8d6642e13c92431c8c054220b84418000491f2401ece46c301589c431d8c4521e0b0300c000491733b9b0c65e2b1348a3c1c0c4501f0a838120004910335188b054271147e37178a4421a098340e000490843c1bcd0612c13086401c8b04e210c0440c000490003d1c4ca602c94c94401a8c054210c83c1200048f78401d4da632d94c90431d8c852220c0441400048eff391a4c65d2a1348e421f0dc5c250e8481400048e9233980b45226918803e1c0c052230c8441200048e133b9bcd8672f160a04d228e45e270d8481400048d96399acc65c291348c3d1a0b450210d8581600048d213719cbc53269187634168a4421e0a03c0e00048ca23a1b0c65e2c13c923e1b0bc4e1d0b83c0e00048c2a391acc85c28930843d1c0c054210b8341000048bae3b9c0d05d2b138903e1c0b8481c070280600048b313a1b0c65a289247e3b198b04216088280800048aa1431fcee6b3115c9a45208d854230c0400c00048a293899cc458291348e401d8c454230e04c1a000489ad3b1bcca5c2a134863b1b0b8461c0b8381000048934399b4c85e29930883c1b0bc4a1d0b82c0a000488be3718cb6562711c803a190bc4c1e0b83c0c0004883b3c1c4ca5e2a9448c3e1c8cc581f0c04014000487bd3b1b4c85e2a928843b190b04e1d0b8380e000487413a9b0ca5b29130883e1a8c4561f0e05018000486b7421e8de683095c9c431c0c058210d03c0a000486383c1c0cc602c9448e3d1c8c850220f05016000485bd3a1b8d4612c138883d1a0b44e1f0c038120004853a3d9c4ce602c9488c3d198a8441a0a8340a000484c436198bc58281147e3b1a0b4461d0b03c10000484443c9b8c85d2c14890401c0c050230d8481c000483cb399a4c05a291248038170a4441d0c048160004834d3a1b0ce622e14c98421b8b84a1d0b03c0e000482c83f9d8d6642f154a2481f8d458240e04412000482483d1c4d05e2c94890421b0b44e200b8400e000481c43c1c4d4612c9489646200e462290f04c120004813f3f1ccd8632f15c9c461e0d858240e85014000480bd3e9e4e26a311549e47210e460260d8441000048044391acc259279148039190ac461d098381200047fbc419e4e2662d95c9e471d8cc561f0b8400e00 else 0x4bdef3e9e4de652f1549e441f0d85a230e05c180004bd6f3b1b0c85e2b93c94431c0b8481f0d050140004bce9401e4d8622d95094421d8cc56240f054120004bc6a3e1c8d8642d1408e411c8c852200d844140004bbf1371a8c65b27920823c1b8c854220e058140004bb64429ecea6d3116ca2441c0c054210d044100004baea389bccc622c13888411c8c44c1d0a83c0e0004ba6a3a1acc25b2a1348c3b1b8c0501f0a8300e0004b9f23919cc25c2a94492401b0c456220d84c180004b978391b4ce622e14c9a441d8d456220c8400e0004b8fd399b0c65f2b140883d1b8c850200d038100004b880399a4be59271107a37190a440190a8340a0004b8013b9bcc85c2b130883b198a8461d0b038100004b78c369a0c45a2891c7a37188b04e200c03c140004b70b3c9c0cc5b2a934883d1b8b04a1d0b838100004b69935198be57271188237180a84c1c0b8380e0004b61a3c9c8d8612c94894441b0ac441b0a8300e0004b5953f1d8dc672f1609c49200d85c250d040120004b52534994bc5729128883c1b8b44c1e0c040140004b4ab3819cbc58261188239190ac481d0b83c140004b426409d8d6622e15496451f8d05a260e048140004b3a43e1d8e0682f9589e451d8d0521e0c03c160004b3213e1d8dc632e95ca44c210ec5a220c850160004b2aa37998b85626118803e1a0bc481e0a83c120004b23335994c45b291248439190a84a1d0b038120004b1bc37198ba5b299388e3d1b0b8501e0b8400e0004b1234821cfe7535174a84b218e864260e04c0e0004b0a83b9bcce5f2d138883e1a8b0481c0b84c100004b025401e0e46830160a249218e864270f84c120004afac3a1a8ce602c14c94421e0c44a1d0b03c0c0004af363719cbe5c2a1348a3d1a0ac441909834120004aeb33e9ccdc69301609e411d0d45a240c0380c0004ae39391a0c45b29130843c178a8461d0b834100004adbc3b1b8c45c2a93088401a0b452210b03c0e0004ad4636998c25c2a13488391a0b4521e0b8300e0004accf379a0c0582711c803a1809c3a190a038100004ac47409e0e068309649e461e8d8521f0c8400e0004abd13799cc85b2912c8e401b0c04a1e0c03c0e0004ab57389a4c45928928883f198b44e1f0b840100004aad63a9c0ce622c14090401c0c050210b83c100004aa5f36198c25b2a92888401d0c050200b040100004a9e6391a8c65f2b13c8c3c1a0b44c1e0b8340c0004a97037994c25a2a9288039190b04e210c03c120004a8ec3d1c0d2622d9449a411e0d454220d834100004a871381acc65d2a9348a3e1a8bc50230e04c140004a7e8401d0da622992c863b1a0a4481e0c84c140004a77534990be5628120843a198b04c1d0b840140004a6f33e1dce0682f15490401c8d052210b8380a0004a67e37998bc56279288a3a188a4461b0a83c100004a5ff3c9ccd6602b930803a1689c441c09838100004a573429f0e46a3015c9c481e0cc52230c844120004a4f83a9a4c05627918823b1a0b04c1d0a840100004a4873497cb2522290072321689440160782c0a0004a41535188b65627924803b198b0481a090200c0004a38e3f1d0dc652d94498431e0d05a240c850160004a3083f9d8da622d94490401b8b84c1e0c03c0e0004a29436190b451261147a37178a0401a0a0380e0004a20e411f4ea6a30968a4451f0d460270e060140004a1913a9acc85d2b9408e3d198ac441d0c0340a0004a1173a9b0ca602c1449a411c0c856210c040100004a0923d9ccde652f96ca64a1f8d458200c83c100004a02731970a84f249107c351789c421a0a02c0600049f9743208f07235980b653228e8662a0e04c1200049f1d3b1b4ce5e2a12886401d0cc56240d84c0e00) else (if i < 37 then 0x4dd633d9d0d0632c94094401c0ac4e1c08834100004dce13d1b4d0602c13c8e401d8cc521f0d84c160004dc683a9b8ca5f2c9388e411c8c456230e8400c0004dbe53e1ccda642f94c94421b8bc4c1f0c038140004db7238194b853281247a371a0a8441c0c03c0c0004daf8391a4c45827930883b188ac4e1e0b03c0c0004da7d3a1b0ca5c2b13c943f1b8c454230d050120004da0636998c057281288a3e1b8b44c1e0b03c0e0004d9873b1ccd8622b934903f1c0cc54240d8541a0004d90a399acc85f2c140903f1a0ac4e1f0c044120004d88c3c1c0d4602b138843a190a8481e090380c0004d8103a19cbe592993080391a8b452200c04c160004d7973b1b8cc5d2a13c94441e0c850220d854140004d71e389a8c45e2b14898441c0cc5a230c0400c0004d69f3b1b8ca5e2c94c90401d0c852230d854140004d623391b8d0602d95098451d8d05a250e03c140004d5a83a1b4d2642d95094411d8c4561f0a83c120004d5323899cbe5728924863b180a0461c0b044140004d4ba389b0cc5c2c134883a1889c421c0b028060004d44835984b4552791c7e37160983e19090340e0004d3cc391a4c65c2b1388c3d1c8c052230d840120004d3493c9d0e0672d94098441d0cc50220d040160004d2c93c9bcca602c1408e3c1a8b0441c0b844100004d24b3a1a8c458289348c3f1b8b84e210c040140004d1cd3b1b0c65c2b1308a3c1b0c050210d03c140004d1573819cc45a289287e3a198b44e1d0b0400e0004d0d83b1bcca5b289308a3c1a0b850220e044120004d06137188ba532410c82351689c3a180802c080004cfe03c1c8d05e2a13c8e3e1a8a84a1f0b83c100004cf66399a8c85d2b9388c3f1c8c050210d84c160004cee73d1c4d2602c140903c1c0b84e1f0c0340c0004ce5e401dce2672e9549c431d8cc501f0b83c120004cdd4429dcd45f2c14898401c0c44c1f0c844120004cd573a9acc65b291308a3c1b0bc56230e84c160004ccde37998c25a29124843b180a03e170782c0a0004cc5e3d1c0d2622992888411d0c052210c840160004cbdd3b1c4d6642c93c8e3c1a8b04c1d0a83c0c0004cb5b3c1c4d4602c9448e411c8c858220d854140004cae03b9b0ca5e2b1448e3f1b8c450210c040100004ca6a389b0cc5f2c138843a1a8c44c1e0b840120004c9ea3b1bccc5d2a93894411c0b44a1d0c840100004c9693c9c8d2602c148903e1a0bc501d0c03c0e0004c8eb3b1bccc5f2b9388c3f1a8a8481c0a03c120004c873399b0ce602d14894421c8b84e1e0c03c0e0004c7f03e1ccd05e2c14092441e0c454230d84c160004c7723b9c0d45e299388c411c8c84e200c840120004c6ef3e1d8da673096498411d0d45a240e84c160004c67b381b0ca5c2a1308a3c1c0bc4a1c0a03c0e0004c5f93b9c0d05f2a930883b190b0441e0b0300c0004c57a3b9bcca602c1489a411b8bc50210c848120004c4f83d9d0d8642e95094431b8ac421c098300e0004c47f399bcca5d2b13880381889c441d0a030100004c3ff3c1c8ce5d2b93c92411c8b4441b0a8380c0004c37f3a1b8ce602b93c96441e8d854200c840140004c2fb3e9e4e0663015898451e8d054200b8340c0004c2773d9c8d2622c15094401b0b04a210a83c120004c1ec411e0e26a31170a6491f0d058250e840100004c16e3c9bcd25f2c140903f1b8b44c1f0c0440e0004c0f5369a0c25a2a9388e3d1c0c0461e0d040100004c07a399a8c85b2a12c883f1b8c456220b834080004bffb3b9c0d2632c94090411f0d85e250e050160004bf773d9c4de662e1549a461f0d456200c844120004bef53e1d4dc612c93894421e0d05a230d848120004be733d1c4d0622e15094421e0d452210c8481000 else (if i < 38 then 0x4fc98421f4ec6d32968aa471d0d45a260e050180004fc2337194be5928920863b1a8b8481d0b028060004fba63b1b8cc602d94c98451e0cc56230c03c120004fb283a1acc458299288a431d8cc541e0a0340e0004faa23f9d8e0642f15c9c471e0d856250e848180004fa2c381a0c25c2b138903f1b8b8481d0a83c120004f9ba35984b2532491076301488c3c1709038080004f941381a0c057281288a3e1d0cc56220d8440e0004f8cf35988b855271187835178903c15060280a0004f8543b9c0ce5d2b9388a3d1b0b0441d0a0340c0004f7d73c1c0d2622d1388a3d190a8441b0b040120004f7513e9e0e46b32170a0481c8cc52220d048120004f6d13b1b8c65c299348c3c1b0c04c1f0c84c120004f65c371a0c45d2a13c8c3e1a8b44a1d0a834100004f5e735990c2582a1308c3f1c8c056220b8440c0004f5663d9c4d6612c1408c3b1a8b0461c0a8300e0004f4ea3b1b0ca5d29928883e1b0c04c1e0b0380e0004f4683d1bcca5f2c94c943e1b8c054220b0400e0004f3e93c1c4d8642c94496421c8c456210d040140004f37a33184ae53271147a37190ac44190902c0a0004f2f2401d8dc632e9589a451d8c852200b834100004f27c3699cc057281147635180ac461b0a03c100004f206399b4cc5e2993c843c190ac4a1b098340e0004f17d3e9e8e4672e1448a3f1c0c452240e0500e0004f10a35188b8532590872311589844190983c100004f08f3b9b4cc5e2a92c8c3c190b0461d0b838120004f004411f0e86a2f96094451e0c84c1d0b83c120004ef8f36194b655271147434160983c1707818060004ef1c3598cb853269107a3817898401b09030060004ee9a3c1b8ca5e2c148943f1c0c050220c0340a0004ee1a3b9c0d8642d94090411a0a4441d090380c0004ed95411dce4672f14496421b8c8501f0b02c0a0004ed113c1c8d05d2b13086401a8c44e1b090300c0004ec943a9bcd4612b9388e411c0c0521c0a0400a0004ec163b9d0d25d2a13c92411c0c4561e0d040120004eb9d3799cbc592992c843e1b8b84e210e0501a0004eb2b36988ae4f23908783a178a04a1909834060004eab03919cbc5928924843c198ac441709840100004ea2f3e1bcc45728120883b1a0c052260d048140004e9ab3b9c4d2612d1409a421d8c858230e040140004e9283c1d4da672f9609e451e0c854220c8400c0004e8a93b1b4ca5d2b938943f1b8bc4a1f0b83c0e0004e82d3a9c0d2602c14498451f8e05c260f854140004e7bd35184b6572691c8037188a4461d09030100004e7363f1c8da652d94c9a461e8c8541f0c040120004e6bc3a9a4c45e2b138863b1a8b8501e0b03c0e0004e6403a1a8c85c2993488401d0c44c1e0b8400a0004e5bd3f1d0d0622c9408a3d1b8b84c1f0a8400e0004e53f3c9b4ca602a928863c1a8b44a1c09838060004e4b83f9d4d8632b13c94411e8d45c250d8380e0004e44a34190b253281147a36188a04419078280c0004e3d735194be592a1247e35168a43e1a0a040100004e3533d1ccdc66301549a441d0cc54220c03c0a0004e2d23c1c4cc5d2a13c883d1a8c050220c03c0c0004e2553b1b0cc5f2c94092401c8b44a1a0a83c140004e1c9421ece66c3116896411c8b84c210c03c100004e14c399b8c65d289208236178a44216088340e0004e0d83798cb853261107c37180a04219080300a0004e05e389acc65e2a9348e401d8c452200d040140004dfdd3d1d4dc682f95c9a421d0c052210b8300e0004df4f429f8e66c2f95c94451d8d05c260f050180004ded7371a0c05929128863c1b0bc4c1f0a038100004de6136984b851261047834188983c190a030080004dde43c1bcd05e2b94896451e0c854210d0481600 else 0x5180200000000000000000000000000000000000005177f3d1c0ca5d2a124883d1c0bc481e0b04014000517153217cb051269107a38178a43e1a0a83c0e000516a037198c45d2b12c86391a0a43c18088280a0005161e3d1c4d45f2b93c8c3d1a8b0481f0b844160005159b3d1c0d2612d15096461d8dc5e270f0441000051521391b8c256279248034160983a1a098300a000514a9399a4c055271187c3b188a8421b0a04010000514283a9bccc5e2a12c883d1b8c8581f0b84010000513a73a9b8c8602a93c8e3b178a0441d0a828080005132e3819cbc5526918843a1889c40170a83c0c000512a5421f4e0652e94c96411d8d456220d05c1a0005123135990ba592a9348c3f1b0b454230f05014000511be379a8c25c2a9408c3f1c8b04a1c0c8441400051147371a8c05827924863b198b852210c0300e000510ca3a99cc45c28920843a1a0b856200b840120005105735188b453251007234178903e190a0341200050fd63b9b4ca5c2a9288c431c8c4501e0c0341400050f563c1b8c65a2912884391a0b04a1b0c0440e00050ee634178aa4e249107a38188ac461c0a02c1000050e5d409e0e46c3196c9e4c200dc5a250f0501600050de43b1b0c85d2a9388c3d1b8c454220c0481600050d603e1c4d4642f15c9e46200dc5620090340c00050cd9411d0d8662f14c8c401e0cc56210d0541600050c5b391a0cc602b1388e3e188a8401a070240a00050bdc3d1ccd8642f9649e471f8d458230d03c0800050b5d3c1ccd8652e964a24a208e464250f0581600050aec3598cb4502510876321408c3c180903c0c00050a6d3d1ccce622e95498451e0cc56250c04410000509f5389accc5b2b138903c190a8441b0a0240a000509733b9c8ce5d2c1388a3c1b8bc54230d04c0e000508ee3e1ccd0612b13c94401d0b846190a0441400050872399c0ca5c291188038170943e1a0982408000507f43b1c0cc5e2a13892411c8c4501f0b8340c0005077e381a0bc592791c843a1a0b8481a0983c14000506f93d9d8da642e14c9c451d0cc58210e04c140005068b32978ae51251087c37180b0461a090340a0005060e3b1bcd0622d1448e441e8c456210b8400c000505913a9acca5f2b138923a1b0c052210d8400e0005050e3f9d4d6652f95c9c481f8e456220c84c160005049b34978b25426924823d188ac4e210d84412000504173e9d8d6642d94c9a421c8cc56200b8401200050389411e8e4662f1609e4a210d45a220b0381000050312399b4ce5e2a9308a3c1b0bc4e1f0a8340e0005029a379a0c85a2911c863d1b0b84e210b8380e0005022a34184b85628928843c1b0b84c1d0c03c14000501aa3d9dcda632d14896411d0d056220c82c080005011d429e0e2663116c9e451c0c44c200b8400e000500a13b1c0d0662e95498421d0d054250f048120005001f3d1c4da652f9509a401c0bc4e1f0b038120004ff973f9d0d8642e15ca24b208dc5c250d84c180004ff1b381acc45b2a93c90421c8bc58240e0440c0004fe9b3d9dcda663196ca4491f8dc5e270e050160004fe193a9c0cc602e15498461e0d056260e0580e0004fda0399b4ce602c93888411d0c452220b83c100004fd25399b4c85b279148038190b04a1f0b0401a00))))))

private def checkpoint (i : ℕ) : ℕ :=
  let word := (packet (i/1024) >>> (168*((i%1024)/16))) % (2^168)
  (word >>> 144) + ((word >>> (9*(i%16))) % 512)

private def raw (j : ℕ) : ℕ := fromBlocks checkpoint (fun r => quick (number r)) j

private def small (n : ℕ) : ℕ := if 5≤n then 3 else if 3≤n then 2 else if 2≤n then 1 else 0


def fast (n : ℕ) : ℕ := raw (index n) + small n

private def step (i : ℕ) := checkpoint (i+1) == checkpoint i + tally (fun r => quick (number r)) (32*i) 32

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

private theorem batch0 : covered 0 38 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38 : covered 38 77 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch77 : covered 77 116 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch116 : covered 116 155 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch155 : covered 155 193 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch193 : covered 193 232 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch232 : covered 232 271 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch271 : covered 271 310 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch310 : covered 310 348 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch348 : covered 348 387 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch387 : covered 387 426 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch426 : covered 426 465 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch465 : covered 465 504 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch504 : covered 504 543 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch543 : covered 543 582 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch582 : covered 582 621 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch621 : covered 621 659 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch659 : covered 659 698 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch698 : covered 698 737 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch737 : covered 737 776 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch776 : covered 776 815 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch815 : covered 815 854 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch854 : covered 854 893 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch893 : covered 893 932 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch932 : covered 932 970 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch970 : covered 970 1009 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1009 : covered 1009 1048 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1048 : covered 1048 1087 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1087 : covered 1087 1126 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1126 : covered 1126 1165 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1165 : covered 1165 1204 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1204 : covered 1204 1243 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1243 : covered 1243 1281 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1281 : covered 1281 1320 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1320 : covered 1320 1359 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1359 : covered 1359 1398 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1398 : covered 1398 1437 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1437 : covered 1437 1476 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1476 : covered 1476 1515 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1515 : covered 1515 1554 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1554 : covered 1554 1592 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1592 : covered 1592 1631 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1631 : covered 1631 1670 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1670 : covered 1670 1709 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1709 : covered 1709 1748 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1748 : covered 1748 1787 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1787 : covered 1787 1826 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1826 : covered 1826 1865 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1865 : covered 1865 1903 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1903 : covered 1903 1942 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1942 : covered 1942 1981 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1981 : covered 1981 2020 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2020 : covered 2020 2059 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2059 : covered 2059 2098 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2098 : covered 2098 2137 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2137 : covered 2137 2176 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2176 : covered 2176 2214 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2214 : covered 2214 2253 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2253 : covered 2253 2292 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2292 : covered 2292 2331 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2331 : covered 2331 2370 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2370 : covered 2370 2409 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2409 : covered 2409 2448 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2448 : covered 2448 2487 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2487 : covered 2487 2525 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2525 : covered 2525 2564 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2564 : covered 2564 2603 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2603 : covered 2603 2642 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2642 : covered 2642 2680 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2680 : covered 2680 2719 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2719 : covered 2719 2758 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2758 : covered 2758 2797 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2797 : covered 2797 2835 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2835 : covered 2835 2874 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2874 : covered 2874 2913 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2913 : covered 2913 2952 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2952 : covered 2952 2991 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2991 : covered 2991 3030 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3030 : covered 3030 3069 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3069 : covered 3069 3108 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3108 : covered 3108 3146 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3146 : covered 3146 3185 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3185 : covered 3185 3224 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3224 : covered 3224 3263 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3263 : covered 3263 3302 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3302 : covered 3302 3341 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3341 : covered 3341 3380 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3380 : covered 3380 3419 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3419 : covered 3419 3457 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3457 : covered 3457 3496 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3496 : covered 3496 3535 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3535 : covered 3535 3574 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3574 : covered 3574 3613 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3613 : covered 3613 3652 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3652 : covered 3652 3691 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3691 : covered 3691 3730 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3730 : covered 3730 3768 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3768 : covered 3768 3807 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3807 : covered 3807 3846 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3846 : covered 3846 3885 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3885 : covered 3885 3924 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3924 : covered 3924 3963 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3963 : covered 3963 4002 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4002 : covered 4002 4041 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4041 : covered 4041 4079 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4079 : covered 4079 4118 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4118 : covered 4118 4157 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4157 : covered 4157 4196 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4196 : covered 4196 4235 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4235 : covered 4235 4274 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4274 : covered 4274 4313 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4313 : covered 4313 4352 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4352 : covered 4352 4390 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4390 : covered 4390 4429 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4429 : covered 4429 4468 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4468 : covered 4468 4507 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4507 : covered 4507 4546 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4546 : covered 4546 4585 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4585 : covered 4585 4624 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4624 : covered 4624 4663 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4663 : covered 4663 4701 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4701 : covered 4701 4740 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4740 : covered 4740 4779 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4779 : covered 4779 4818 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4818 : covered 4818 4857 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4857 : covered 4857 4896 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4896 : covered 4896 4935 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4935 : covered 4935 4974 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4974 : covered 4974 5012 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5012 : covered 5012 5051 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5051 : covered 5051 5090 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5090 : covered 5090 5129 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5129 : covered 5129 5167 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5167 : covered 5167 5206 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5206 : covered 5206 5245 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5245 : covered 5245 5284 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5284 : covered 5284 5322 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5322 : covered 5322 5361 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5361 : covered 5361 5400 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5400 : covered 5400 5439 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5439 : covered 5439 5478 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5478 : covered 5478 5517 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5517 : covered 5517 5556 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5556 : covered 5556 5595 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5595 : covered 5595 5633 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5633 : covered 5633 5672 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5672 : covered 5672 5711 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5711 : covered 5711 5750 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5750 : covered 5750 5789 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5789 : covered 5789 5828 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5828 : covered 5828 5867 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5867 : covered 5867 5906 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5906 : covered 5906 5944 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5944 : covered 5944 5983 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5983 : covered 5983 6022 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6022 : covered 6022 6061 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6061 : covered 6061 6100 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6100 : covered 6100 6139 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6139 : covered 6139 6178 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6178 : covered 6178 6217 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6217 : covered 6217 6255 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6255 : covered 6255 6294 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6294 : covered 6294 6333 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6333 : covered 6333 6372 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6372 : covered 6372 6411 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6411 : covered 6411 6450 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6450 : covered 6450 6489 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6489 : covered 6489 6528 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6528 : covered 6528 6566 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6566 : covered 6566 6605 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6605 : covered 6605 6644 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6644 : covered 6644 6683 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6683 : covered 6683 6722 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6722 : covered 6722 6761 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6761 : covered 6761 6800 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6800 : covered 6800 6839 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6839 : covered 6839 6877 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6877 : covered 6877 6916 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6916 : covered 6916 6955 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6955 : covered 6955 6994 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6994 : covered 6994 7033 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7033 : covered 7033 7072 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7072 : covered 7072 7111 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7111 : covered 7111 7150 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7150 : covered 7150 7188 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7188 : covered 7188 7227 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7227 : covered 7227 7266 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7266 : covered 7266 7305 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7305 : covered 7305 7344 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7344 : covered 7344 7383 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7383 : covered 7383 7422 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7422 : covered 7422 7461 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7461 : covered 7461 7499 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7499 : covered 7499 7538 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7538 : covered 7538 7577 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7577 : covered 7577 7616 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7616 : covered 7616 7654 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7654 : covered 7654 7693 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7693 : covered 7693 7732 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7732 : covered 7732 7771 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7771 : covered 7771 7809 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7809 : covered 7809 7848 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7848 : covered 7848 7887 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7887 : covered 7887 7926 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7926 : covered 7926 7965 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7965 : covered 7965 8004 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8004 : covered 8004 8043 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8043 : covered 8043 8082 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8082 : covered 8082 8120 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8120 : covered 8120 8159 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8159 : covered 8159 8198 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8198 : covered 8198 8237 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8237 : covered 8237 8276 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8276 : covered 8276 8315 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8315 : covered 8315 8354 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8354 : covered 8354 8393 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8393 : covered 8393 8431 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8431 : covered 8431 8470 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8470 : covered 8470 8509 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8509 : covered 8509 8548 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8548 : covered 8548 8587 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8587 : covered 8587 8626 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8626 : covered 8626 8665 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8665 : covered 8665 8704 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8704 : covered 8704 8742 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8742 : covered 8742 8781 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8781 : covered 8781 8820 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8820 : covered 8820 8859 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8859 : covered 8859 8898 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8898 : covered 8898 8937 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8937 : covered 8937 8976 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8976 : covered 8976 9015 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9015 : covered 9015 9053 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9053 : covered 9053 9092 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9092 : covered 9092 9131 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9131 : covered 9131 9170 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9170 : covered 9170 9209 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9209 : covered 9209 9248 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9248 : covered 9248 9287 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9287 : covered 9287 9326 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9326 : covered 9326 9364 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9364 : covered 9364 9403 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9403 : covered 9403 9442 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9442 : covered 9442 9481 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9481 : covered 9481 9520 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9520 : covered 9520 9559 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9559 : covered 9559 9598 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9598 : covered 9598 9637 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9637 : covered 9637 9675 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9675 : covered 9675 9714 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9714 : covered 9714 9753 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9753 : covered 9753 9792 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9792 : covered 9792 9831 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9831 : covered 9831 9870 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9870 : covered 9870 9909 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9909 : covered 9909 9948 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9948 : covered 9948 9986 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9986 : covered 9986 10025 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10025 : covered 10025 10064 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10064 : covered 10064 10103 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10103 : covered 10103 10141 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10141 : covered 10141 10180 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10180 : covered 10180 10219 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10219 : covered 10219 10258 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10258 : covered 10258 10296 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10296 : covered 10296 10335 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10335 : covered 10335 10374 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10374 : covered 10374 10413 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10413 : covered 10413 10452 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10452 : covered 10452 10491 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10491 : covered 10491 10530 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10530 : covered 10530 10569 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10569 : covered 10569 10607 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10607 : covered 10607 10646 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10646 : covered 10646 10685 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10685 : covered 10685 10724 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10724 : covered 10724 10763 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10763 : covered 10763 10802 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10802 : covered 10802 10841 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10841 : covered 10841 10880 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10880 : covered 10880 10918 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10918 : covered 10918 10957 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10957 : covered 10957 10996 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10996 : covered 10996 11035 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11035 : covered 11035 11074 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11074 : covered 11074 11113 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11113 : covered 11113 11152 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11152 : covered 11152 11191 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11191 : covered 11191 11229 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11229 : covered 11229 11268 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11268 : covered 11268 11307 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11307 : covered 11307 11346 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11346 : covered 11346 11385 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11385 : covered 11385 11424 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11424 : covered 11424 11463 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11463 : covered 11463 11502 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11502 : covered 11502 11540 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11540 : covered 11540 11579 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11579 : covered 11579 11618 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11618 : covered 11618 11657 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11657 : covered 11657 11696 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11696 : covered 11696 11735 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11735 : covered 11735 11774 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11774 : covered 11774 11813 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11813 : covered 11813 11851 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11851 : covered 11851 11890 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11890 : covered 11890 11929 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11929 : covered 11929 11968 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11968 : covered 11968 12007 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12007 : covered 12007 12046 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12046 : covered 12046 12085 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12085 : covered 12085 12124 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12124 : covered 12124 12162 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12162 : covered 12162 12201 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12201 : covered 12201 12240 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12240 : covered 12240 12279 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12279 : covered 12279 12318 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12318 : covered 12318 12357 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12357 : covered 12357 12396 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12396 : covered 12396 12435 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12435 : covered 12435 12473 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12473 : covered 12473 12512 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12512 : covered 12512 12551 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12551 : covered 12551 12590 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12590 : covered 12590 12628 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12628 : covered 12628 12667 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12667 : covered 12667 12706 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12706 : covered 12706 12745 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12745 : covered 12745 12783 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12783 : covered 12783 12822 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12822 : covered 12822 12861 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12861 : covered 12861 12900 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12900 : covered 12900 12939 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12939 : covered 12939 12978 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12978 : covered 12978 13017 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13017 : covered 13017 13056 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13056 : covered 13056 13094 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13094 : covered 13094 13133 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13133 : covered 13133 13172 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13172 : covered 13172 13211 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13211 : covered 13211 13250 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13250 : covered 13250 13289 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13289 : covered 13289 13328 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13328 : covered 13328 13367 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13367 : covered 13367 13405 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13405 : covered 13405 13444 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13444 : covered 13444 13483 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13483 : covered 13483 13522 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13522 : covered 13522 13561 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13561 : covered 13561 13600 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13600 : covered 13600 13639 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13639 : covered 13639 13678 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13678 : covered 13678 13716 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13716 : covered 13716 13755 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13755 : covered 13755 13794 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13794 : covered 13794 13833 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13833 : covered 13833 13872 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13872 : covered 13872 13911 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13911 : covered 13911 13950 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13950 : covered 13950 13989 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13989 : covered 13989 14027 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14027 : covered 14027 14066 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14066 : covered 14066 14105 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14105 : covered 14105 14144 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14144 : covered 14144 14183 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14183 : covered 14183 14222 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14222 : covered 14222 14261 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14261 : covered 14261 14300 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14300 : covered 14300 14338 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14338 : covered 14338 14377 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14377 : covered 14377 14416 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14416 : covered 14416 14455 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14455 : covered 14455 14494 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14494 : covered 14494 14533 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14533 : covered 14533 14572 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14572 : covered 14572 14611 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14611 : covered 14611 14649 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14649 : covered 14649 14688 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14688 : covered 14688 14727 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14727 : covered 14727 14766 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14766 : covered 14766 14805 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14805 : covered 14805 14844 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14844 : covered 14844 14883 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14883 : covered 14883 14922 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14922 : covered 14922 14960 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14960 : covered 14960 14999 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14999 : covered 14999 15038 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15038 : covered 15038 15077 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15077 : covered 15077 15115 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15115 : covered 15115 15154 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15154 : covered 15154 15193 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15193 : covered 15193 15232 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15232 : covered 15232 15270 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15270 : covered 15270 15309 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15309 : covered 15309 15348 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15348 : covered 15348 15387 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15387 : covered 15387 15426 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15426 : covered 15426 15465 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15465 : covered 15465 15504 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15504 : covered 15504 15543 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15543 : covered 15543 15581 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15581 : covered 15581 15620 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15620 : covered 15620 15659 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15659 : covered 15659 15698 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15698 : covered 15698 15737 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15737 : covered 15737 15776 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15776 : covered 15776 15815 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15815 : covered 15815 15854 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15854 : covered 15854 15892 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15892 : covered 15892 15931 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15931 : covered 15931 15970 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15970 : covered 15970 16009 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16009 : covered 16009 16048 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16048 : covered 16048 16087 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16087 : covered 16087 16126 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16126 : covered 16126 16165 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16165 : covered 16165 16203 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16203 : covered 16203 16242 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16242 : covered 16242 16281 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16281 : covered 16281 16320 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16320 : covered 16320 16359 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16359 : covered 16359 16398 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16398 : covered 16398 16437 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16437 : covered 16437 16476 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16476 : covered 16476 16514 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16514 : covered 16514 16553 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16553 : covered 16553 16592 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16592 : covered 16592 16631 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16631 : covered 16631 16670 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16670 : covered 16670 16709 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16709 : covered 16709 16748 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16748 : covered 16748 16787 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16787 : covered 16787 16825 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16825 : covered 16825 16864 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16864 : covered 16864 16903 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16903 : covered 16903 16942 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16942 : covered 16942 16981 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16981 : covered 16981 17020 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17020 : covered 17020 17059 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17059 : covered 17059 17098 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17098 : covered 17098 17136 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17136 : covered 17136 17175 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17175 : covered 17175 17214 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17214 : covered 17214 17253 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17253 : covered 17253 17292 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17292 : covered 17292 17331 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17331 : covered 17331 17370 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17370 : covered 17370 17409 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17409 : covered 17409 17447 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17447 : covered 17447 17486 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17486 : covered 17486 17525 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17525 : covered 17525 17564 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17564 : covered 17564 17602 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17602 : covered 17602 17641 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17641 : covered 17641 17680 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17680 : covered 17680 17719 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17719 : covered 17719 17757 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17757 : covered 17757 17796 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17796 : covered 17796 17835 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17835 : covered 17835 17874 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17874 : covered 17874 17913 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17913 : covered 17913 17952 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17952 : covered 17952 17991 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17991 : covered 17991 18030 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18030 : covered 18030 18068 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18068 : covered 18068 18107 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18107 : covered 18107 18146 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18146 : covered 18146 18185 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18185 : covered 18185 18224 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18224 : covered 18224 18263 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18263 : covered 18263 18302 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18302 : covered 18302 18341 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18341 : covered 18341 18379 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18379 : covered 18379 18418 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18418 : covered 18418 18457 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18457 : covered 18457 18496 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18496 : covered 18496 18535 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18535 : covered 18535 18574 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18574 : covered 18574 18613 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18613 : covered 18613 18652 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18652 : covered 18652 18690 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18690 : covered 18690 18729 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18729 : covered 18729 18768 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18768 : covered 18768 18807 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18807 : covered 18807 18846 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18846 : covered 18846 18885 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18885 : covered 18885 18924 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18924 : covered 18924 18963 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18963 : covered 18963 19001 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19001 : covered 19001 19040 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19040 : covered 19040 19079 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19079 : covered 19079 19118 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19118 : covered 19118 19157 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19157 : covered 19157 19196 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19196 : covered 19196 19235 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19235 : covered 19235 19274 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19274 : covered 19274 19312 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19312 : covered 19312 19351 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19351 : covered 19351 19390 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19390 : covered 19390 19429 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19429 : covered 19429 19468 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19468 : covered 19468 19507 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19507 : covered 19507 19546 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19546 : covered 19546 19585 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19585 : covered 19585 19623 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19623 : covered 19623 19662 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19662 : covered 19662 19701 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19701 : covered 19701 19740 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19740 : covered 19740 19779 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19779 : covered 19779 19818 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19818 : covered 19818 19857 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19857 : covered 19857 19896 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19896 : covered 19896 19934 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19934 : covered 19934 19973 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19973 : covered 19973 20012 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20012 : covered 20012 20051 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20051 : covered 20051 20089 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20089 : covered 20089 20128 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20128 : covered 20128 20167 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20167 : covered 20167 20206 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20206 : covered 20206 20244 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20244 : covered 20244 20283 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20283 : covered 20283 20322 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20322 : covered 20322 20361 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20361 : covered 20361 20400 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20400 : covered 20400 20439 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20439 : covered 20439 20478 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20478 : covered 20478 20517 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20517 : covered 20517 20555 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20555 : covered 20555 20594 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20594 : covered 20594 20633 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20633 : covered 20633 20672 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20672 : covered 20672 20711 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20711 : covered 20711 20750 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20750 : covered 20750 20789 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20789 : covered 20789 20828 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20828 : covered 20828 20866 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20866 : covered 20866 20905 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20905 : covered 20905 20944 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20944 : covered 20944 20983 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20983 : covered 20983 21022 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21022 : covered 21022 21061 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21061 : covered 21061 21100 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21100 : covered 21100 21139 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21139 : covered 21139 21177 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21177 : covered 21177 21216 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21216 : covered 21216 21255 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21255 : covered 21255 21294 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21294 : covered 21294 21333 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21333 : covered 21333 21372 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21372 : covered 21372 21411 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21411 : covered 21411 21450 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21450 : covered 21450 21488 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21488 : covered 21488 21527 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21527 : covered 21527 21566 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21566 : covered 21566 21605 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21605 : covered 21605 21644 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21644 : covered 21644 21683 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21683 : covered 21683 21722 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21722 : covered 21722 21761 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21761 : covered 21761 21799 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21799 : covered 21799 21838 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21838 : covered 21838 21877 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21877 : covered 21877 21916 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21916 : covered 21916 21955 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21955 : covered 21955 21994 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21994 : covered 21994 22033 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22033 : covered 22033 22072 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22072 : covered 22072 22110 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22110 : covered 22110 22149 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22149 : covered 22149 22188 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22188 : covered 22188 22227 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22227 : covered 22227 22266 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22266 : covered 22266 22305 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22305 : covered 22305 22344 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22344 : covered 22344 22383 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22383 : covered 22383 22421 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22421 : covered 22421 22460 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22460 : covered 22460 22499 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22499 : covered 22499 22538 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22538 : covered 22538 22576 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22576 : covered 22576 22615 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22615 : covered 22615 22654 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22654 : covered 22654 22693 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22693 : covered 22693 22731 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22731 : covered 22731 22770 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22770 : covered 22770 22809 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22809 : covered 22809 22848 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22848 : covered 22848 22887 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22887 : covered 22887 22926 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22926 : covered 22926 22965 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22965 : covered 22965 23004 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23004 : covered 23004 23042 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23042 : covered 23042 23081 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23081 : covered 23081 23120 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23120 : covered 23120 23159 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23159 : covered 23159 23198 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23198 : covered 23198 23237 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23237 : covered 23237 23276 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23276 : covered 23276 23315 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23315 : covered 23315 23353 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23353 : covered 23353 23392 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23392 : covered 23392 23431 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23431 : covered 23431 23470 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23470 : covered 23470 23509 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23509 : covered 23509 23548 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23548 : covered 23548 23587 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23587 : covered 23587 23626 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23626 : covered 23626 23664 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23664 : covered 23664 23703 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23703 : covered 23703 23742 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23742 : covered 23742 23781 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23781 : covered 23781 23820 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23820 : covered 23820 23859 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23859 : covered 23859 23898 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23898 : covered 23898 23937 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23937 : covered 23937 23975 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23975 : covered 23975 24014 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24014 : covered 24014 24053 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24053 : covered 24053 24092 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24092 : covered 24092 24131 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24131 : covered 24131 24170 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24170 : covered 24170 24209 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24209 : covered 24209 24248 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24248 : covered 24248 24286 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24286 : covered 24286 24325 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24325 : covered 24325 24364 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24364 : covered 24364 24403 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24403 : covered 24403 24442 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24442 : covered 24442 24481 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24481 : covered 24481 24520 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24520 : covered 24520 24559 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24559 : covered 24559 24597 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24597 : covered 24597 24636 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24636 : covered 24636 24675 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24675 : covered 24675 24714 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24714 : covered 24714 24753 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24753 : covered 24753 24792 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24792 : covered 24792 24831 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24831 : covered 24831 24870 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24870 : covered 24870 24908 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24908 : covered 24908 24947 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24947 : covered 24947 24986 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24986 : covered 24986 25025 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25025 : covered 25025 25063 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25063 : covered 25063 25102 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25102 : covered 25102 25141 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25141 : covered 25141 25180 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25180 : covered 25180 25218 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25218 : covered 25218 25257 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25257 : covered 25257 25296 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25296 : covered 25296 25335 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25335 : covered 25335 25374 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25374 : covered 25374 25413 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25413 : covered 25413 25452 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25452 : covered 25452 25491 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25491 : covered 25491 25529 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25529 : covered 25529 25568 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25568 : covered 25568 25607 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25607 : covered 25607 25646 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25646 : covered 25646 25685 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25685 : covered 25685 25724 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25724 : covered 25724 25763 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25763 : covered 25763 25802 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25802 : covered 25802 25840 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25840 : covered 25840 25879 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25879 : covered 25879 25918 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25918 : covered 25918 25957 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25957 : covered 25957 25996 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25996 : covered 25996 26035 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26035 : covered 26035 26074 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26074 : covered 26074 26113 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26113 : covered 26113 26151 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26151 : covered 26151 26190 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26190 : covered 26190 26229 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26229 : covered 26229 26268 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26268 : covered 26268 26307 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26307 : covered 26307 26346 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26346 : covered 26346 26385 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26385 : covered 26385 26424 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26424 : covered 26424 26462 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26462 : covered 26462 26501 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26501 : covered 26501 26540 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26540 : covered 26540 26579 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26579 : covered 26579 26618 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26618 : covered 26618 26657 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26657 : covered 26657 26696 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26696 : covered 26696 26735 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26735 : covered 26735 26773 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26773 : covered 26773 26812 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26812 : covered 26812 26851 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26851 : covered 26851 26890 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26890 : covered 26890 26929 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26929 : covered 26929 26968 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch26968 : covered 26968 27007 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27007 : covered 27007 27046 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27046 : covered 27046 27084 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27084 : covered 27084 27123 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27123 : covered 27123 27162 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27162 : covered 27162 27201 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27201 : covered 27201 27240 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27240 : covered 27240 27279 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27279 : covered 27279 27318 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27318 : covered 27318 27357 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27357 : covered 27357 27395 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27395 : covered 27395 27434 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27434 : covered 27434 27473 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27473 : covered 27473 27512 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27512 : covered 27512 27550 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27550 : covered 27550 27589 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27589 : covered 27589 27628 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27628 : covered 27628 27667 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27667 : covered 27667 27705 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27705 : covered 27705 27744 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27744 : covered 27744 27783 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27783 : covered 27783 27822 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27822 : covered 27822 27861 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27861 : covered 27861 27900 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27900 : covered 27900 27939 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27939 : covered 27939 27978 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch27978 : covered 27978 28016 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28016 : covered 28016 28055 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28055 : covered 28055 28094 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28094 : covered 28094 28133 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28133 : covered 28133 28172 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28172 : covered 28172 28211 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28211 : covered 28211 28250 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28250 : covered 28250 28289 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28289 : covered 28289 28327 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28327 : covered 28327 28366 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28366 : covered 28366 28405 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28405 : covered 28405 28444 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28444 : covered 28444 28483 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28483 : covered 28483 28522 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28522 : covered 28522 28561 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28561 : covered 28561 28600 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28600 : covered 28600 28638 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28638 : covered 28638 28677 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28677 : covered 28677 28716 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28716 : covered 28716 28755 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28755 : covered 28755 28794 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28794 : covered 28794 28833 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28833 : covered 28833 28872 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28872 : covered 28872 28911 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28911 : covered 28911 28949 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28949 : covered 28949 28988 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch28988 : covered 28988 29027 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29027 : covered 29027 29066 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29066 : covered 29066 29105 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29105 : covered 29105 29144 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29144 : covered 29144 29183 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29183 : covered 29183 29222 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29222 : covered 29222 29260 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29260 : covered 29260 29299 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29299 : covered 29299 29338 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29338 : covered 29338 29377 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29377 : covered 29377 29416 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29416 : covered 29416 29455 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29455 : covered 29455 29494 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29494 : covered 29494 29533 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29533 : covered 29533 29571 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29571 : covered 29571 29610 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29610 : covered 29610 29649 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29649 : covered 29649 29688 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29688 : covered 29688 29727 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29727 : covered 29727 29766 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29766 : covered 29766 29805 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29805 : covered 29805 29844 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29844 : covered 29844 29882 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29882 : covered 29882 29921 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29921 : covered 29921 29960 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29960 : covered 29960 29999 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch29999 : covered 29999 30037 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30037 : covered 30037 30076 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30076 : covered 30076 30115 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30115 : covered 30115 30154 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30154 : covered 30154 30192 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30192 : covered 30192 30231 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30231 : covered 30231 30270 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30270 : covered 30270 30309 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30309 : covered 30309 30348 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30348 : covered 30348 30387 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30387 : covered 30387 30426 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30426 : covered 30426 30465 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30465 : covered 30465 30503 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30503 : covered 30503 30542 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30542 : covered 30542 30581 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30581 : covered 30581 30620 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30620 : covered 30620 30659 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30659 : covered 30659 30698 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30698 : covered 30698 30737 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30737 : covered 30737 30776 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30776 : covered 30776 30814 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30814 : covered 30814 30853 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30853 : covered 30853 30892 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30892 : covered 30892 30931 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30931 : covered 30931 30970 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch30970 : covered 30970 31009 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31009 : covered 31009 31048 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31048 : covered 31048 31087 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31087 : covered 31087 31125 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31125 : covered 31125 31164 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31164 : covered 31164 31203 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31203 : covered 31203 31242 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31242 : covered 31242 31281 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31281 : covered 31281 31320 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31320 : covered 31320 31359 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31359 : covered 31359 31398 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31398 : covered 31398 31436 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31436 : covered 31436 31475 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31475 : covered 31475 31514 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31514 : covered 31514 31553 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31553 : covered 31553 31592 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31592 : covered 31592 31631 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31631 : covered 31631 31670 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31670 : covered 31670 31709 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31709 : covered 31709 31747 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31747 : covered 31747 31786 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31786 : covered 31786 31825 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31825 : covered 31825 31864 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31864 : covered 31864 31903 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31903 : covered 31903 31942 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31942 : covered 31942 31981 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch31981 : covered 31981 32020 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32020 : covered 32020 32058 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32058 : covered 32058 32097 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32097 : covered 32097 32136 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32136 : covered 32136 32175 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32175 : covered 32175 32214 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32214 : covered 32214 32253 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32253 : covered 32253 32292 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32292 : covered 32292 32331 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32331 : covered 32331 32369 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32369 : covered 32369 32408 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32408 : covered 32408 32447 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32447 : covered 32447 32486 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32486 : covered 32486 32524 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32524 : covered 32524 32563 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32563 : covered 32563 32602 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32602 : covered 32602 32641 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32641 : covered 32641 32679 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32679 : covered 32679 32718 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32718 : covered 32718 32757 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32757 : covered 32757 32796 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32796 : covered 32796 32835 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32835 : covered 32835 32874 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32874 : covered 32874 32913 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32913 : covered 32913 32952 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32952 : covered 32952 32990 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch32990 : covered 32990 33029 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33029 : covered 33029 33068 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33068 : covered 33068 33107 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33107 : covered 33107 33146 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33146 : covered 33146 33185 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33185 : covered 33185 33224 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33224 : covered 33224 33263 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33263 : covered 33263 33301 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33301 : covered 33301 33340 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33340 : covered 33340 33379 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33379 : covered 33379 33418 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33418 : covered 33418 33457 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33457 : covered 33457 33496 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33496 : covered 33496 33535 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33535 : covered 33535 33574 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33574 : covered 33574 33612 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33612 : covered 33612 33651 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33651 : covered 33651 33690 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33690 : covered 33690 33729 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33729 : covered 33729 33768 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33768 : covered 33768 33807 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33807 : covered 33807 33846 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33846 : covered 33846 33885 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33885 : covered 33885 33923 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33923 : covered 33923 33962 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch33962 : covered 33962 34001 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34001 : covered 34001 34040 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34040 : covered 34040 34079 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34079 : covered 34079 34118 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34118 : covered 34118 34157 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34157 : covered 34157 34196 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34196 : covered 34196 34234 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34234 : covered 34234 34273 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34273 : covered 34273 34312 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34312 : covered 34312 34351 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34351 : covered 34351 34390 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34390 : covered 34390 34429 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34429 : covered 34429 34468 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34468 : covered 34468 34507 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34507 : covered 34507 34545 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34545 : covered 34545 34584 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34584 : covered 34584 34623 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34623 : covered 34623 34662 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34662 : covered 34662 34701 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34701 : covered 34701 34740 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34740 : covered 34740 34779 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34779 : covered 34779 34818 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34818 : covered 34818 34856 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34856 : covered 34856 34895 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34895 : covered 34895 34934 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34934 : covered 34934 34973 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch34973 : covered 34973 35011 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35011 : covered 35011 35050 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35050 : covered 35050 35089 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35089 : covered 35089 35128 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35128 : covered 35128 35166 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35166 : covered 35166 35205 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35205 : covered 35205 35244 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35244 : covered 35244 35283 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35283 : covered 35283 35322 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35322 : covered 35322 35361 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35361 : covered 35361 35400 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35400 : covered 35400 35439 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35439 : covered 35439 35477 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35477 : covered 35477 35516 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35516 : covered 35516 35555 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35555 : covered 35555 35594 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35594 : covered 35594 35633 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35633 : covered 35633 35672 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35672 : covered 35672 35711 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35711 : covered 35711 35750 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35750 : covered 35750 35788 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35788 : covered 35788 35827 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35827 : covered 35827 35866 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35866 : covered 35866 35905 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35905 : covered 35905 35944 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35944 : covered 35944 35983 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch35983 : covered 35983 36022 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36022 : covered 36022 36061 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36061 : covered 36061 36099 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36099 : covered 36099 36138 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36138 : covered 36138 36177 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36177 : covered 36177 36216 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36216 : covered 36216 36255 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36255 : covered 36255 36294 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36294 : covered 36294 36333 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36333 : covered 36333 36372 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36372 : covered 36372 36410 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36410 : covered 36410 36449 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36449 : covered 36449 36488 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36488 : covered 36488 36527 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36527 : covered 36527 36566 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36566 : covered 36566 36605 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36605 : covered 36605 36644 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36644 : covered 36644 36683 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36683 : covered 36683 36721 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36721 : covered 36721 36760 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36760 : covered 36760 36799 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36799 : covered 36799 36838 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36838 : covered 36838 36877 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36877 : covered 36877 36916 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36916 : covered 36916 36955 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36955 : covered 36955 36994 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch36994 : covered 36994 37032 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37032 : covered 37032 37071 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37071 : covered 37071 37110 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37110 : covered 37110 37149 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37149 : covered 37149 37188 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37188 : covered 37188 37227 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37227 : covered 37227 37266 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37266 : covered 37266 37305 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37305 : covered 37305 37343 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37343 : covered 37343 37382 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37382 : covered 37382 37421 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37421 : covered 37421 37460 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37460 : covered 37460 37498 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37498 : covered 37498 37537 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37537 : covered 37537 37576 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37576 : covered 37576 37615 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37615 : covered 37615 37653 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37653 : covered 37653 37692 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37692 : covered 37692 37731 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37731 : covered 37731 37770 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37770 : covered 37770 37809 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37809 : covered 37809 37848 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37848 : covered 37848 37887 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37887 : covered 37887 37926 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37926 : covered 37926 37964 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch37964 : covered 37964 38003 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38003 : covered 38003 38042 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38042 : covered 38042 38081 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38081 : covered 38081 38120 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38120 : covered 38120 38159 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38159 : covered 38159 38198 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38198 : covered 38198 38237 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38237 : covered 38237 38275 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38275 : covered 38275 38314 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38314 : covered 38314 38353 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38353 : covered 38353 38392 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38392 : covered 38392 38431 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38431 : covered 38431 38470 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38470 : covered 38470 38509 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38509 : covered 38509 38548 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38548 : covered 38548 38586 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38586 : covered 38586 38625 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38625 : covered 38625 38664 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38664 : covered 38664 38703 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38703 : covered 38703 38742 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38742 : covered 38742 38781 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38781 : covered 38781 38820 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38820 : covered 38820 38859 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38859 : covered 38859 38897 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38897 : covered 38897 38936 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38936 : covered 38936 38975 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch38975 : covered 38975 39014 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39014 : covered 39014 39053 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39053 : covered 39053 39092 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39092 : covered 39092 39131 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39131 : covered 39131 39170 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39170 : covered 39170 39208 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39208 : covered 39208 39247 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39247 : covered 39247 39286 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39286 : covered 39286 39325 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39325 : covered 39325 39364 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39364 : covered 39364 39403 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39403 : covered 39403 39442 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39442 : covered 39442 39481 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39481 : covered 39481 39519 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39519 : covered 39519 39558 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39558 : covered 39558 39597 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39597 : covered 39597 39636 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39636 : covered 39636 39675 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39675 : covered 39675 39714 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39714 : covered 39714 39753 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch39753 : covered 39753 39792 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 15000 in
private theorem allrows : covered 0 39792 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch0 batch38) (joinCoverage batch77 batch116)) (joinCoverage (joinCoverage batch155 batch193) (joinCoverage batch232 batch271))) (joinCoverage (joinCoverage (joinCoverage batch310 batch348) (joinCoverage batch387 batch426)) (joinCoverage (joinCoverage batch465 batch504) (joinCoverage batch543 batch582)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch621 batch659) (joinCoverage batch698 batch737)) (joinCoverage (joinCoverage batch776 batch815) (joinCoverage batch854 batch893))) (joinCoverage (joinCoverage (joinCoverage batch932 batch970) (joinCoverage batch1009 batch1048)) (joinCoverage (joinCoverage batch1087 batch1126) (joinCoverage batch1165 batch1204))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch1243 batch1281) (joinCoverage batch1320 batch1359)) (joinCoverage (joinCoverage batch1398 batch1437) (joinCoverage batch1476 batch1515))) (joinCoverage (joinCoverage (joinCoverage batch1554 batch1592) (joinCoverage batch1631 batch1670)) (joinCoverage (joinCoverage batch1709 batch1748) (joinCoverage batch1787 batch1826)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch1865 batch1903) (joinCoverage batch1942 batch1981)) (joinCoverage (joinCoverage batch2020 batch2059) (joinCoverage batch2098 batch2137))) (joinCoverage (joinCoverage (joinCoverage batch2176 batch2214) (joinCoverage batch2253 batch2292)) (joinCoverage (joinCoverage batch2331 batch2370) (joinCoverage batch2409 batch2448)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch2487 batch2525) (joinCoverage batch2564 batch2603)) (joinCoverage (joinCoverage batch2642 batch2680) (joinCoverage batch2719 batch2758))) (joinCoverage (joinCoverage (joinCoverage batch2797 batch2835) (joinCoverage batch2874 batch2913)) (joinCoverage (joinCoverage batch2952 batch2991) (joinCoverage batch3030 batch3069)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch3108 batch3146) (joinCoverage batch3185 batch3224)) (joinCoverage (joinCoverage batch3263 batch3302) (joinCoverage batch3341 batch3380))) (joinCoverage (joinCoverage (joinCoverage batch3419 batch3457) (joinCoverage batch3496 batch3535)) (joinCoverage (joinCoverage batch3574 batch3613) (joinCoverage batch3652 batch3691))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch3730 batch3768) (joinCoverage batch3807 batch3846)) (joinCoverage (joinCoverage batch3885 batch3924) (joinCoverage batch3963 batch4002))) (joinCoverage (joinCoverage (joinCoverage batch4041 batch4079) (joinCoverage batch4118 batch4157)) (joinCoverage (joinCoverage batch4196 batch4235) (joinCoverage batch4274 batch4313)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch4352 batch4390) (joinCoverage batch4429 batch4468)) (joinCoverage (joinCoverage batch4507 batch4546) (joinCoverage batch4585 batch4624))) (joinCoverage (joinCoverage (joinCoverage batch4663 batch4701) (joinCoverage batch4740 batch4779)) (joinCoverage (joinCoverage batch4818 batch4857) (joinCoverage batch4896 batch4935))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch4974 batch5012) (joinCoverage batch5051 batch5090)) (joinCoverage (joinCoverage batch5129 batch5167) (joinCoverage batch5206 batch5245))) (joinCoverage (joinCoverage (joinCoverage batch5284 batch5322) (joinCoverage batch5361 batch5400)) (joinCoverage (joinCoverage batch5439 batch5478) (joinCoverage batch5517 batch5556)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch5595 batch5633) (joinCoverage batch5672 batch5711)) (joinCoverage (joinCoverage batch5750 batch5789) (joinCoverage batch5828 batch5867))) (joinCoverage (joinCoverage (joinCoverage batch5906 batch5944) (joinCoverage batch5983 batch6022)) (joinCoverage (joinCoverage batch6061 batch6100) (joinCoverage batch6139 batch6178))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch6217 batch6255) (joinCoverage batch6294 batch6333)) (joinCoverage (joinCoverage batch6372 batch6411) (joinCoverage batch6450 batch6489))) (joinCoverage (joinCoverage (joinCoverage batch6528 batch6566) (joinCoverage batch6605 batch6644)) (joinCoverage (joinCoverage batch6683 batch6722) (joinCoverage batch6761 batch6800)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch6839 batch6877) (joinCoverage batch6916 batch6955)) (joinCoverage (joinCoverage batch6994 batch7033) (joinCoverage batch7072 batch7111))) (joinCoverage (joinCoverage (joinCoverage batch7150 batch7188) (joinCoverage batch7227 batch7266)) (joinCoverage (joinCoverage batch7305 batch7344) (joinCoverage batch7383 batch7422)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch7461 batch7499) (joinCoverage batch7538 batch7577)) (joinCoverage (joinCoverage batch7616 batch7654) (joinCoverage batch7693 batch7732))) (joinCoverage (joinCoverage (joinCoverage batch7771 batch7809) (joinCoverage batch7848 batch7887)) (joinCoverage (joinCoverage batch7926 batch7965) (joinCoverage batch8004 batch8043)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch8082 batch8120) (joinCoverage batch8159 batch8198)) (joinCoverage (joinCoverage batch8237 batch8276) (joinCoverage batch8315 batch8354))) (joinCoverage (joinCoverage (joinCoverage batch8393 batch8431) (joinCoverage batch8470 batch8509)) (joinCoverage (joinCoverage batch8548 batch8587) (joinCoverage batch8626 batch8665))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch8704 batch8742) (joinCoverage batch8781 batch8820)) (joinCoverage (joinCoverage batch8859 batch8898) (joinCoverage batch8937 batch8976))) (joinCoverage (joinCoverage (joinCoverage batch9015 batch9053) (joinCoverage batch9092 batch9131)) (joinCoverage (joinCoverage batch9170 batch9209) (joinCoverage batch9248 batch9287)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch9326 batch9364) (joinCoverage batch9403 batch9442)) (joinCoverage (joinCoverage batch9481 batch9520) (joinCoverage batch9559 batch9598))) (joinCoverage (joinCoverage (joinCoverage batch9637 batch9675) (joinCoverage batch9714 batch9753)) (joinCoverage (joinCoverage batch9792 batch9831) (joinCoverage batch9870 batch9909)))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch9948 batch9986) (joinCoverage batch10025 batch10064)) (joinCoverage (joinCoverage batch10103 batch10141) (joinCoverage batch10180 batch10219))) (joinCoverage (joinCoverage (joinCoverage batch10258 batch10296) (joinCoverage batch10335 batch10374)) (joinCoverage (joinCoverage batch10413 batch10452) (joinCoverage batch10491 batch10530)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch10569 batch10607) (joinCoverage batch10646 batch10685)) (joinCoverage (joinCoverage batch10724 batch10763) (joinCoverage batch10802 batch10841))) (joinCoverage (joinCoverage (joinCoverage batch10880 batch10918) (joinCoverage batch10957 batch10996)) (joinCoverage (joinCoverage batch11035 batch11074) (joinCoverage batch11113 batch11152))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch11191 batch11229) (joinCoverage batch11268 batch11307)) (joinCoverage (joinCoverage batch11346 batch11385) (joinCoverage batch11424 batch11463))) (joinCoverage (joinCoverage (joinCoverage batch11502 batch11540) (joinCoverage batch11579 batch11618)) (joinCoverage (joinCoverage batch11657 batch11696) (joinCoverage batch11735 batch11774)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch11813 batch11851) (joinCoverage batch11890 batch11929)) (joinCoverage (joinCoverage batch11968 batch12007) (joinCoverage batch12046 batch12085))) (joinCoverage (joinCoverage (joinCoverage batch12124 batch12162) (joinCoverage batch12201 batch12240)) (joinCoverage (joinCoverage batch12279 batch12318) (joinCoverage batch12357 batch12396)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch12435 batch12473) (joinCoverage batch12512 batch12551)) (joinCoverage (joinCoverage batch12590 batch12628) (joinCoverage batch12667 batch12706))) (joinCoverage (joinCoverage (joinCoverage batch12745 batch12783) (joinCoverage batch12822 batch12861)) (joinCoverage (joinCoverage batch12900 batch12939) (joinCoverage batch12978 batch13017)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch13056 batch13094) (joinCoverage batch13133 batch13172)) (joinCoverage (joinCoverage batch13211 batch13250) (joinCoverage batch13289 batch13328))) (joinCoverage (joinCoverage (joinCoverage batch13367 batch13405) (joinCoverage batch13444 batch13483)) (joinCoverage (joinCoverage batch13522 batch13561) (joinCoverage batch13600 batch13639))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch13678 batch13716) (joinCoverage batch13755 batch13794)) (joinCoverage (joinCoverage batch13833 batch13872) (joinCoverage batch13911 batch13950))) (joinCoverage (joinCoverage (joinCoverage batch13989 batch14027) (joinCoverage batch14066 batch14105)) (joinCoverage (joinCoverage batch14144 batch14183) (joinCoverage batch14222 batch14261)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch14300 batch14338) (joinCoverage batch14377 batch14416)) (joinCoverage (joinCoverage batch14455 batch14494) (joinCoverage batch14533 batch14572))) (joinCoverage (joinCoverage (joinCoverage batch14611 batch14649) (joinCoverage batch14688 batch14727)) (joinCoverage (joinCoverage batch14766 batch14805) (joinCoverage batch14844 batch14883))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch14922 batch14960) (joinCoverage batch14999 batch15038)) (joinCoverage (joinCoverage batch15077 batch15115) (joinCoverage batch15154 batch15193))) (joinCoverage (joinCoverage (joinCoverage batch15232 batch15270) (joinCoverage batch15309 batch15348)) (joinCoverage (joinCoverage batch15387 batch15426) (joinCoverage batch15465 batch15504)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch15543 batch15581) (joinCoverage batch15620 batch15659)) (joinCoverage (joinCoverage batch15698 batch15737) (joinCoverage batch15776 batch15815))) (joinCoverage (joinCoverage (joinCoverage batch15854 batch15892) (joinCoverage batch15931 batch15970)) (joinCoverage (joinCoverage batch16009 batch16048) (joinCoverage batch16087 batch16126))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch16165 batch16203) (joinCoverage batch16242 batch16281)) (joinCoverage (joinCoverage batch16320 batch16359) (joinCoverage batch16398 batch16437))) (joinCoverage (joinCoverage (joinCoverage batch16476 batch16514) (joinCoverage batch16553 batch16592)) (joinCoverage (joinCoverage batch16631 batch16670) (joinCoverage batch16709 batch16748)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch16787 batch16825) (joinCoverage batch16864 batch16903)) (joinCoverage (joinCoverage batch16942 batch16981) (joinCoverage batch17020 batch17059))) (joinCoverage (joinCoverage (joinCoverage batch17098 batch17136) (joinCoverage batch17175 batch17214)) (joinCoverage (joinCoverage batch17253 batch17292) (joinCoverage batch17331 batch17370)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch17409 batch17447) (joinCoverage batch17486 batch17525)) (joinCoverage (joinCoverage batch17564 batch17602) (joinCoverage batch17641 batch17680))) (joinCoverage (joinCoverage (joinCoverage batch17719 batch17757) (joinCoverage batch17796 batch17835)) (joinCoverage (joinCoverage batch17874 batch17913) (joinCoverage batch17952 batch17991)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch18030 batch18068) (joinCoverage batch18107 batch18146)) (joinCoverage (joinCoverage batch18185 batch18224) (joinCoverage batch18263 batch18302))) (joinCoverage (joinCoverage (joinCoverage batch18341 batch18379) (joinCoverage batch18418 batch18457)) (joinCoverage (joinCoverage batch18496 batch18535) (joinCoverage batch18574 batch18613))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch18652 batch18690) (joinCoverage batch18729 batch18768)) (joinCoverage (joinCoverage batch18807 batch18846) (joinCoverage batch18885 batch18924))) (joinCoverage (joinCoverage (joinCoverage batch18963 batch19001) (joinCoverage batch19040 batch19079)) (joinCoverage (joinCoverage batch19118 batch19157) (joinCoverage batch19196 batch19235)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch19274 batch19312) (joinCoverage batch19351 batch19390)) (joinCoverage (joinCoverage batch19429 batch19468) (joinCoverage batch19507 batch19546))) (joinCoverage (joinCoverage (joinCoverage batch19585 batch19623) (joinCoverage batch19662 batch19701)) (joinCoverage (joinCoverage batch19740 batch19779) (joinCoverage batch19818 batch19857))))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch19896 batch19934) (joinCoverage batch19973 batch20012)) (joinCoverage (joinCoverage batch20051 batch20089) (joinCoverage batch20128 batch20167))) (joinCoverage (joinCoverage (joinCoverage batch20206 batch20244) (joinCoverage batch20283 batch20322)) (joinCoverage (joinCoverage batch20361 batch20400) (joinCoverage batch20439 batch20478)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch20517 batch20555) (joinCoverage batch20594 batch20633)) (joinCoverage (joinCoverage batch20672 batch20711) (joinCoverage batch20750 batch20789))) (joinCoverage (joinCoverage (joinCoverage batch20828 batch20866) (joinCoverage batch20905 batch20944)) (joinCoverage (joinCoverage batch20983 batch21022) (joinCoverage batch21061 batch21100))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch21139 batch21177) (joinCoverage batch21216 batch21255)) (joinCoverage (joinCoverage batch21294 batch21333) (joinCoverage batch21372 batch21411))) (joinCoverage (joinCoverage (joinCoverage batch21450 batch21488) (joinCoverage batch21527 batch21566)) (joinCoverage (joinCoverage batch21605 batch21644) (joinCoverage batch21683 batch21722)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch21761 batch21799) (joinCoverage batch21838 batch21877)) (joinCoverage (joinCoverage batch21916 batch21955) (joinCoverage batch21994 batch22033))) (joinCoverage (joinCoverage (joinCoverage batch22072 batch22110) (joinCoverage batch22149 batch22188)) (joinCoverage (joinCoverage batch22227 batch22266) (joinCoverage batch22305 batch22344)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch22383 batch22421) (joinCoverage batch22460 batch22499)) (joinCoverage (joinCoverage batch22538 batch22576) (joinCoverage batch22615 batch22654))) (joinCoverage (joinCoverage (joinCoverage batch22693 batch22731) (joinCoverage batch22770 batch22809)) (joinCoverage (joinCoverage batch22848 batch22887) (joinCoverage batch22926 batch22965)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch23004 batch23042) (joinCoverage batch23081 batch23120)) (joinCoverage (joinCoverage batch23159 batch23198) (joinCoverage batch23237 batch23276))) (joinCoverage (joinCoverage (joinCoverage batch23315 batch23353) (joinCoverage batch23392 batch23431)) (joinCoverage (joinCoverage batch23470 batch23509) (joinCoverage batch23548 batch23587))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch23626 batch23664) (joinCoverage batch23703 batch23742)) (joinCoverage (joinCoverage batch23781 batch23820) (joinCoverage batch23859 batch23898))) (joinCoverage (joinCoverage (joinCoverage batch23937 batch23975) (joinCoverage batch24014 batch24053)) (joinCoverage (joinCoverage batch24092 batch24131) (joinCoverage batch24170 batch24209)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch24248 batch24286) (joinCoverage batch24325 batch24364)) (joinCoverage (joinCoverage batch24403 batch24442) (joinCoverage batch24481 batch24520))) (joinCoverage (joinCoverage (joinCoverage batch24559 batch24597) (joinCoverage batch24636 batch24675)) (joinCoverage (joinCoverage batch24714 batch24753) (joinCoverage batch24792 batch24831))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch24870 batch24908) (joinCoverage batch24947 batch24986)) (joinCoverage (joinCoverage batch25025 batch25063) (joinCoverage batch25102 batch25141))) (joinCoverage (joinCoverage (joinCoverage batch25180 batch25218) (joinCoverage batch25257 batch25296)) (joinCoverage (joinCoverage batch25335 batch25374) (joinCoverage batch25413 batch25452)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch25491 batch25529) (joinCoverage batch25568 batch25607)) (joinCoverage (joinCoverage batch25646 batch25685) (joinCoverage batch25724 batch25763))) (joinCoverage (joinCoverage (joinCoverage batch25802 batch25840) (joinCoverage batch25879 batch25918)) (joinCoverage (joinCoverage batch25957 batch25996) (joinCoverage batch26035 batch26074))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch26113 batch26151) (joinCoverage batch26190 batch26229)) (joinCoverage (joinCoverage batch26268 batch26307) (joinCoverage batch26346 batch26385))) (joinCoverage (joinCoverage (joinCoverage batch26424 batch26462) (joinCoverage batch26501 batch26540)) (joinCoverage (joinCoverage batch26579 batch26618) (joinCoverage batch26657 batch26696)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch26735 batch26773) (joinCoverage batch26812 batch26851)) (joinCoverage (joinCoverage batch26890 batch26929) (joinCoverage batch26968 batch27007))) (joinCoverage (joinCoverage (joinCoverage batch27046 batch27084) (joinCoverage batch27123 batch27162)) (joinCoverage (joinCoverage batch27201 batch27240) (joinCoverage batch27279 batch27318)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch27357 batch27395) (joinCoverage batch27434 batch27473)) (joinCoverage (joinCoverage batch27512 batch27550) (joinCoverage batch27589 batch27628))) (joinCoverage (joinCoverage (joinCoverage batch27667 batch27705) (joinCoverage batch27744 batch27783)) (joinCoverage (joinCoverage batch27822 batch27861) (joinCoverage batch27900 batch27939)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch27978 batch28016) (joinCoverage batch28055 batch28094)) (joinCoverage (joinCoverage batch28133 batch28172) (joinCoverage batch28211 batch28250))) (joinCoverage (joinCoverage (joinCoverage batch28289 batch28327) (joinCoverage batch28366 batch28405)) (joinCoverage (joinCoverage batch28444 batch28483) (joinCoverage batch28522 batch28561))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch28600 batch28638) (joinCoverage batch28677 batch28716)) (joinCoverage (joinCoverage batch28755 batch28794) (joinCoverage batch28833 batch28872))) (joinCoverage (joinCoverage (joinCoverage batch28911 batch28949) (joinCoverage batch28988 batch29027)) (joinCoverage (joinCoverage batch29066 batch29105) (joinCoverage batch29144 batch29183)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch29222 batch29260) (joinCoverage batch29299 batch29338)) (joinCoverage (joinCoverage batch29377 batch29416) (joinCoverage batch29455 batch29494))) (joinCoverage (joinCoverage (joinCoverage batch29533 batch29571) (joinCoverage batch29610 batch29649)) (joinCoverage (joinCoverage batch29688 batch29727) (joinCoverage batch29766 batch29805)))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch29844 batch29882) (joinCoverage batch29921 batch29960)) (joinCoverage (joinCoverage batch29999 batch30037) (joinCoverage batch30076 batch30115))) (joinCoverage (joinCoverage (joinCoverage batch30154 batch30192) (joinCoverage batch30231 batch30270)) (joinCoverage (joinCoverage batch30309 batch30348) (joinCoverage batch30387 batch30426)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch30465 batch30503) (joinCoverage batch30542 batch30581)) (joinCoverage (joinCoverage batch30620 batch30659) (joinCoverage batch30698 batch30737))) (joinCoverage (joinCoverage (joinCoverage batch30776 batch30814) (joinCoverage batch30853 batch30892)) (joinCoverage (joinCoverage batch30931 batch30970) (joinCoverage batch31009 batch31048))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch31087 batch31125) (joinCoverage batch31164 batch31203)) (joinCoverage (joinCoverage batch31242 batch31281) (joinCoverage batch31320 batch31359))) (joinCoverage (joinCoverage (joinCoverage batch31398 batch31436) (joinCoverage batch31475 batch31514)) (joinCoverage (joinCoverage batch31553 batch31592) (joinCoverage batch31631 batch31670)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch31709 batch31747) (joinCoverage batch31786 batch31825)) (joinCoverage (joinCoverage batch31864 batch31903) (joinCoverage batch31942 batch31981))) (joinCoverage (joinCoverage (joinCoverage batch32020 batch32058) (joinCoverage batch32097 batch32136)) (joinCoverage (joinCoverage batch32175 batch32214) (joinCoverage batch32253 batch32292)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch32331 batch32369) (joinCoverage batch32408 batch32447)) (joinCoverage (joinCoverage batch32486 batch32524) (joinCoverage batch32563 batch32602))) (joinCoverage (joinCoverage (joinCoverage batch32641 batch32679) (joinCoverage batch32718 batch32757)) (joinCoverage (joinCoverage batch32796 batch32835) (joinCoverage batch32874 batch32913)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch32952 batch32990) (joinCoverage batch33029 batch33068)) (joinCoverage (joinCoverage batch33107 batch33146) (joinCoverage batch33185 batch33224))) (joinCoverage (joinCoverage (joinCoverage batch33263 batch33301) (joinCoverage batch33340 batch33379)) (joinCoverage (joinCoverage batch33418 batch33457) (joinCoverage batch33496 batch33535))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch33574 batch33612) (joinCoverage batch33651 batch33690)) (joinCoverage (joinCoverage batch33729 batch33768) (joinCoverage batch33807 batch33846))) (joinCoverage (joinCoverage (joinCoverage batch33885 batch33923) (joinCoverage batch33962 batch34001)) (joinCoverage (joinCoverage batch34040 batch34079) (joinCoverage batch34118 batch34157)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch34196 batch34234) (joinCoverage batch34273 batch34312)) (joinCoverage (joinCoverage batch34351 batch34390) (joinCoverage batch34429 batch34468))) (joinCoverage (joinCoverage (joinCoverage batch34507 batch34545) (joinCoverage batch34584 batch34623)) (joinCoverage (joinCoverage batch34662 batch34701) (joinCoverage batch34740 batch34779))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch34818 batch34856) (joinCoverage batch34895 batch34934)) (joinCoverage (joinCoverage batch34973 batch35011) (joinCoverage batch35050 batch35089))) (joinCoverage (joinCoverage (joinCoverage batch35128 batch35166) (joinCoverage batch35205 batch35244)) (joinCoverage (joinCoverage batch35283 batch35322) (joinCoverage batch35361 batch35400)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch35439 batch35477) (joinCoverage batch35516 batch35555)) (joinCoverage (joinCoverage batch35594 batch35633) (joinCoverage batch35672 batch35711))) (joinCoverage (joinCoverage (joinCoverage batch35750 batch35788) (joinCoverage batch35827 batch35866)) (joinCoverage (joinCoverage batch35905 batch35944) (joinCoverage batch35983 batch36022))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch36061 batch36099) (joinCoverage batch36138 batch36177)) (joinCoverage (joinCoverage batch36216 batch36255) (joinCoverage batch36294 batch36333))) (joinCoverage (joinCoverage (joinCoverage batch36372 batch36410) (joinCoverage batch36449 batch36488)) (joinCoverage (joinCoverage batch36527 batch36566) (joinCoverage batch36605 batch36644)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch36683 batch36721) (joinCoverage batch36760 batch36799)) (joinCoverage (joinCoverage batch36838 batch36877) (joinCoverage batch36916 batch36955))) (joinCoverage (joinCoverage (joinCoverage batch36994 batch37032) (joinCoverage batch37071 batch37110)) (joinCoverage (joinCoverage batch37149 batch37188) (joinCoverage batch37227 batch37266)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch37305 batch37343) (joinCoverage batch37382 batch37421)) (joinCoverage (joinCoverage batch37460 batch37498) (joinCoverage batch37537 batch37576))) (joinCoverage (joinCoverage (joinCoverage batch37615 batch37653) (joinCoverage batch37692 batch37731)) (joinCoverage (joinCoverage batch37770 batch37809) (joinCoverage batch37848 batch37887)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch37926 batch37964) (joinCoverage batch38003 batch38042)) (joinCoverage (joinCoverage batch38081 batch38120) (joinCoverage batch38159 batch38198))) (joinCoverage (joinCoverage (joinCoverage batch38237 batch38275) (joinCoverage batch38314 batch38353)) (joinCoverage (joinCoverage batch38392 batch38431) (joinCoverage batch38470 batch38509))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch38548 batch38586) (joinCoverage batch38625 batch38664)) (joinCoverage (joinCoverage batch38703 batch38742) (joinCoverage batch38781 batch38820))) (joinCoverage (joinCoverage (joinCoverage batch38859 batch38897) (joinCoverage batch38936 batch38975)) (joinCoverage (joinCoverage batch39014 batch39053) (joinCoverage batch39092 batch39131)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch39170 batch39208) (joinCoverage batch39247 batch39286)) (joinCoverage (joinCoverage batch39325 batch39364) (joinCoverage batch39403 batch39442))) (joinCoverage (joinCoverage (joinCoverage batch39481 batch39519) (joinCoverage batch39558 batch39597)) (joinCoverage (joinCoverage batch39636 batch39675) (joinCoverage batch39714 batch39753))))))))))

theorem fast_correct (n : ℕ) (bound : n ≤ 4775000) : fast n = Nat.primeCounting n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases smallN : n < 6
    · have tests : ∀ i : Fin 7, fast i.val = Nat.primeCounting i.val := by decide +kernel
      exact tests ⟨n+1,by omega⟩
    · have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤4775000 by omega)
        have within : index n / 32 < 39792 := by omega
        have chk := beq_iff_eq.mp (allrows _ (Nat.zero_le _) within)
        change checkpoint (index n/32+1) = checkpoint (index n/32) +
          tally (fun j => quick (number j)) (32*(index n/32)) 32 at chk
        have h := fromBlocks_succ checkpoint (fun j => quick (number j)) (index n) chk
        change raw (index n+1) = raw (index n) + (if quick (number (index n)) then 1 else 0) at h
        rw [whose] at h
        simp only [fast,e,h,unchanged]
        by_cases hp : (n+1).Prime
        · simp [hp,(quick_ok bound).mpr hp,Nat.add_right_comm]
        · simp [hp,mt (quick_ok bound).mp hp]
def prime (n : ℕ) : Bool := quick n

theorem prime_ok (n : ℕ) (hn : n≤4775000) : prime n=true ↔ n.Prime := quick_ok hn

end CheckpointA10425Slim


namespace HybridBound10425

def fast (n : ℕ) : ℕ :=
  if n≤206781 then WheelTableA94.fast n else CheckpointA10425Slim.fast n

theorem fast_correct (n : ℕ) (hn : n≤4775000) : fast n=Nat.primeCounting n := by
  unfold fast
  split_ifs with small
  · exact WheelTableA94.fast_correct n small
  · exact CheckpointA10425Slim.fast_correct n hn

end HybridBound10425


/- The Legendre and Meissel identities below are the public Physbuzz reduction
for OEIS A247824, itself crediting Daniel Veljjanoski and rleshner. The numerical proof below certifies one of the residual ranks. -/
open Finset
namespace Endpoint10425

lemma legendre {ps : List ℕ} (hsort : ps.Pairwise (· > ·)) (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hcomp : ∀ p ∈ ps, ∀ q, Nat.Prime q → q < p → q ∈ ps) (x : ℕ) :
    ps.foldr (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x =
      ((Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)).card := by
  let sieveSet (ps : List ℕ) (x : ℕ) := (Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)
  have mem_sieveSet {ps : List ℕ} {x n : ℕ} :
      n ∈ sieveSet ps x ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ ps, ¬ p ∣ n := by
    simp [sieveSet]

  have sieveSet_nil (x : ℕ) : sieveSet [] x = Finset.Icc 1 x := by
    ext n; simp [sieveSet]

  /- Legendre's recursion step. -/
  have card_sieveSet_cons {p : ℕ} {ps : List ℕ} (hp : p.Prime) (hps : ∀ q ∈ ps, q.Prime ∧ q ≠ p)
      (x : ℕ) :
      (sieveSet (p :: ps) x).card = (sieveSet ps x).card - (sieveSet ps (x / p)).card := by
    have hsplit : sieveSet (p :: ps) x = (sieveSet ps x).filter (fun n => ¬ p ∣ n) := by
      ext n; simp [sieveSet, List.mem_cons]; tauto
    have himage : (sieveSet ps x).filter (fun n => p ∣ n) = (sieveSet ps (x / p)).image (p * ·) := by
      ext n
      simp only [Finset.mem_filter, mem_sieveSet, Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨h1, hx⟩, hq⟩, ⟨m, rfl⟩⟩
        refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp at h1
          · exact hm
        · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [mul_comm]; exact hx)
        · intro q hq' hdvd
          exact hq q hq' (dvd_mul_of_dvd_right hdvd p)
      · rintro ⟨m, ⟨⟨h1, hm⟩, hq⟩, rfl⟩
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
        · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero (by omega))
        · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp.pos).1 hm
        · intro q hq' hdvd
          obtain ⟨hqp, hqne⟩ := hps q hq'
          rcases (Nat.Prime.dvd_mul hqp).1 hdvd with h | h
          · exact hqne ((Nat.prime_dvd_prime_iff_eq hqp hp).1 h)
          · exact hq q hq' h
    have hcard := Finset.card_filter_add_card_filter_not (s := sieveSet ps x) (fun n => p ∣ n)
    rw [himage, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)] at hcard
    rw [hsplit]
    omega

  /- Pruning: below `p`, only `1` survives the sieve by all primes less than `p`. -/
  have card_sieveSet_of_lt {p : ℕ} {ps : List ℕ} (hps : ∀ q ∈ ps, q.Prime)
      (hcomplete : ∀ q, q.Prime → q < p → q ∈ ps) {x : ℕ} (hx : x < p) :
      (sieveSet (p :: ps) x).card = if x = 0 then 0 else 1 := by
    split_ifs with h0
    · subst h0; simp [sieveSet]
    · have : sieveSet (p :: ps) x = {1} := by
        ext n
        simp only [mem_sieveSet, Finset.mem_singleton, List.mem_cons, forall_eq_or_imp]
        constructor
        · rintro ⟨⟨h1, hnx⟩, -, hq⟩
          by_contra hne
          have hn1 : n ≠ 1 := hne
          have hmf := Nat.minFac_prime hn1
          have hlt : Nat.minFac n < p := lt_of_le_of_lt (Nat.minFac_le (by omega)) (by omega)
          exact hq _ (hcomplete _ hmf hlt) (Nat.minFac_dvd n)
        · rintro rfl
          refine ⟨⟨le_rfl, by omega⟩, ?_, ?_⟩
          · intro h
            have := Nat.le_of_dvd one_pos h
            omega
          · intro q hq; exact Nat.Prime.not_dvd_one (hps q hq)
      rw [this, Finset.card_singleton]

  change _ = (sieveSet ps x).card
  induction ps generalizing x with
  | nil => simp [sieveSet_nil]
  | cons p ps ih =>
    obtain ⟨hgt,hs⟩ := List.pairwise_cons.mp hsort
    have hp := hprime p List.mem_cons_self
    have hq (q) (hq : q ∈ ps) := hprime q (List.mem_cons_of_mem p hq)
    have hc (q) (h : q.Prime) (lt : q < p) : q ∈ ps := by
      rcases List.mem_cons.mp (hcomp p List.mem_cons_self q h lt) with eq | hm
      · omega
      · exact hm
    have closed (r) (hr : r ∈ ps) (q) (h : q.Prime) (lt : q < r) := hc q h (lt.trans (hgt r hr))
    simp only [List.foldr_cons]
    split_ifs with lt zero
    · rw [card_sieveSet_of_lt hq hc lt, if_pos zero]
    · rw [card_sieveSet_of_lt hq hc lt, if_neg zero]
    · rw [card_sieveSet_cons hp (fun q h => ⟨hq q h, (hgt q h).ne⟩), ih hs hq closed, ih hs hq closed]

lemma legendre_range (y x : ℕ) :
    (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr
      (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x) =
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card := by
  let ps := ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse
  have mem (p : ℕ) : p ∈ ps ↔ p ∈ Nat.primesLE y := by simp [ps, Nat.mem_primesLE]
  have hsort : ps.Pairwise (· > ·) := by
    apply List.pairwise_reverse.mpr
    exact List.pairwise_lt_range.filter _
  have e := legendre hsort (fun p hp => Nat.prime_of_mem_primesLE ((mem p).mp hp))
    (fun p hp q hq hlt => (mem q).mpr (Nat.mem_primesLE.mpr ⟨hlt.le.trans (Nat.le_of_mem_primesLE ((mem p).mp hp)), hq⟩)) x
  convert e using 1
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem]

/-- At a cube-root cutoff, every surviving composite has exactly two prime factors,
with multiplicity. Sorting the factors makes this parametrization injective. -/
lemma meissel {x y z : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) :
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card +
      (Nat.primesLE y).card = 1 + (Nat.primesLE x).card +
      ∑ p ∈ (Nat.primesLE z).filter (y < ·), ((Nat.primesLE (x/p)).filter (p ≤ ·)).card := by
  classical
  let R := (Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)
  let T := R.filter (fun n => n ≠ 1 ∧ ¬n.Prime)
  let B := (Nat.primesLE z).filter (y < ·)
  let Q (p : ℕ) := (Nat.primesLE (x/p)).filter (p ≤ ·)
  have memR (n) : n ∈ R ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ Nat.primesLE y, ¬ p ∣ n := by simp [R]
  have memT (n) : n ∈ T ↔ n ∈ R ∧ n ≠ 1 ∧ ¬n.Prime := by simp [T]
  have memB (p) : p ∈ B ↔ (p ≤ z ∧ p.Prime) ∧ y < p := by simp [B, Nat.mem_primesLE]
  have memQ (p q) : q ∈ Q p ↔ (q ≤ x/p ∧ q.Prime) ∧ p ≤ q := by simp [Q, Nat.mem_primesLE]
  have least {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p ≤ q) : (p*q).minFac = p := by
    have hn : p*q ≠ 1 := by have := hp.two_le; have := hq.two_le; nlinarith
    have hm := Nat.minFac_prime hn
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q))
    rcases hm.dvd_mul.mp (Nat.minFac_dvd (p*q)) with a | b
    · exact ((Nat.prime_dvd_prime_iff_eq hm hp).mp a).symm.le
    · exact pq.trans_eq ((Nat.prime_dvd_prime_iff_eq hm hq).mp b).symm
  have pair : (B.sigma Q).card = T.card := by
    apply card_bij (fun a _ => a.1 * a.2)
    · intro ⟨p,q⟩ h
      obtain ⟨hb,hq⟩ := mem_sigma.mp h
      obtain ⟨⟨_,pp⟩,yp⟩ := (memB p).mp hb
      obtain ⟨⟨ub,qp⟩,ord⟩ := (memQ p q).mp hq
      have pos := Nat.mul_pos pp.pos qp.pos
      have bound : p*q ≤ x := by simpa [mul_comm] using (Nat.le_div_iff_mul_le pp.pos).mp ub
      apply (memT _).mpr
      refine ⟨(memR _).mpr ⟨⟨pos,bound⟩, ?_⟩, ?_, ?_⟩
      · intro r hr hd
        obtain ⟨ry,rp⟩ := Nat.mem_primesLE.mp hr
        rcases rp.dvd_mul.mp hd with a | b
        · have := (Nat.prime_dvd_prime_iff_eq rp pp).mp a; omega
        · have := (Nat.prime_dvd_prime_iff_eq rp qp).mp b; omega
      · have := pp.two_le; have := qp.two_le; dsimp; nlinarith
      · intro prime
        have := (Nat.prime_dvd_prime_iff_eq pp prime).mp (dvd_mul_right p q)
        have := pp.two_le; have := qp.two_le; dsimp at *; nlinarith
    · intro ⟨p,q⟩ ha ⟨r,s⟩ hb eq
      obtain ⟨ha,hq⟩ := mem_sigma.mp ha
      obtain ⟨hb,hs⟩ := mem_sigma.mp hb
      obtain ⟨⟨_,pp⟩,_⟩ := (memB p).mp ha
      obtain ⟨⟨_,rp⟩,_⟩ := (memB r).mp hb
      obtain ⟨⟨_,qp⟩,a⟩ := (memQ p q).mp hq
      obtain ⟨⟨_,sp⟩,b⟩ := (memQ r s).mp hs
      change p*q=r*s at eq
      have same := (least pp qp a).symm.trans ((congrArg Nat.minFac eq).trans (least rp sp b))
      subst r
      obtain rfl := Nat.eq_of_mul_eq_mul_left pp.pos eq
      rfl
    · intro n hn
      obtain ⟨hr,ne,np⟩ := (memT n).mp hn
      obtain ⟨⟨pos,bound⟩,rough⟩ := (memR n).mp hr
      let p := n.minFac
      let q := n / p
      have pp : p.Prime := Nat.minFac_prime ne
      have product : p*q = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      have ord : p ≤ q := Nat.minFac_le_div pos np
      have yp : y < p := by
        by_contra! h
        exact rough _ (Nat.mem_primesLE.mpr ⟨h,pp⟩) (Nat.minFac_dvd n)
      have qp : q.Prime := by
        by_contra hq
        have qpos : 0 < q := pp.pos.trans_le ord
        have qq := Nat.minFac_sq_le_self qpos hq
        have qne : q ≠ 1 := by have := pp.two_le; omega
        have rprime := Nat.minFac_prime qne
        have yr : y < q.minFac := by
          by_contra! h
          apply rough _ (Nat.mem_primesLE.mpr ⟨h,rprime⟩)
          rw [← product]
          exact dvd_mul_of_dvd_right (Nat.minFac_dvd q) _
        have b := Nat.mul_le_mul (show y+1 ≤ p by omega)
          (le_trans (Nat.pow_le_pow_left (show y+1 ≤ q.minFac by omega) 2) qq)
        nlinarith only [product,b,bound,cube]
      have pz : p ≤ z := by
        by_contra! h
        have a := Nat.mul_le_mul (show z+1≤p by omega) (show z+1≤q by omega)
        nlinarith only [product,a,sq,bound]
      refine ⟨⟨p,q⟩, mem_sigma.mpr ⟨(memB _).mpr ⟨⟨pz,pp⟩,yp⟩,
        (memQ _ _).mpr ⟨⟨(Nat.le_div_iff_mul_le pp.pos).mpr ?_,qp⟩,ord⟩⟩, product⟩
      simpa [mul_comm,product] using (product.le.trans bound)
  have primepart : R.filter Nat.Prime = (Nat.primesLE x).filter (fun n => ¬ n ≤ y) := by
    ext n
    simp only [mem_filter,memR,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨_,ub⟩,r⟩,np⟩
      exact ⟨⟨ub,np⟩,fun h => r n ⟨h,np⟩ (dvd_refl n)⟩
    · rintro ⟨⟨ub,np⟩,gt⟩
      refine ⟨⟨⟨np.one_le,ub⟩,fun p hp hd => ?_⟩, np⟩
      exact gt (((Nat.prime_dvd_prime_iff_eq hp.2 np).mp hd) ▸ hp.1)
  have low : (Nat.primesLE x).filter (· ≤ y) = Nat.primesLE y := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨h.1.trans hy,h.2⟩,h.1⟩⟩
  have other : R.filter (fun n => ¬n.Prime) = insert 1 T := by
    ext n
    simp only [mem_filter,mem_insert,memT]
    constructor
    · rintro ⟨hr,hp⟩; by_cases h : n=1
      · exact Or.inl h
      · exact Or.inr ⟨hr,h,hp⟩
    · rintro (rfl | ⟨hr,_,hp⟩)
      · exact ⟨(memR _).mpr ⟨⟨le_rfl,hx⟩,fun p hp => (Nat.prime_of_mem_primesLE hp).not_dvd_one⟩,Nat.not_prime_one⟩
      · exact ⟨hr,hp⟩
  have one : 1 ∉ T := fun h => ((memT 1).mp h).2.1 rfl
  have v := card_filter_add_card_filter_not (s:=R) Nat.Prime
  have w := card_filter_add_card_filter_not (s:=Nat.primesLE x) (· ≤ y)
  rw [primepart,other,card_insert_of_notMem one] at v
  rw [low] at w
  rw [card_sigma] at pair
  change R.card + _ = 1 + _ + ∑ p ∈ B, (Q p).card
  omega

/-- Interval subtraction evaluates each row of the semiprime count using only ordinary prime counts. -/
lemma prime_row {p t : ℕ} (pos : 0 < p) (le : p ≤ t) :
    ((Nat.primesLE t).filter (p ≤ ·)).card = Nat.primeCounting t - Nat.primeCounting (p-1) := by
  have eq : (Nat.primesLE t).filter (fun n => ¬p ≤ n) = Nat.primesLE (p-1) := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,pr⟩,lt⟩; exact ⟨by omega,pr⟩
    · rintro ⟨ub,pr⟩; exact ⟨⟨by omega,pr⟩,by omega⟩
  have h := card_filter_add_card_filter_not (s:=Nat.primesLE t) (p ≤ ·)
  rw [eq, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h
  omega

lemma rank_of_parts {x y z a b r : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) (zs : z*z ≤ x)
    (sieved : (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr
      (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x) +
      (Nat.primesLE y).card = a)
    (pairs : (∑ p ∈ (Nat.primesLE z).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = b)
    (result : 1+r+b = a) : Nat.primeCounting x = r := by
  have e := meissel hx hy cube sq
  have row (p : ℕ) (hp : p ∈ (Nat.primesLE z).filter (y < ·)) := by
    have bound := Nat.le_of_mem_primesLE (mem_filter.mp hp).1
    have pos := (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
    exact prime_row pos ((Nat.le_div_iff_mul_le pos).mpr ((Nat.mul_le_mul bound bound).trans zs))
  rw [legendre_range] at sieved
  rw [sum_congr rfl row, pairs, Nat.primesLE_card_eq_primeCounting x] at e
  omega

def advance (p : ℕ) (f : ℕ → ℕ) (x : ℕ) :=
  if x < p then (if x=0 then 0 else 1) else f x - f (x/p)

private def evalPhi (table : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], t => t
  | p :: ps, t => if p=11 then ShortPeriod.wheel t else if t < p then (if t=0 then 0 else 1) else
      if t < (p+1)^2 then 1 + table t - table p else
        evalPhi table ps t - evalPhi table ps (t/p)

private theorem square_cut {p t : ℕ} (hp : 0 < p) (pt : p ≤ t) (square : t < (p+1)^2) :
    (((List.range (p+1)).filter (fun n => decide n.Prime)).reverse.foldr advance id) t +
      Nat.primeCounting p = 1 + Nat.primeCounting t := by
  have cube : t < (p+1)^3 :=
    lt_of_lt_of_le square (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))
  have empty : (Nat.primesLE p).filter (p < ·) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact (not_lt_of_ge (Nat.le_of_mem_primesLE (Finset.mem_filter.mp hn).1))
      (Finset.mem_filter.mp hn).2
  have h := meissel (x:=t) (y:=p) (z:=p) (by omega) pt cube square
  simp only [empty,Finset.sum_empty,Nat.add_zero,Nat.primesLE_card_eq_primeCounting] at h
  rw [←legendre_range] at h
  exact h

private theorem refine_row {bound p : ℕ} (tab : ℕ → ℕ) (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t)
    (ps : List ℕ) (lst : ((List.range (p+1)).filter (fun n => decide n.Prime)).reverse = p::ps)
    (prev : ∀ t, ps.foldr advance id t = evalPhi tab ps t)
    (pos : 0 < p) (cap : (p+1)^2 ≤ bound+1) : ∀ t,
    (p::ps).foldr advance id t = evalPhi tab (p::ps) t := by
  intro t
  by_cases hbase : p=11
  · subst p
    have val : (11::ps).foldr advance id t = ShortPeriod.wheel t := by
      rw [←lst]
      exact (legendre_range 11 t).trans (ShortPeriod.count_rough t)
    simpa [evalPhi] using val
  by_cases sm : t < p
  · simp [List.foldr_cons,advance,evalPhi,hbase,sm]
  · by_cases short : t < (p+1)^2
    · have h := square_cut pos (by omega : p ≤ t) short
      rw [lst] at h
      rw [evalPhi,if_neg hbase,if_neg sm,if_pos short,ok t (by omega),ok p (by omega)]
      omega
    · simp only [List.foldr_cons,advance,evalPhi,if_neg hbase,if_neg sm,if_neg short,prev]

private theorem merge_filter (f : ℕ → Bool) (lo a b : ℕ) (l r : List ℕ)
    (hl : (List.range' lo a).filter f = l) (hr : (List.range' (lo+a) b).filter f = r) :
    (List.range' lo (a+b)).filter f = l++r := by
  rw [←List.range'_append_1,List.filter_append,hl,hr]

private theorem eval_delta (tab : ℕ → ℕ) (ps : List ℕ) (p n q old dec ans : ℕ)
    (notWheel : p≠11) (le : p ≤ n) (sq : (p+1)^2 ≤ n) (div : n/p = q)
    (base : evalPhi tab ps n = old) (cut : evalPhi tab ps q = dec) (sub : old-dec=ans) :
    evalPhi tab (p::ps) n = ans := by
  rw [evalPhi,if_neg notWheel,if_neg (not_lt.mpr le),if_neg (not_lt.mpr sq),div,base,cut,sub]

private theorem assemble {x y z a b r : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) (zs : z*z ≤ x)
    (sieved : (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id x) +
      (Nat.primesLE y).card = a)
    (rows : (∑ p ∈ (Nat.primesLE z).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = b)
    (total : 1+r+b=a) : Nat.primeCounting x=r := by
  exact rank_of_parts hx hy cube sq zs sieved rows total

private theorem agree_range {bound : ℕ} (table : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → table t = Nat.primeCounting t)
    (y : ℕ) (cap : (y+1)^2 ≤ bound+1) :
    ∀ t, (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id) t =
      evalPhi table ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse t := by
  induction y with
  | zero => simp [List.range_succ,evalPhi]
  | succ n ih =>
    have c : (n+1)^2 ≤ bound+1 :=
      le_trans (Nat.pow_le_pow_left (by omega : n+1 ≤ n+1+1) 2) cap
    by_cases hp : (n+1).Prime
    · have row : ((List.range (n+1+1)).filter (fun p => decide p.Prime)).reverse =
          (n+1) :: ((List.range (n+1)).filter (fun p => decide p.Prime)).reverse := by
        rw [List.range_succ (n:=n+1),List.filter_append,List.reverse_append]
        simp [hp]
      rw [row]
      exact refine_row table ok _ row (ih c) (by omega) cap
    · have row : ((List.range (n+1+1)).filter (fun p => decide p.Prime)).reverse =
          ((List.range (n+1)).filter (fun p => decide p.Prime)).reverse := by
        rw [List.range_succ (n:=n+1),List.filter_append,List.reverse_append]
        simp [hp]
      rw [row]
      exact ih c

private def contribution (x y : ℕ) (tab : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then tab (x/p) - tab (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z b value : ℕ} (tab : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, n≤b → tab n = Nat.primeCounting n)
    (prime_ok : ∀ n, n≤b → (prime n=true ↔ n.Prime))
    (hz : z≤b) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y tab prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y tab prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p≤b := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ (le_trans ub hq),ok _ (by omega : p-1≤b)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y tab prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y tab prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result


private abbrev tab := HybridBound10425.fast
private abbrev F := evalPhi tab

private abbrev prime := CheckpointA10425Slim.prime
private theorem prime_ok (n : ℕ) (hn : n≤4775000) : prime n=true ↔ n.Prime := CheckpointA10425Slim.prime_ok n hn


private theorem takeStep {ps : List ℕ} {p q prev cut ans : ℕ}
    (notWheel : p≠11) (base : F ps 10425579253=prev) (part : F ps q=cut) (div : 10425579253/p=q)
    (le : p≤10425579253) (sq : (p+1)^2≤10425579253) (sub : prev-cut=ans) :
    F (p::ps) 10425579253=ans := eval_delta tab ps p 10425579253 q prev cut ans notWheel le sq div base part sub


private def ps0 : List ℕ := []
private theorem v0 : F ps0 10425579253=10425579253 := rfl

private def ps1 : List ℕ := 2::ps0
private theorem c1 : F ps0 5212789626=5212789626 := by decide +kernel
private theorem v1 : F ps1 10425579253=5212789627 :=
  takeStep (p:=2) (by decide) v0 c1 rfl (by decide) (by decide) rfl

private def ps2 : List ℕ := 3::ps1
private theorem c2 : F ps1 3475193084=1737596542 := by decide +kernel
private theorem v2 : F ps2 10425579253=3475193085 :=
  takeStep (p:=3) (by decide) v1 c2 rfl (by decide) (by decide) rfl

private def ps3 : List ℕ := 5::ps2
private theorem c3 : F ps2 2085115850=695038617 := by decide +kernel
private theorem v3 : F ps3 10425579253=2780154468 :=
  takeStep (p:=5) (by decide) v2 c3 rfl (by decide) (by decide) rfl

private def ps4 : List ℕ := 7::ps3
private theorem c4 : F ps3 1489368464=397164924 := by decide +kernel
private theorem v4 : F ps4 10425579253=2382989544 :=
  takeStep (p:=7) (by decide) v3 c4 rfl (by decide) (by decide) rfl

private def ps5 : List ℕ := 11::ps4
private theorem c5 : F ps4 947779932=216635412 := by decide +kernel
private theorem v5 : F ps5 10425579253=2166354132 := by decide +kernel

private def ps6 : List ℕ := 13::ps5
private theorem c6 : F ps5 801967634=166642626 := by decide +kernel
private theorem v6 : F ps6 10425579253=1999711506 :=
  takeStep (p:=13) (by decide) v5 c6 rfl (by decide) (by decide) rfl

private def ps7 : List ℕ := 17::ps6
private theorem c7 : F ps6 613269367=117630090 := by decide +kernel
private theorem v7 : F ps7 10425579253=1882081416 :=
  takeStep (p:=17) (by decide) v6 c7 rfl (by decide) (by decide) rfl

private def ps8 : List ℕ := 19::ps7
private theorem c8 : F ps7 548714697=99056918 := by decide +kernel
private theorem v8 : F ps8 10425579253=1783024498 :=
  takeStep (p:=19) (by decide) v7 c8 rfl (by decide) (by decide) rfl

private def ps9 : List ℕ := 23::ps8
private theorem c9 : F ps8 453286054=77522804 := by decide +kernel
private theorem v9 : F ps9 10425579253=1705501694 :=
  takeStep (p:=23) (by decide) v8 c9 rfl (by decide) (by decide) rfl

private def ps10 : List ℕ := 29::ps9
private theorem c10 : F ps9 359502732=58810403 := by decide +kernel
private theorem v10 : F ps10 10425579253=1646691291 :=
  takeStep (p:=29) (by decide) v9 c10 rfl (by decide) (by decide) rfl

private def ps11 : List ℕ := 31::ps10
private theorem c11 : F ps10 336309008=53119072 := by decide +kernel
private theorem v11 : F ps11 10425579253=1593572219 :=
  takeStep (p:=31) (by decide) v10 c11 rfl (by decide) (by decide) rfl

private def ps12 : List ℕ := 37::ps11
private theorem c12 : F ps11 281772412=43069511 := by decide +kernel
private theorem v12 : F ps12 10425579253=1550502708 :=
  takeStep (p:=37) (by decide) v11 c12 rfl (by decide) (by decide) rfl

private def ps13 : List ℕ := 41::ps12
private theorem c13 : F ps12 254282420=37817126 := by decide +kernel
private theorem v13 : F ps13 10425579253=1512685582 :=
  takeStep (p:=41) (by decide) v12 c13 rfl (by decide) (by decide) rfl

private def ps14 : List ℕ := 43::ps13
private theorem c14 : F ps13 242455331=35178743 := by decide +kernel
private theorem v14 : F ps14 10425579253=1477506839 :=
  takeStep (p:=43) (by decide) v13 c14 rfl (by decide) (by decide) rfl

private def ps15 : List ℕ := 47::ps14
private theorem c15 : F ps14 221820835=31436362 := by decide +kernel
private theorem v15 : F ps15 10425579253=1446070477 :=
  takeStep (p:=47) (by decide) v14 c15 rfl (by decide) (by decide) rfl

private def ps16 : List ℕ := 53::ps15
private theorem c16 : F ps15 196709042=27284493 := by decide +kernel
private theorem v16 : F ps16 10425579253=1418785984 :=
  takeStep (p:=53) (by decide) v15 c16 rfl (by decide) (by decide) rfl

private def ps17 : List ℕ := 59::ps16
private theorem c17 : F ps16 176704733=24047433 := by decide +kernel
private theorem v17 : F ps17 10425579253=1394738551 :=
  takeStep (p:=59) (by decide) v16 c17 rfl (by decide) (by decide) rfl

private def ps18 : List ℕ := 61::ps17
private theorem c18 : F ps17 170911135=22864831 := by decide +kernel
private theorem v18 : F ps18 10425579253=1371873720 :=
  takeStep (p:=61) (by decide) v17 c18 rfl (by decide) (by decide) rfl

private def ps19 : List ℕ := 67::ps18
private theorem c19 : F ps18 155605660=20475969 := by decide +kernel
private theorem v19 : F ps19 10425579253=1351397751 :=
  takeStep (p:=67) (by decide) v18 c19 rfl (by decide) (by decide) rfl

private def ps20 : List ℕ := 71::ps19
private theorem c20 : F ps19 146839144=19033892 := by decide +kernel
private theorem v20 : F ps20 10425579253=1332363859 :=
  takeStep (p:=71) (by decide) v19 c20 rfl (by decide) (by decide) rfl

private def ps21 : List ℕ := 73::ps20
private theorem c21 : F ps20 142816154=18251477 := by decide +kernel
private theorem v21 : F ps21 10425579253=1314112382 :=
  takeStep (p:=73) (by decide) v20 c21 rfl (by decide) (by decide) rfl

private def ps22 : List ℕ := 79::ps21
private theorem c22 : F ps21 131969357=16633926 := by decide +kernel
private theorem v22 : F ps22 10425579253=1297478456 :=
  takeStep (p:=79) (by decide) v21 c22 rfl (by decide) (by decide) rfl

private def ps23 : List ℕ := 83::ps22
private theorem c23 : F ps22 125609388=15631462 := by decide +kernel
private theorem v23 : F ps23 10425579253=1281846994 :=
  takeStep (p:=83) (by decide) v22 c23 rfl (by decide) (by decide) rfl

private def ps24 : List ℕ := 89::ps23
private theorem c24 : F ps23 117141339=14401460 := by decide +kernel
private theorem v24 : F ps24 10425579253=1267445534 :=
  takeStep (p:=89) (by decide) v23 c24 rfl (by decide) (by decide) rfl

private def ps25 : List ℕ := 97::ps24
private theorem c25 : F ps24 107480198=13064623 := by decide +kernel
private theorem v25 : F ps25 10425579253=1254380911 :=
  takeStep (p:=97) (by decide) v24 c25 rfl (by decide) (by decide) rfl

private def ps26 : List ℕ := 101::ps25
private theorem c26 : F ps25 103223556=12417319 := by decide +kernel
private theorem v26 : F ps26 10425579253=1241963592 :=
  takeStep (p:=101) (by decide) v25 c26 rfl (by decide) (by decide) rfl

private def ps27 : List ℕ := 103::ps26
private theorem c27 : F ps26 101219216=12055138 := by decide +kernel
private theorem v27 : F ps27 10425579253=1229908454 :=
  takeStep (p:=103) (by decide) v26 c27 rfl (by decide) (by decide) rfl

private def ps28 : List ℕ := 107::ps27
private theorem c28 : F ps27 97435320=11491316 := by decide +kernel
private theorem v28 : F ps28 10425579253=1218417138 :=
  takeStep (p:=107) (by decide) v27 c28 rfl (by decide) (by decide) rfl

private def ps29 : List ℕ := 109::ps28
private theorem c29 : F ps28 95647516=11174602 := by decide +kernel
private theorem v29 : F ps29 10425579253=1207242536 :=
  takeStep (p:=109) (by decide) v28 c29 rfl (by decide) (by decide) rfl

private def ps30 : List ℕ := 113::ps29
private theorem c30 : F ps29 92261763=10679763 := by decide +kernel
private theorem v30 : F ps30 10425579253=1196562773 :=
  takeStep (p:=113) (by decide) v29 c30 rfl (by decide) (by decide) rfl

private def ps31 : List ℕ := 127::ps30
private theorem c31 : F ps30 82091175=9418172 := by decide +kernel
private theorem v31 : F ps31 10425579253=1187144601 :=
  takeStep (p:=127) (by decide) v30 c31 rfl (by decide) (by decide) rfl

private def ps32 : List ℕ := 131::ps31
private theorem c32 : F ps31 79584574=9058717 := by decide +kernel
private theorem v32 : F ps32 10425579253=1178085884 :=
  takeStep (p:=131) (by decide) v31 c32 rfl (by decide) (by decide) rfl

private def ps33 : List ℕ := 137::ps32
private theorem c33 : F ps32 76099118=8596002 := by decide +kernel
private theorem v33 : F ps33 10425579253=1169489882 :=
  takeStep (p:=137) (by decide) v32 c33 rfl (by decide) (by decide) rfl

private def ps34 : List ℕ := 139::ps33
private theorem c34 : F ps33 75004167=8410725 := by decide +kernel
private theorem v34 : F ps34 10425579253=1161079157 :=
  takeStep (p:=139) (by decide) v33 c34 rfl (by decide) (by decide) rfl

private def ps35 : List ℕ := 149::ps34
private theorem c35 : F ps34 69970330=7790290 := by decide +kernel
private theorem v35 : F ps35 10425579253=1153288867 :=
  takeStep (p:=149) (by decide) v34 c35 rfl (by decide) (by decide) rfl

private def ps36 : List ℕ := 151::ps35
private theorem c36 : F ps35 69043571=7635959 := by decide +kernel
private theorem v36 : F ps36 10425579253=1145652908 :=
  takeStep (p:=151) (by decide) v35 c36 rfl (by decide) (by decide) rfl

private def ps37 : List ℕ := 157::ps36
private theorem c37 : F ps36 66404963=7296145 := by decide +kernel
private theorem v37 : F ps37 10425579253=1138356763 :=
  takeStep (p:=157) (by decide) v36 c37 rfl (by decide) (by decide) rfl

private def ps38 : List ℕ := 163::ps37
private theorem c38 : F ps37 63960608=6983629 := by decide +kernel
private theorem v38 : F ps38 10425579253=1131373134 :=
  takeStep (p:=163) (by decide) v37 c38 rfl (by decide) (by decide) rfl

private def ps39 : List ℕ := 167::ps38
private theorem c39 : F ps38 62428618=6775318 := by decide +kernel
private theorem v39 : F ps39 10425579253=1124597816 :=
  takeStep (p:=167) (by decide) v38 c39 rfl (by decide) (by decide) rfl

private def ps40 : List ℕ := 173::ps39
private theorem c40 : F ps39 60263463=6502070 := by decide +kernel
private theorem v40 : F ps40 10425579253=1118095746 :=
  takeStep (p:=173) (by decide) v39 c40 rfl (by decide) (by decide) rfl

private def ps41 : List ℕ := 179::ps40
private theorem c41 : F ps40 58243459=6248805 := by decide +kernel
private theorem v41 : F ps41 10425579253=1111846941 :=
  takeStep (p:=179) (by decide) v40 c41 rfl (by decide) (by decide) rfl

private def ps42 : List ℕ := 181::ps41
private theorem c42 : F ps41 57599885=6146103 := by decide +kernel
private theorem v42 : F ps42 10425579253=1105700838 :=
  takeStep (p:=181) (by decide) v41 c42 rfl (by decide) (by decide) rfl

private def ps43 : List ℕ := 191::ps42
private theorem c43 : F ps42 54584184=5793440 := by decide +kernel
private theorem v43 : F ps43 10425579253=1099907398 :=
  takeStep (p:=191) (by decide) v42 c43 rfl (by decide) (by decide) rfl

private def ps44 : List ℕ := 193::ps43
private theorem c44 : F ps43 54018545=5704367 := by decide +kernel
private theorem v44 : F ps44 10425579253=1094203031 :=
  takeStep (p:=193) (by decide) v43 c44 rfl (by decide) (by decide) rfl

private def ps45 : List ℕ := 197::ps44
private theorem c45 : F ps44 52921722=5560708 := by decide +kernel
private theorem v45 : F ps45 10425579253=1088642323 :=
  takeStep (p:=197) (by decide) v44 c45 rfl (by decide) (by decide) rfl

private def ps46 : List ℕ := 199::ps45
private theorem c46 : F ps45 52389845=5477909 := by decide +kernel
private theorem v46 : F ps46 10425579253=1083164414 :=
  takeStep (p:=199) (by decide) v45 c46 rfl (by decide) (by decide) rfl

private def ps47 : List ℕ := 211::ps46
private theorem c47 : F ps46 49410328=5141876 := by decide +kernel
private theorem v47 : F ps47 10425579253=1078022538 :=
  takeStep (p:=211) (by decide) v46 c47 rfl (by decide) (by decide) rfl

private def ps48 : List ℕ := 223::ps47
private theorem c48 : F ps47 46751476=4843671 := by decide +kernel
private theorem v48 : F ps48 10425579253=1073178867 :=
  takeStep (p:=223) (by decide) v47 c48 rfl (by decide) (by decide) rfl

private def ps49 : List ℕ := 227::ps48
private theorem c49 : F ps48 45927661=4738104 := by decide +kernel
private theorem v49 : F ps49 10425579253=1068440763 :=
  takeStep (p:=227) (by decide) v48 c49 rfl (by decide) (by decide) rfl

private def ps50 : List ℕ := 229::ps49
private theorem c50 : F ps49 45526546=4676972 := by decide +kernel
private theorem v50 : F ps50 10425579253=1063763791 :=
  takeStep (p:=229) (by decide) v49 c50 rfl (by decide) (by decide) rfl

private def ps51 : List ℕ := 233::ps50
private theorem c51 : F ps50 44744975=4577660 := by decide +kernel
private theorem v51 : F ps51 10425579253=1059186131 :=
  takeStep (p:=233) (by decide) v50 c51 rfl (by decide) (by decide) rfl

private def ps52 : List ℕ := 239::ps51
private theorem c52 : F ps51 43621670=4444795 := by decide +kernel
private theorem v52 : F ps52 10425579253=1054741336 :=
  takeStep (p:=239) (by decide) v51 c52 rfl (by decide) (by decide) rfl

private def ps53 : List ℕ := 241::ps52
private theorem c53 : F ps52 43259664=4390479 := by decide +kernel
private theorem v53 : F ps53 10425579253=1050350857 :=
  takeStep (p:=241) (by decide) v52 c53 rfl (by decide) (by decide) rfl

private def ps54 : List ℕ := 251::ps53
private theorem c54 : F ps53 41536172=4199368 := by decide +kernel
private theorem v54 : F ps54 10425579253=1046151489 :=
  takeStep (p:=251) (by decide) v53 c54 rfl (by decide) (by decide) rfl

private def ps55 : List ℕ := 257::ps54
private theorem c55 : F ps54 40566456=4086020 := by decide +kernel
private theorem v55 : F ps55 10425579253=1042065469 :=
  takeStep (p:=257) (by decide) v54 c55 rfl (by decide) (by decide) rfl

private def ps56 : List ℕ := 263::ps55
private theorem c56 : F ps55 39640985=3978295 := by decide +kernel
private theorem v56 : F ps56 10425579253=1038087174 :=
  takeStep (p:=263) (by decide) v55 c56 rfl (by decide) (by decide) rfl

private def ps57 : List ℕ := 269::ps56
private theorem c57 : F ps56 38756800=3875678 := by decide +kernel
private theorem v57 : F ps57 10425579253=1034211496 :=
  takeStep (p:=269) (by decide) v56 c57 rfl (by decide) (by decide) rfl

private def ps58 : List ℕ := 271::ps57
private theorem c58 : F ps57 38470772=3833545 := by decide +kernel
private theorem v58 : F ps58 10425579253=1030377951 :=
  takeStep (p:=271) (by decide) v57 c58 rfl (by decide) (by decide) rfl

private def ps59 : List ℕ := 277::ps58
private theorem c59 : F ps58 37637470=3737463 := by decide +kernel
private theorem v59 : F ps59 10425579253=1026640488 :=
  takeStep (p:=277) (by decide) v58 c59 rfl (by decide) (by decide) rfl

private def ps60 : List ℕ := 281::ps59
private theorem c60 : F ps59 37101705=3671699 := by decide +kernel
private theorem v60 : F ps60 10425579253=1022968789 :=
  takeStep (p:=281) (by decide) v59 c60 rfl (by decide) (by decide) rfl

private def ps61 : List ℕ := 283::ps60
private theorem c61 : F ps60 36839502=3633420 := by decide +kernel
private theorem v61 : F ps61 10425579253=1019335369 :=
  takeStep (p:=283) (by decide) v60 c61 rfl (by decide) (by decide) rfl

private def ps62 : List ℕ := 293::ps61
private theorem c62 : F ps61 35582181=3497817 := by decide +kernel
private theorem v62 : F ps62 10425579253=1015837552 :=
  takeStep (p:=293) (by decide) v61 c62 rfl (by decide) (by decide) rfl

private def ps63 : List ℕ := 307::ps62
private theorem c63 : F ps62 33959541=3327739 := by decide +kernel
private theorem v63 : F ps63 10425579253=1012509813 :=
  takeStep (p:=307) (by decide) v62 c63 rfl (by decide) (by decide) rfl

private def ps64 : List ℕ := 311::ps63
private theorem c64 : F ps63 33522762=3274684 := by decide +kernel
private theorem v64 : F ps64 10425579253=1009235129 :=
  takeStep (p:=311) (by decide) v63 c64 rfl (by decide) (by decide) rfl

private def ps65 : List ℕ := 313::ps64
private theorem c65 : F ps64 33308559=3243628 := by decide +kernel
private theorem v65 : F ps65 10425579253=1005991501 :=
  takeStep (p:=313) (by decide) v64 c65 rfl (by decide) (by decide) rfl

private def ps66 : List ℕ := 317::ps65
private theorem c66 : F ps65 32888262=3192764 := by decide +kernel
private theorem v66 : F ps66 10425579253=1002798737 :=
  takeStep (p:=317) (by decide) v65 c66 rfl (by decide) (by decide) rfl

private def ps67 : List ℕ := 331::ps66
private theorem c67 : F ps66 31497218=3048322 := by decide +kernel
private theorem v67 : F ps67 10425579253=999750415 :=
  takeStep (p:=331) (by decide) v66 c67 rfl (by decide) (by decide) rfl

private def ps68 : List ℕ := 337::ps67
private theorem c68 : F ps67 30936436=2985133 := by decide +kernel
private theorem v68 : F ps68 10425579253=996765282 :=
  takeStep (p:=337) (by decide) v67 c68 rfl (by decide) (by decide) rfl

private def ps69 : List ℕ := 347::ps68
private theorem c69 : F ps68 30044896=2890525 := by decide +kernel
private theorem v69 : F ps69 10425579253=993874757 :=
  takeStep (p:=347) (by decide) v68 c69 rfl (by decide) (by decide) rfl

private def ps70 : List ℕ := 349::ps69
private theorem c70 : F ps69 29872719=2865629 := by decide +kernel
private theorem v70 : F ps70 10425579253=991009128 :=
  takeStep (p:=349) (by decide) v69 c70 rfl (by decide) (by decide) rfl

private def ps71 : List ℕ := 353::ps70
private theorem c71 : F ps70 29534218=2824906 := by decide +kernel
private theorem v71 : F ps71 10425579253=988184222 :=
  takeStep (p:=353) (by decide) v70 c71 rfl (by decide) (by decide) rfl

private def ps72 : List ℕ := 359::ps71
private theorem c72 : F ps71 29040610=2769670 := by decide +kernel
private theorem v72 : F ps72 10425579253=985414552 :=
  takeStep (p:=359) (by decide) v71 c72 rfl (by decide) (by decide) rfl

private def ps73 : List ℕ := 367::ps72
private theorem c73 : F ps72 28407572=2701586 := by decide +kernel
private theorem v73 : F ps73 10425579253=982712966 :=
  takeStep (p:=367) (by decide) v72 c73 rfl (by decide) (by decide) rfl

private def ps74 : List ℕ := 373::ps73
private theorem c74 : F ps73 27950614=2650603 := by decide +kernel
private theorem v74 : F ps74 10425579253=980062363 :=
  takeStep (p:=373) (by decide) v73 c74 rfl (by decide) (by decide) rfl

private def ps75 : List ℕ := 379::ps74
private theorem c75 : F ps74 27508124=2601329 := by decide +kernel
private theorem v75 : F ps75 10425579253=977461034 :=
  takeStep (p:=379) (by decide) v74 c75 rfl (by decide) (by decide) rfl

private def ps76 : List ℕ := 383::ps75
private theorem c76 : F ps75 27220833=2567075 := by decide +kernel
private theorem v76 : F ps76 10425579253=974893959 :=
  takeStep (p:=383) (by decide) v75 c76 rfl (by decide) (by decide) rfl

private def ps77 : List ℕ := 389::ps76
private theorem c77 : F ps76 26800974=2520522 := by decide +kernel
private theorem v77 : F ps77 10425579253=972373437 :=
  takeStep (p:=389) (by decide) v76 c77 rfl (by decide) (by decide) rfl

private def ps78 : List ℕ := 397::ps77
private theorem c78 : F ps77 26260904=2462914 := by decide +kernel
private theorem v78 : F ps78 10425579253=969910523 :=
  takeStep (p:=397) (by decide) v77 c78 rfl (by decide) (by decide) rfl

private def ps79 : List ℕ := 401::ps78
private theorem c79 : F ps78 25998950=2431812 := by decide +kernel
private theorem v79 : F ps79 10425579253=967478711 :=
  takeStep (p:=401) (by decide) v78 c79 rfl (by decide) (by decide) rfl

private def ps80 : List ℕ := 409::ps79
private theorem c80 : F ps79 25490413=2377730 := by decide +kernel
private theorem v80 : F ps80 10425579253=965100981 :=
  takeStep (p:=409) (by decide) v79 c80 rfl (by decide) (by decide) rfl

private def ps81 : List ℕ := 419::ps80
private theorem c81 : F ps80 24882050=2314730 := by decide +kernel
private theorem v81 : F ps81 10425579253=962786251 :=
  takeStep (p:=419) (by decide) v80 c81 rfl (by decide) (by decide) rfl

private def ps82 : List ℕ := 421::ps81
private theorem c82 : F ps81 24763846=2297782 := by decide +kernel
private theorem v82 : F ps82 10425579253=960488469 :=
  takeStep (p:=421) (by decide) v81 c82 rfl (by decide) (by decide) rfl

private def ps83 : List ℕ := 431::ps82
private theorem c83 : F ps82 24189279=2238450 := by decide +kernel
private theorem v83 : F ps83 10425579253=958250019 :=
  takeStep (p:=431) (by decide) v82 c83 rfl (by decide) (by decide) rfl

private def ps84 : List ℕ := 433::ps83
private theorem c84 : F ps83 24077550=2222478 := by decide +kernel
private theorem v84 : F ps84 10425579253=956027541 :=
  takeStep (p:=433) (by decide) v83 c84 rfl (by decide) (by decide) rfl

private def ps85 : List ℕ := 439::ps84
private theorem c85 : F ps84 23748472=2186398 := by decide +kernel
private theorem v85 : F ps85 10425579253=953841143 :=
  takeStep (p:=439) (by decide) v84 c85 rfl (by decide) (by decide) rfl

private def ps86 : List ℕ := 443::ps85
private theorem c86 : F ps85 23534038=2161193 := by decide +kernel
private theorem v86 : F ps86 10425579253=951679950 :=
  takeStep (p:=443) (by decide) v85 c86 rfl (by decide) (by decide) rfl

private def ps87 : List ℕ := 449::ps86
private theorem c87 : F ps86 23219552=2126839 := by decide +kernel
private theorem v87 : F ps87 10425579253=949553111 :=
  takeStep (p:=449) (by decide) v86 c87 rfl (by decide) (by decide) rfl

private def ps88 : List ℕ := 457::ps87
private theorem c88 : F ps87 22813083=2084272 := by decide +kernel
private theorem v88 : F ps88 10425579253=947468839 :=
  takeStep (p:=457) (by decide) v87 c88 rfl (by decide) (by decide) rfl

private def ps89 : List ℕ := 461::ps88
private theorem c89 : F ps88 22615139=2061034 := by decide +kernel
private theorem v89 : F ps89 10425579253=945407805 :=
  takeStep (p:=461) (by decide) v88 c89 rfl (by decide) (by decide) rfl

private def ps90 : List ℕ := 463::ps89
private theorem c90 : F ps89 22517449=2047127 := by decide +kernel
private theorem v90 : F ps90 10425579253=943360678 :=
  takeStep (p:=463) (by decide) v89 c90 rfl (by decide) (by decide) rfl

private def ps91 : List ℕ := 467::ps90
private theorem c91 : F ps90 22324580=2024623 := by decide +kernel
private theorem v91 : F ps91 10425579253=941336055 :=
  takeStep (p:=467) (by decide) v90 c91 rfl (by decide) (by decide) rfl

private def ps92 : List ℕ := 479::ps91
private theorem c92 : F ps91 21765301=1968807 := by decide +kernel
private theorem v92 : F ps92 10425579253=939367248 :=
  takeStep (p:=479) (by decide) v91 c92 rfl (by decide) (by decide) rfl

private def ps93 : List ℕ := 487::ps92
private theorem c93 : F ps92 21407760=1931651 := by decide +kernel
private theorem v93 : F ps93 10425579253=937435597 :=
  takeStep (p:=487) (by decide) v92 c93 rfl (by decide) (by decide) rfl

private def ps94 : List ℕ := 491::ps93
private theorem c94 : F ps93 21233358=1911311 := by decide +kernel
private theorem v94 : F ps94 10425579253=935524286 :=
  takeStep (p:=491) (by decide) v93 c94 rfl (by decide) (by decide) rfl

private def ps95 : List ℕ := 499::ps94
private theorem c95 : F ps94 20892944=1876054 := by decide +kernel
private theorem v95 : F ps95 10425579253=933648232 :=
  takeStep (p:=499) (by decide) v94 c95 rfl (by decide) (by decide) rfl

private def ps96 : List ℕ := 503::ps95
private theorem c96 : F ps95 20726797=1856771 := by decide +kernel
private theorem v96 : F ps96 10425579253=931791461 :=
  takeStep (p:=503) (by decide) v95 c96 rfl (by decide) (by decide) rfl

private def ps97 : List ℕ := 509::ps96
private theorem c97 : F ps96 20482473=1830495 := by decide +kernel
private theorem v97 : F ps97 10425579253=929960966 :=
  takeStep (p:=509) (by decide) v96 c97 rfl (by decide) (by decide) rfl

private def ps98 : List ℕ := 521::ps97
private theorem c98 : F ps97 20010708=1783921 := by decide +kernel
private theorem v98 : F ps98 10425579253=928177045 :=
  takeStep (p:=521) (by decide) v97 c98 rfl (by decide) (by decide) rfl

private def ps99 : List ℕ := 523::ps98
private theorem c99 : F ps98 19934185=1773094 := by decide +kernel
private theorem v99 : F ps99 10425579253=926403951 :=
  takeStep (p:=523) (by decide) v98 c99 rfl (by decide) (by decide) rfl

private def ps100 : List ℕ := 541::ps99
private theorem c100 : F ps99 19270941=1709671 := by decide +kernel
private theorem v100 : F ps100 10425579253=924694280 :=
  takeStep (p:=541) (by decide) v99 c100 rfl (by decide) (by decide) rfl

private def ps101 : List ℕ := 547::ps100
private theorem c101 : F ps100 19059559=1687112 := by decide +kernel
private theorem v101 : F ps101 10425579253=923007168 :=
  takeStep (p:=547) (by decide) v100 c101 rfl (by decide) (by decide) rfl

private def ps102 : List ℕ := 557::ps101
private theorem c102 : F ps101 18717377=1652911 := by decide +kernel
private theorem v102 : F ps102 10425579253=921354257 :=
  takeStep (p:=557) (by decide) v101 c102 rfl (by decide) (by decide) rfl

private def ps103 : List ℕ := 563::ps102
private theorem c103 : F ps102 18517902=1631601 := by decide +kernel
private theorem v103 : F ps103 10425579253=919722656 :=
  takeStep (p:=563) (by decide) v102 c103 rfl (by decide) (by decide) rfl

private def ps104 : List ℕ := 569::ps103
private theorem c104 : F ps103 18322634=1610864 := by decide +kernel
private theorem v104 : F ps104 10425579253=918111792 :=
  takeStep (p:=569) (by decide) v103 c104 rfl (by decide) (by decide) rfl

private def ps105 : List ℕ := 571::ps104
private theorem c105 : F ps104 18258457=1601803 := by decide +kernel
private theorem v105 : F ps105 10425579253=916509989 :=
  takeStep (p:=571) (by decide) v104 c105 rfl (by decide) (by decide) rfl

private def ps106 : List ℕ := 577::ps105
private theorem c106 : F ps105 18068594=1581667 := by decide +kernel
private theorem v106 : F ps106 10425579253=914928322 :=
  takeStep (p:=577) (by decide) v105 c106 rfl (by decide) (by decide) rfl

private def ps107 : List ℕ := 587::ps106
private theorem c107 : F ps106 17760782=1551208 := by decide +kernel
private theorem v107 : F ps107 10425579253=913377114 :=
  takeStep (p:=587) (by decide) v106 c107 rfl (by decide) (by decide) rfl

private def ps108 : List ℕ := 593::ps107
private theorem c108 : F ps107 17581077=1532185 := by decide +kernel
private theorem v108 : F ps108 10425579253=911844929 :=
  takeStep (p:=593) (by decide) v107 c108 rfl (by decide) (by decide) rfl

private def ps109 : List ℕ := 599::ps108
private theorem c109 : F ps108 17404973=1513530 := by decide +kernel
private theorem v109 : F ps109 10425579253=910331399 :=
  takeStep (p:=599) (by decide) v108 c109 rfl (by decide) (by decide) rfl

private def ps110 : List ℕ := 601::ps109
private theorem c110 : F ps109 17347053=1505375 := by decide +kernel
private theorem v110 : F ps110 10425579253=908826024 :=
  takeStep (p:=601) (by decide) v109 c110 rfl (by decide) (by decide) rfl

private def ps111 : List ℕ := 607::ps110
private theorem c111 : F ps110 17175583=1487286 := by decide +kernel
private theorem v111 : F ps111 10425579253=907338738 :=
  takeStep (p:=607) (by decide) v110 c111 rfl (by decide) (by decide) rfl

private def ps112 : List ℕ := 613::ps111
private theorem c112 : F ps111 17007470=1469602 := by decide +kernel
private theorem v112 : F ps112 10425579253=905869136 :=
  takeStep (p:=613) (by decide) v111 c112 rfl (by decide) (by decide) rfl

private def ps113 : List ℕ := 617::ps112
private theorem c113 : F ps112 16897211=1457005 := by decide +kernel
private theorem v113 : F ps113 10425579253=904412131 :=
  takeStep (p:=617) (by decide) v112 c113 rfl (by decide) (by decide) rfl

private def ps114 : List ℕ := 619::ps113
private theorem c114 : F ps113 16842615=1449374 := by decide +kernel
private theorem v114 : F ps114 10425579253=902962757 :=
  takeStep (p:=619) (by decide) v113 c114 rfl (by decide) (by decide) rfl

private def ps115 : List ℕ := 631::ps114
private theorem c115 : F ps114 16522312=1418561 := by decide +kernel
private theorem v115 : F ps115 10425579253=901544196 :=
  takeStep (p:=631) (by decide) v114 c115 rfl (by decide) (by decide) rfl

private def ps116 : List ℕ := 641::ps115
private theorem c116 : F ps115 16264554=1393438 := by decide +kernel
private theorem v116 : F ps116 10425579253=900150758 :=
  takeStep (p:=641) (by decide) v115 c116 rfl (by decide) (by decide) rfl

private def ps117 : List ℕ := 643::ps116
private theorem c117 : F ps116 16213964=1386354 := by decide +kernel
private theorem v117 : F ps117 10425579253=898764404 :=
  takeStep (p:=643) (by decide) v116 c117 rfl (by decide) (by decide) rfl

private def ps118 : List ℕ := 647::ps117
private theorem c118 : F ps117 16113723=1375005 := by decide +kernel
private theorem v118 : F ps118 10425579253=897389399 :=
  takeStep (p:=647) (by decide) v117 c118 rfl (by decide) (by decide) rfl

private def ps119 : List ℕ := 653::ps118
private theorem c119 : F ps118 15965665=1359589 := by decide +kernel
private theorem v119 : F ps119 10425579253=896029810 :=
  takeStep (p:=653) (by decide) v118 c119 rfl (by decide) (by decide) rfl

private def ps120 : List ℕ := 659::ps119
private theorem c120 : F ps119 15820302=1344411 := by decide +kernel
private theorem v120 : F ps120 10425579253=894685399 :=
  takeStep (p:=659) (by decide) v119 c120 rfl (by decide) (by decide) rfl

private def ps121 : List ℕ := 661::ps120
private theorem c121 : F ps120 15772434=1337740 := by decide +kernel
private theorem v121 : F ps121 10425579253=893347659 :=
  takeStep (p:=661) (by decide) v120 c121 rfl (by decide) (by decide) rfl

private def ps122 : List ℕ := 673::ps121
private theorem c122 : F ps121 15491202=1310986 := by decide +kernel
private theorem v122 : F ps122 10425579253=892036673 :=
  takeStep (p:=673) (by decide) v121 c122 rfl (by decide) (by decide) rfl

private def ps123 : List ℕ := 677::ps122
private theorem c123 : F ps122 15399673=1300682 := by decide +kernel
private theorem v123 : F ps123 10425579253=890735991 :=
  takeStep (p:=677) (by decide) v122 c123 rfl (by decide) (by decide) rfl

private def ps124 : List ℕ := 683::ps123
private theorem c124 : F ps123 15264391=1286703 := by decide +kernel
private theorem v124 : F ps124 10425579253=889449288 :=
  takeStep (p:=683) (by decide) v123 c124 rfl (by decide) (by decide) rfl

private def ps125 : List ℕ := 691::ps124
private theorem c125 : F ps124 15087668=1269206 := by decide +kernel
private theorem v125 : F ps125 10425579253=888180082 :=
  takeStep (p:=691) (by decide) v124 c125 rfl (by decide) (by decide) rfl

private def ps126 : List ℕ := 701::ps125
private theorem c126 : F ps125 14872438=1248532 := by decide +kernel
private theorem v126 : F ps126 10425579253=886931550 :=
  takeStep (p:=701) (by decide) v125 c126 rfl (by decide) (by decide) rfl

private def ps127 : List ℕ := 709::ps126
private theorem c127 : F ps126 14704625=1231953 := by decide +kernel
private theorem v127 : F ps127 10425579253=885699597 :=
  takeStep (p:=709) (by decide) v126 c127 rfl (by decide) (by decide) rfl

private def ps128 : List ℕ := 719::ps127
private theorem c128 : F ps127 14500110=1212394 := by decide +kernel
private theorem v128 : F ps128 10425579253=884487203 :=
  takeStep (p:=719) (by decide) v127 c128 rfl (by decide) (by decide) rfl

private def ps129 : List ℕ := 727::ps128
private theorem c129 : F ps128 14340549=1196652 := by decide +kernel
private theorem v129 : F ps129 10425579253=883290551 :=
  takeStep (p:=727) (by decide) v128 c129 rfl (by decide) (by decide) rfl

private def ps130 : List ℕ := 733::ps129
private theorem c130 : F ps129 14223164=1184596 := by decide +kernel
private theorem v130 : F ps130 10425579253=882105955 :=
  takeStep (p:=733) (by decide) v129 c130 rfl (by decide) (by decide) rfl

private def ps131 : List ℕ := 739::ps130
private theorem c131 : F ps130 14107685=1172770 := by decide +kernel
private theorem v131 : F ps131 10425579253=880933185 :=
  takeStep (p:=739) (by decide) v130 c131 rfl (by decide) (by decide) rfl

private def ps132 : List ℕ := 743::ps131
private theorem c132 : F ps131 14031735=1164333 := by decide +kernel
private theorem v132 : F ps132 10425579253=879768852 :=
  takeStep (p:=743) (by decide) v131 c132 rfl (by decide) (by decide) rfl

private def ps133 : List ℕ := 751::ps132
private theorem c133 : F ps132 13882262=1149718 := by decide +kernel
private theorem v133 : F ps133 10425579253=878619134 :=
  takeStep (p:=751) (by decide) v132 c133 rfl (by decide) (by decide) rfl

private def ps134 : List ℕ := 757::ps133
private theorem c134 : F ps133 13772231=1138437 := by decide +kernel
private theorem v134 : F ps134 10425579253=877480697 :=
  takeStep (p:=757) (by decide) v133 c134 rfl (by decide) (by decide) rfl

private def ps135 : List ℕ := 761::ps134
private theorem c135 : F ps134 13699841=1130386 := by decide +kernel
private theorem v135 : F ps135 10425579253=876350311 :=
  takeStep (p:=761) (by decide) v134 c135 rfl (by decide) (by decide) rfl

private def ps136 : List ℕ := 769::ps135
private theorem c136 : F ps135 13557320=1116489 := by decide +kernel
private theorem v136 : F ps136 10425579253=875233822 :=
  takeStep (p:=769) (by decide) v135 c136 rfl (by decide) (by decide) rfl

private def ps137 : List ℕ := 773::ps136
private theorem c137 : F ps136 13487165=1108754 := by decide +kernel
private theorem v137 : F ps137 10425579253=874125068 :=
  takeStep (p:=773) (by decide) v136 c137 rfl (by decide) (by decide) rfl

private def ps138 : List ℕ := 787::ps137
private theorem c138 : F ps137 13247241=1086826 := by decide +kernel
private theorem v138 : F ps138 10425579253=873038242 :=
  takeStep (p:=787) (by decide) v137 c138 rfl (by decide) (by decide) rfl

private def ps139 : List ℕ := 797::ps138
private theorem c139 : F ps138 13081027=1071169 := by decide +kernel
private theorem v139 : F ps139 10425579253=871967073 :=
  takeStep (p:=797) (by decide) v138 c139 rfl (by decide) (by decide) rfl

private def ps140 : List ℕ := 809::ps139
private theorem c140 : F ps139 12886995=1053288 := by decide +kernel
private theorem v140 : F ps140 10425579253=870913785 :=
  takeStep (p:=809) (by decide) v139 c140 rfl (by decide) (by decide) rfl

private def ps141 : List ℕ := 811::ps140
private theorem c141 : F ps140 12855214=1048933 := by decide +kernel
private theorem v141 : F ps141 10425579253=869864852 :=
  takeStep (p:=811) (by decide) v140 c141 rfl (by decide) (by decide) rfl

private def ps142 : List ℕ := 821::ps141
private theorem c142 : F ps141 12698634=1034164 := by decide +kernel
private theorem v142 : F ps142 10425579253=868830688 :=
  takeStep (p:=821) (by decide) v141 c142 rfl (by decide) (by decide) rfl

private def ps143 : List ℕ := 823::ps142
private theorem c143 : F ps142 12667775=1029948 := by decide +kernel
private theorem v143 : F ps143 10425579253=867800740 :=
  takeStep (p:=823) (by decide) v142 c143 rfl (by decide) (by decide) rfl

private def ps144 : List ℕ := 827::ps143
private theorem c144 : F ps143 12606504=1023198 := by decide +kernel
private theorem v144 : F ps144 10425579253=866777542 :=
  takeStep (p:=827) (by decide) v143 c144 rfl (by decide) (by decide) rfl

private def ps145 : List ℕ := 829::ps144
private theorem c145 : F ps144 12576090=1019049 := by decide +kernel
private theorem v145 : F ps145 10425579253=865758493 :=
  takeStep (p:=829) (by decide) v144 c145 rfl (by decide) (by decide) rfl

private def ps146 : List ℕ := 839::ps145
private theorem c146 : F ps145 12426196=1005095 := by decide +kernel
private theorem v146 : F ps146 10425579253=864753398 :=
  takeStep (p:=839) (by decide) v145 c146 rfl (by decide) (by decide) rfl

private def ps147 : List ℕ := 853::ps146
private theorem c147 : F ps146 12222250=986660 := by decide +kernel
private theorem v147 : F ps147 10425579253=863766738 :=
  takeStep (p:=853) (by decide) v146 c147 rfl (by decide) (by decide) rfl

private def ps148 : List ℕ := 857::ps147
private theorem c148 : F ps147 12165203=980426 := by decide +kernel
private theorem v148 : F ps148 10425579253=862786312 :=
  takeStep (p:=857) (by decide) v147 c148 rfl (by decide) (by decide) rfl

private def ps149 : List ℕ := 859::ps148
private theorem c149 : F ps148 12136879=976570 := by decide +kernel
private theorem v149 : F ps149 10425579253=861809742 :=
  takeStep (p:=859) (by decide) v148 c149 rfl (by decide) (by decide) rfl

private def ps150 : List ℕ := 863::ps149
private theorem c150 : F ps149 12080624=970450 := by decide +kernel
private theorem v150 : F ps150 10425579253=860839292 :=
  takeStep (p:=863) (by decide) v149 c150 rfl (by decide) (by decide) rfl

private def ps151 : List ℕ := 877::ps150
private theorem c151 : F ps150 11887775=953181 := by decide +kernel
private theorem v151 : F ps151 10425579253=859886111 :=
  takeStep (p:=877) (by decide) v150 c151 rfl (by decide) (by decide) rfl

private def ps152 : List ℕ := 881::ps151
private theorem c152 : F ps151 11833801=947307 := by decide +kernel
private theorem v152 : F ps152 10425579253=858938804 :=
  takeStep (p:=881) (by decide) v151 c152 rfl (by decide) (by decide) rfl

private def ps153 : List ℕ := 883::ps152
private theorem c153 : F ps152 11806998=943691 := by decide +kernel
private theorem v153 : F ps153 10425579253=857995113 :=
  takeStep (p:=883) (by decide) v152 c153 rfl (by decide) (by decide) rfl

private def ps154 : List ℕ := 887::ps153
private theorem c154 : F ps153 11753753=937900 := by decide +kernel
private theorem v154 : F ps154 10425579253=857057213 :=
  takeStep (p:=887) (by decide) v153 c154 rfl (by decide) (by decide) rfl

private def ps155 : List ℕ := 907::ps154
private theorem c155 : F ps154 11494574=915376 := by decide +kernel
private theorem v155 : F ps155 10425579253=856141837 :=
  takeStep (p:=907) (by decide) v154 c155 rfl (by decide) (by decide) rfl

private def ps156 : List ℕ := 911::ps155
private theorem c156 : F ps155 11444104=909893 := by decide +kernel
private theorem v156 : F ps156 10425579253=855231944 :=
  takeStep (p:=911) (by decide) v155 c156 rfl (by decide) (by decide) rfl

private def ps157 : List ℕ := 919::ps156
private theorem c157 : F ps156 11344482=900498 := by decide +kernel
private theorem v157 : F ps157 10425579253=854331446 :=
  takeStep (p:=919) (by decide) v156 c157 rfl (by decide) (by decide) rfl

private def ps158 : List ℕ := 929::ps157
private theorem c158 : F ps157 11222367=889317 := by decide +kernel
private theorem v158 : F ps158 10425579253=853442129 :=
  takeStep (p:=929) (by decide) v157 c158 rfl (by decide) (by decide) rfl

private def ps159 : List ℕ := 937::ps158
private theorem c159 : F ps158 11126552=880273 := by decide +kernel
private theorem v159 : F ps159 10425579253=852561856 :=
  takeStep (p:=937) (by decide) v158 c159 rfl (by decide) (by decide) rfl

private def ps160 : List ℕ := 941::ps159
private theorem c160 : F ps159 11079255=875203 := by decide +kernel
private theorem v160 : F ps160 10425579253=851686653 :=
  takeStep (p:=941) (by decide) v159 c160 rfl (by decide) (by decide) rfl

private def ps161 : List ℕ := 947::ps160
private theorem c161 : F ps160 11009059=868296 := by decide +kernel
private theorem v161 : F ps161 10425579253=850818357 :=
  takeStep (p:=947) (by decide) v160 c161 rfl (by decide) (by decide) rfl

private def ps162 : List ℕ := 953::ps161
private theorem c162 : F ps161 10939747=861485 := by decide +kernel
private theorem v162 : F ps162 10425579253=849956872 :=
  takeStep (p:=953) (by decide) v161 c162 rfl (by decide) (by decide) rfl

private def ps163 : List ℕ := 967::ps162
private theorem c163 : F ps162 10781364=847518 := by decide +kernel
private theorem v163 : F ps163 10425579253=849109354 :=
  takeStep (p:=967) (by decide) v162 c163 rfl (by decide) (by decide) rfl

private def ps164 : List ℕ := 971::ps163
private theorem c164 : F ps163 10736950=842772 := by decide +kernel
private theorem v164 : F ps164 10425579253=848266582 :=
  takeStep (p:=971) (by decide) v163 c164 rfl (by decide) (by decide) rfl

private def ps165 : List ℕ := 977::ps164
private theorem c165 : F ps164 10671012=836283 := by decide +kernel
private theorem v165 : F ps165 10425579253=847430299 :=
  takeStep (p:=977) (by decide) v164 c165 rfl (by decide) (by decide) rfl

private def ps166 : List ℕ := 983::ps165
private theorem c166 : F ps165 10605879=829903 := by decide +kernel
private theorem v166 : F ps166 10425579253=846600396 :=
  takeStep (p:=983) (by decide) v165 c166 rfl (by decide) (by decide) rfl

private def ps167 : List ℕ := 991::ps166
private theorem c167 : F ps166 10520261=821921 := by decide +kernel
private theorem v167 : F ps167 10425579253=845778475 :=
  takeStep (p:=991) (by decide) v166 c167 rfl (by decide) (by decide) rfl

private def ps168 : List ℕ := 997::ps167
private theorem c168 : F ps167 10456950=815748 := by decide +kernel
private theorem v168 : F ps168 10425579253=844962727 :=
  takeStep (p:=997) (by decide) v167 c168 rfl (by decide) (by decide) rfl

private def ps169 : List ℕ := 1009::ps168
private theorem c169 : F ps168 10332585=804685 := by decide +kernel
private theorem v169 : F ps169 10425579253=844158042 :=
  takeStep (p:=1009) (by decide) v168 c169 rfl (by decide) (by decide) rfl

private def ps170 : List ℕ := 1013::ps169
private theorem c170 : F ps169 10291786=800369 := by decide +kernel
private theorem v170 : F ps170 10425579253=843357673 :=
  takeStep (p:=1013) (by decide) v169 c170 rfl (by decide) (by decide) rfl

private def ps171 : List ℕ := 1019::ps170
private theorem c171 : F ps170 10231186=794479 := by decide +kernel
private theorem v171 : F ps171 10425579253=842563194 :=
  takeStep (p:=1019) (by decide) v170 c171 rfl (by decide) (by decide) rfl

private def ps172 : List ℕ := 1021::ps171
private theorem c172 : F ps171 10211145=791803 := by decide +kernel
private theorem v172 : F ps172 10425579253=841771391 :=
  takeStep (p:=1021) (by decide) v171 c172 rfl (by decide) (by decide) rfl

private def ps173 : List ℕ := 1031::ps172
private theorem c173 : F ps172 10112104=782936 := by decide +kernel
private theorem v173 : F ps173 10425579253=840988455 :=
  takeStep (p:=1031) (by decide) v172 c173 rfl (by decide) (by decide) rfl

private def ps174 : List ℕ := 1033::ps173
private theorem c174 : F ps173 10092525=780361 := by decide +kernel
private theorem v174 : F ps174 10425579253=840208094 :=
  takeStep (p:=1033) (by decide) v173 c174 rfl (by decide) (by decide) rfl

private def ps175 : List ℕ := 1039::ps174
private theorem c175 : F ps174 10034243=774733 := by decide +kernel
private theorem v175 : F ps175 10425579253=839433361 :=
  takeStep (p:=1039) (by decide) v174 c175 rfl (by decide) (by decide) rfl

private def ps176 : List ℕ := 1049::ps175
private theorem c176 : F ps175 9938588=766182 := by decide +kernel
private theorem v176 : F ps176 10425579253=838667179 :=
  takeStep (p:=1049) (by decide) v175 c176 rfl (by decide) (by decide) rfl

private def ps177 : List ℕ := 1051::ps176
private theorem c177 : F ps176 9919675=763700 := by decide +kernel
private theorem v177 : F ps177 10425579253=837903479 :=
  takeStep (p:=1051) (by decide) v176 c177 rfl (by decide) (by decide) rfl

private def ps178 : List ℕ := 1061::ps177
private theorem c178 : F ps177 9826182=755392 := by decide +kernel
private theorem v178 : F ps178 10425579253=837148087 :=
  takeStep (p:=1061) (by decide) v177 c178 rfl (by decide) (by decide) rfl

private def ps179 : List ℕ := 1063::ps178
private theorem c179 : F ps178 9807694=752961 := by decide +kernel
private theorem v179 : F ps179 10425579253=836395126 :=
  takeStep (p:=1063) (by decide) v178 c179 rfl (by decide) (by decide) rfl

private def ps180 : List ℕ := 1069::ps179
private theorem c180 : F ps179 9752646=747706 := by decide +kernel
private theorem v180 : F ps180 10425579253=835647420 :=
  takeStep (p:=1069) (by decide) v179 c180 rfl (by decide) (by decide) rfl

private def ps181 : List ℕ := 1087::ps180
private theorem c181 : F ps180 9591149=734117 := by decide +kernel
private theorem v181 : F ps181 10425579253=834913303 :=
  takeStep (p:=1087) (by decide) v180 c181 rfl (by decide) (by decide) rfl

private def ps182 : List ℕ := 1091::ps181
private theorem c182 : F ps181 9555984=730419 := by decide +kernel
private theorem v182 : F ps182 10425579253=834182884 :=
  takeStep (p:=1091) (by decide) v181 c182 rfl (by decide) (by decide) rfl

private def ps183 : List ℕ := 1093::ps182
private theorem c183 : F ps182 9538498=728124 := by decide +kernel
private theorem v183 : F ps183 10425579253=833454760 :=
  takeStep (p:=1093) (by decide) v182 c183 rfl (by decide) (by decide) rfl

private def ps184 : List ℕ := 1097::ps183
private theorem c184 : F ps183 9503718=724525 := by decide +kernel
private theorem v184 : F ps184 10425579253=832730235 :=
  takeStep (p:=1097) (by decide) v183 c184 rfl (by decide) (by decide) rfl

private def ps185 : List ℕ := 1103::ps184
private theorem c185 : F ps184 9452021=719639 := by decide +kernel
private theorem v185 : F ps185 10425579253=832010596 :=
  takeStep (p:=1103) (by decide) v184 c185 rfl (by decide) (by decide) rfl

private def ps186 : List ℕ := 1109::ps185
private theorem c186 : F ps185 9400883=714785 := by decide +kernel
private theorem v186 : F ps186 10425579253=831295811 :=
  takeStep (p:=1109) (by decide) v185 c186 rfl (by decide) (by decide) rfl

private def ps187 : List ℕ := 1117::ps186
private theorem c187 : F ps186 9333553=708682 := by decide +kernel
private theorem v187 : F ps187 10425579253=830587129 :=
  takeStep (p:=1117) (by decide) v186 c187 rfl (by decide) (by decide) rfl

private def ps188 : List ℕ := 1123::ps187
private theorem c188 : F ps187 9283685=703963 := by decide +kernel
private theorem v188 : F ps188 10425579253=829883166 :=
  takeStep (p:=1123) (by decide) v187 c188 rfl (by decide) (by decide) rfl

private def ps189 : List ℕ := 1129::ps188
private theorem c189 : F ps188 9234348=699307 := by decide +kernel
private theorem v189 : F ps189 10425579253=829183859 :=
  takeStep (p:=1129) (by decide) v188 c189 rfl (by decide) (by decide) rfl

private def ps190 : List ℕ := 1151::ps189
private theorem c190 : F ps189 9057844=684801 := by decide +kernel
private theorem v190 : F ps190 10425579253=828499058 :=
  takeStep (p:=1151) (by decide) v189 c190 rfl (by decide) (by decide) rfl

private def ps191 : List ℕ := 1153::ps190
private theorem c191 : F ps190 9042132=682806 := by decide +kernel
private theorem v191 : F ps191 10425579253=827816252 :=
  takeStep (p:=1153) (by decide) v190 c191 rfl (by decide) (by decide) rfl

private def ps192 : List ℕ := 1163::ps191
private theorem c192 : F ps191 8964384=676027 := by decide +kernel
private theorem v192 : F ps192 10425579253=827140225 :=
  takeStep (p:=1163) (by decide) v191 c192 rfl (by decide) (by decide) rfl

private def ps193 : List ℕ := 1171::ps192
private theorem c193 : F ps192 8903141=670541 := by decide +kernel
private theorem v193 : F ps193 10425579253=826469684 :=
  takeStep (p:=1171) (by decide) v192 c193 rfl (by decide) (by decide) rfl

private def ps194 : List ℕ := 1181::ps193
private theorem c194 : F ps193 8827755=664022 := by decide +kernel
private theorem v194 : F ps194 10425579253=825805662 :=
  takeStep (p:=1181) (by decide) v193 c194 rfl (by decide) (by decide) rfl

private def ps195 : List ℕ := 1187::ps194
private theorem c195 : F ps194 8783133=659852 := by decide +kernel
private theorem v195 : F ps195 10425579253=825145810 :=
  takeStep (p:=1187) (by decide) v194 c195 rfl (by decide) (by decide) rfl

private def ps196 : List ℕ := 1193::ps195
private theorem c196 : F ps195 8738959=655704 := by decide +kernel
private theorem v196 : F ps196 10425579253=824490106 :=
  takeStep (p:=1193) (by decide) v195 c196 rfl (by decide) (by decide) rfl

private def ps197 : List ℕ := 1201::ps196
private theorem c197 : F ps196 8680748=650474 := by decide +kernel
private theorem v197 : F ps197 10425579253=823839632 :=
  takeStep (p:=1201) (by decide) v196 c197 rfl (by decide) (by decide) rfl

private def ps198 : List ℕ := 1213::ps197
private theorem c198 : F ps197 8594871=643193 := by decide +kernel
private theorem v198 : F ps198 10425579253=823196439 :=
  takeStep (p:=1213) (by decide) v197 c198 rfl (by decide) (by decide) rfl

private def ps199 : List ℕ := 1217::ps198
private theorem c199 : F ps198 8566622=640308 := by decide +kernel
private theorem v199 : F ps199 10425579253=822556131 :=
  takeStep (p:=1217) (by decide) v198 c199 rfl (by decide) (by decide) rfl

private def ps200 : List ℕ := 1223::ps199
private theorem c200 : F ps199 8524594=636381 := by decide +kernel
private theorem v200 : F ps200 10425579253=821919750 :=
  takeStep (p:=1223) (by decide) v199 c200 rfl (by decide) (by decide) rfl

private def ps201 : List ℕ := 1229::ps200
private theorem c201 : F ps200 8482977=632502 := by decide +kernel
private theorem v201 : F ps201 10425579253=821287248 :=
  takeStep (p:=1229) (by decide) v200 c201 rfl (by decide) (by decide) rfl

private def ps202 : List ℕ := 1231::ps201
private theorem c202 : F ps201 8469195=630759 := by decide +kernel
private theorem v202 : F ps202 10425579253=820656489 :=
  takeStep (p:=1231) (by decide) v201 c202 rfl (by decide) (by decide) rfl

private def ps203 : List ℕ := 1237::ps202
private theorem c203 : F ps202 8428115=626976 := by decide +kernel
private theorem v203 : F ps203 10425579253=820029513 :=
  takeStep (p:=1237) (by decide) v202 c203 rfl (by decide) (by decide) rfl

private def ps204 : List ℕ := 1249::ps203
private theorem c204 : F ps203 8347141=620206 := by decide +kernel
private theorem v204 : F ps204 10425579253=819409307 :=
  takeStep (p:=1249) (by decide) v203 c204 rfl (by decide) (by decide) rfl

private def ps205 : List ℕ := 1259::ps204
private theorem c205 : F ps204 8280841=614547 := by decide +kernel
private theorem v205 : F ps205 10425579253=818794760 :=
  takeStep (p:=1259) (by decide) v204 c205 rfl (by decide) (by decide) rfl

private def ps206 : List ℕ := 1277::ps205
private theorem c206 : F ps205 8164118=605073 := by decide +kernel
private theorem v206 : F ps206 10425579253=818189687 :=
  takeStep (p:=1277) (by decide) v205 c206 rfl (by decide) (by decide) rfl

private def ps207 : List ℕ := 1279::ps206
private theorem c207 : F ps206 8151352=603476 := by decide +kernel
private theorem v207 : F ps207 10425579253=817586211 :=
  takeStep (p:=1279) (by decide) v206 c207 rfl (by decide) (by decide) rfl

private def ps208 : List ℕ := 1283::ps207
private theorem c208 : F ps207 8125938=600931 := by decide +kernel
private theorem v208 : F ps208 10425579253=816985280 :=
  takeStep (p:=1283) (by decide) v207 c208 rfl (by decide) (by decide) rfl

private def ps209 : List ℕ := 1289::ps208
private theorem c209 : F ps208 8088114=597477 := by decide +kernel
private theorem v209 : F ps209 10425579253=816387803 :=
  takeStep (p:=1289) (by decide) v208 c209 rfl (by decide) (by decide) rfl

private def ps210 : List ℕ := 1291::ps209
private theorem c210 : F ps209 8075584=595956 := by decide +kernel
private theorem v210 : F ps210 10425579253=815791847 :=
  takeStep (p:=1291) (by decide) v209 c210 rfl (by decide) (by decide) rfl

private def ps211 : List ℕ := 1297::ps210
private theorem c211 : F ps210 8038226=592506 := by decide +kernel
private theorem v211 : F ps211 10425579253=815199341 :=
  takeStep (p:=1297) (by decide) v210 c211 rfl (by decide) (by decide) rfl

private def ps212 : List ℕ := 1301::ps211
private theorem c212 : F ps211 8013512=590084 := by decide +kernel
private theorem v212 : F ps212 10425579253=814609257 :=
  takeStep (p:=1301) (by decide) v211 c212 rfl (by decide) (by decide) rfl

private def ps213 : List ℕ := 1303::ps212
private theorem c213 : F ps212 8001212=588573 := by decide +kernel
private theorem v213 : F ps213 10425579253=814020684 :=
  takeStep (p:=1303) (by decide) v212 c213 rfl (by decide) (by decide) rfl

private def ps214 : List ℕ := 1307::ps213
private theorem c214 : F ps213 7976724=586159 := by decide +kernel
private theorem v214 : F ps214 10425579253=813434525 :=
  takeStep (p:=1307) (by decide) v213 c214 rfl (by decide) (by decide) rfl

private def ps215 : List ℕ := 1319::ps214
private theorem c215 : F ps214 7904154=580138 := by decide +kernel
private theorem v215 : F ps215 10425579253=812854387 :=
  takeStep (p:=1319) (by decide) v214 c215 rfl (by decide) (by decide) rfl

private def ps216 : List ℕ := 1321::ps215
private theorem c216 : F ps215 7892187=578701 := by decide +kernel
private theorem v216 : F ps216 10425579253=812275686 :=
  takeStep (p:=1321) (by decide) v215 c216 rfl (by decide) (by decide) rfl

private def ps217 : List ℕ := 1327::ps216
private theorem c217 : F ps216 7856502=575455 := by decide +kernel
private theorem v217 : F ps217 10425579253=811700231 :=
  takeStep (p:=1327) (by decide) v216 c217 rfl (by decide) (by decide) rfl

private def ps218 : List ℕ := 1361::ps217
private theorem c218 : F ps217 7660234=560338 := by decide +kernel
private theorem v218 : F ps218 10425579253=811139893 :=
  takeStep (p:=1361) (by decide) v217 c218 rfl (by decide) (by decide) rfl

private def ps219 : List ℕ := 1367::ps218
private theorem c219 : F ps218 7626612=557312 := by decide +kernel
private theorem v219 : F ps219 10425579253=810582581 :=
  takeStep (p:=1367) (by decide) v218 c219 rfl (by decide) (by decide) rfl

private def ps220 : List ℕ := 1373::ps219
private theorem c220 : F ps219 7593284=554296 := by decide +kernel
private theorem v220 : F ps220 10425579253=810028285 :=
  takeStep (p:=1373) (by decide) v219 c220 rfl (by decide) (by decide) rfl

private def ps221 : List ℕ := 1381::ps220
private theorem c221 : F ps220 7549297=550556 := by decide +kernel
private theorem v221 : F ps221 10425579253=809477729 :=
  takeStep (p:=1381) (by decide) v220 c221 rfl (by decide) (by decide) rfl

private def ps222 : List ℕ := 1399::ps221
private theorem c222 : F ps221 7452165=542920 := by decide +kernel
private theorem v222 : F ps222 10425579253=808934809 :=
  takeStep (p:=1399) (by decide) v221 c222 rfl (by decide) (by decide) rfl

private def ps223 : List ℕ := 1409::ps222
private theorem c223 : F ps222 7399275=538511 := by decide +kernel
private theorem v223 : F ps223 10425579253=808396298 :=
  takeStep (p:=1409) (by decide) v222 c223 rfl (by decide) (by decide) rfl

private def ps224 : List ℕ := 1423::ps223
private theorem c224 : F ps223 7326478=532691 := by decide +kernel
private theorem v224 : F ps224 10425579253=807863607 :=
  takeStep (p:=1423) (by decide) v223 c224 rfl (by decide) (by decide) rfl

private def ps225 : List ℕ := 1427::ps224
private theorem c225 : F ps224 7305942=530711 := by decide +kernel
private theorem v225 : F ps225 10425579253=807332896 :=
  takeStep (p:=1427) (by decide) v224 c225 rfl (by decide) (by decide) rfl

private def ps226 : List ℕ := 1429::ps225
private theorem c226 : F ps225 7295716=529504 := by decide +kernel
private theorem v226 : F ps226 10425579253=806803392 :=
  takeStep (p:=1429) (by decide) v225 c226 rfl (by decide) (by decide) rfl

private def ps227 : List ℕ := 1433::ps226
private theorem c227 : F ps226 7275351=527544 := by decide +kernel
private theorem v227 : F ps227 10425579253=806275848 :=
  takeStep (p:=1433) (by decide) v226 c227 rfl (by decide) (by decide) rfl

private def ps228 : List ℕ := 1439::ps227
private theorem c228 : F ps227 7245016=524867 := by decide +kernel
private theorem v228 : F ps228 10425579253=805750981 :=
  takeStep (p:=1439) (by decide) v227 c228 rfl (by decide) (by decide) rfl

private def ps229 : List ℕ := 1447::ps228
private theorem c229 : F ps228 7204961=521479 := by decide +kernel
private theorem v229 : F ps229 10425579253=805229502 :=
  takeStep (p:=1447) (by decide) v228 c229 rfl (by decide) (by decide) rfl

private def ps230 : List ℕ := 1451::ps229
private theorem c230 : F ps229 7185099=519588 := by decide +kernel
private theorem v230 : F ps230 10425579253=804709914 :=
  takeStep (p:=1451) (by decide) v229 c230 rfl (by decide) (by decide) rfl

private def ps231 : List ℕ := 1453::ps230
private theorem c231 : F ps230 7175209=518449 := by decide +kernel
private theorem v231 : F ps231 10425579253=804191465 :=
  takeStep (p:=1453) (by decide) v230 c231 rfl (by decide) (by decide) rfl

private def ps232 : List ℕ := 1459::ps231
private theorem c232 : F ps231 7145702=515860 := by decide +kernel
private theorem v232 : F ps232 10425579253=803675605 :=
  takeStep (p:=1459) (by decide) v231 c232 rfl (by decide) (by decide) rfl

private def ps233 : List ℕ := 1471::ps232
private theorem c233 : F ps232 7087409=511200 := by decide +kernel
private theorem v233 : F ps233 10425579253=803164405 :=
  takeStep (p:=1471) (by decide) v232 c233 rfl (by decide) (by decide) rfl

private def ps234 : List ℕ := 1481::ps233
private theorem c234 : F ps233 7039553=507316 := by decide +kernel
private theorem v234 : F ps234 10425579253=802657089 :=
  takeStep (p:=1481) (by decide) v233 c234 rfl (by decide) (by decide) rfl

private def ps235 : List ℕ := 1483::ps234
private theorem c235 : F ps234 7030060=506198 := by decide +kernel
private theorem v235 : F ps235 10425579253=802150891 :=
  takeStep (p:=1483) (by decide) v234 c235 rfl (by decide) (by decide) rfl

private def ps236 : List ℕ := 1487::ps235
private theorem c236 : F ps235 7011149=504396 := by decide +kernel
private theorem v236 : F ps236 10425579253=801646495 :=
  takeStep (p:=1487) (by decide) v235 c236 rfl (by decide) (by decide) rfl

private def ps237 : List ℕ := 1489::ps236
private theorem c237 : F ps236 7001732=503326 := by decide +kernel
private theorem v237 : F ps237 10425579253=801143169 :=
  takeStep (p:=1489) (by decide) v236 c237 rfl (by decide) (by decide) rfl

private def ps238 : List ℕ := 1493::ps237
private theorem c238 : F ps237 6982973=501573 := by decide +kernel
private theorem v238 : F ps238 10425579253=800641596 :=
  takeStep (p:=1493) (by decide) v237 c238 rfl (by decide) (by decide) rfl

private def ps239 : List ℕ := 1499::ps238
private theorem c239 : F ps238 6955022=499175 := by decide +kernel
private theorem v239 : F ps239 10425579253=800142421 :=
  takeStep (p:=1499) (by decide) v238 c239 rfl (by decide) (by decide) rfl

private def ps240 : List ℕ := 1511::ps239
private theorem c240 : F ps239 6899787=494768 := by decide +kernel
private theorem v240 : F ps240 10425579253=799647653 :=
  takeStep (p:=1511) (by decide) v239 c240 rfl (by decide) (by decide) rfl

private def ps241 : List ℕ := 1523::ps240
private theorem c241 : F ps240 6845423=490437 := by decide +kernel
private theorem v241 : F ps241 10425579253=799157216 :=
  takeStep (p:=1523) (by decide) v240 c241 rfl (by decide) (by decide) rfl

private def ps242 : List ℕ := 1531::ps241
private theorem c242 : F ps241 6809653=487460 := by decide +kernel
private theorem v242 : F ps242 10425579253=798669756 :=
  takeStep (p:=1531) (by decide) v241 c242 rfl (by decide) (by decide) rfl

private def ps243 : List ℕ := 1543::ps242
private theorem c243 : F ps242 6756694=483313 := by decide +kernel
private theorem v243 : F ps243 10425579253=798186443 :=
  takeStep (p:=1543) (by decide) v242 c243 rfl (by decide) (by decide) rfl

private def ps244 : List ℕ := 1549::ps243
private theorem c244 : F ps243 6730522=481066 := by decide +kernel
private theorem v244 : F ps244 10425579253=797705377 :=
  takeStep (p:=1549) (by decide) v243 c244 rfl (by decide) (by decide) rfl

private def ps245 : List ℕ := 1553::ps244
private theorem c245 : F ps244 6713186=479463 := by decide +kernel
private theorem v245 : F ps245 10425579253=797225914 :=
  takeStep (p:=1553) (by decide) v244 c245 rfl (by decide) (by decide) rfl

private def ps246 : List ℕ := 1559::ps245
private theorem c246 : F ps245 6687350=477239 := by decide +kernel
private theorem v246 : F ps246 10425579253=796748675 :=
  takeStep (p:=1559) (by decide) v245 c246 rfl (by decide) (by decide) rfl

private def ps247 : List ℕ := 1567::ps246
private theorem c247 : F ps246 6653209=474475 := by decide +kernel
private theorem v247 : F ps247 10425579253=796274200 :=
  takeStep (p:=1567) (by decide) v246 c247 rfl (by decide) (by decide) rfl

private def ps248 : List ℕ := 1571::ps247
private theorem c248 : F ps247 6636269=472925 := by decide +kernel
private theorem v248 : F ps248 10425579253=795801275 :=
  takeStep (p:=1571) (by decide) v247 c248 rfl (by decide) (by decide) rfl

private def ps249 : List ℕ := 1579::ps248
private theorem c249 : F ps248 6602646=470195 := by decide +kernel
private theorem v249 : F ps249 10425579253=795331080 :=
  takeStep (p:=1579) (by decide) v248 c249 rfl (by decide) (by decide) rfl

private def ps250 : List ℕ := 1583::ps249
private theorem c250 : F ps249 6585962=468686 := by decide +kernel
private theorem v250 : F ps250 10425579253=794862394 :=
  takeStep (p:=1583) (by decide) v249 c250 rfl (by decide) (by decide) rfl

private def ps251 : List ℕ := 1597::ps250
private theorem c251 : F ps250 6528227=464213 := by decide +kernel
private theorem v251 : F ps251 10425579253=794398181 :=
  takeStep (p:=1597) (by decide) v250 c251 rfl (by decide) (by decide) rfl

private def ps252 : List ℕ := 1601::ps251
private theorem c252 : F ps251 6511917=462752 := by decide +kernel
private theorem v252 : F ps252 10425579253=793935429 :=
  takeStep (p:=1601) (by decide) v251 c252 rfl (by decide) (by decide) rfl

private def ps253 : List ℕ := 1607::ps252
private theorem c253 : F ps252 6487603=460695 := by decide +kernel
private theorem v253 : F ps253 10425579253=793474734 :=
  takeStep (p:=1607) (by decide) v252 c253 rfl (by decide) (by decide) rfl

private def ps254 : List ℕ := 1609::ps253
private theorem c254 : F ps253 6479539=459818 := by decide +kernel
private theorem v254 : F ps254 10425579253=793014916 :=
  takeStep (p:=1609) (by decide) v253 c254 rfl (by decide) (by decide) rfl

private def ps255 : List ℕ := 1613::ps254
private theorem c255 : F ps254 6463471=458384 := by decide +kernel
private theorem v255 : F ps255 10425579253=792556532 :=
  takeStep (p:=1613) (by decide) v254 c255 rfl (by decide) (by decide) rfl

private def ps256 : List ℕ := 1619::ps255
private theorem c256 : F ps255 6439517=456387 := by decide +kernel
private theorem v256 : F ps256 10425579253=792100145 :=
  takeStep (p:=1619) (by decide) v255 c256 rfl (by decide) (by decide) rfl

private def ps257 : List ℕ := 1621::ps256
private theorem c257 : F ps256 6431572=455538 := by decide +kernel
private theorem v257 : F ps257 10425579253=791644607 :=
  takeStep (p:=1621) (by decide) v256 c257 rfl (by decide) (by decide) rfl

private def ps258 : List ℕ := 1627::ps257
private theorem c258 : F ps257 6407854=453566 := by decide +kernel
private theorem v258 : F ps258 10425579253=791191041 :=
  takeStep (p:=1627) (by decide) v257 c258 rfl (by decide) (by decide) rfl

private def ps259 : List ℕ := 1637::ps258
private theorem c259 : F ps258 6368710=450567 := by decide +kernel
private theorem v259 : F ps259 10425579253=790740474 :=
  takeStep (p:=1637) (by decide) v258 c259 rfl (by decide) (by decide) rfl

private def ps260 : List ℕ := 1657::ps259
private theorem c260 : F ps259 6291840=444846 := by decide +kernel
private theorem v260 : F ps260 10425579253=790295628 :=
  takeStep (p:=1657) (by decide) v259 c260 rfl (by decide) (by decide) rfl

private def ps261 : List ℕ := 1663::ps260
private theorem c261 : F ps260 6269139=442949 := by decide +kernel
private theorem v261 : F ps261 10425579253=789852679 :=
  takeStep (p:=1663) (by decide) v260 c261 rfl (by decide) (by decide) rfl

private def ps262 : List ℕ := 1667::ps261
private theorem c262 : F ps261 6254096=441615 := by decide +kernel
private theorem v262 : F ps262 10425579253=789411064 :=
  takeStep (p:=1667) (by decide) v261 c262 rfl (by decide) (by decide) rfl

private def ps263 : List ℕ := 1669::ps262
private theorem c263 : F ps262 6246602=440830 := by decide +kernel
private theorem v263 : F ps263 10425579253=788970234 :=
  takeStep (p:=1669) (by decide) v262 c263 rfl (by decide) (by decide) rfl

private def ps264 : List ℕ := 1693::ps263
private theorem c264 : F ps263 6158050=434381 := by decide +kernel
private theorem v264 : F ps264 10425579253=788535853 :=
  takeStep (p:=1693) (by decide) v263 c264 rfl (by decide) (by decide) rfl

private def ps265 : List ℕ := 1697::ps264
private theorem c265 : F ps264 6143535=433112 := by decide +kernel
private theorem v265 : F ps265 10425579253=788102741 :=
  takeStep (p:=1697) (by decide) v264 c265 rfl (by decide) (by decide) rfl

private def ps266 : List ℕ := 1699::ps265
private theorem c266 : F ps265 6136303=432362 := by decide +kernel
private theorem v266 : F ps266 10425579253=787670379 :=
  takeStep (p:=1699) (by decide) v265 c266 rfl (by decide) (by decide) rfl

private def ps267 : List ℕ := 1709::ps266
private theorem c267 : F ps266 6100397=429631 := by decide +kernel
private theorem v267 : F ps267 10425579253=787240748 :=
  takeStep (p:=1709) (by decide) v266 c267 rfl (by decide) (by decide) rfl

private def ps268 : List ℕ := 1721::ps267
private theorem c268 : F ps267 6057861=426432 := by decide +kernel
private theorem v268 : F ps268 10425579253=786814316 :=
  takeStep (p:=1721) (by decide) v267 c268 rfl (by decide) (by decide) rfl

private def ps269 : List ℕ := 1723::ps268
private theorem c269 : F ps268 6050829=425701 := by decide +kernel
private theorem v269 : F ps269 10425579253=786388615 :=
  takeStep (p:=1723) (by decide) v268 c269 rfl (by decide) (by decide) rfl

private def ps270 : List ℕ := 1733::ps269
private theorem c270 : F ps269 6015914=423072 := by decide +kernel
private theorem v270 : F ps270 10425579253=785965543 :=
  takeStep (p:=1733) (by decide) v269 c270 rfl (by decide) (by decide) rfl

private def ps271 : List ℕ := 1741::ps270
private theorem c271 : F ps270 5988270=420937 := by decide +kernel
private theorem v271 : F ps271 10425579253=785544606 :=
  takeStep (p:=1741) (by decide) v270 c271 rfl (by decide) (by decide) rfl

private def ps272 : List ℕ := 1747::ps271
private theorem c272 : F ps271 5967704=419308 := by decide +kernel
private theorem v272 : F ps272 10425579253=785125298 :=
  takeStep (p:=1747) (by decide) v271 c272 rfl (by decide) (by decide) rfl

private def ps273 : List ℕ := 1753::ps272
private theorem c273 : F ps272 5947278=417684 := by decide +kernel
private theorem v273 : F ps273 10425579253=784707614 :=
  takeStep (p:=1753) (by decide) v272 c273 rfl (by decide) (by decide) rfl

private def ps274 : List ℕ := 1759::ps273
private theorem c274 : F ps273 5926992=416079 := by decide +kernel
private theorem v274 : F ps274 10425579253=784291535 :=
  takeStep (p:=1759) (by decide) v273 c274 rfl (by decide) (by decide) rfl

private def ps275 : List ℕ := 1777::ps274
private theorem c275 : F ps274 5866955=411662 := by decide +kernel
private theorem v275 : F ps275 10425579253=783879873 :=
  takeStep (p:=1777) (by decide) v274 c275 rfl (by decide) (by decide) rfl

private def ps276 : List ℕ := 1783::ps275
private theorem c276 : F ps275 5847212=410132 := by decide +kernel
private theorem v276 : F ps276 10425579253=783469741 :=
  takeStep (p:=1783) (by decide) v275 c276 rfl (by decide) (by decide) rfl

private def ps277 : List ℕ := 1787::ps276
private theorem c277 : F ps276 5834123=409032 := by decide +kernel
private theorem v277 : F ps277 10425579253=783060709 :=
  takeStep (p:=1787) (by decide) v276 c277 rfl (by decide) (by decide) rfl

private def ps278 : List ℕ := 1789::ps277
private theorem c278 : F ps277 5827601=408399 := by decide +kernel
private theorem v278 : F ps278 10425579253=782652310 :=
  takeStep (p:=1789) (by decide) v277 c278 rfl (by decide) (by decide) rfl

private def ps279 : List ℕ := 1801::ps278
private theorem c279 : F ps278 5788772=405555 := by decide +kernel
private theorem v279 : F ps279 10425579253=782246755 :=
  takeStep (p:=1801) (by decide) v278 c279 rfl (by decide) (by decide) rfl

private def ps280 : List ℕ := 1811::ps279
private theorem c280 : F ps279 5756807=403221 := by decide +kernel
private theorem v280 : F ps280 10425579253=781843534 :=
  takeStep (p:=1811) (by decide) v279 c280 rfl (by decide) (by decide) rfl

private def ps281 : List ℕ := 1823::ps280
private theorem c281 : F ps280 5718913=400458 := by decide +kernel
private theorem v281 : F ps281 10425579253=781443076 :=
  takeStep (p:=1823) (by decide) v280 c281 rfl (by decide) (by decide) rfl

private def ps282 : List ℕ := 1831::ps281
private theorem c282 : F ps281 5693926=398546 := by decide +kernel
private theorem v282 : F ps282 10425579253=781044530 :=
  takeStep (p:=1831) (by decide) v281 c282 rfl (by decide) (by decide) rfl

private def ps283 : List ℕ := 1847::ps282
private theorem c283 : F ps282 5644601=395009 := by decide +kernel
private theorem v283 : F ps283 10425579253=780649521 :=
  takeStep (p:=1847) (by decide) v282 c283 rfl (by decide) (by decide) rfl

private def ps284 : List ℕ := 1861::ps283
private theorem c284 : F ps283 5602138=391963 := by decide +kernel
private theorem v284 : F ps284 10425579253=780257558 :=
  takeStep (p:=1861) (by decide) v283 c284 rfl (by decide) (by decide) rfl

private def ps285 : List ℕ := 1867::ps284
private theorem c285 : F ps284 5584134=390593 := by decide +kernel
private theorem v285 : F ps285 10425579253=779866965 :=
  takeStep (p:=1867) (by decide) v284 c285 rfl (by decide) (by decide) rfl

private def ps286 : List ℕ := 1871::ps285
private theorem c286 : F ps285 5572196=389648 := by decide +kernel
private theorem v286 : F ps286 10425579253=779477317 :=
  takeStep (p:=1871) (by decide) v285 c286 rfl (by decide) (by decide) rfl

private def ps287 : List ℕ := 1873::ps286
private theorem c287 : F ps286 5566246=389071 := by decide +kernel
private theorem v287 : F ps287 10425579253=779088246 :=
  takeStep (p:=1873) (by decide) v286 c287 rfl (by decide) (by decide) rfl

private def ps288 : List ℕ := 1877::ps287
private theorem c288 : F ps287 5554384=388127 := by decide +kernel
private theorem v288 : F ps288 10425579253=778700119 :=
  takeStep (p:=1877) (by decide) v287 c288 rfl (by decide) (by decide) rfl

private def ps289 : List ℕ := 1879::ps288
private theorem c289 : F ps288 5548472=387584 := by decide +kernel
private theorem v289 : F ps289 10425579253=778312535 :=
  takeStep (p:=1879) (by decide) v288 c289 rfl (by decide) (by decide) rfl

private def ps290 : List ℕ := 1889::ps289
private theorem c290 : F ps289 5519099=385470 := by decide +kernel
private theorem v290 : F ps290 10425579253=777927065 :=
  takeStep (p:=1889) (by decide) v289 c290 rfl (by decide) (by decide) rfl

private def ps291 : List ℕ := 1901::ps290
private theorem c291 : F ps290 5484260=382994 := by decide +kernel
private theorem v291 : F ps291 10425579253=777544071 :=
  takeStep (p:=1901) (by decide) v290 c291 rfl (by decide) (by decide) rfl

private def ps292 : List ℕ := 1907::ps291
private theorem c292 : F ps291 5467005=381712 := by decide +kernel
private theorem v292 : F ps292 10425579253=777162359 :=
  takeStep (p:=1907) (by decide) v291 c292 rfl (by decide) (by decide) rfl

private def ps293 : List ℕ := 1913::ps292
private theorem c293 : F ps292 5449858=380400 := by decide +kernel
private theorem v293 : F ps293 10425579253=776781959 :=
  takeStep (p:=1913) (by decide) v292 c293 rfl (by decide) (by decide) rfl

private def ps294 : List ℕ := 1931::ps293
private theorem c294 : F ps293 5399057=376839 := by decide +kernel
private theorem v294 : F ps294 10425579253=776405120 :=
  takeStep (p:=1931) (by decide) v293 c294 rfl (by decide) (by decide) rfl

private def ps295 : List ℕ := 1933::ps294
private theorem c295 : F ps294 5393470=376352 := by decide +kernel
private theorem v295 : F ps295 10425579253=776028768 :=
  takeStep (p:=1933) (by decide) v294 c295 rfl (by decide) (by decide) rfl

private def ps296 : List ℕ := 1949::ps295
private theorem c296 : F ps295 5349194=373241 := by decide +kernel
private theorem v296 : F ps296 10425579253=775655527 :=
  takeStep (p:=1949) (by decide) v295 c296 rfl (by decide) (by decide) rfl

private def ps297 : List ℕ := 1951::ps296
private theorem c297 : F ps296 5343710=372774 := by decide +kernel
private theorem v297 : F ps297 10425579253=775282753 :=
  takeStep (p:=1951) (by decide) v296 c297 rfl (by decide) (by decide) rfl

private def ps298 : List ℕ := 1973::ps297
private theorem c298 : F ps297 5284125=368636 := by decide +kernel
private theorem v298 : F ps298 10425579253=774914117 :=
  takeStep (p:=1973) (by decide) v297 c298 rfl (by decide) (by decide) rfl

private def ps299 : List ℕ := 1979::ps298
private theorem c299 : F ps298 5268104=367488 := by decide +kernel
private theorem v299 : F ps299 10425579253=774546629 :=
  takeStep (p:=1979) (by decide) v298 c299 rfl (by decide) (by decide) rfl

private def ps300 : List ℕ := 1987::ps299
private theorem c300 : F ps299 5246894=365967 := by decide +kernel
private theorem v300 : F ps300 10425579253=774180662 :=
  takeStep (p:=1987) (by decide) v299 c300 rfl (by decide) (by decide) rfl

private def ps301 : List ℕ := 1993::ps300
private theorem c301 : F ps300 5231098=364820 := by decide +kernel
private theorem v301 : F ps301 10425579253=773815842 :=
  takeStep (p:=1993) (by decide) v300 c301 rfl (by decide) (by decide) rfl

private def ps302 : List ℕ := 1997::ps301
private theorem c302 : F ps301 5220620=364037 := by decide +kernel
private theorem v302 : F ps302 10425579253=773451805 :=
  takeStep (p:=1997) (by decide) v301 c302 rfl (by decide) (by decide) rfl

private def ps303 : List ℕ := 1999::ps302
private theorem c303 : F ps302 5215397=363609 := by decide +kernel
private theorem v303 : F ps303 10425579253=773088196 :=
  takeStep (p:=1999) (by decide) v302 c303 rfl (by decide) (by decide) rfl

private def ps304 : List ℕ := 2003::ps303
private theorem c304 : F ps303 5204982=362835 := by decide +kernel
private theorem v304 : F ps304 10425579253=772725361 :=
  takeStep (p:=2003) (by decide) v303 c304 rfl (by decide) (by decide) rfl

private def ps305 : List ℕ := 2011::ps304
private theorem c305 : F ps304 5184276=361369 := by decide +kernel
private theorem v305 : F ps305 10425579253=772363992 :=
  takeStep (p:=2011) (by decide) v304 c305 rfl (by decide) (by decide) rfl

private def ps306 : List ℕ := 2017::ps305
private theorem c306 : F ps305 5168854=360281 := by decide +kernel
private theorem v306 : F ps306 10425579253=772003711 :=
  takeStep (p:=2017) (by decide) v305 c306 rfl (by decide) (by decide) rfl

private def ps307 : List ℕ := 2027::ps306
private theorem c307 : F ps306 5143354=358528 := by decide +kernel
private theorem v307 : F ps307 10425579253=771645183 :=
  takeStep (p:=2027) (by decide) v306 c307 rfl (by decide) (by decide) rfl

private def ps308 : List ℕ := 2029::ps307
private theorem c308 : F ps307 5138284=358121 := by decide +kernel
private theorem v308 : F ps308 10425579253=771287062 :=
  takeStep (p:=2029) (by decide) v307 c308 rfl (by decide) (by decide) rfl

private def ps309 : List ℕ := 2039::ps308
private theorem c309 : F ps308 5113084=356375 := by decide +kernel
private theorem v309 : F ps309 10425579253=770930687 :=
  takeStep (p:=2039) (by decide) v308 c309 rfl (by decide) (by decide) rfl

private def ps310 : List ℕ := 2053::ps309
private theorem c310 : F ps309 5078216=354000 := by decide +kernel
private theorem v310 : F ps310 10425579253=770576687 :=
  takeStep (p:=2053) (by decide) v309 c310 rfl (by decide) (by decide) rfl

private def ps311 : List ℕ := 2063::ps310
private theorem c311 : F ps310 5053601=352316 := by decide +kernel
private theorem v311 : F ps311 10425579253=770224371 :=
  takeStep (p:=2063) (by decide) v310 c311 rfl (by decide) (by decide) rfl

private def ps312 : List ℕ := 2069::ps311
private theorem c312 : F ps311 5038945=351296 := by decide +kernel
private theorem v312 : F ps312 10425579253=769873075 :=
  takeStep (p:=2069) (by decide) v311 c312 rfl (by decide) (by decide) rfl

private def ps313 : List ℕ := 2081::ps312
private theorem c313 : F ps312 5009889=349325 := by decide +kernel
private theorem v313 : F ps313 10425579253=769523750 :=
  takeStep (p:=2081) (by decide) v312 c313 rfl (by decide) (by decide) rfl

private def ps314 : List ℕ := 2083::ps313
private theorem c314 : F ps313 5005078=348963 := by decide +kernel
private theorem v314 : F ps314 10425579253=769174787 :=
  takeStep (p:=2083) (by decide) v313 c314 rfl (by decide) (by decide) rfl

private def ps315 : List ℕ := 2087::ps314
private theorem c315 : F ps314 4995485=348298 := by decide +kernel
private theorem v315 : F ps315 10425579253=768826489 :=
  takeStep (p:=2087) (by decide) v314 c315 rfl (by decide) (by decide) rfl

private def ps316 : List ℕ := 2089::ps315
private theorem c316 : F ps315 4990703=347949 := by decide +kernel
private theorem v316 : F ps316 10425579253=768478540 :=
  takeStep (p:=2089) (by decide) v315 c316 rfl (by decide) (by decide) rfl

private def ps317 : List ℕ := 2099::ps316
private theorem c317 : F ps316 4966926=346317 := by decide +kernel
private theorem v317 : F ps317 10425579253=768132223 :=
  takeStep (p:=2099) (by decide) v316 c317 rfl (by decide) (by decide) rfl

private def ps318 : List ℕ := 2111::ps317
private theorem c318 : F ps317 4938692=344407 := by decide +kernel
private theorem v318 : F ps318 10425579253=767787816 :=
  takeStep (p:=2111) (by decide) v317 c318 rfl (by decide) (by decide) rfl

private def ps319 : List ℕ := 2113::ps318
private theorem c319 : F ps318 4934017=344061 := by decide +kernel
private theorem v319 : F ps319 10425579253=767443755 :=
  takeStep (p:=2113) (by decide) v318 c319 rfl (by decide) (by decide) rfl

private def ps320 : List ℕ := 2129::ps319
private theorem c320 : F ps319 4896937=341605 := by decide +kernel
private theorem v320 : F ps320 10425579253=767102150 :=
  takeStep (p:=2129) (by decide) v319 c320 rfl (by decide) (by decide) rfl

private def ps321 : List ℕ := 2131::ps320
private theorem c321 : F ps320 4892341=341266 := by decide +kernel
private theorem v321 : F ps321 10425579253=766760884 :=
  takeStep (p:=2131) (by decide) v320 c321 rfl (by decide) (by decide) rfl

private def ps322 : List ℕ := 2137::ps321
private theorem c322 : F ps321 4878605=340313 := by decide +kernel
private theorem v322 : F ps322 10425579253=766420571 :=
  takeStep (p:=2137) (by decide) v321 c322 rfl (by decide) (by decide) rfl

private def ps323 : List ℕ := 2141::ps322
private theorem c323 : F ps322 4869490=339708 := by decide +kernel
private theorem v323 : F ps323 10425579253=766080863 :=
  takeStep (p:=2141) (by decide) v322 c323 rfl (by decide) (by decide) rfl

private def ps324 : List ℕ := 2143::ps323
private theorem c324 : F ps323 4864945=339387 := by decide +kernel
private theorem v324 : F ps324 10425579253=765741476 :=
  takeStep (p:=2143) (by decide) v323 c324 rfl (by decide) (by decide) rfl

private def ps325 : List ℕ := 2153::ps324
private theorem c325 : F ps324 4842349=337906 := by decide +kernel
private theorem v325 : F ps325 10425579253=765403570 :=
  takeStep (p:=2153) (by decide) v324 c325 rfl (by decide) (by decide) rfl

private def ps326 : List ℕ := 2161::ps325
private theorem c326 : F ps325 4824423=336727 := by decide +kernel
private theorem v326 : F ps326 10425579253=765066843 :=
  takeStep (p:=2161) (by decide) v325 c326 rfl (by decide) (by decide) rfl

private def ps327 : List ℕ := 2179::ps326
private theorem c327 : F ps326 4784570=334120 := by decide +kernel
private theorem v327 : F ps327 10425579253=764732723 :=
  takeStep (p:=2179) (by decide) v326 c327 rfl (by decide) (by decide) rfl

private theorem filter_from_test {bound : ℕ} (test : ℕ → Bool)
    (ok : ∀ n, n≤bound → (test n=true ↔ n.Prime)) (y : ℕ) (hy : y≤bound) :
    (List.range (y+1)).filter (fun n => decide n.Prime) =
      (List.range (y+1)).filter test := by
  apply List.filter_congr
  intro n member
  have nbound : n≤bound := by have := List.mem_range.mp member; omega
  by_cases hp : n.Prime
  · simp [hp,(ok n nbound).mpr hp]
  · have miss : test n=false := Bool.eq_false_iff.mpr (mt (ok n nbound).mp hp)
    simp [hp,miss]

private def l0_68 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67]
private theorem l0_68ok : (List.range' 0 68).filter prime = l0_68 :=
  by decide +kernel

private def l68_136 : List ℕ := [71,73,79,83,89,97,101,103,107,109,113,127,131]
private theorem l68_136ok : (List.range' 68 68).filter prime = l68_136 :=
  by decide +kernel

private def l0_136 : List ℕ := l0_68 ++ l68_136
private theorem l0_136ok : (List.range' 0 136).filter prime = l0_136 :=
  merge_filter _ 0 68 68 _ _ l0_68ok l68_136ok

private def l136_204 : List ℕ := [137,139,149,151,157,163,167,173,179,181,191,193,197,199]
private theorem l136_204ok : (List.range' 136 68).filter prime = l136_204 :=
  by decide +kernel

private def l204_273 : List ℕ := [211,223,227,229,233,239,241,251,257,263,269,271]
private theorem l204_273ok : (List.range' 204 69).filter prime = l204_273 :=
  by decide +kernel

private def l136_273 : List ℕ := l136_204 ++ l204_273
private theorem l136_273ok : (List.range' 136 137).filter prime = l136_273 :=
  merge_filter _ 136 68 69 _ _ l136_204ok l204_273ok

private def l0_273 : List ℕ := l0_136 ++ l136_273
private theorem l0_273ok : (List.range' 0 273).filter prime = l0_273 :=
  merge_filter _ 0 136 137 _ _ l0_136ok l136_273ok

private def l273_341 : List ℕ := [277,281,283,293,307,311,313,317,331,337]
private theorem l273_341ok : (List.range' 273 68).filter prime = l273_341 :=
  by decide +kernel

private def l341_409 : List ℕ := [347,349,353,359,367,373,379,383,389,397,401]
private theorem l341_409ok : (List.range' 341 68).filter prime = l341_409 :=
  by decide +kernel

private def l273_409 : List ℕ := l273_341 ++ l341_409
private theorem l273_409ok : (List.range' 273 136).filter prime = l273_409 :=
  merge_filter _ 273 68 68 _ _ l273_341ok l341_409ok

private def l409_477 : List ℕ := [409,419,421,431,433,439,443,449,457,461,463,467]
private theorem l409_477ok : (List.range' 409 68).filter prime = l409_477 :=
  by decide +kernel

private def l477_546 : List ℕ := [479,487,491,499,503,509,521,523,541]
private theorem l477_546ok : (List.range' 477 69).filter prime = l477_546 :=
  by decide +kernel

private def l409_546 : List ℕ := l409_477 ++ l477_546
private theorem l409_546ok : (List.range' 409 137).filter prime = l409_546 :=
  merge_filter _ 409 68 69 _ _ l409_477ok l477_546ok

private def l273_546 : List ℕ := l273_409 ++ l409_546
private theorem l273_546ok : (List.range' 273 273).filter prime = l273_546 :=
  merge_filter _ 273 136 137 _ _ l273_409ok l409_546ok

private def l0_546 : List ℕ := l0_273 ++ l273_546
private theorem l0_546ok : (List.range' 0 546).filter prime = l0_546 :=
  merge_filter _ 0 273 273 _ _ l0_273ok l273_546ok

private def l546_614 : List ℕ := [547,557,563,569,571,577,587,593,599,601,607,613]
private theorem l546_614ok : (List.range' 546 68).filter prime = l546_614 :=
  by decide +kernel

private def l614_682 : List ℕ := [617,619,631,641,643,647,653,659,661,673,677]
private theorem l614_682ok : (List.range' 614 68).filter prime = l614_682 :=
  by decide +kernel

private def l546_682 : List ℕ := l546_614 ++ l614_682
private theorem l546_682ok : (List.range' 546 136).filter prime = l546_682 :=
  merge_filter _ 546 68 68 _ _ l546_614ok l614_682ok

private def l682_750 : List ℕ := [683,691,701,709,719,727,733,739,743]
private theorem l682_750ok : (List.range' 682 68).filter prime = l682_750 :=
  by decide +kernel

private def l750_819 : List ℕ := [751,757,761,769,773,787,797,809,811]
private theorem l750_819ok : (List.range' 750 69).filter prime = l750_819 :=
  by decide +kernel

private def l682_819 : List ℕ := l682_750 ++ l750_819
private theorem l682_819ok : (List.range' 682 137).filter prime = l682_819 :=
  merge_filter _ 682 68 69 _ _ l682_750ok l750_819ok

private def l546_819 : List ℕ := l546_682 ++ l682_819
private theorem l546_819ok : (List.range' 546 273).filter prime = l546_819 :=
  merge_filter _ 546 136 137 _ _ l546_682ok l682_819ok

private def l819_887 : List ℕ := [821,823,827,829,839,853,857,859,863,877,881,883]
private theorem l819_887ok : (List.range' 819 68).filter prime = l819_887 :=
  by decide +kernel

private def l887_955 : List ℕ := [887,907,911,919,929,937,941,947,953]
private theorem l887_955ok : (List.range' 887 68).filter prime = l887_955 :=
  by decide +kernel

private def l819_955 : List ℕ := l819_887 ++ l887_955
private theorem l819_955ok : (List.range' 819 136).filter prime = l819_955 :=
  merge_filter _ 819 68 68 _ _ l819_887ok l887_955ok

private def l955_1023 : List ℕ := [967,971,977,983,991,997,1009,1013,1019,1021]
private theorem l955_1023ok : (List.range' 955 68).filter prime = l955_1023 :=
  by decide +kernel

private def l1023_1092 : List ℕ := [1031,1033,1039,1049,1051,1061,1063,1069,1087,1091]
private theorem l1023_1092ok : (List.range' 1023 69).filter prime = l1023_1092 :=
  by decide +kernel

private def l955_1092 : List ℕ := l955_1023 ++ l1023_1092
private theorem l955_1092ok : (List.range' 955 137).filter prime = l955_1092 :=
  merge_filter _ 955 68 69 _ _ l955_1023ok l1023_1092ok

private def l819_1092 : List ℕ := l819_955 ++ l955_1092
private theorem l819_1092ok : (List.range' 819 273).filter prime = l819_1092 :=
  merge_filter _ 819 136 137 _ _ l819_955ok l955_1092ok

private def l546_1092 : List ℕ := l546_819 ++ l819_1092
private theorem l546_1092ok : (List.range' 546 546).filter prime = l546_1092 :=
  merge_filter _ 546 273 273 _ _ l546_819ok l819_1092ok

private def l0_1092 : List ℕ := l0_546 ++ l546_1092
private theorem l0_1092ok : (List.range' 0 1092).filter prime = l0_1092 :=
  merge_filter _ 0 546 546 _ _ l0_546ok l546_1092ok

private def l1092_1160 : List ℕ := [1093,1097,1103,1109,1117,1123,1129,1151,1153]
private theorem l1092_1160ok : (List.range' 1092 68).filter prime = l1092_1160 :=
  by decide +kernel

private def l1160_1228 : List ℕ := [1163,1171,1181,1187,1193,1201,1213,1217,1223]
private theorem l1160_1228ok : (List.range' 1160 68).filter prime = l1160_1228 :=
  by decide +kernel

private def l1092_1228 : List ℕ := l1092_1160 ++ l1160_1228
private theorem l1092_1228ok : (List.range' 1092 136).filter prime = l1092_1228 :=
  merge_filter _ 1092 68 68 _ _ l1092_1160ok l1160_1228ok

private def l1228_1296 : List ℕ := [1229,1231,1237,1249,1259,1277,1279,1283,1289,1291]
private theorem l1228_1296ok : (List.range' 1228 68).filter prime = l1228_1296 :=
  by decide +kernel

private def l1296_1365 : List ℕ := [1297,1301,1303,1307,1319,1321,1327,1361]
private theorem l1296_1365ok : (List.range' 1296 69).filter prime = l1296_1365 :=
  by decide +kernel

private def l1228_1365 : List ℕ := l1228_1296 ++ l1296_1365
private theorem l1228_1365ok : (List.range' 1228 137).filter prime = l1228_1365 :=
  merge_filter _ 1228 68 69 _ _ l1228_1296ok l1296_1365ok

private def l1092_1365 : List ℕ := l1092_1228 ++ l1228_1365
private theorem l1092_1365ok : (List.range' 1092 273).filter prime = l1092_1365 :=
  merge_filter _ 1092 136 137 _ _ l1092_1228ok l1228_1365ok

private def l1365_1433 : List ℕ := [1367,1373,1381,1399,1409,1423,1427,1429]
private theorem l1365_1433ok : (List.range' 1365 68).filter prime = l1365_1433 :=
  by decide +kernel

private def l1433_1501 : List ℕ := [1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499]
private theorem l1433_1501ok : (List.range' 1433 68).filter prime = l1433_1501 :=
  by decide +kernel

private def l1365_1501 : List ℕ := l1365_1433 ++ l1433_1501
private theorem l1365_1501ok : (List.range' 1365 136).filter prime = l1365_1501 :=
  merge_filter _ 1365 68 68 _ _ l1365_1433ok l1433_1501ok

private def l1501_1569 : List ℕ := [1511,1523,1531,1543,1549,1553,1559,1567]
private theorem l1501_1569ok : (List.range' 1501 68).filter prime = l1501_1569 :=
  by decide +kernel

private def l1569_1638 : List ℕ := [1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637]
private theorem l1569_1638ok : (List.range' 1569 69).filter prime = l1569_1638 :=
  by decide +kernel

private def l1501_1638 : List ℕ := l1501_1569 ++ l1569_1638
private theorem l1501_1638ok : (List.range' 1501 137).filter prime = l1501_1638 :=
  merge_filter _ 1501 68 69 _ _ l1501_1569ok l1569_1638ok

private def l1365_1638 : List ℕ := l1365_1501 ++ l1501_1638
private theorem l1365_1638ok : (List.range' 1365 273).filter prime = l1365_1638 :=
  merge_filter _ 1365 136 137 _ _ l1365_1501ok l1501_1638ok

private def l1092_1638 : List ℕ := l1092_1365 ++ l1365_1638
private theorem l1092_1638ok : (List.range' 1092 546).filter prime = l1092_1638 :=
  merge_filter _ 1092 273 273 _ _ l1092_1365ok l1365_1638ok

private def l1638_1706 : List ℕ := [1657,1663,1667,1669,1693,1697,1699]
private theorem l1638_1706ok : (List.range' 1638 68).filter prime = l1638_1706 :=
  by decide +kernel

private def l1706_1774 : List ℕ := [1709,1721,1723,1733,1741,1747,1753,1759]
private theorem l1706_1774ok : (List.range' 1706 68).filter prime = l1706_1774 :=
  by decide +kernel

private def l1638_1774 : List ℕ := l1638_1706 ++ l1706_1774
private theorem l1638_1774ok : (List.range' 1638 136).filter prime = l1638_1774 :=
  merge_filter _ 1638 68 68 _ _ l1638_1706ok l1706_1774ok

private def l1774_1842 : List ℕ := [1777,1783,1787,1789,1801,1811,1823,1831]
private theorem l1774_1842ok : (List.range' 1774 68).filter prime = l1774_1842 :=
  by decide +kernel

private def l1842_1911 : List ℕ := [1847,1861,1867,1871,1873,1877,1879,1889,1901,1907]
private theorem l1842_1911ok : (List.range' 1842 69).filter prime = l1842_1911 :=
  by decide +kernel

private def l1774_1911 : List ℕ := l1774_1842 ++ l1842_1911
private theorem l1774_1911ok : (List.range' 1774 137).filter prime = l1774_1911 :=
  merge_filter _ 1774 68 69 _ _ l1774_1842ok l1842_1911ok

private def l1638_1911 : List ℕ := l1638_1774 ++ l1774_1911
private theorem l1638_1911ok : (List.range' 1638 273).filter prime = l1638_1911 :=
  merge_filter _ 1638 136 137 _ _ l1638_1774ok l1774_1911ok

private def l1911_1979 : List ℕ := [1913,1931,1933,1949,1951,1973]
private theorem l1911_1979ok : (List.range' 1911 68).filter prime = l1911_1979 :=
  by decide +kernel

private def l1979_2048 : List ℕ := [1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039]
private theorem l1979_2048ok : (List.range' 1979 69).filter prime = l1979_2048 :=
  by decide +kernel

private def l1911_2048 : List ℕ := l1911_1979 ++ l1979_2048
private theorem l1911_2048ok : (List.range' 1911 137).filter prime = l1911_2048 :=
  merge_filter _ 1911 68 69 _ _ l1911_1979ok l1979_2048ok

private def l2048_2116 : List ℕ := [2053,2063,2069,2081,2083,2087,2089,2099,2111,2113]
private theorem l2048_2116ok : (List.range' 2048 68).filter prime = l2048_2116 :=
  by decide +kernel

private def l2116_2185 : List ℕ := [2129,2131,2137,2141,2143,2153,2161,2179]
private theorem l2116_2185ok : (List.range' 2116 69).filter prime = l2116_2185 :=
  by decide +kernel

private def l2048_2185 : List ℕ := l2048_2116 ++ l2116_2185
private theorem l2048_2185ok : (List.range' 2048 137).filter prime = l2048_2185 :=
  merge_filter _ 2048 68 69 _ _ l2048_2116ok l2116_2185ok

private def l1911_2185 : List ℕ := l1911_2048 ++ l2048_2185
private theorem l1911_2185ok : (List.range' 1911 274).filter prime = l1911_2185 :=
  merge_filter _ 1911 137 137 _ _ l1911_2048ok l2048_2185ok

private def l1638_2185 : List ℕ := l1638_1911 ++ l1911_2185
private theorem l1638_2185ok : (List.range' 1638 547).filter prime = l1638_2185 :=
  merge_filter _ 1638 273 274 _ _ l1638_1911ok l1911_2185ok

private def l1092_2185 : List ℕ := l1092_1638 ++ l1638_2185
private theorem l1092_2185ok : (List.range' 1092 1093).filter prime = l1092_2185 :=
  merge_filter _ 1092 546 547 _ _ l1092_1638ok l1638_2185ok

private def l0_2185 : List ℕ := l0_1092 ++ l1092_2185
private theorem l0_2185ok : (List.range' 0 2185).filter prime = l0_2185 :=
  merge_filter _ 0 1092 1093 _ _ l0_1092ok l1092_2185ok

set_option maxRecDepth 8000 in
private theorem last_row :
    ((List.range (2184+1)).filter (fun p => decide p.Prime)).reverse = ps327 := by
  rw [filter_from_test prime prime_ok 2184 (by decide),List.range_eq_range',l0_2185ok]
  rfl

private theorem left_from_rows {bound x y val total : ℕ} (tab : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t) (ps : List ℕ)
    (cap : (y+1)^2 ≤ bound+1) (yb : y ≤ bound)
    (row : ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse = ps)
    (value : evalPhi tab ps x = val) (sum : val+tab y=total) :
    (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id x) +
      (Nat.primesLE y).card = total := by
  rw [agree_range tab ok y cap,row,value,Nat.primesLE_card_eq_primeCounting,←ok y yb,sum]

set_option maxRecDepth 8000 in
private theorem left_part :
    (((List.range (2184+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id 10425579253) +
    (Nat.primesLE 2184).card = 764733050 := by
  exact left_from_rows tab HybridBound10425.fast_correct ps327 (by decide) (by decide) last_row (show evalPhi tab ps327 10425579253 = 764732723 from v327) (by decide +kernel)

private abbrev term := contribution 10425579253 2184 tab prime

private theorem s0 : blockSum term 0 398 0 := by unfold blockSum; decide +kernel

private theorem s398 : blockSum term 398 399 0 := by unfold blockSum; decide +kernel

private theorem s797 : blockSum term 797 399 0 := by unfold blockSum; decide +kernel

private theorem s1196 : blockSum term 1196 399 0 := by unfold blockSum; decide +kernel

private theorem s1595 : blockSum term 1595 398 0 := by unfold blockSum; decide +kernel

private theorem s1993 : blockSum term 1993 399 8905026 := by unfold blockSum; decide +kernel

private theorem s2392 : blockSum term 2392 399 14188690 := by unfold blockSum; decide +kernel

private theorem s2791 : blockSum term 2791 399 11499782 := by unfold blockSum; decide +kernel

private theorem s3190 : blockSum term 3190 398 11289154 := by unfold blockSum; decide +kernel

private theorem s3588 : blockSum term 3588 399 9408952 := by unfold blockSum; decide +kernel

private theorem s3987 : blockSum term 3987 399 8757715 := by unfold blockSum; decide +kernel

private theorem s4386 : blockSum term 4386 399 7532889 := by unfold blockSum; decide +kernel

private theorem s4785 : blockSum term 4785 399 7430246 := by unfold blockSum; decide +kernel

private theorem s5184 : blockSum term 5184 399 6747768 := by unfold blockSum; decide +kernel

private theorem s5583 : blockSum term 5583 399 6056615 := by unfold blockSum; decide +kernel

private theorem s5982 : blockSum term 5982 399 6304956 := by unfold blockSum; decide +kernel

private theorem s6381 : blockSum term 6381 398 4644022 := by unfold blockSum; decide +kernel

private theorem s6779 : blockSum term 6779 399 5204449 := by unfold blockSum; decide +kernel

private theorem s7178 : blockSum term 7178 399 4706561 := by unfold blockSum; decide +kernel

private theorem s7577 : blockSum term 7577 399 4591396 := by unfold blockSum; decide +kernel

private theorem s7976 : blockSum term 7976 399 4081302 := by unfold blockSum; decide +kernel

private theorem s8375 : blockSum term 8375 399 4179019 := by unfold blockSum; decide +kernel

private theorem s8774 : blockSum term 8774 399 3832425 := by unfold blockSum; decide +kernel

private theorem s9173 : blockSum term 9173 399 4019049 := by unfold blockSum; decide +kernel

private theorem s9572 : blockSum term 9572 398 3694893 := by unfold blockSum; decide +kernel

private theorem s9970 : blockSum term 9970 399 3396937 := by unfold blockSum; decide +kernel

private theorem s10369 : blockSum term 10369 399 3048538 := by unfold blockSum; decide +kernel

private theorem s10768 : blockSum term 10768 399 3017719 := by unfold blockSum; decide +kernel

private theorem s11167 : blockSum term 11167 399 2847447 := by unfold blockSum; decide +kernel

private theorem s11566 : blockSum term 11566 399 2888436 := by unfold blockSum; decide +kernel

private theorem s11965 : blockSum term 11965 399 2735380 := by unfold blockSum; decide +kernel

private theorem s12364 : blockSum term 12364 399 3040951 := by unfold blockSum; decide +kernel

private theorem s12763 : blockSum term 12763 398 2696883 := by unfold blockSum; decide +kernel

private theorem s13161 : blockSum term 13161 399 2376919 := by unfold blockSum; decide +kernel

private theorem s13560 : blockSum term 13560 399 2604614 := by unfold blockSum; decide +kernel

private theorem s13959 : blockSum term 13959 399 2016230 := by unfold blockSum; decide +kernel

private theorem s14358 : blockSum term 14358 398 2521513 := by unfold blockSum; decide +kernel

private theorem s14756 : blockSum term 14756 399 2293512 := by unfold blockSum; decide +kernel

private theorem s15155 : blockSum term 15155 399 2341467 := by unfold blockSum; decide +kernel

private theorem s15554 : blockSum term 15554 399 2282995 := by unfold blockSum; decide +kernel

private theorem s15953 : blockSum term 15953 398 1923762 := by unfold blockSum; decide +kernel

private theorem s16351 : blockSum term 16351 399 1976837 := by unfold blockSum; decide +kernel

private theorem s16750 : blockSum term 16750 399 1882378 := by unfold blockSum; decide +kernel

private theorem s17149 : blockSum term 17149 399 1980818 := by unfold blockSum; decide +kernel

private theorem s17548 : blockSum term 17548 399 1844505 := by unfold blockSum; decide +kernel

private theorem s17947 : blockSum term 17947 399 2028891 := by unfold blockSum; decide +kernel

private theorem s18346 : blockSum term 18346 399 1633188 := by unfold blockSum; decide +kernel

private theorem s18745 : blockSum term 18745 399 1424907 := by unfold blockSum; decide +kernel

private theorem s19144 : blockSum term 19144 398 1860100 := by unfold blockSum; decide +kernel

private theorem s19542 : blockSum term 19542 399 1574784 := by unfold blockSum; decide +kernel

private theorem s19941 : blockSum term 19941 399 1706586 := by unfold blockSum; decide +kernel

private theorem s20340 : blockSum term 20340 399 1513554 := by unfold blockSum; decide +kernel

private theorem s20739 : blockSum term 20739 399 1561762 := by unfold blockSum; decide +kernel

private theorem s21138 : blockSum term 21138 399 1645403 := by unfold blockSum; decide +kernel

private theorem s21537 : blockSum term 21537 399 1539998 := by unfold blockSum; decide +kernel

private theorem s21936 : blockSum term 21936 399 1547404 := by unfold blockSum; decide +kernel

private theorem s22335 : blockSum term 22335 398 1444875 := by unfold blockSum; decide +kernel

private theorem s22733 : blockSum term 22733 399 1490420 := by unfold blockSum; decide +kernel

private theorem s23132 : blockSum term 23132 399 1117061 := by unfold blockSum; decide +kernel

private theorem s23531 : blockSum term 23531 399 1679006 := by unfold blockSum; decide +kernel

private theorem s23930 : blockSum term 23930 399 1279504 := by unfold blockSum; decide +kernel

private theorem s24329 : blockSum term 24329 399 1157720 := by unfold blockSum; decide +kernel

private theorem s24728 : blockSum term 24728 399 1202298 := by unfold blockSum; decide +kernel

private theorem s25127 : blockSum term 25127 399 1214466 := by unfold blockSum; decide +kernel

private theorem s25526 : blockSum term 25526 398 1256961 := by unfold blockSum; decide +kernel

private theorem s25924 : blockSum term 25924 399 1298198 := by unfold blockSum; decide +kernel

private theorem s26323 : blockSum term 26323 399 1185144 := by unfold blockSum; decide +kernel

private theorem s26722 : blockSum term 26722 399 1255806 := by unfold blockSum; decide +kernel

private theorem s27121 : blockSum term 27121 398 912004 := by unfold blockSum; decide +kernel

private theorem s27519 : blockSum term 27519 399 1187457 := by unfold blockSum; decide +kernel

private theorem s27918 : blockSum term 27918 399 1084012 := by unfold blockSum; decide +kernel

private theorem s28317 : blockSum term 28317 399 1234593 := by unfold blockSum; decide +kernel

private theorem s28716 : blockSum term 28716 398 968264 := by unfold blockSum; decide +kernel

private theorem s29114 : blockSum term 29114 399 1117407 := by unfold blockSum; decide +kernel

private theorem s29513 : blockSum term 29513 399 912218 := by unfold blockSum; decide +kernel

private theorem s29912 : blockSum term 29912 399 1003788 := by unfold blockSum; decide +kernel

private theorem s30311 : blockSum term 30311 399 962662 := by unfold blockSum; decide +kernel

private theorem s30710 : blockSum term 30710 399 948971 := by unfold blockSum; decide +kernel

private theorem s31109 : blockSum term 31109 399 986595 := by unfold blockSum; decide +kernel

private theorem s31508 : blockSum term 31508 399 922000 := by unfold blockSum; decide +kernel

private theorem s31907 : blockSum term 31907 398 932140 := by unfold blockSum; decide +kernel

private theorem s32305 : blockSum term 32305 399 1040522 := by unfold blockSum; decide +kernel

private theorem s32704 : blockSum term 32704 399 976455 := by unfold blockSum; decide +kernel

private theorem s33103 : blockSum term 33103 399 891879 := by unfold blockSum; decide +kernel

private theorem s33502 : blockSum term 33502 399 1018519 := by unfold blockSum; decide +kernel

private theorem s33901 : blockSum term 33901 399 775522 := by unfold blockSum; decide +kernel

private theorem s34300 : blockSum term 34300 399 944683 := by unfold blockSum; decide +kernel

private theorem s34699 : blockSum term 34699 399 776297 := by unfold blockSum; decide +kernel

private theorem s35098 : blockSum term 35098 398 809900 := by unfold blockSum; decide +kernel

private theorem s35496 : blockSum term 35496 399 734436 := by unfold blockSum; decide +kernel

private theorem s35895 : blockSum term 35895 399 830987 := by unfold blockSum; decide +kernel

private theorem s36294 : blockSum term 36294 399 819655 := by unfold blockSum; decide +kernel

private theorem s36693 : blockSum term 36693 399 871103 := by unfold blockSum; decide +kernel

private theorem s37092 : blockSum term 37092 399 715748 := by unfold blockSum; decide +kernel

private theorem s37491 : blockSum term 37491 399 807844 := by unfold blockSum; decide +kernel

private theorem s37890 : blockSum term 37890 399 676829 := by unfold blockSum; decide +kernel

private theorem s38289 : blockSum term 38289 398 668294 := by unfold blockSum; decide +kernel

private theorem s38687 : blockSum term 38687 399 737505 := by unfold blockSum; decide +kernel

private theorem s39086 : blockSum term 39086 399 784663 := by unfold blockSum; decide +kernel

private theorem s39485 : blockSum term 39485 399 754523 := by unfold blockSum; decide +kernel

private theorem s39884 : blockSum term 39884 399 652038 := by unfold blockSum; decide +kernel

private theorem s40283 : blockSum term 40283 399 570252 := by unfold blockSum; decide +kernel

private theorem s40682 : blockSum term 40682 399 708425 := by unfold blockSum; decide +kernel

private theorem s41081 : blockSum term 41081 399 699323 := by unfold blockSum; decide +kernel

private theorem s41480 : blockSum term 41480 398 672599 := by unfold blockSum; decide +kernel

private theorem s41878 : blockSum term 41878 399 733792 := by unfold blockSum; decide +kernel

private theorem s42277 : blockSum term 42277 399 706831 := by unfold blockSum; decide +kernel

private theorem s42676 : blockSum term 42676 399 731287 := by unfold blockSum; decide +kernel

private theorem s43075 : blockSum term 43075 399 486547 := by unfold blockSum; decide +kernel

private theorem s43474 : blockSum term 43474 399 580046 := by unfold blockSum; decide +kernel

private theorem s43873 : blockSum term 43873 399 687037 := by unfold blockSum; decide +kernel

private theorem s44272 : blockSum term 44272 399 565258 := by unfold blockSum; decide +kernel

private theorem s44671 : blockSum term 44671 398 574878 := by unfold blockSum; decide +kernel

private theorem s45069 : blockSum term 45069 399 551872 := by unfold blockSum; decide +kernel

private theorem s45468 : blockSum term 45468 399 575425 := by unfold blockSum; decide +kernel

private theorem s45867 : blockSum term 45867 399 506789 := by unfold blockSum; decide +kernel

private theorem s46266 : blockSum term 46266 399 576293 := by unfold blockSum; decide +kernel

private theorem s46665 : blockSum term 46665 399 509392 := by unfold blockSum; decide +kernel

private theorem s47064 : blockSum term 47064 399 547044 := by unfold blockSum; decide +kernel

private theorem s47463 : blockSum term 47463 399 583628 := by unfold blockSum; decide +kernel

private theorem s47862 : blockSum term 47862 398 489924 := by unfold blockSum; decide +kernel

private theorem s48260 : blockSum term 48260 399 526638 := by unfold blockSum; decide +kernel

private theorem s48659 : blockSum term 48659 399 548098 := by unfold blockSum; decide +kernel

private theorem s49058 : blockSum term 49058 399 527573 := by unfold blockSum; decide +kernel

private theorem s49457 : blockSum term 49457 399 534324 := by unfold blockSum; decide +kernel

private theorem s49856 : blockSum term 49856 399 500326 := by unfold blockSum; decide +kernel

private theorem s50255 : blockSum term 50255 399 493770 := by unfold blockSum; decide +kernel

private theorem s50654 : blockSum term 50654 399 421408 := by unfold blockSum; decide +kernel

private theorem s51053 : blockSum term 51053 398 507254 := by unfold blockSum; decide +kernel

private theorem s51451 : blockSum term 51451 399 501130 := by unfold blockSum; decide +kernel

private theorem s51850 : blockSum term 51850 399 456814 := by unfold blockSum; decide +kernel

private theorem s52249 : blockSum term 52249 399 438492 := by unfold blockSum; decide +kernel

private theorem s52648 : blockSum term 52648 398 432916 := by unfold blockSum; decide +kernel

private theorem s53046 : blockSum term 53046 399 488547 := by unfold blockSum; decide +kernel

private theorem s53445 : blockSum term 53445 399 409833 := by unfold blockSum; decide +kernel

private theorem s53844 : blockSum term 53844 399 405058 := by unfold blockSum; decide +kernel

private theorem s54243 : blockSum term 54243 398 505022 := by unfold blockSum; decide +kernel

private theorem s54641 : blockSum term 54641 399 371124 := by unfold blockSum; decide +kernel

private theorem s55040 : blockSum term 55040 399 389417 := by unfold blockSum; decide +kernel

private theorem s55439 : blockSum term 55439 399 463285 := by unfold blockSum; decide +kernel

private theorem s55838 : blockSum term 55838 399 390460 := by unfold blockSum; decide +kernel

private theorem s56237 : blockSum term 56237 399 439965 := by unfold blockSum; decide +kernel

private theorem s56636 : blockSum term 56636 399 423367 := by unfold blockSum; decide +kernel

private theorem s57035 : blockSum term 57035 399 439050 := by unfold blockSum; decide +kernel

private theorem s57434 : blockSum term 57434 398 380298 := by unfold blockSum; decide +kernel

private theorem s57832 : blockSum term 57832 399 406558 := by unfold blockSum; decide +kernel

private theorem s58231 : blockSum term 58231 399 349566 := by unfold blockSum; decide +kernel

private theorem s58630 : blockSum term 58630 399 355204 := by unfold blockSum; decide +kernel

private theorem s59029 : blockSum term 59029 399 410350 := by unfold blockSum; decide +kernel

private theorem s59428 : blockSum term 59428 399 375302 := by unfold blockSum; decide +kernel

private theorem s59827 : blockSum term 59827 399 321385 := by unfold blockSum; decide +kernel

private theorem s60226 : blockSum term 60226 399 298156 := by unfold blockSum; decide +kernel

private theorem s60625 : blockSum term 60625 398 351240 := by unfold blockSum; decide +kernel

private theorem s61023 : blockSum term 61023 399 299461 := by unfold blockSum; decide +kernel

private theorem s61422 : blockSum term 61422 399 350788 := by unfold blockSum; decide +kernel

private theorem s61821 : blockSum term 61821 399 346000 := by unfold blockSum; decide +kernel

private theorem s62220 : blockSum term 62220 399 278451 := by unfold blockSum; decide +kernel

private theorem s62619 : blockSum term 62619 399 301500 := by unfold blockSum; decide +kernel

private theorem s63018 : blockSum term 63018 399 306193 := by unfold blockSum; decide +kernel

private theorem s63417 : blockSum term 63417 399 388214 := by unfold blockSum; decide +kernel

private theorem s63816 : blockSum term 63816 398 255163 := by unfold blockSum; decide +kernel

private theorem s64214 : blockSum term 64214 399 260182 := by unfold blockSum; decide +kernel

private theorem s64613 : blockSum term 64613 399 281465 := by unfold blockSum; decide +kernel

private theorem s65012 : blockSum term 65012 399 301989 := by unfold blockSum; decide +kernel

private theorem s65411 : blockSum term 65411 398 321648 := by unfold blockSum; decide +kernel

private theorem s65809 : blockSum term 65809 399 285433 := by unfold blockSum; decide +kernel

private theorem s66208 : blockSum term 66208 399 257581 := by unfold blockSum; decide +kernel

private theorem s66607 : blockSum term 66607 399 269594 := by unfold blockSum; decide +kernel

private theorem s67006 : blockSum term 67006 398 273307 := by unfold blockSum; decide +kernel

private theorem s67404 : blockSum term 67404 399 314008 := by unfold blockSum; decide +kernel

private theorem s67803 : blockSum term 67803 399 243128 := by unfold blockSum; decide +kernel

private theorem s68202 : blockSum term 68202 399 239432 := by unfold blockSum; decide +kernel

private theorem s68601 : blockSum term 68601 399 242950 := by unfold blockSum; decide +kernel

private theorem s69000 : blockSum term 69000 399 239196 := by unfold blockSum; decide +kernel

private theorem s69399 : blockSum term 69399 399 207978 := by unfold blockSum; decide +kernel

private theorem s69798 : blockSum term 69798 399 258969 := by unfold blockSum; decide +kernel

private theorem s70197 : blockSum term 70197 398 254930 := by unfold blockSum; decide +kernel

private theorem s70595 : blockSum term 70595 399 244120 := by unfold blockSum; decide +kernel

private theorem s70994 : blockSum term 70994 399 253190 := by unfold blockSum; decide +kernel

private theorem s71393 : blockSum term 71393 399 223625 := by unfold blockSum; decide +kernel

private theorem s71792 : blockSum term 71792 399 251356 := by unfold blockSum; decide +kernel

private theorem s72191 : blockSum term 72191 399 204087 := by unfold blockSum; decide +kernel

private theorem s72590 : blockSum term 72590 399 237203 := by unfold blockSum; decide +kernel

private theorem s72989 : blockSum term 72989 399 191610 := by unfold blockSum; decide +kernel

private theorem s73388 : blockSum term 73388 398 211903 := by unfold blockSum; decide +kernel

private theorem s73786 : blockSum term 73786 399 190890 := by unfold blockSum; decide +kernel

private theorem s74185 : blockSum term 74185 399 216042 := by unfold blockSum; decide +kernel

private theorem s74584 : blockSum term 74584 399 206580 := by unfold blockSum; decide +kernel

private theorem s74983 : blockSum term 74983 399 186579 := by unfold blockSum; decide +kernel

private theorem s75382 : blockSum term 75382 399 204823 := by unfold blockSum; decide +kernel

private theorem s75781 : blockSum term 75781 399 180008 := by unfold blockSum; decide +kernel

private theorem s76180 : blockSum term 76180 399 171451 := by unfold blockSum; decide +kernel

private theorem s76579 : blockSum term 76579 398 173389 := by unfold blockSum; decide +kernel

private theorem s76977 : blockSum term 76977 399 179950 := by unfold blockSum; decide +kernel

private theorem s77376 : blockSum term 77376 399 210910 := by unfold blockSum; decide +kernel

private theorem s77775 : blockSum term 77775 399 153949 := by unfold blockSum; decide +kernel

private theorem s78174 : blockSum term 78174 398 155830 := by unfold blockSum; decide +kernel

private theorem s78572 : blockSum term 78572 399 152781 := by unfold blockSum; decide +kernel

private theorem s78971 : blockSum term 78971 399 158825 := by unfold blockSum; decide +kernel

private theorem s79370 : blockSum term 79370 399 146977 := by unfold blockSum; decide +kernel

private theorem s79769 : blockSum term 79769 398 161577 := by unfold blockSum; decide +kernel

private theorem s80167 : blockSum term 80167 399 149685 := by unfold blockSum; decide +kernel

private theorem s80566 : blockSum term 80566 399 171364 := by unfold blockSum; decide +kernel

private theorem s80965 : blockSum term 80965 399 155169 := by unfold blockSum; decide +kernel

private theorem s81364 : blockSum term 81364 399 139620 := by unfold blockSum; decide +kernel

private theorem s81763 : blockSum term 81763 399 136570 := by unfold blockSum; decide +kernel

private theorem s82162 : blockSum term 82162 399 145173 := by unfold blockSum; decide +kernel

private theorem s82561 : blockSum term 82561 399 123240 := by unfold blockSum; decide +kernel

private theorem s82960 : blockSum term 82960 398 123934 := by unfold blockSum; decide +kernel

private theorem s83358 : blockSum term 83358 399 121144 := by unfold blockSum; decide +kernel

private theorem s83757 : blockSum term 83757 399 111284 := by unfold blockSum; decide +kernel

private theorem s84156 : blockSum term 84156 399 135615 := by unfold blockSum; decide +kernel

private theorem s84555 : blockSum term 84555 399 95912 := by unfold blockSum; decide +kernel

private theorem s84954 : blockSum term 84954 399 116224 := by unfold blockSum; decide +kernel

private theorem s85353 : blockSum term 85353 399 116143 := by unfold blockSum; decide +kernel

private theorem s85752 : blockSum term 85752 399 91649 := by unfold blockSum; decide +kernel

private theorem s86151 : blockSum term 86151 398 121683 := by unfold blockSum; decide +kernel

private theorem s86549 : blockSum term 86549 399 83679 := by unfold blockSum; decide +kernel

private theorem s86948 : blockSum term 86948 399 100911 := by unfold blockSum; decide +kernel

private theorem s87347 : blockSum term 87347 399 111468 := by unfold blockSum; decide +kernel

private theorem s87746 : blockSum term 87746 399 81868 := by unfold blockSum; decide +kernel

private theorem s88145 : blockSum term 88145 399 66756 := by unfold blockSum; decide +kernel

private theorem s88544 : blockSum term 88544 399 89532 := by unfold blockSum; decide +kernel

private theorem s88943 : blockSum term 88943 399 86706 := by unfold blockSum; decide +kernel

private theorem s89342 : blockSum term 89342 398 86211 := by unfold blockSum; decide +kernel

private theorem s89740 : blockSum term 89740 399 92069 := by unfold blockSum; decide +kernel

private theorem s90139 : blockSum term 90139 399 79865 := by unfold blockSum; decide +kernel

private theorem s90538 : blockSum term 90538 399 64519 := by unfold blockSum; decide +kernel

private theorem s90937 : blockSum term 90937 399 70217 := by unfold blockSum; decide +kernel

private theorem s91336 : blockSum term 91336 399 61905 := by unfold blockSum; decide +kernel

private theorem s91735 : blockSum term 91735 399 61499 := by unfold blockSum; decide +kernel

private theorem s92134 : blockSum term 92134 399 71155 := by unfold blockSum; decide +kernel

private theorem s92533 : blockSum term 92533 398 69720 := by unfold blockSum; decide +kernel

private theorem s92931 : blockSum term 92931 399 61400 := by unfold blockSum; decide +kernel

private theorem s93330 : blockSum term 93330 399 46285 := by unfold blockSum; decide +kernel

private theorem s93729 : blockSum term 93729 399 52863 := by unfold blockSum; decide +kernel

private theorem s94128 : blockSum term 94128 399 44580 := by unfold blockSum; decide +kernel

private theorem s94527 : blockSum term 94527 399 49068 := by unfold blockSum; decide +kernel

private theorem s94926 : blockSum term 94926 399 48634 := by unfold blockSum; decide +kernel

private theorem s95325 : blockSum term 95325 399 42074 := by unfold blockSum; decide +kernel

private theorem s95724 : blockSum term 95724 398 37158 := by unfold blockSum; decide +kernel

private theorem s96122 : blockSum term 96122 399 36668 := by unfold blockSum; decide +kernel

private theorem s96521 : blockSum term 96521 399 31106 := by unfold blockSum; decide +kernel

private theorem s96920 : blockSum term 96920 399 27331 := by unfold blockSum; decide +kernel

private theorem s97319 : blockSum term 97319 399 27650 := by unfold blockSum; decide +kernel

private theorem s97718 : blockSum term 97718 399 23652 := by unfold blockSum; decide +kernel

private theorem s98117 : blockSum term 98117 399 22570 := by unfold blockSum; decide +kernel

private theorem s98516 : blockSum term 98516 399 21449 := by unfold blockSum; decide +kernel

private theorem s98915 : blockSum term 98915 398 18877 := by unfold blockSum; decide +kernel

private theorem s99313 : blockSum term 99313 399 15394 := by unfold blockSum; decide +kernel

private theorem s99712 : blockSum term 99712 399 13016 := by unfold blockSum; decide +kernel

private theorem s100111 : blockSum term 100111 399 10203 := by unfold blockSum; decide +kernel

private theorem s100510 : blockSum term 100510 399 7649 := by unfold blockSum; decide +kernel

private theorem s100909 : blockSum term 100909 399 6822 := by unfold blockSum; decide +kernel

private theorem s101308 : blockSum term 101308 399 4151 := by unfold blockSum; decide +kernel

private theorem s101707 : blockSum term 101707 399 1504 := by unfold blockSum; decide +kernel

private theorem rows : blockSum term 0 102106 291216679 := (join_sums term (lo:=0) (a:=51053) (b:=51053) (join_sums term (lo:=0) (a:=25526) (b:=25527) (join_sums term (lo:=0) (a:=12763) (b:=12763) (join_sums term (lo:=0) (a:=6381) (b:=6382) (join_sums term (lo:=0) (a:=3190) (b:=3191) (join_sums term (lo:=0) (a:=1595) (b:=1595) (join_sums term (lo:=0) (a:=797) (b:=798) (join_sums term (lo:=0) (a:=398) (b:=399) s0 s398) (join_sums term (lo:=797) (a:=399) (b:=399) s797 s1196)) (join_sums term (lo:=1595) (a:=797) (b:=798) (join_sums term (lo:=1595) (a:=398) (b:=399) s1595 s1993) (join_sums term (lo:=2392) (a:=399) (b:=399) s2392 s2791))) (join_sums term (lo:=3190) (a:=1595) (b:=1596) (join_sums term (lo:=3190) (a:=797) (b:=798) (join_sums term (lo:=3190) (a:=398) (b:=399) s3190 s3588) (join_sums term (lo:=3987) (a:=399) (b:=399) s3987 s4386)) (join_sums term (lo:=4785) (a:=798) (b:=798) (join_sums term (lo:=4785) (a:=399) (b:=399) s4785 s5184) (join_sums term (lo:=5583) (a:=399) (b:=399) s5583 s5982)))) (join_sums term (lo:=6381) (a:=3191) (b:=3191) (join_sums term (lo:=6381) (a:=1595) (b:=1596) (join_sums term (lo:=6381) (a:=797) (b:=798) (join_sums term (lo:=6381) (a:=398) (b:=399) s6381 s6779) (join_sums term (lo:=7178) (a:=399) (b:=399) s7178 s7577)) (join_sums term (lo:=7976) (a:=798) (b:=798) (join_sums term (lo:=7976) (a:=399) (b:=399) s7976 s8375) (join_sums term (lo:=8774) (a:=399) (b:=399) s8774 s9173))) (join_sums term (lo:=9572) (a:=1595) (b:=1596) (join_sums term (lo:=9572) (a:=797) (b:=798) (join_sums term (lo:=9572) (a:=398) (b:=399) s9572 s9970) (join_sums term (lo:=10369) (a:=399) (b:=399) s10369 s10768)) (join_sums term (lo:=11167) (a:=798) (b:=798) (join_sums term (lo:=11167) (a:=399) (b:=399) s11167 s11566) (join_sums term (lo:=11965) (a:=399) (b:=399) s11965 s12364))))) (join_sums term (lo:=12763) (a:=6381) (b:=6382) (join_sums term (lo:=12763) (a:=3190) (b:=3191) (join_sums term (lo:=12763) (a:=1595) (b:=1595) (join_sums term (lo:=12763) (a:=797) (b:=798) (join_sums term (lo:=12763) (a:=398) (b:=399) s12763 s13161) (join_sums term (lo:=13560) (a:=399) (b:=399) s13560 s13959)) (join_sums term (lo:=14358) (a:=797) (b:=798) (join_sums term (lo:=14358) (a:=398) (b:=399) s14358 s14756) (join_sums term (lo:=15155) (a:=399) (b:=399) s15155 s15554))) (join_sums term (lo:=15953) (a:=1595) (b:=1596) (join_sums term (lo:=15953) (a:=797) (b:=798) (join_sums term (lo:=15953) (a:=398) (b:=399) s15953 s16351) (join_sums term (lo:=16750) (a:=399) (b:=399) s16750 s17149)) (join_sums term (lo:=17548) (a:=798) (b:=798) (join_sums term (lo:=17548) (a:=399) (b:=399) s17548 s17947) (join_sums term (lo:=18346) (a:=399) (b:=399) s18346 s18745)))) (join_sums term (lo:=19144) (a:=3191) (b:=3191) (join_sums term (lo:=19144) (a:=1595) (b:=1596) (join_sums term (lo:=19144) (a:=797) (b:=798) (join_sums term (lo:=19144) (a:=398) (b:=399) s19144 s19542) (join_sums term (lo:=19941) (a:=399) (b:=399) s19941 s20340)) (join_sums term (lo:=20739) (a:=798) (b:=798) (join_sums term (lo:=20739) (a:=399) (b:=399) s20739 s21138) (join_sums term (lo:=21537) (a:=399) (b:=399) s21537 s21936))) (join_sums term (lo:=22335) (a:=1595) (b:=1596) (join_sums term (lo:=22335) (a:=797) (b:=798) (join_sums term (lo:=22335) (a:=398) (b:=399) s22335 s22733) (join_sums term (lo:=23132) (a:=399) (b:=399) s23132 s23531)) (join_sums term (lo:=23930) (a:=798) (b:=798) (join_sums term (lo:=23930) (a:=399) (b:=399) s23930 s24329) (join_sums term (lo:=24728) (a:=399) (b:=399) s24728 s25127)))))) (join_sums term (lo:=25526) (a:=12763) (b:=12764) (join_sums term (lo:=25526) (a:=6381) (b:=6382) (join_sums term (lo:=25526) (a:=3190) (b:=3191) (join_sums term (lo:=25526) (a:=1595) (b:=1595) (join_sums term (lo:=25526) (a:=797) (b:=798) (join_sums term (lo:=25526) (a:=398) (b:=399) s25526 s25924) (join_sums term (lo:=26323) (a:=399) (b:=399) s26323 s26722)) (join_sums term (lo:=27121) (a:=797) (b:=798) (join_sums term (lo:=27121) (a:=398) (b:=399) s27121 s27519) (join_sums term (lo:=27918) (a:=399) (b:=399) s27918 s28317))) (join_sums term (lo:=28716) (a:=1595) (b:=1596) (join_sums term (lo:=28716) (a:=797) (b:=798) (join_sums term (lo:=28716) (a:=398) (b:=399) s28716 s29114) (join_sums term (lo:=29513) (a:=399) (b:=399) s29513 s29912)) (join_sums term (lo:=30311) (a:=798) (b:=798) (join_sums term (lo:=30311) (a:=399) (b:=399) s30311 s30710) (join_sums term (lo:=31109) (a:=399) (b:=399) s31109 s31508)))) (join_sums term (lo:=31907) (a:=3191) (b:=3191) (join_sums term (lo:=31907) (a:=1595) (b:=1596) (join_sums term (lo:=31907) (a:=797) (b:=798) (join_sums term (lo:=31907) (a:=398) (b:=399) s31907 s32305) (join_sums term (lo:=32704) (a:=399) (b:=399) s32704 s33103)) (join_sums term (lo:=33502) (a:=798) (b:=798) (join_sums term (lo:=33502) (a:=399) (b:=399) s33502 s33901) (join_sums term (lo:=34300) (a:=399) (b:=399) s34300 s34699))) (join_sums term (lo:=35098) (a:=1595) (b:=1596) (join_sums term (lo:=35098) (a:=797) (b:=798) (join_sums term (lo:=35098) (a:=398) (b:=399) s35098 s35496) (join_sums term (lo:=35895) (a:=399) (b:=399) s35895 s36294)) (join_sums term (lo:=36693) (a:=798) (b:=798) (join_sums term (lo:=36693) (a:=399) (b:=399) s36693 s37092) (join_sums term (lo:=37491) (a:=399) (b:=399) s37491 s37890))))) (join_sums term (lo:=38289) (a:=6382) (b:=6382) (join_sums term (lo:=38289) (a:=3191) (b:=3191) (join_sums term (lo:=38289) (a:=1595) (b:=1596) (join_sums term (lo:=38289) (a:=797) (b:=798) (join_sums term (lo:=38289) (a:=398) (b:=399) s38289 s38687) (join_sums term (lo:=39086) (a:=399) (b:=399) s39086 s39485)) (join_sums term (lo:=39884) (a:=798) (b:=798) (join_sums term (lo:=39884) (a:=399) (b:=399) s39884 s40283) (join_sums term (lo:=40682) (a:=399) (b:=399) s40682 s41081))) (join_sums term (lo:=41480) (a:=1595) (b:=1596) (join_sums term (lo:=41480) (a:=797) (b:=798) (join_sums term (lo:=41480) (a:=398) (b:=399) s41480 s41878) (join_sums term (lo:=42277) (a:=399) (b:=399) s42277 s42676)) (join_sums term (lo:=43075) (a:=798) (b:=798) (join_sums term (lo:=43075) (a:=399) (b:=399) s43075 s43474) (join_sums term (lo:=43873) (a:=399) (b:=399) s43873 s44272)))) (join_sums term (lo:=44671) (a:=3191) (b:=3191) (join_sums term (lo:=44671) (a:=1595) (b:=1596) (join_sums term (lo:=44671) (a:=797) (b:=798) (join_sums term (lo:=44671) (a:=398) (b:=399) s44671 s45069) (join_sums term (lo:=45468) (a:=399) (b:=399) s45468 s45867)) (join_sums term (lo:=46266) (a:=798) (b:=798) (join_sums term (lo:=46266) (a:=399) (b:=399) s46266 s46665) (join_sums term (lo:=47064) (a:=399) (b:=399) s47064 s47463))) (join_sums term (lo:=47862) (a:=1595) (b:=1596) (join_sums term (lo:=47862) (a:=797) (b:=798) (join_sums term (lo:=47862) (a:=398) (b:=399) s47862 s48260) (join_sums term (lo:=48659) (a:=399) (b:=399) s48659 s49058)) (join_sums term (lo:=49457) (a:=798) (b:=798) (join_sums term (lo:=49457) (a:=399) (b:=399) s49457 s49856) (join_sums term (lo:=50255) (a:=399) (b:=399) s50255 s50654))))))) (join_sums term (lo:=51053) (a:=25526) (b:=25527) (join_sums term (lo:=51053) (a:=12763) (b:=12763) (join_sums term (lo:=51053) (a:=6381) (b:=6382) (join_sums term (lo:=51053) (a:=3190) (b:=3191) (join_sums term (lo:=51053) (a:=1595) (b:=1595) (join_sums term (lo:=51053) (a:=797) (b:=798) (join_sums term (lo:=51053) (a:=398) (b:=399) s51053 s51451) (join_sums term (lo:=51850) (a:=399) (b:=399) s51850 s52249)) (join_sums term (lo:=52648) (a:=797) (b:=798) (join_sums term (lo:=52648) (a:=398) (b:=399) s52648 s53046) (join_sums term (lo:=53445) (a:=399) (b:=399) s53445 s53844))) (join_sums term (lo:=54243) (a:=1595) (b:=1596) (join_sums term (lo:=54243) (a:=797) (b:=798) (join_sums term (lo:=54243) (a:=398) (b:=399) s54243 s54641) (join_sums term (lo:=55040) (a:=399) (b:=399) s55040 s55439)) (join_sums term (lo:=55838) (a:=798) (b:=798) (join_sums term (lo:=55838) (a:=399) (b:=399) s55838 s56237) (join_sums term (lo:=56636) (a:=399) (b:=399) s56636 s57035)))) (join_sums term (lo:=57434) (a:=3191) (b:=3191) (join_sums term (lo:=57434) (a:=1595) (b:=1596) (join_sums term (lo:=57434) (a:=797) (b:=798) (join_sums term (lo:=57434) (a:=398) (b:=399) s57434 s57832) (join_sums term (lo:=58231) (a:=399) (b:=399) s58231 s58630)) (join_sums term (lo:=59029) (a:=798) (b:=798) (join_sums term (lo:=59029) (a:=399) (b:=399) s59029 s59428) (join_sums term (lo:=59827) (a:=399) (b:=399) s59827 s60226))) (join_sums term (lo:=60625) (a:=1595) (b:=1596) (join_sums term (lo:=60625) (a:=797) (b:=798) (join_sums term (lo:=60625) (a:=398) (b:=399) s60625 s61023) (join_sums term (lo:=61422) (a:=399) (b:=399) s61422 s61821)) (join_sums term (lo:=62220) (a:=798) (b:=798) (join_sums term (lo:=62220) (a:=399) (b:=399) s62220 s62619) (join_sums term (lo:=63018) (a:=399) (b:=399) s63018 s63417))))) (join_sums term (lo:=63816) (a:=6381) (b:=6382) (join_sums term (lo:=63816) (a:=3190) (b:=3191) (join_sums term (lo:=63816) (a:=1595) (b:=1595) (join_sums term (lo:=63816) (a:=797) (b:=798) (join_sums term (lo:=63816) (a:=398) (b:=399) s63816 s64214) (join_sums term (lo:=64613) (a:=399) (b:=399) s64613 s65012)) (join_sums term (lo:=65411) (a:=797) (b:=798) (join_sums term (lo:=65411) (a:=398) (b:=399) s65411 s65809) (join_sums term (lo:=66208) (a:=399) (b:=399) s66208 s66607))) (join_sums term (lo:=67006) (a:=1595) (b:=1596) (join_sums term (lo:=67006) (a:=797) (b:=798) (join_sums term (lo:=67006) (a:=398) (b:=399) s67006 s67404) (join_sums term (lo:=67803) (a:=399) (b:=399) s67803 s68202)) (join_sums term (lo:=68601) (a:=798) (b:=798) (join_sums term (lo:=68601) (a:=399) (b:=399) s68601 s69000) (join_sums term (lo:=69399) (a:=399) (b:=399) s69399 s69798)))) (join_sums term (lo:=70197) (a:=3191) (b:=3191) (join_sums term (lo:=70197) (a:=1595) (b:=1596) (join_sums term (lo:=70197) (a:=797) (b:=798) (join_sums term (lo:=70197) (a:=398) (b:=399) s70197 s70595) (join_sums term (lo:=70994) (a:=399) (b:=399) s70994 s71393)) (join_sums term (lo:=71792) (a:=798) (b:=798) (join_sums term (lo:=71792) (a:=399) (b:=399) s71792 s72191) (join_sums term (lo:=72590) (a:=399) (b:=399) s72590 s72989))) (join_sums term (lo:=73388) (a:=1595) (b:=1596) (join_sums term (lo:=73388) (a:=797) (b:=798) (join_sums term (lo:=73388) (a:=398) (b:=399) s73388 s73786) (join_sums term (lo:=74185) (a:=399) (b:=399) s74185 s74584)) (join_sums term (lo:=74983) (a:=798) (b:=798) (join_sums term (lo:=74983) (a:=399) (b:=399) s74983 s75382) (join_sums term (lo:=75781) (a:=399) (b:=399) s75781 s76180)))))) (join_sums term (lo:=76579) (a:=12763) (b:=12764) (join_sums term (lo:=76579) (a:=6381) (b:=6382) (join_sums term (lo:=76579) (a:=3190) (b:=3191) (join_sums term (lo:=76579) (a:=1595) (b:=1595) (join_sums term (lo:=76579) (a:=797) (b:=798) (join_sums term (lo:=76579) (a:=398) (b:=399) s76579 s76977) (join_sums term (lo:=77376) (a:=399) (b:=399) s77376 s77775)) (join_sums term (lo:=78174) (a:=797) (b:=798) (join_sums term (lo:=78174) (a:=398) (b:=399) s78174 s78572) (join_sums term (lo:=78971) (a:=399) (b:=399) s78971 s79370))) (join_sums term (lo:=79769) (a:=1595) (b:=1596) (join_sums term (lo:=79769) (a:=797) (b:=798) (join_sums term (lo:=79769) (a:=398) (b:=399) s79769 s80167) (join_sums term (lo:=80566) (a:=399) (b:=399) s80566 s80965)) (join_sums term (lo:=81364) (a:=798) (b:=798) (join_sums term (lo:=81364) (a:=399) (b:=399) s81364 s81763) (join_sums term (lo:=82162) (a:=399) (b:=399) s82162 s82561)))) (join_sums term (lo:=82960) (a:=3191) (b:=3191) (join_sums term (lo:=82960) (a:=1595) (b:=1596) (join_sums term (lo:=82960) (a:=797) (b:=798) (join_sums term (lo:=82960) (a:=398) (b:=399) s82960 s83358) (join_sums term (lo:=83757) (a:=399) (b:=399) s83757 s84156)) (join_sums term (lo:=84555) (a:=798) (b:=798) (join_sums term (lo:=84555) (a:=399) (b:=399) s84555 s84954) (join_sums term (lo:=85353) (a:=399) (b:=399) s85353 s85752))) (join_sums term (lo:=86151) (a:=1595) (b:=1596) (join_sums term (lo:=86151) (a:=797) (b:=798) (join_sums term (lo:=86151) (a:=398) (b:=399) s86151 s86549) (join_sums term (lo:=86948) (a:=399) (b:=399) s86948 s87347)) (join_sums term (lo:=87746) (a:=798) (b:=798) (join_sums term (lo:=87746) (a:=399) (b:=399) s87746 s88145) (join_sums term (lo:=88544) (a:=399) (b:=399) s88544 s88943))))) (join_sums term (lo:=89342) (a:=6382) (b:=6382) (join_sums term (lo:=89342) (a:=3191) (b:=3191) (join_sums term (lo:=89342) (a:=1595) (b:=1596) (join_sums term (lo:=89342) (a:=797) (b:=798) (join_sums term (lo:=89342) (a:=398) (b:=399) s89342 s89740) (join_sums term (lo:=90139) (a:=399) (b:=399) s90139 s90538)) (join_sums term (lo:=90937) (a:=798) (b:=798) (join_sums term (lo:=90937) (a:=399) (b:=399) s90937 s91336) (join_sums term (lo:=91735) (a:=399) (b:=399) s91735 s92134))) (join_sums term (lo:=92533) (a:=1595) (b:=1596) (join_sums term (lo:=92533) (a:=797) (b:=798) (join_sums term (lo:=92533) (a:=398) (b:=399) s92533 s92931) (join_sums term (lo:=93330) (a:=399) (b:=399) s93330 s93729)) (join_sums term (lo:=94128) (a:=798) (b:=798) (join_sums term (lo:=94128) (a:=399) (b:=399) s94128 s94527) (join_sums term (lo:=94926) (a:=399) (b:=399) s94926 s95325)))) (join_sums term (lo:=95724) (a:=3191) (b:=3191) (join_sums term (lo:=95724) (a:=1595) (b:=1596) (join_sums term (lo:=95724) (a:=797) (b:=798) (join_sums term (lo:=95724) (a:=398) (b:=399) s95724 s96122) (join_sums term (lo:=96521) (a:=399) (b:=399) s96521 s96920)) (join_sums term (lo:=97319) (a:=798) (b:=798) (join_sums term (lo:=97319) (a:=399) (b:=399) s97319 s97718) (join_sums term (lo:=98117) (a:=399) (b:=399) s98117 s98516))) (join_sums term (lo:=98915) (a:=1595) (b:=1596) (join_sums term (lo:=98915) (a:=797) (b:=798) (join_sums term (lo:=98915) (a:=398) (b:=399) s98915 s99313) (join_sums term (lo:=99712) (a:=399) (b:=399) s99712 s100111)) (join_sums term (lo:=100510) (a:=798) (b:=798) (join_sums term (lo:=100510) (a:=399) (b:=399) s100510 s100909) (join_sums term (lo:=101308) (a:=399) (b:=399) s101308 s101707))))))))

set_option maxRecDepth 8000 in
private theorem right_part :
    (∑ p ∈ (Nat.primesLE 102105).filter (2184 < ·),
      (Nat.primeCounting (10425579253/p) - Nat.primeCounting (p-1))) = 291216679 :=
  right_from_blocks tab prime HybridBound10425.fast_correct prime_ok (by decide) (by decide) rows

set_option maxRecDepth 12000 in
theorem exact_count : Nat.primeCounting 10425579253 = 473516370 :=
  assemble (x:=10425579253) (y:=2184) (z:=102105) (a:=764733050) (b:=291216679) (r:=473516370)
    (by decide) (by decide) (by decide) (by decide) (by decide) left_part right_part (by decide)
end Endpoint10425
