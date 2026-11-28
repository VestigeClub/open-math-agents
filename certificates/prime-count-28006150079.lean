import FormalConjectures.OEIS.«247824»

/-!
# A certified value of the prime-counting function at 28,006,150,079

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
namespace CheckpointA28006Slim

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
  if n≤55 then decide n.Prime else n.gcd 12696403353658275925965100847566516959580321051449436762275840000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤3037) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 55 = 12696403353658275925965100847566516959580321051449436762275840000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 55 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤3037 then light n else n.gcd 8056519825705701763971687075598816284918681691370567212524645706663360775645994100495732009052536490123350325473701743311804042866169268320517299294264874894818899742292891728335772836469916346202572983415488401753488320522101151513112050383682415413614823641667617659766172401685914473731950071987851817618566078983221866385979232384880140001447527183824542741497842229619421701940539538179123485247782146476651818296005291303480603163499105693572094836083213552772200057626170523290117164904914008954700212272500441105658119179188535081042623927333795633835711279794843805254037966682693503660126986120550678321655200435716006396039706544951236579160546459931603787381588243472870036039960923590160764749134777920441158084969919747799030187656841443056573877759628783426378769457176420416160625477424194347360586263869354674239699564649790294464196266243077254443042042134284703168836290506448182641968264878670893575564252744454237461303175728389922674094513657941347113354438289978993021957611700594687792958419026605711113152125786026556939138630977268966259952884856867872594943704132212175721232590518035113061309868028981341068607561071332859706532284315171182796288857896714253621581940146557545122511239862105348609360224042825329597033800507863513242779150865660259609580586532830 == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd 8056519825705701763971687075598816284918681691370567212524645706663360775645994100495732009052536490123350325473701743311804042866169268320517299294264874894818899742292891728335772836469916346202572983415488401753488320522101151513112050383682415413614823641667617659766172401685914473731950071987851817618566078983221866385979232384880140001447527183824542741497842229619421701940539538179123485247782146476651818296005291303480603163499105693572094836083213552772200057626170523290117164904914008954700212272500441105658119179188535081042623927333795633835711279794843805254037966682693503660126986120550678321655200435716006396039706544951236579160546459931603787381588243472870036039960923590160764749134777920441158084969919747799030187656841443056573877759628783426378769457176420416160625477424194347360586263869354674239699564649790294464196266243077254443042042134284703168836290506448182641968264878670893575564252744454237461303175728389922674094513657941347113354438289978993021957611700594687792958419026605711113152125786026556939138630977268966259952884856867872594943704132212175721232590518035113061309868028981341068607561071332859706532284315171182796288857896714253621581940146557545122511239862105348609360224042825329597033800507863513242779150865660259609580586532830 == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl

private theorem sm0 : smallValid 0 23 := by unfold smallValid; decide +kernel

private theorem sm23 : smallValid 23 24 := by unfold smallValid; decide +kernel

private theorem sm47 : smallValid 47 23 := by unfold smallValid; decide +kernel

private theorem sm70 : smallValid 70 24 := by unfold smallValid; decide +kernel

private theorem sm94 : smallValid 94 23 := by unfold smallValid; decide +kernel

private theorem sm117 : smallValid 117 24 := by unfold smallValid; decide +kernel

private theorem sm141 : smallValid 141 24 := by unfold smallValid; decide +kernel

private theorem sm165 : smallValid 165 24 := by unfold smallValid; decide +kernel

private theorem sm189 : smallValid 189 23 := by unfold smallValid; decide +kernel

private theorem sm212 : smallValid 212 24 := by unfold smallValid; decide +kernel

private theorem sm236 : smallValid 236 24 := by unfold smallValid; decide +kernel

private theorem sm260 : smallValid 260 24 := by unfold smallValid; decide +kernel

private theorem sm284 : smallValid 284 23 := by unfold smallValid; decide +kernel

private theorem sm307 : smallValid 307 24 := by unfold smallValid; decide +kernel

private theorem sm331 : smallValid 331 24 := by unfold smallValid; decide +kernel

private theorem sm355 : smallValid 355 24 := by unfold smallValid; decide +kernel

private theorem sm379 : smallValid 379 23 := by unfold smallValid; decide +kernel

private theorem sm402 : smallValid 402 24 := by unfold smallValid; decide +kernel

private theorem sm426 : smallValid 426 24 := by unfold smallValid; decide +kernel

private theorem sm450 : smallValid 450 24 := by unfold smallValid; decide +kernel

private theorem sm474 : smallValid 474 23 := by unfold smallValid; decide +kernel

private theorem sm497 : smallValid 497 24 := by unfold smallValid; decide +kernel

private theorem sm521 : smallValid 521 24 := by unfold smallValid; decide +kernel

private theorem sm545 : smallValid 545 24 := by unfold smallValid; decide +kernel

private theorem sm569 : smallValid 569 23 := by unfold smallValid; decide +kernel

private theorem sm592 : smallValid 592 24 := by unfold smallValid; decide +kernel

private theorem sm616 : smallValid 616 24 := by unfold smallValid; decide +kernel

private theorem sm640 : smallValid 640 24 := by unfold smallValid; decide +kernel

private theorem sm664 : smallValid 664 23 := by unfold smallValid; decide +kernel

private theorem sm687 : smallValid 687 24 := by unfold smallValid; decide +kernel

private theorem sm711 : smallValid 711 24 := by unfold smallValid; decide +kernel

private theorem sm735 : smallValid 735 24 := by unfold smallValid; decide +kernel

private theorem sm759 : smallValid 759 23 := by unfold smallValid; decide +kernel

private theorem sm782 : smallValid 782 24 := by unfold smallValid; decide +kernel

private theorem sm806 : smallValid 806 24 := by unfold smallValid; decide +kernel

private theorem sm830 : smallValid 830 24 := by unfold smallValid; decide +kernel

private theorem sm854 : smallValid 854 23 := by unfold smallValid; decide +kernel

private theorem sm877 : smallValid 877 24 := by unfold smallValid; decide +kernel

private theorem sm901 : smallValid 901 24 := by unfold smallValid; decide +kernel

private theorem sm925 : smallValid 925 24 := by unfold smallValid; decide +kernel

private theorem sm949 : smallValid 949 23 := by unfold smallValid; decide +kernel

private theorem sm972 : smallValid 972 24 := by unfold smallValid; decide +kernel

private theorem sm996 : smallValid 996 24 := by unfold smallValid; decide +kernel

private theorem sm1020 : smallValid 1020 24 := by unfold smallValid; decide +kernel

private theorem sm1044 : smallValid 1044 23 := by unfold smallValid; decide +kernel

private theorem sm1067 : smallValid 1067 24 := by unfold smallValid; decide +kernel

private theorem sm1091 : smallValid 1091 24 := by unfold smallValid; decide +kernel

private theorem sm1115 : smallValid 1115 24 := by unfold smallValid; decide +kernel

private theorem sm1139 : smallValid 1139 23 := by unfold smallValid; decide +kernel

private theorem sm1162 : smallValid 1162 24 := by unfold smallValid; decide +kernel

private theorem sm1186 : smallValid 1186 24 := by unfold smallValid; decide +kernel

private theorem sm1210 : smallValid 1210 24 := by unfold smallValid; decide +kernel

private theorem sm1234 : smallValid 1234 23 := by unfold smallValid; decide +kernel

private theorem sm1257 : smallValid 1257 24 := by unfold smallValid; decide +kernel

private theorem sm1281 : smallValid 1281 24 := by unfold smallValid; decide +kernel

private theorem sm1305 : smallValid 1305 24 := by unfold smallValid; decide +kernel

private theorem sm1329 : smallValid 1329 23 := by unfold smallValid; decide +kernel

private theorem sm1352 : smallValid 1352 24 := by unfold smallValid; decide +kernel

private theorem sm1376 : smallValid 1376 24 := by unfold smallValid; decide +kernel

private theorem sm1400 : smallValid 1400 24 := by unfold smallValid; decide +kernel

private theorem sm1424 : smallValid 1424 23 := by unfold smallValid; decide +kernel

private theorem sm1447 : smallValid 1447 24 := by unfold smallValid; decide +kernel

private theorem sm1471 : smallValid 1471 24 := by unfold smallValid; decide +kernel

private theorem sm1495 : smallValid 1495 24 := by unfold smallValid; decide +kernel

private theorem sm1519 : smallValid 1519 23 := by unfold smallValid; decide +kernel

private theorem sm1542 : smallValid 1542 24 := by unfold smallValid; decide +kernel

private theorem sm1566 : smallValid 1566 23 := by unfold smallValid; decide +kernel

private theorem sm1589 : smallValid 1589 24 := by unfold smallValid; decide +kernel

private theorem sm1613 : smallValid 1613 23 := by unfold smallValid; decide +kernel

private theorem sm1636 : smallValid 1636 24 := by unfold smallValid; decide +kernel

private theorem sm1660 : smallValid 1660 24 := by unfold smallValid; decide +kernel

private theorem sm1684 : smallValid 1684 24 := by unfold smallValid; decide +kernel

private theorem sm1708 : smallValid 1708 23 := by unfold smallValid; decide +kernel

private theorem sm1731 : smallValid 1731 24 := by unfold smallValid; decide +kernel

private theorem sm1755 : smallValid 1755 24 := by unfold smallValid; decide +kernel

private theorem sm1779 : smallValid 1779 24 := by unfold smallValid; decide +kernel

private theorem sm1803 : smallValid 1803 23 := by unfold smallValid; decide +kernel

private theorem sm1826 : smallValid 1826 24 := by unfold smallValid; decide +kernel

private theorem sm1850 : smallValid 1850 24 := by unfold smallValid; decide +kernel

private theorem sm1874 : smallValid 1874 24 := by unfold smallValid; decide +kernel

private theorem sm1898 : smallValid 1898 23 := by unfold smallValid; decide +kernel

private theorem sm1921 : smallValid 1921 24 := by unfold smallValid; decide +kernel

private theorem sm1945 : smallValid 1945 24 := by unfold smallValid; decide +kernel

private theorem sm1969 : smallValid 1969 24 := by unfold smallValid; decide +kernel

private theorem sm1993 : smallValid 1993 23 := by unfold smallValid; decide +kernel

private theorem sm2016 : smallValid 2016 24 := by unfold smallValid; decide +kernel

private theorem sm2040 : smallValid 2040 24 := by unfold smallValid; decide +kernel

private theorem sm2064 : smallValid 2064 24 := by unfold smallValid; decide +kernel

private theorem sm2088 : smallValid 2088 23 := by unfold smallValid; decide +kernel

private theorem sm2111 : smallValid 2111 24 := by unfold smallValid; decide +kernel

private theorem sm2135 : smallValid 2135 24 := by unfold smallValid; decide +kernel

private theorem sm2159 : smallValid 2159 24 := by unfold smallValid; decide +kernel

private theorem sm2183 : smallValid 2183 23 := by unfold smallValid; decide +kernel

private theorem sm2206 : smallValid 2206 24 := by unfold smallValid; decide +kernel

private theorem sm2230 : smallValid 2230 24 := by unfold smallValid; decide +kernel

private theorem sm2254 : smallValid 2254 24 := by unfold smallValid; decide +kernel

private theorem sm2278 : smallValid 2278 23 := by unfold smallValid; decide +kernel

private theorem sm2301 : smallValid 2301 24 := by unfold smallValid; decide +kernel

private theorem sm2325 : smallValid 2325 24 := by unfold smallValid; decide +kernel

private theorem sm2349 : smallValid 2349 24 := by unfold smallValid; decide +kernel

private theorem sm2373 : smallValid 2373 23 := by unfold smallValid; decide +kernel

private theorem sm2396 : smallValid 2396 24 := by unfold smallValid; decide +kernel

private theorem sm2420 : smallValid 2420 24 := by unfold smallValid; decide +kernel

private theorem sm2444 : smallValid 2444 24 := by unfold smallValid; decide +kernel

private theorem sm2468 : smallValid 2468 23 := by unfold smallValid; decide +kernel

private theorem sm2491 : smallValid 2491 24 := by unfold smallValid; decide +kernel

private theorem sm2515 : smallValid 2515 24 := by unfold smallValid; decide +kernel

private theorem sm2539 : smallValid 2539 24 := by unfold smallValid; decide +kernel

private theorem sm2563 : smallValid 2563 23 := by unfold smallValid; decide +kernel

private theorem sm2586 : smallValid 2586 24 := by unfold smallValid; decide +kernel

private theorem sm2610 : smallValid 2610 24 := by unfold smallValid; decide +kernel

private theorem sm2634 : smallValid 2634 24 := by unfold smallValid; decide +kernel

private theorem sm2658 : smallValid 2658 23 := by unfold smallValid; decide +kernel

private theorem sm2681 : smallValid 2681 24 := by unfold smallValid; decide +kernel

private theorem sm2705 : smallValid 2705 24 := by unfold smallValid; decide +kernel

private theorem sm2729 : smallValid 2729 24 := by unfold smallValid; decide +kernel

private theorem sm2753 : smallValid 2753 23 := by unfold smallValid; decide +kernel

private theorem sm2776 : smallValid 2776 24 := by unfold smallValid; decide +kernel

private theorem sm2800 : smallValid 2800 24 := by unfold smallValid; decide +kernel

private theorem sm2824 : smallValid 2824 24 := by unfold smallValid; decide +kernel

private theorem sm2848 : smallValid 2848 23 := by unfold smallValid; decide +kernel

private theorem sm2871 : smallValid 2871 24 := by unfold smallValid; decide +kernel

private theorem sm2895 : smallValid 2895 24 := by unfold smallValid; decide +kernel

private theorem sm2919 : smallValid 2919 24 := by unfold smallValid; decide +kernel

private theorem sm2943 : smallValid 2943 23 := by unfold smallValid; decide +kernel

private theorem sm2966 : smallValid 2966 24 := by unfold smallValid; decide +kernel

private theorem sm2990 : smallValid 2990 24 := by unfold smallValid; decide +kernel

private theorem sm3014 : smallValid 3014 24 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤3037) (hp : p.Prime) : p ∣ 8056519825705701763971687075598816284918681691370567212524645706663360775645994100495732009052536490123350325473701743311804042866169268320517299294264874894818899742292891728335772836469916346202572983415488401753488320522101151513112050383682415413614823641667617659766172401685914473731950071987851817618566078983221866385979232384880140001447527183824542741497842229619421701940539538179123485247782146476651818296005291303480603163499105693572094836083213552772200057626170523290117164904914008954700212272500441105658119179188535081042623927333795633835711279794843805254037966682693503660126986120550678321655200435716006396039706544951236579160546459931603787381588243472870036039960923590160764749134777920441158084969919747799030187656841443056573877759628783426378769457176420416160625477424194347360586263869354674239699564649790294464196266243077254443042042134284703168836290506448182641968264878670893575564252744454237461303175728389922674094513657941347113354438289978993021957611700594687792958419026605711113152125786026556939138630977268966259952884856867872594943704132212175721232590518035113061309868028981341068607561071332859706532284315171182796288857896714253621581940146557545122511239862105348609360224042825329597033800507863513242779150865660259609580586532830 := by
  have all : smallValid 0 3038 := (joinSmall (lo:=0) (a:=1519) (b:=1519) (joinSmall (lo:=0) (a:=759) (b:=760) (joinSmall (lo:=0) (a:=379) (b:=380) (joinSmall (lo:=0) (a:=189) (b:=190) (joinSmall (lo:=0) (a:=94) (b:=95) (joinSmall (lo:=0) (a:=47) (b:=47) (joinSmall (lo:=0) (a:=23) (b:=24) sm0 sm23) (joinSmall (lo:=47) (a:=23) (b:=24) sm47 sm70)) (joinSmall (lo:=94) (a:=47) (b:=48) (joinSmall (lo:=94) (a:=23) (b:=24) sm94 sm117) (joinSmall (lo:=141) (a:=24) (b:=24) sm141 sm165))) (joinSmall (lo:=189) (a:=95) (b:=95) (joinSmall (lo:=189) (a:=47) (b:=48) (joinSmall (lo:=189) (a:=23) (b:=24) sm189 sm212) (joinSmall (lo:=236) (a:=24) (b:=24) sm236 sm260)) (joinSmall (lo:=284) (a:=47) (b:=48) (joinSmall (lo:=284) (a:=23) (b:=24) sm284 sm307) (joinSmall (lo:=331) (a:=24) (b:=24) sm331 sm355)))) (joinSmall (lo:=379) (a:=190) (b:=190) (joinSmall (lo:=379) (a:=95) (b:=95) (joinSmall (lo:=379) (a:=47) (b:=48) (joinSmall (lo:=379) (a:=23) (b:=24) sm379 sm402) (joinSmall (lo:=426) (a:=24) (b:=24) sm426 sm450)) (joinSmall (lo:=474) (a:=47) (b:=48) (joinSmall (lo:=474) (a:=23) (b:=24) sm474 sm497) (joinSmall (lo:=521) (a:=24) (b:=24) sm521 sm545))) (joinSmall (lo:=569) (a:=95) (b:=95) (joinSmall (lo:=569) (a:=47) (b:=48) (joinSmall (lo:=569) (a:=23) (b:=24) sm569 sm592) (joinSmall (lo:=616) (a:=24) (b:=24) sm616 sm640)) (joinSmall (lo:=664) (a:=47) (b:=48) (joinSmall (lo:=664) (a:=23) (b:=24) sm664 sm687) (joinSmall (lo:=711) (a:=24) (b:=24) sm711 sm735))))) (joinSmall (lo:=759) (a:=380) (b:=380) (joinSmall (lo:=759) (a:=190) (b:=190) (joinSmall (lo:=759) (a:=95) (b:=95) (joinSmall (lo:=759) (a:=47) (b:=48) (joinSmall (lo:=759) (a:=23) (b:=24) sm759 sm782) (joinSmall (lo:=806) (a:=24) (b:=24) sm806 sm830)) (joinSmall (lo:=854) (a:=47) (b:=48) (joinSmall (lo:=854) (a:=23) (b:=24) sm854 sm877) (joinSmall (lo:=901) (a:=24) (b:=24) sm901 sm925))) (joinSmall (lo:=949) (a:=95) (b:=95) (joinSmall (lo:=949) (a:=47) (b:=48) (joinSmall (lo:=949) (a:=23) (b:=24) sm949 sm972) (joinSmall (lo:=996) (a:=24) (b:=24) sm996 sm1020)) (joinSmall (lo:=1044) (a:=47) (b:=48) (joinSmall (lo:=1044) (a:=23) (b:=24) sm1044 sm1067) (joinSmall (lo:=1091) (a:=24) (b:=24) sm1091 sm1115)))) (joinSmall (lo:=1139) (a:=190) (b:=190) (joinSmall (lo:=1139) (a:=95) (b:=95) (joinSmall (lo:=1139) (a:=47) (b:=48) (joinSmall (lo:=1139) (a:=23) (b:=24) sm1139 sm1162) (joinSmall (lo:=1186) (a:=24) (b:=24) sm1186 sm1210)) (joinSmall (lo:=1234) (a:=47) (b:=48) (joinSmall (lo:=1234) (a:=23) (b:=24) sm1234 sm1257) (joinSmall (lo:=1281) (a:=24) (b:=24) sm1281 sm1305))) (joinSmall (lo:=1329) (a:=95) (b:=95) (joinSmall (lo:=1329) (a:=47) (b:=48) (joinSmall (lo:=1329) (a:=23) (b:=24) sm1329 sm1352) (joinSmall (lo:=1376) (a:=24) (b:=24) sm1376 sm1400)) (joinSmall (lo:=1424) (a:=47) (b:=48) (joinSmall (lo:=1424) (a:=23) (b:=24) sm1424 sm1447) (joinSmall (lo:=1471) (a:=24) (b:=24) sm1471 sm1495)))))) (joinSmall (lo:=1519) (a:=759) (b:=760) (joinSmall (lo:=1519) (a:=379) (b:=380) (joinSmall (lo:=1519) (a:=189) (b:=190) (joinSmall (lo:=1519) (a:=94) (b:=95) (joinSmall (lo:=1519) (a:=47) (b:=47) (joinSmall (lo:=1519) (a:=23) (b:=24) sm1519 sm1542) (joinSmall (lo:=1566) (a:=23) (b:=24) sm1566 sm1589)) (joinSmall (lo:=1613) (a:=47) (b:=48) (joinSmall (lo:=1613) (a:=23) (b:=24) sm1613 sm1636) (joinSmall (lo:=1660) (a:=24) (b:=24) sm1660 sm1684))) (joinSmall (lo:=1708) (a:=95) (b:=95) (joinSmall (lo:=1708) (a:=47) (b:=48) (joinSmall (lo:=1708) (a:=23) (b:=24) sm1708 sm1731) (joinSmall (lo:=1755) (a:=24) (b:=24) sm1755 sm1779)) (joinSmall (lo:=1803) (a:=47) (b:=48) (joinSmall (lo:=1803) (a:=23) (b:=24) sm1803 sm1826) (joinSmall (lo:=1850) (a:=24) (b:=24) sm1850 sm1874)))) (joinSmall (lo:=1898) (a:=190) (b:=190) (joinSmall (lo:=1898) (a:=95) (b:=95) (joinSmall (lo:=1898) (a:=47) (b:=48) (joinSmall (lo:=1898) (a:=23) (b:=24) sm1898 sm1921) (joinSmall (lo:=1945) (a:=24) (b:=24) sm1945 sm1969)) (joinSmall (lo:=1993) (a:=47) (b:=48) (joinSmall (lo:=1993) (a:=23) (b:=24) sm1993 sm2016) (joinSmall (lo:=2040) (a:=24) (b:=24) sm2040 sm2064))) (joinSmall (lo:=2088) (a:=95) (b:=95) (joinSmall (lo:=2088) (a:=47) (b:=48) (joinSmall (lo:=2088) (a:=23) (b:=24) sm2088 sm2111) (joinSmall (lo:=2135) (a:=24) (b:=24) sm2135 sm2159)) (joinSmall (lo:=2183) (a:=47) (b:=48) (joinSmall (lo:=2183) (a:=23) (b:=24) sm2183 sm2206) (joinSmall (lo:=2230) (a:=24) (b:=24) sm2230 sm2254))))) (joinSmall (lo:=2278) (a:=380) (b:=380) (joinSmall (lo:=2278) (a:=190) (b:=190) (joinSmall (lo:=2278) (a:=95) (b:=95) (joinSmall (lo:=2278) (a:=47) (b:=48) (joinSmall (lo:=2278) (a:=23) (b:=24) sm2278 sm2301) (joinSmall (lo:=2325) (a:=24) (b:=24) sm2325 sm2349)) (joinSmall (lo:=2373) (a:=47) (b:=48) (joinSmall (lo:=2373) (a:=23) (b:=24) sm2373 sm2396) (joinSmall (lo:=2420) (a:=24) (b:=24) sm2420 sm2444))) (joinSmall (lo:=2468) (a:=95) (b:=95) (joinSmall (lo:=2468) (a:=47) (b:=48) (joinSmall (lo:=2468) (a:=23) (b:=24) sm2468 sm2491) (joinSmall (lo:=2515) (a:=24) (b:=24) sm2515 sm2539)) (joinSmall (lo:=2563) (a:=47) (b:=48) (joinSmall (lo:=2563) (a:=23) (b:=24) sm2563 sm2586) (joinSmall (lo:=2610) (a:=24) (b:=24) sm2610 sm2634)))) (joinSmall (lo:=2658) (a:=190) (b:=190) (joinSmall (lo:=2658) (a:=95) (b:=95) (joinSmall (lo:=2658) (a:=47) (b:=48) (joinSmall (lo:=2658) (a:=23) (b:=24) sm2658 sm2681) (joinSmall (lo:=2705) (a:=24) (b:=24) sm2705 sm2729)) (joinSmall (lo:=2753) (a:=47) (b:=48) (joinSmall (lo:=2753) (a:=23) (b:=24) sm2753 sm2776) (joinSmall (lo:=2800) (a:=24) (b:=24) sm2800 sm2824))) (joinSmall (lo:=2848) (a:=95) (b:=95) (joinSmall (lo:=2848) (a:=47) (b:=48) (joinSmall (lo:=2848) (a:=23) (b:=24) sm2848 sm2871) (joinSmall (lo:=2895) (a:=24) (b:=24) sm2895 sm2919)) (joinSmall (lo:=2943) (a:=47) (b:=48) (joinSmall (lo:=2943) (a:=23) (b:=24) sm2943 sm2966) (joinSmall (lo:=2990) (a:=24) (b:=24) sm2990 sm3014)))))))
  have good : (List.range 3038).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd 8056519825705701763971687075598816284918681691370567212524645706663360775645994100495732009052536490123350325473701743311804042866169268320517299294264874894818899742292891728335772836469916346202572983415488401753488320522101151513112050383682415413614823641667617659766172401685914473731950071987851817618566078983221866385979232384880140001447527183824542741497842229619421701940539538179123485247782146476651818296005291303480603163499105693572094836083213552772200057626170523290117164904914008954700212272500441105658119179188535081042623927333795633835711279794843805254037966682693503660126986120550678321655200435716006396039706544951236579160546459931603787381588243472870036039960923590160764749134777920441158084969919747799030187656841443056573877759628783426378769457176420416160625477424194347360586263869354674239699564649790294464196266243077254443042042134284703168836290506448182641968264878670893575564252744454237461303175728389922674094513657941347113354438289978993021957611700594687792958419026605711113152125786026556939138630977268966259952884856867872594943704132212175721232590518035113061309868028981341068607561071332859706532284315171182796288857896714253621581940146557545122511239862105348609360224042825329597033800507863513242779150865660259609580586532830 ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd 8056519825705701763971687075598816284918681691370567212524645706663360775645994100495732009052536490123350325473701743311804042866169268320517299294264874894818899742292891728335772836469916346202572983415488401753488320522101151513112050383682415413614823641667617659766172401685914473731950071987851817618566078983221866385979232384880140001447527183824542741497842229619421701940539538179123485247782146476651818296005291303480603163499105693572094836083213552772200057626170523290117164904914008954700212272500441105658119179188535081042623927333795633835711279794843805254037966682693503660126986120550678321655200435716006396039706544951236579160546459931603787381588243472870036039960923590160764749134777920441158084969919747799030187656841443056573877759628783426378769457176420416160625477424194347360586263869354674239699564649790294464196266243077254443042042134284703168836290506448182641968264878670893575564252744454237461303175728389922674094513657941347113354438289978993021957611700594687792958419026605711113152125786026556939138630977268966259952884856867872594943704132212175721232590518035113061309868028981341068607561071332859706532284315171182796288857896714253621581940146557545122511239862105348609360224042825329597033800507863513242779150865660259609580586532830 = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p 8056519825705701763971687075598816284918681691370567212524645706663360775645994100495732009052536490123350325473701743311804042866169268320517299294264874894818899742292891728335772836469916346202572983415488401753488320522101151513112050383682415413614823641667617659766172401685914473731950071987851817618566078983221866385979232384880140001447527183824542741497842229619421701940539538179123485247782146476651818296005291303480603163499105693572094836083213552772200057626170523290117164904914008954700212272500441105658119179188535081042623927333795633835711279794843805254037966682693503660126986120550678321655200435716006396039706544951236579160546459931603787381588243472870036039960923590160764749134777920441158084969919747799030187656841443056573877759628783426378769457176420416160625477424194347360586263869354674239699564649790294464196266243077254443042042134284703168836290506448182641968264878670893575564252744454237461303175728389922674094513657941347113354438289978993021957611700594687792958419026605711113152125786026556939138630977268966259952884856867872594943704132212175721232590518035113061309868028981341068607561071332859706532284315171182796288857896714253621581940146557545122511239862105348609360224042825329597033800507863513242779150865660259609580586532830)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p 8056519825705701763971687075598816284918681691370567212524645706663360775645994100495732009052536490123350325473701743311804042866169268320517299294264874894818899742292891728335772836469916346202572983415488401753488320522101151513112050383682415413614823641667617659766172401685914473731950071987851817618566078983221866385979232384880140001447527183824542741497842229619421701940539538179123485247782146476651818296005291303480603163499105693572094836083213552772200057626170523290117164904914008954700212272500441105658119179188535081042623927333795633835711279794843805254037966682693503660126986120550678321655200435716006396039706544951236579160546459931603787381588243472870036039960923590160764749134777920441158084969919747799030187656841443056573877759628783426378769457176420416160625477424194347360586263869354674239699564649790294464196266243077254443042042134284703168836290506448182641968264878670893575564252744454237461303175728389922674094513657941347113354438289978993021957611700594687792958419026605711113152125786026556939138630977268966259952884856867872594943704132212175721232590518035113061309868028981341068607561071332859706532284315171182796288857896714253621581940146557545122511239862105348609360224042825329597033800507863513242779150865660259609580586532830
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 9223368) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : 8056519825705701763971687075598816284918681691370567212524645706663360775645994100495732009052536490123350325473701743311804042866169268320517299294264874894818899742292891728335772836469916346202572983415488401753488320522101151513112050383682415413614823641667617659766172401685914473731950071987851817618566078983221866385979232384880140001447527183824542741497842229619421701940539538179123485247782146476651818296005291303480603163499105693572094836083213552772200057626170523290117164904914008954700212272500441105658119179188535081042623927333795633835711279794843805254037966682693503660126986120550678321655200435716006396039706544951236579160546459931603787381588243472870036039960923590160764749134777920441158084969919747799030187656841443056573877759628783426378769457176420416160625477424194347360586263869354674239699564649790294464196266243077254443042042134284703168836290506448182641968264878670893575564252744454237461303175728389922674094513657941347113354438289978993021957611700594687792958419026605711113152125786026556939138630977268966259952884856867872594943704132212175721232590518035113061309868028981341068607561071332859706532284315171182796288857896714253621581940146557545122511239862105348609360224042825329597033800507863513242779150865660259609580586532830 ∣ Nat.factorial 3037 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 3037 := by
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
  c (j/96) + tally f (96*(j/96)) (j%96)

theorem fromBlocks_succ (c : ℕ → ℕ) (f : ℕ → Bool) (j : ℕ)
    (boundary : c (j/96+1) = c (j/96) + tally f (96*(j/96)) 96) :
    fromBlocks c f (j+1) = fromBlocks c f j + (if f j then 1 else 0) := by
  have split := Nat.div_add_mod j 96
  have hs := tally_succ f (96*(j/96)) (j%96)
  rw [split] at hs
  unfold fromBlocks
  by_cases h : j%96=95
  · have div : (j+1)/96 = j/96+1 := by omega
    have rem : (j+1)%96 = 0 := by omega
    rw [div,rem,boundary]
    rw [show j%96+1=96 by omega] at hs
    simp [tally] at *
    omega
  · have div : (j+1)/96 = j/96 := by omega
    have rem : (j+1)%96 = j%96+1 := by omega
    rw [div,rem,hs]
    omega


private def packet (i : ℕ) : ℕ := (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x78f636a66cbd15e27a49c810eb1942c0498750b81000e800007740342608b294625643c7f0e219c2c44a0710a61000d00000758034c63cbb95d27a480828e318e2a4480720b00e00c8000073b235c63cbb15c280488838ed19c2bc4a8750c00ec108000071f434c628b794d26a4687d0e218e2a04606e0a60c80c800007032348630bb15b276474800e318a2a4468710ae0ec0e000006e6e35462cb6955278474810e11902b0468700a60d00e000006ca2364650b795526e494828e419429c4306a0a40dc0e000006ac937a684c29652964c0880f11a02d44a8770b40ec0e800006900356634b9950272480828e11822944486d09a0d00c80000673b34a628b815826c4607f8e51942c8498750ae0ec1180000656637266cbd15e27a4807e0e219a2c0488740a80dc0c8000063a934061cb695026a45c808e018c2a0460720ac0f00c0000061e335a648bc15b27e498848ee19a2c4490780ac0d80d00000602b342628b615326e484800e71962944286c0a80e00e000005e5f35e624b79502604547e0de18a2a4460710a40e00f000005c9735662cb614f25c4607c0dd1902a44806c0a20d80e000005ab7380680c396a2924ac8a0fa1a02b4490760ae0e40f0000058f434862cb614f25e45c7c8da1842944586e0a60dc0d00000572336e654bb95a27e484858f01a42d04c8740b21001080000555436c668c09642924a0828e81ac2dc4d87d0c01000f800005384364670bc15c27e484828eb19429c4806e0aa0ec0f0000051b335e63cb89562784707f0e31882a04206a0a80d80d800004ff934060cb694925e4387a0da1862904606f0a40dc0b800004e1537e674bf962280478830e81902bc488750b00f00e000004c3a37a67cc396228a4ac878f21a22d04b0790c20e80e800004a6c35864cbc15d274470808e81962c04c8790b60e81000000488e3826a0c91732b04e08d8fd1b62e84b87f0be104120000046b936e67cc015b28a488828e919a2b44b87a0b60fc120000044e736c660c016328c49c870f01a22cc498760b00e811000004313374664bd9602904a0840ec1982b8480710aa0e00d00000412f38e68cc41672904c48b8f81ae2f04f87b0b20e40e800003f4b38a6b4c316d29c4c0870f11ac300530880c810411800003d7636c660c0166290494808e018c2c4490740ac0d40e000003b9937e674c0160288494838e618a2a0450700ae0f00f8000039c336c660be9612824a0878ee19e2cc4a8750aa0f80f8000037e8380670c1166284490850ed1a42d84c8730aa0f0130000036013906b4c81702a64d48d8fa1b62fc4d8790b20f81000000341c38c688c09632924ac860ed1a02c84a0700ae0e00d80000323a38a698c69702ac4d8890f41ae2cc4b0770b00fc1180000304a3a46dccb1782ac4cc8b8f31a62e04d87c0c210811000002e6638e6a8c516e2aa4c88a0fa1b02dc4c8750b20d80c800002c783a46bcc81732ac4d88c0fb1b02e84e07f0bc1040e000002a853986c8c916e2aa4d88c8fd1b22ec4e87d0c61180e8000028a03946a4c696d2aa4c0890f71ac2d44c0770ac0f00f0000026af3a26b4c91702a04f08e0fa1ac2e84e07d0c01000f8000024c03a26e0ce97d2b24dc8a8f61b02ec4e87c0bc0ec0d0000022c03c4718d41892d2528941061cc3105308b0d212c130000020d03a26dcc99792b24d88b0f41a62c44c07e0ae0e40e000001ecf3b8704d017e2c650c919061ca32c5388a0ce12011800001cd53bc6f4cc97a2ba4f08f1031b82ec4f07e0bc0fc0f800001acd3ca70cd29842d6520949081c83004f07e0ba0ec108000018c93cc718d59892cc514921061d0304510810c8120150000016c83ca718d31842cc514941071d4338550850ca114118000014b53e8738d61892ca510939071c0310520830c00f81080000129c3ea73cd89952e253c961091d0318538830c610c0f8000010843f476cde1982f6548991171f0354560870ca1000e800000e693f6760dc9942de53c9910e1de324530840ca10811800000c3d40a7a0e019f2f05509610f1de324530850ca11010800000a084187ace19a430c5749e9181e4348570910e411c120000007bf446808ed1b73225a8a49261fc3645a8970ea1381480000056a46283cf71ca3465e0aa1292163886009a0e6124110000002f24a48b9041e0372644b413e2323cc650a20f614c1400000000058aa813b24b4427d0e319e2da508898e11621f422800 else (if i < 2 then 0xe60b3205f0b214726443c790d517a27c4306c0a40f40f00000e4633185ccab1442564287a0d017028c4386c0a20d40d80000e2aa346618b694f26c46c7e0db18a2a4478780aa0d80e80000e1102fa59ca593523440c758d41762704486909c0c80b00000df663265f4ae94125043c798d817e2884006a0940b80b00000ddaa3405f0b114c25c4587a0dc1902ac4386b09c0d00c00000dc043125a8aa93423c404730d11702684206c0aa0e40e00000da5132c5e8b394a25c4487b8da17e288458700a20dc0a80000d8a831e5e4b114225a43c7b0da18229c438660a20e00e80000d6f33345f0b194a24e4347c0e518c2b8488770b61041200000d54c31a5cca913523a418780d117a28c4206c09e0b40d80000d3a23265c8ab13d24240c750cf16a2603f05e0880b80700000d1ef32e5ecb014825c4507e8e21842884586a09a0d40d00000d03f32c5f8b294b25843c788d3176278430680a60d80e00000ce923245f8b314726043c7a8d717629c4486709e0c80d80000cce73245f0b294125043c7c0d8176274410680a00d00a00000cb3831e5c0a793623c410758d61742804306b0a40e00f80000c9953145d8b094c2604447d0df18a29c468710a60e00c80000c7ee3165ccad93d23a3f4718cd1682703e0610960c40c80000c64b3125c4ab13c2484347a0d717c284418650980dc0d80000c49b32c5f8b1947252440790de1802ac488780b60f00f00000c2e43325f0af1482504507c8dc17e2904706e0a40e81100000c13333060cb314725643c7a0d718627c4306c0a20dc0e00000bf8232e604ae14325a440798d517627c4106c09a0d00c00000bdcf3285f0b294a2564507a8de17e2ac4486c09e0d00f80000bc2331a5bca8939242420780da17828c460740b01001000000ba673425f4b094824c434788d31722904486a09e0d00d00000b8ad33c5f8b09472604507a8e01842904506f0aa0f00e00000b6f8330600b114a2624507c8e118a2904386b0a80e80e00000b54931e5bcab138242414740cc1702744206b0a40bc0a80000b3933285e8b194c25842c788df1942bc498720a60cc0c80000b1e53265e4b014625a420758d61802ac4506f0ac0e80e80000b02c34061cb614f26e4607d0e21922a8468700a60f40f80000ae823225ecb094525044c7b0e21922a0470700ac0f81000000acd33285fcb014625c4587c8de18429c480790ae0e00c80000ab2432a5f8b114b2564507c8e0182290450760b40f01080000a96e33c610b394d26846c810e41922ac468710a40c80e80000a7b733c5fcb515026645c7c0da17a28c4406e0a20dc0d80000a5f234e640b714f2624447b0d81862b4488740ae0f80f00000a4473225f4b19432524407a0d71702804306a09e0d40e00000a2983245d8b0942246410760cf1642543f86609e0d80f00000a0d7346624b515126244c7c0dd18c29c4586e0ae10411000009f1a340608b294925a4487b0da1902a8468710b00f00f000009d7031e5d4ac1352383f4720c814e2283a05e08e0cc0d000009bab34a624b995126e468810e11982b0470760b20ec0f0000099f3336614b71542744707c8da17e288438690980c80b800009827362640ba1582764607f0e51922bc478700a20c40d00000967133e610b6951256440798d41702844206809e0e80f0000094c332c5e8b314c2604487b8e11902a44706e0b20f00e00000930f332600b19472624687f8ea19e2c84c8780b00e00e0000091653185c4af941250430798dd1822a4490780b60f00f000008fa633e5f8b0144252440798d51702783e8650940bc0a000008dda362658be1632904a8850ec1a02bc4b87c0b60f811000008c1a344620b514826444c790d317c2884506a09e0d00a800008a61342620b594d2664547c0dd1762804306a0a00dc0d00000889d34c634b615326645c7d8dd182298490730b00e00f8000086de33a5f8b315326846c828e618a2ac488730ae0d40c80000852a32c5ecaf13f23e42c780d917a2784086d0a60d00c8000083753345f4b19462604547e8e61922b0480720b00e40e0000081ad35a65cbc15b28a4ac858ee1aa2e44d07d0b61080e800007ff0346614b594c254430790d51742744306f0a80f00f000007e3234261cb514e2604447a0d817627c4406f0a20d80f000007c6d354634b795326e470828e719c2b04b07a0ba0f40c800007ac43145c8ab93b2303f4718cd15a2583d06208a0cc0b800 else 0x14edd3105b8ab937238414758d31662704086508e0cc0e800014d3d30c594a4939240424770d517628c448720aa0f410800014b9a3165b4a89332343fc738cb1582243885808e0b80d800014a002fc594a412f232404710c8164270410670a00d40c00001485d3185d0ad94124a418770ce1602503b05f0980c00b8000146bf3105b8a91392343e86e0c315a2503d8590920c40d8000145183165d8ab93823c410758d01682683f0660980cc0e0000143842fa584a592f2203c46d0be14e25c3d8610920dc0b8000141e83085a4a793222c3f8730cf16e2643e0650960d40e8000140572f0574a312f22a3f0708ca160278418680960c00b800013eb730c5b0a813523a414788d8176270420670960c40d000013d232fa57ca31282143cc6b8c31562543d86208e0bc0c000013b8330c59ca893423c408738cd16c2543d05d0860cc0a8000139e63045b4a913a232404750d21722704186809c0d00d80001383c30e5bcab940256434798da17e2a04706a0a20dc0f80001369c304598a6937244420758d21762804286b09e0d80c0000134f63165e0af93d23e41c780d2174288458730a60dc0d80001334731a5d4ae145246424788d317a288458710ae0fc1000001319e3205d8ad13e24c414778d818028c450700a80e40b0000130023045aca8137234404718cc16826c4186c09c0cc0e800012e68302598a312d2343fc728cc1702904286609a0cc0b000012cd62f4568a292d2203dc700c515e2443a85c0860b80f000012b402f8594a392a22a3f4750d016c274410670920ac0a00001298d336604b414825a448788d51742884406e0aa0f00f0000127f33025b8ab939244430768d31742784206b09e0d00d0000126572f658ca11272203d86f8c415822c3a05b08809c0b0000124b430e5bca9939240414768d61742804386c0ac0f80f8000123242f056c9f9262263dc6f8c41542483c86108a0b00d00001217a31c5e0ad94024442c798d816c2703f0660940c40d000011fdc3105bca7933240418748d21762884406909c0c00c800011e40302590a612d236400750d216e268400630920b80c000011c8d33a60cb414b2664647d0da18628c428690ac0e00e800011ae73205d0ae13d2484407a0d717e2884206b09a0dc0e80001195b2e45689e9222143dc710ce170270410660900c40b80001179834e638b69502604607d8dc1862904386f0aa0e40d80001160e2de564a012a21e3dc6f0c415223c3a8590800bc0b8000114653145bcaa13924241c780d41722704306b0960d80e0000112c13145c0a99322363f4748d11722804306d09e0e00c00001112330e5a0a613022c3ec740ca1682683d0630900b80c800010f7032c5e4ae94224842c770d216e27c4306f0a60f00e800010dd22f8594a492c2343fc738d316c2543f06c0a40e40d800010c19340614b314a2624587b8dc1882b8480730ae0f411800010a7730e5d4af946248410740d516a2703f8660960c80c0000108d33145b8aa9382383fc720ca16226c3f0650920d40d80001072931c5e0af13e254444788da18629c4306f0ae0f0108000105893125d0ac144256448798d917c2884486e0960d8108000103ed3025a8a793623840c728cc16826c428690a40d00d0000102443265d8b014b2624687c8d91862844386d0a60d00d80001009e3225d4ae1472544487d0dc1862a44686f0a00d00f80000fef03245e4ad13c242424780d41702644005d0840b80a00000fd473145d0a913a23e420750d417227c4006b0a20e01100000fbad308598a613522a3ec6f8c314e2383985d08a0ac0880000fa0231e5c8ac137234400710cd1602703f0670a40e00f80000f8523205ccac93e2564447a8dd1822a84386c0a80d00e80000f6a93265e4ac93924643c770cf16c274408650920c00a80000f4f93225e8ad13e244428778d91822944386e0a40c80e00000f34d3205e4b2944256428760d4176288440710a20d80c80000f1ad30a5a0a813623a410768d317827c4106809c0cc0d80000effe32a5f0ae14224c4387a0d817c2844486a0a80e00f80000ee49330600af14525843c788d6174288460720a80d80e00000eca53105aca793322e3e8708c915c26c408680a40d80b80000eaf032e5ecae1442544487b8d917a270410700a20f00f80000e95f2e6574a09252223d06f0bd14a2403d05f0900c00f00000e7b831e5d8ad142252428798dc1862a4430690a20e40e800)) else (if i < 4 then 0x1b5552f6578a41322223d46f0c614c2343d06309a0bc0b00001b3c62e0584a713a236400740ce16625c3e0640900b80c00001b22d2fe58ca41292183c86d8c314623c3b8660920c00b00001b08c30e5c4ad93f250428740cb1662643e06509c0c40d80001aef7306598a51322303e8710c816c27c438670980d80e80001ad652e856c9f1282203ec700c615a258400660960bc0980001abc43105c4aa13924841c778d2174288438730ae0e00e00001aa213145b8ab93a238418758d016624c4006d0980c40c00001a87f31a5dcad94624e434760d2172280420690a40dc0b80001a6f62e2568a112821e3c86e8c615023c3c0650940cc0c00001a5742d05609c9242183e0720ce17427c430680960bc0a80001a3e22ec574a09282203dc6e0c21582503a05b07e0ac0b80001a25d2ce5389a92520e3a46b0c014c2443a85e08c0c00d00001a09d3365f8b514a25444c7d0da17828c4286a0a20d80f000019f102e45689f928220400720cc15a2483d8630900c00d800019d832e0574a19282223dc6d8bd13e2143885607c0a40a800019bd93285ecae94124a42c7a0dc18228c4406d0960c00b800019a442f257ca112c2223d06e8c315a2483d8610960c80e8000198ae2fa58ca51322303f0728c715e2543e05e0880bc0d8000197123045b4a79342343f8730cb16a2744386a09e0c40b80001957830c5a0a613323442c790d61782704086409c0d80c0000193eb2ee56ca21292203f46e0c114a228390630940c80b0000192592f4584a49302323fc740d016c2784206c0a00e40f8000190b830e5b0aa139236410730d016c2644006909c0dc0f000018f252e856ca1930238408738cb1642683e06709a0b80a800018d9a2e2570a112a2223d06d0c51642683d85f08c0bc0c000018bfa3085b8ab13d242414720c71562283786008a0b80b000018a5e2f459ca59332283e8700c715c2403d06509a0d00c8000188cb302594a6936238400738cf15c2403c8610900a80a800018731304594a692e2323f0740d217a280428680960dc0c8000185992fe594a593222e3f0718c816427c4586f09c0d40d0000184122e05509c12221c3c46d0bf1542383a05f08c0b80c8000182673265dcb1142254444778d417627c4386d0a40d40c0000180d02fe5a4a893b240404720ca1602643f06809a0c40b000017f452dc55c9f12921c3cc6f8c01462383e06809e0d80d800017da93065aca81372303f8718c715e2643d0620900b80a800017c013165c4aa9332323ec708cb16a270400620920c40b000017a6130e5b4a993a244430770d216825c4006708a0b40d0000178ce2f45649f1232063b46d0c01562443a8600940c40c80001772431e5d0aa93d246410740d01742543d05e09c0dc0d0000175862fa590a513123c414760cf16c2804406c0a20d80e0000174042d25409b1191fa3a46a0c01442243905c0900ac0b8000172742ee594a39262163dc6d0c515c2403b85a07e0a0090000170d92f4580a292a21e3d0710c415a2503d05c08c0c80b800016f3d2fc5acac13323240c748d016e2844286208e0c40e800016d9032a5e0af143248440778d6174280400690980c80c800016c0e2d25449c1222163e06d0c31542383a05c0900c40d800016a7d2ec570a212e2263e8730c915c258408630940c40e0000168e52fc5a8a413122c400730d216a26c418680980c80c8000167413105b4ab13823e420770d21742844486b09a0b80b00001659c3245d8ab94024e430778d117627c428660a20e8108000163f13245d8ab93f24a418780ce1682684006609a0c00a0000162582f8584a31322323fc738cf1642684206b09c0c40e0000160bc3045a8a7939238404750cd16e260430680a00e010000015f0c32e5d0a893b240408728cf1642684186b0a20cc0b000015d6b31059ca713422a3d4708c615e24c408650920b40b800015bc531c5c4aa13523a400728cc16a270438720ac0e00c000015a372fa594a512f22a3e0720ce164260408670a40d00a0000158a52ea57ca392e2243e0738ca16a270408690920d80b8000157003105bca913a238400740d016c25c3f0630980c80c0000155563105b0aa93c23a414748d31762844306d0ac0f00f0000153ca2f6598a6938248420738c71622584186e0a60f80f0000152303085a8a913c246410758ce1682744306e0a80dc0c00001508531e5c4ab139242428768d91682683e0640a00d00d000 else (if i < 5 then 0x219c62d853c9a91d20a3a86a0bb1482203785c0880bc0b8000218452d25449d9282243ec728c91642683e86409e0f00e8000216aa302598a793123a3f4730d216425c3f06a0a20d40d0000215083105bca913823440c718c716425c400680a20e80d0000213862d45449e1252143c86e0c815e2744306a0a00d00e8000211f62f0574a19312323f8730cd16c2804306e0a00d40c8000210602fc594a613322e3f8710c515824c3d05d0920e00c000020ecb2f85a0a713624441c758d2178294428660960b80c800020d372f85a4a9137236400720cc1642744186d0a60d80d000020baf2de5509b91e2163cc6e8c415a268400650940b40b800020a192fc594a393023a408750d0166274420670a60ec0e8000208882f6580a512c21e3c46e8c615c25c3e06008c0cc0c0000206f12f0568a092a21a3dc738ce15e2583f8660a20dc1080002055f2fc588a392d2283f0700c816a26c420660980c80d0000203f12ae508951171fe39c688c214a2483d06008a0c00c8000202612f057ca412e232410730d116a278408660940cc0b0000200b53285e0ae948250414778d41782944586d09e0d40c80001ff2c2e8574a092d21e3e4710c51622684086c0a60dc0f80001fda02de5549e1212183c06e8c01562483c8600940c00d00001fc1c2e254c9b91c20a3bc6b0be14a2403c05f0880a40b00001fa8f2e25589c91f2043a0690bc1462103605707e0b00a80001f9012e45609f1292243d06c0c215c2443985a08e0c00d00001f7782da5449a92120e3ac690b91462343c85e0880b00b00001f5e12f8584a392e2223ec708c51582503e8620900c40e00001f44d2f458ca593624241c770d6172268408690a00dc0e00001f2b32fa59ca69302263dc728ca1602543d8670a00c40d80001f12b2e0558a01242163c06b8be14a22c3a0610900d80b00001efa62d654c9e12220e3a8670b31382043905d08a0c00a00001ee0a2fe5a4a8136236414760d11642543c0640940bc0a80001ec742fe588a412921e3e46d8c214c2483c06509e0d80f80001eacc32c5ecb09432564407b8d516c27c4206709c0cc0b80001e94a2dc574a292a2223c06b8be14e2403c0610900c00d00001e7b6302598a7938246414770d017227c3f86409a0c80d00001e6262d85509f1282223e86f8c51542283705b0860c80b80001e48930a5a8a7935232404740d016e2684086909a0cc0d80001e3162ba528979181f8398668ba1502383d0650a40d40d00001e1733125c4aa13b23a404758ce1622643e86309a0cc0e80001dfd431a5ccab14224c438760d616e284408620920c40d00001de472ec574a392e21e3e8720c715a2543c86208c0bc0b00001dcba2dc54c9c12421a3b86d0c014a234398530800a40a80001db2d2ea574a312d2263dc6c8c214e24c3f0630960c80d00001d98131e5d4b014725c45c808e418a2a84806e0a40e01000001d7f92dc54c9b92121a3d86e8c615c2403a05d0900c00d80001d66f2da5409b9192063b0698b61422243a85c0900cc0d80001d4dd2ea5689d1282103b86b8c41502544106209e0d00c00001d3552d65509b92421c3dc700c815e2383c8600880ac0900001d1c52f257ca292d2203ec728c815c264400610920d00d00001d02f2f4578a213021e3d46e0c61542383f0660a40e80f80001cea42f4578a192a2143cc6d0c01502203905f0840d00d00001cd063105ccac13c240410750cd1782804186c09e0e40b80001cb742e8580a393222c3ec718c41602444106a0a40c80c80001c9dc302590a693422a3f0708cc15a2583d05d08a0b80b80001c84f2f2574a7134232400730cc1622683e8660a00f40f00001c6bf2f0584a41292283d46d0bf1502443c05f0880ac0980001c53f2ce5409d92521c3d46e8c114c2343b85c07e0a40b00001c3ae2ee578a392d2263d86d0be1482383a06108c0c00b80001c2252d85649f12421c3d06f0c51502383b85b07e0940880001c0892fe5a0a813222c3fc740ce164270418670900ac0b00001bedf3185b4aa14025244c7a8dc1882a44586c0960d40c80001bd512e6560a21282183cc6e8be1422303b05c08e0ac0b80001bbb230e5bcaa93923e41c780da178284430660a40d80f80001ba0e30e5d0ad94224842c780cf1682804206c0a80e40f80001b8822f258ca593923a404740ce1622643f0630980d40e00001b6e83065a0a692d22c3ec700c5152228388550800ac0b800 else 0x27d013125d4af144246400748d116e280430740a80dc0c000027b762f4584a412e2323e8718cd15c25c3f06b0a20e40d000027a0b2aa4fc971192063ac6d0bd14e2403985b0820a8098000278782f0588a312a21e3dc6d8c915e25c4286609c0d80b8000276ea2ea5649f12a2243e06f8c915e2603e8650940c00b0000275682dc55c9f92a2263e4700ca15e25c4106d09e0e4108000273d62fe57ca212c2243f0748ce16c284440700a00d80d0000272572d65589d91e2163c86e8bd13c21c3905b0840b00c8000270d72ce5409e92421e3d46d0c014e2343905e0860b40d000026f343145c0ad137240418730c81602643e06609a0c00a800026dad2d65589f1202123b86c8bf1442183885e0920d00c000026c1f2e6570a312b2283f0720cf16e2704005e0880a809800026a8d2ee56c9e9272203dc6e8c01522483f0640a00d00d8000269012ee5689d9202103c06f0c7164258408670980cc0d80002676730a5b4ac13e24441c780d4174278430710aa0ec100000265ed2ce5409d92220a3d06c8c21522383c05d08c0d00b00002645c2f0590a7936238404750ce158264408680940c40d8000262d82d65449d12221e3d46f0c715c2583d86109c0d40c0000261442f2590a79302323fc710ca168260410650940d80e000025fb32ee588a592b2263e8700c815a2583e06509a0c00d000025e362d45409c11d2163c86f0c416024c3c8600920b006000025c9d3045a4a7937240420740d016e2684106709a0cc0d000025b1f2cc5449d1202123b8688bd14e2403b8620940c00c80002599a2ca528979191f83ac698c115022c3a05d08c0ac0a80002580d2ec574a293222a3e8718cc1642703d8650960cc0b00002567d2f45a0a512f22c3fc738d21742684085f0920bc0b0000254e43025a4a693c246420760d11782844286c0a60e80e0000253662d0558a092320e3cc6b0c015022c3b0600940c40c8000251e42cc5349a11c20a3c46c8c415a2543b86108e0a80c0000250562f0590a49302243ec6f8c115425c4106d0a00bc0b800024ed32d85589f9282203d86e8c715a2684086209a0d40e000024d382fa5709f9272243e4740cd1662684106709c0d80e000024bb52d25449a91d2143ac6a8c515a2543e0640900c00d000024a272e05649f1232163c46f0c014a2403c85e0960d00c0000248942f4580a292a2203cc6c8bd1482303a05d08c0a00b8000246f230a5b4a9940250428758cd1602704006b0a40e40e8000245702dc54c9d9242123b46b8c11482383d05d08c0b40b0000243cf30a5a0a69362323f86d8c31542503d85f0940d00c00002423e2ec570a11292243dc6e8bf152260400690a00d00e8000240ac2ee57ca393223040c748d316c2804306d09c0e00e800023f1c2f4588a392a22c3ec6f0c615e2603c0650900ac09800023da12c45189911e2143c46b8bd14a2243c05e0920d40c800023c2b2c25309b11e2063b86b0c11482283a85c0800b00a000023a952fc5a0a613223440c728cb1622604006709a0d00e00002390d2ee578a4130232404758d01742884386309a0c00c80002378f2ce5389a12020c3c86a8bb1502543e86508c0c00c0000235f32fa598a712e22c3e4720cc1642643f86a0a00cc0d8000234642f2570a192a21a3bc6b8c214823c3c8620920b40a0000232db2e055c9d12421a3e46f8cb16625c3f06209e0d80e80002313d3085b4aa938240410738cd15e24c3d05e08a0bc0b000022fbd2d452c9811820e3a46b8be1422203785c0860b80b800022e1c30e5b0a7935238410740cb16c2604206609c0e00f000022c813065acaa93423a420760d616e2784306909a0bc0d800022b052c65449a91e20a3a46a8bb1462283985a07c0a8090000229782e055ca212e2283f4718c615a2703f86a0980cc0d8000227e23005b4a893c23e420740ce16c27c4206f0a40d4110000226592dc560a092a2223dc6f0c415a2503b06008c0ac0a8000224c62e457ca613222a3fc718c214e2443e06509e0d80d00002233b2ec560a19282143d46d8bb1442343d06108e0bc0c0000221ac2ea568a192821e3e4728cc1702644106109e0c40e0000220102fe590a312a21e3f0718c31542503e8650920d40d000021e773005a0a6933234414748d016a268448730a20dc0d800021ce02fa57ca312a22a400738c91542343b86309c0d410000021b522ec57ca412e2223e4708c515c2583e0620920bc0b800))) else (if i < 9 then (if i < 7 then 0x2dee82f0594a793723c418770d116827c400660960d00c80002dd642d25389d1222163d06c0bc14c2483b05607e0a00980002dbdc2dc54c9d11c2003bc6a0b714423c3b8630960c80d00002da4c2ee57ca312e2283e8710c715a24c3b8620960c80c00002d8c22e8580a5131238418740d0168268410680a00d00d80002d74b2c051c9891f2143c06b0ba13a20c368580880b80d00002d5c42d85549e9242063c46c0bd1502403d0600960cc0c00002d4442e2568a01272123b06b0c116024c3e0650aa0e80e80002d2b52ee58ca9938242424788d617e2a0470710aa0e00d00002d1232f8590aa93d24a424780e018c2a0470720aa0e40f80002cfa32cc5349a91d2123c46c0c11522483885e08a0b40c00002ce222d455ca31312243e4720c615a254400640940c40b80002cc9f2ca5389a11c20e3b06c8c01542303c0660900ac0a80002cb0d2f257ca19292223ec700cc1622443c8620920bc0f80002c9812ea568a393122e3f0700c81602503f06709e0e40e00002c80e2b4514951192043a86a8bd14e2303985a0840b40c00002c6782f857ca192e21a3d06d0c11522343b85b0820c40c80002c4f72d45409d1222143b86b0c01462383c05d08c0b80b00002c3732d65489a9212183b86c0c216426c3e8650980e00f00002c1ff2b851c951141f23a0690b91402283a05b0800b80b80002c06d2f2560a01212163cc6e0c41622584186a0960cc0e80002bee82d65409b91a2043b06a0bd1462303a85a0880b80b80002bd4d2fc594a592c22c3e06d8c715e2783f06809a0cc0c80002bbc72e2558a212a22c3f4710c71582503c05a0880bc0c80002ba462de5549e120206398668b713c2383705d0880b80c80002b8c02e4564a09252163c86a8bf14a2403c86309a0d00d00002b73c2de55ca192c2263f0728ca1602643f0660960c40b80002b5bc2d4554a09282283f46f0c51562403c05e08e0c80900002b4262fe594a792f22e3f8718ce15e26c420670a20e40e80002b2af2b8510961101fe3a8660b01342243a05307c0a40a00002b1212e85589d92a22a3ec710c716426c430650920cc0b00002af912fe594a793a246430780d718a2904186b0a60c80c00002ae1e2b451c9791c20e3ac678be1502483d0600920dc0b00002ac86300588a312e22c3f4710cd15c2583d0610820bc0c00002aaf82ea584a31312343f8720cb1662483d85c08e0b80a80002a9802c05109991a2043a8678b31302103605b08a0ac0e80002a7f42da5349d1222203e0700c51602583d86509a0c40c00002a6602f858ca613123c3fc748cf16425c410650900d00c00002a4d42e8574a312f22c400710c315c2583c0600900bc0b00002a34d2ec5649f92721c3c86c8c61582643e0650a40ec0e80002a1d72bc5389991a2063a8680b11342143985f08c0c00c00002a04e2e2568a09292223d86d0c215423c3b05d0840b00c000029ebf2f2584a493322e400740cf16c2704306c0a40d00c000029d3d2d05349c92121a3c8700c91622604186b0a60e80d800029bbe2c8528981172043b46c8c21502503b05f0880a40a800029a422c252c9a91e20e3ac690b81422143805b0940b40b0000298c62ce51c9991b2063946a0bb15225c3e8650960b80b00002973a2e65689e12220a3bc6a0b71442343a85f0900c80e0000295ad2ea568a293222e400728cb15a2583d86008a0b8090000294252d05309a91a2083c86c8be14a2303d06408a0bc0b8000292932ec574a312e22a3f4710c51642683f06509a0dc0d80002911f2b8520969121ee390660b41342283b05f08e0c40e800028fa32cc5389c9212163c06e0c214a22c3b0610960d80e000028e033145bcaa13d24241c790d6176288418690a00cc0b800028c6a3025a4a8134236410740ce1682604006b0aa0e00d800028ae22de558a092a22c3ec738d11602483d06509e0d80d0000289423065aca91382323fc728cc160268410670920b40c8000287cb2be5209791b2083cc6e8c715e2483c05b08a0ac0a80002863d2e256ca01282103bc6f0c415023c3d86309e0e00e0000284b92d65509f1262243d86e8c715a2604086a0a00c80c0000283302de5609e91f20e3ac6c0c115222c3c8610980c00a80002819330a5a8a693822a3fc728c71682584006308e0d80e80002801f2b651c949101ee380648b713820c368560800a008800027e9d2cc5309a11c2063a8660b51442383e06209c0e00f000 else (if i < 8 then 0x3400a2cc5349a1222143d86f0c41542683d8660980c80c800033e9a2b65209991e2083b86d8c61642684186409a0cc0b800033d142d454c9b91a2063a8688b813e2243705d0920bc0a000033b9c2c253099118200394648b2140218388550900cc0c800033a112dc5589e92821a3d4718cc16424c3d05e0980c80f80003388d2d65509e11f21039c688ba1402343a85a08a0a00880003370f2d05349b1192063ac6b8c314e2403d06709a0cc0c0000335862da5689e1262143dc6e8c515a24c3d8600880c40b8000334072ce5389c9242163cc6c0c1146214380510780a00a00003328e2be508961122063b4688b413c2283785407a0a0090000331052de5609f92421a3d06c0c51582483c0630960c40c000032f7e2e45689e9212103dc700c81662503e8660940c40c000032e102aa5009410e1f8390680b613820c3685a0820b40b800032c992c651c951121f0378620b1134208348530780a40a000032b0b2ee560a212e2243e06f8c11462443c0610840b40b8000329862d25509e1242143ac6c0bf15424c3f8660a00e00c8000328122ca5409e9272163c46d0c014822c3b05b08c0c00b0000326882e4570a092321a3ec6f0c014e2403b05f07c0b00a80003250b2ca54ca012721c3e86d8bc14c23c3b85c0940d80d80003237b2f2598a6135230408728cc15e258410690a00d00d8000321e030258ca192c22a3f8700cc16a264408670900bc0c8000320702bc5249b1202143d86e8c416025c3f8690980d40e800031edd2fc57ca41342263f0718c916025c3f0650a40c80b800031d4e2f657ca513323c408770d616e2704286b0a00e40f800031bc22ec568a19232103bc690b61442383d86208c0c40c000031a2b2fe5a0a512e2263dc6f0c815e25c3f86809e0ec0b8000318aa2ce5249811820638c678b814c2403b05c08e0c00a8000317352c0514979121ee368608ad1301f8368540760a8080000315a52f0570a31292263ec710c81642543c05f08e0c00d8000314292ca5409911a20e3b4698bc14e2483d06108c0b80800003129e2ee57ca312f2283ec720cd16426c4286b0a20e00d00003111f2d6568a312d2243d86e8ca15c2503c86209c0d40b000030f902f6594a6933238408750ce16c26c3f06609e0c80d000030e162c65309991d20e3b8678b913e22c368590820b40c000030c9a2cc53c9a91b2043a4668b713c2283b85e0940c80d800030b102d65509e92421c3d8700ce1602604086e0a60d80d00003098d2d45449e12020a3a4678ba14821c3785b0840b00b8000308142c45389a9232163d06e8c715e2543f05f0900b8098000306a32b85109590c1e4378628b3134208368560800a40b8000305242d252c999171fa39c698bf15623c3d0630a80e00e8000303912f0564a292921a3d06d8c41562443e86409a0cc0e0000302092e45549d9262203cc6f8c615c260400640900c80d0000300852d65509f1202163bc658b713c2103705b0880c40b00002fef72e857ca212b2263d8720c91662583d06209a0d00d80002fd6e2e8578a112a2183e06d8c51542483f0650940d80e80002fbe12e85649e92521c3d46f8c41542583e86609a0b80c00002fa5c2e45449d12321e3d46e8c515c2443e0630900a80b80002f8d82d254ca012a2243cc6e0c31562283b85d0880b00800002f7692aa4f88f90e1f2384680bb14a22c3b8610860ac0b80002f5e42de568a092e2223cc6b8b51422203905b0920b80b80002f4512f8584a713923c41c750ce174290440680a60d80d00002f2cd2dc5489d12120a3c06d8c915e2583b05f0940b80a80002f13d2ea578a392c2263e8708c61662783f8620940c00f00002efb52d85549d12921c3e06a8bf1462303985d0820b40a80002ee372d05409c1212123b86c8c81602503f86e09a0c40d00002eca12ec580a212921e3c86b8bb1482343b8630920c80c80002eb202dc55c9e92a2203e46e8c51522443d05d0880b80c80002e99b2e65589f92c2303fc758d11722784306b0a80d80f80002e8122e85649e11f2203d4708c215423c3d05f08e0c00e00002e6972c65289911b2043b06a0bd1522483d86108c0bc0c80002e51f2c45389a91a2043a86a8c314a2443986008a0ac0a00002e3942e2560a012221a3d86e0bf1442343a05d0840b40b00002e20d2d45609f92b2283f0708c315a25c3d06009e0cc0c00002e0772fc5b0a9936246434798d917828c478720b00fc10800 else 0x3a08a2ce5509d91c20c3c46b8bb15223c3b05e0860b80c000039efc2e0560a01272263f4718c81542343b0640960e40f000039d822c252c981111f4388680b513a2243a0560800b009800039c0d2ba5249c9212163d46f8c51522443a05f0980b80d000039a932c65349b12121a3e4700c815624c3f0660920b40a00003990f2d05409c91f2183c0698bc14e23c3d85f09a0d40d8000397972b850c9711c20a3b06b0b81442483f86d0a40e00d00003960c2e2560a012520e3b46b0be1482243b86008e0c00c0000394912c85409b91f20c3c06d8c21502443c06108e0d40c00003930f2c253c9991c20e3b06b0bc14c2383d8650980d40c8000391892cc5209b92220a3b06a8bf1482383a85e08409c0a80003900f2bc5209a91d20c3ac6c0bf14c2403985b08c0b80b000038e8f2d854c9d1202103bc6a8bb1482383a86008a0b40d000038d1a2c052c979182063c86d0c31582503f0650940bc0b800038b852f8574a012821e3dc6c8c815e25c3f0650900c80c000038a082ca5449b92021c3cc6b0c41522243985e0900b80b8000388802e2564a012821c3d0700c3160258408640a20d00e0000386f82f457ca69332343f8730d0172284408680a40e40e8000385772d2564a2932236408738cc168270400670a20e00c8000384002ca530999111f0370640b514421c3886008e0b4098000382612fc584a513022e400708c91622583c0620960bc0d0000380dc2da5409e92421a3e06e0c61602483d8620920d00b800037f572de574a012a2123c06b0bd14c2343c85e08a0b80a800037dce2d656ca39282143d06c8bc1462243885b07e09c09800037c5a2be51c991172023a8680b71422203886208e0b80c000037ad52e056c9c92320e3a4678b513e2143685507809c0a80003793a30a5b8aa13c238400728cb15a2583f06808c0c80a8000377d32b0514971162043a4668b613c2303c0640980cc0c8000376412ec56ca312e234400730ca15e2643e8660920b00b0000374bd2d854c9a9212163bc6b8bc15023c3c8600920cc0c80003733e2cc5349b9222263c46a0be15a2503c86309e0ec0e0000371c92b850c9811c2063b06e0be14e2483d05f0980d40c8000370412de55ca092f2363f8700cc15e2603e0670940d410800036ecc2bc50c9711920439c698bb15024c3b85e08c0ac0a800036d3e2ee57ca212a2283f0740d316a25c3f0640980d80a800036bbf2ce5389991b2063b8688b9144230398620960c80d000036a352e65609f9292243d46d0c1156254400690960c80c8000368c32b050c971131ec3645d8a611c1d0318540760b8088000367482bc5189911d20e3d06b0bb1402183a85e0940b80c0000365b13005a0a81362323fc758d31742844286b0a20e00c8000364382be5249a1192043a4668b413c21c3a85b0860b40d8000362aa2ea55c9f12721c3dc708c515425c4006309e0d80c8000361192fe58ca492b21e3b46d8c615c2603e8620900b40a800035f922d25389b11d20c3ac690b81422103905a0760a00c000035e132da564a192c22c400708cc15e25c3d8630ac0e810800035c9e2be52c9811f20a3b0688be1482443d8670980cc0b800035b212be5249891b20c3bc6d0bc1482403d85e09c0ec0e00003599c2e2554a19292283fc718d016e2743f06409a0d80c0000358252c2518961162083b86a8c314e21c388580880a80c8000356a62da5549c9242143c86d8c315223c3c86509a0d80b8000355292d8560a01222163dc6e0c11502403b8600900a8090000353b22bc5089911b2083ac680c01402243785707c0a00b00003523f2ba504931131f83a4668b814822c398590880b00a0000350ad2ea564a19232163c06c8c214e25c3f0660980d00c800034f272e0584a492e228404730cf16a25c3f0600940cc0e000034da22d8568a19292263e8748c71502343a06208e0bc0b000034c242c65349c11c20a3b8690bc1422183805507809809800034aa52d45489c9212163d4710c71582543d0620920b80a8000349132ee578a212d2263f4718c41562503c8600880c80c0000347962c85409d11e2103c46e8bf14e2283c8650960b80b8000346122dc568a092f22c3e86f8cb1642603e0680a60cc0c0000344872f2574a19282243dc6f8cb1582583f86408c0b80d8000343102b24fc9290f1f4388650b013a220388610980c40c80003418b2e255c9d92a22c3f8728cd1602603e06109a0cc0d800)) else (if i < 11 then (if i < 10 then 0x3ffe02a64f0929101ee380630b31362043505407e0a40980003fe463085c0aa13e23a408768cd16c2643f8680920b00b00003fcc32d054ca09282203cc6d0bd1562403a85a08c0c00b00003fb452ba5249891c20e3bc6c8c11502503b85d08a0b40c00003f9cc2bc4fc941101f4388680b91462343c05e0920c40d00003f84a2d25409a91a206390650b41322183805e0860ac0a00003f6ed2924e0921091e0374648b3136208388580840bc0a80003f5702c05189711b20a3c46a0bd15a24c3f0650920bc0c80003f3ff2b450c949101fe38c630b41382283805b0880c80d00003f27e2d855ca09272143c86e0bf1562543c8640960d80e00003f1012d453c9a1222123c06b0bb1482483d86308a0ac0a00003ef712e65549d12220c3ac698bf14e23c3e0670a60e01000003edec2dc55c9f9262223e86f8ca1602503e8660920b80a00003ec572f2598a79342323f0720c916e268418670940c00d80003ead32de54c9c12420a3c46c8c3154254400670a40cc0a00003e9462ea58ca292e22a3f8728c61602603e86a0a40d40c80003e7dc2a24ec931091e4388678ba1482303905707e0b80b00003e64f2f0578a112a2163c46c0c1154254408690920d00d00003e4dc2ba520959161fe394658b613822c3b05e08a0bc0c80003e36d2b85049210b1f2384650b31382043605a08a0b40d80003e1e62e05549e12120e3c46d8c715823c3985e08c0b40c80003e0672c65289791a1fc398668b51382203985b08e0bc0d00003dedd2dc5549e92521e3d46f8ca15a2483c8650880ac0b80003dd712b64fc9210f1f437c630b312e20c370560860b40b80003dbeb2da5449c12020c3ac6b0c013e2243b85d0880c00a80003da7f2aa4f49210d1f8388668af1362143985f0880bc0d00003d8f22f4594a492d2263f4710cc15e26c418680a00f40f80003d78a2a24f0909111f4390678af12e200338590880ac0a80003d6152bc51c959192023ac6b0c01502503f0620900d80d00003d4aa2a44e49290b1f037c670b81462343a85b0820a40b00003d3202dc5549e1202103bc690bd13c2383905908c0b40b00003d19b2d6550a0133234400730cc16e27c3f8660900c00d00003d0312a84f4951142043b8680b513c2143805808e0c00b00003cea62ea56ca413122e3fc730d116e26c4206b0a60e40d80003cd3f2aa4f4921121f0394650b51442183705907e0a40a00003cbd02b65049310c1ec394690b914c2343a05b0880a80980003ca612aa500939111ee380680bb1422383d86809a0cc0a00003c8e22c85309911d2083b46e0c816425c3f86909e0cc0e00003c7742ae51c961151ee380648b512e2203805a07c0bc0a00003c6032b64fc951101f439c690bb14a2203a0610820b00b00003c48f2c05109590e1ee390648b213221c3a0600900cc0c00003c30b2ca530999191fc3a4688b91482383d06a09e0d00e80003c1852e254c9c12020e3c06e0bd1522343b0630900b80980003bff32f4580a292d2243e06c0bf14c2343e8670900e00d80003be762ce5389a11d200398688bc14e23c3c8620960d40d00003bcf22de5489c1212143c86b8bf146234388620940bc0a80003bb762d65449a1192083bc6c0bf1582403b06008e0b80c00003b9f12e0580a59302263f4730cd16a26c400670960bc0b80003b8762c8528971141f23986a8b813a22c3a8580900d00f80003b6ed2d65489d91c20c3a8680b713a21c370550800a80c80003b5622ea570a09232203d86d0c215a2403b8600920b40b00003b3e52de55c9f92a2203dc710c715625c3f86b0a60e40d80003b2632cc5489c1222123b0688bf1542383a06308a0c00d00003b0df2d4540a012b2283fc730cc15e25c3d05e08a0b00c80003af662c4520959192083bc6c8c21522483e0650920cc0d80003adc93085a4a893b23c41c758d617c28c420660980cc0900003ac642944d09110d1f238c630b212c20c338520760980880003aaf52aa508949122003a8680ba14a2283885d09609c0980003a97a2d25509e9222103c46f0c51562443b85f0840ac0b80003a7f52d6550a092722c3e8720d016e2884506c0aa0ec1000003a6752d65409d9202123bc6b8be1482343a05b08e0c80b80003a5062b2514981171f8390698b914623c3b05c0900d40d80003a37a2ea56ca112b2263ec730ce16a260420670a00cc0b80003a2072ce5309a9181fa38c658b513c2203805b0840c00a800 else 0x45ee92ac518971161fe38c678b714022c3c05d08e0b80c000045d612e45609e92b2223f4710c615223c3e0650900a40c000045bd32e6578a312f2283ec708cb15c25c408700ae0d00e000045a4f2d65649f92b2183c46c8bd14e2403b05e0920ac0a8000458d32cc5309a11b2083a8690b81462383b05c0900bc0d00004574b2d65549e9282223f46f8cd15c24c3d85e0900b40b0000455d22be53c9b11e2103c06c8c41502583f8680980d80c80004545d2be510971152063bc6d0be14c23c3b85b0800b00a8000452e32c2530989171fa388638a8124208378540840a40a00004515d2d85509f1252163cc6a8c01522383a8640880b00a000044feb2c25349d9242143c46e8c315c2644006b0a20e00b800044e7d2ae500959181fe3ac690be1462303a0640980bc0a000044d172a24e0929131f238c678b91462403e85e08e0c00b800044b962d45549f1262263f8708c31522483b0600920cc0d800044a122d05489d91e20e3d06c0c11542543e0620900b00b0000448a72a24f09390c1e4370640b41422443905807e0ac078000447382a6504941131fa38c650b913e22c3905c08c0b80c0000445cd2a44f09210d1ee35c608aa1321fc3585a0880b40b0000444412de568a292b22e3f0700c415024c3c06208e0b00a8000442bd2e6570a11272223d46c0c114e2403f06b0a40e40c0000441472be5249a91c2083ac688b21382283905a0820ac0a000043fca2c65489d91b2143cc6e8c116424c3d0680900bc0b000043e412da5509d9202143d06e0c715c2503f85e0880b80b800043cca2bc5089711920a3bc6b0bd14420c3785307e0b00b000043b572bc51c9510f1f2384638ae13822c380580880c00c0000439c62f8588a192a21a3f0708ca15a2543e05e0800b00b00004385e2a44e89310e1ec374650b51462283785a0860ac0b8000436e22c45349a12020c3c86d8c61562443c06509a0e40e80004355a2e05389b11f20e3a8688bf1482283785b0800a8098000433d72ce52c9c11d2063a4678b814223c3b86709c0c00a00004325c2ca5449a91c2083bc678bd1422243b0600800b00b0000430e72c452c999182003a0690b413620c370580880b80b800042f772ac500959181fc3ac690b713a2083405608a0ac0a800042e002ba50c981171f63ac6b0b913e2283905c08a0ac0d800042c7e2c85249a91e20a3c46a8bb1402383d05e0920d00d800042b0a2ba528989161fa39c680bf1522503e0630920b00980004298e2c45389c11c2003b8688b514422c398610920b00a8000428032dc5449c9232103c06b8c114e24c3d8640920bc0d8000426992ac4f49290e1ee384660b913e2243905b0880c40e0000425162d652c991192063a0650b213822c3b06609e0d00b8000423942de564a09282243d86f8c015423c3b85c0860b80c8000422052f4580a212d21c3f0700ca1622503d85e0840b40b0000420852d65449b92421c3d86f8be13e2083605408c0bc0b800041f0c2cc53c9c9212183cc6c8bb14021c370590820ac0c000041d7e2e2568a292c22a3fc738cc15c2503d8630980c80b800041c132a64fc929171fc3ac6b0be1442343a05f0820b407000041a962c85389b12521c3d4700c616825c3e86109a0d40e80004191d2bc5189911f2143ac690bc14e2383b85f0940c00b8000417982e05509e91f2143bc6f8c51522543e8610920c8098000416272b45109711a2083b06d0c11502383d06009a0d40c8000414be2a44ec9210f1e0368640ad12c1f43405307e0a0078000413512b4528999182063b46b0bf1502403d8630920c00b8000411c82e6574a492c2283e8710c61602743f06309e0d00d80004104e2ca534971131f2388670bc144224380550800b00b000040ee42a84ec9210d1ec380630ae12e2103785a0840a80c000040d6b2c251098917202394660b11302043605808a0ac09000040bd42fa590a393322c404728cf164254400630980cc10800040a4f2d45409b12320c3bc698b9146234398600920b40c8000408c92da54c9e91f20e3c06c8c21502403a05b08a0c40a0000407522c45209891920039c680b51362003305006e08c0a0000405d62ce52c999181fa38c678bb1562443e06209a0d40c8000404532da550a092721a3d46d0c015c258400670920b00d8000402ce2e05749f92a21c3d46c8bf150230388560820c00d00004014c2d854c9e9202083b46c0c015823c3c05f09c0cc0d800) else (if i < 12 then 0x4bce92ea56ca21292243c86e8c9154268400620940cc0f00004bb642e45589f9262203dc6e0c916e28c4286d0a20c00d00004b9f22bc518989151fe38c660b31402103905c0920c40d80004b8802be52c9991a1fe3a4698ba14a22c3985907a0a40a80004b70b2b4508949131fc3a4690b81502403c85b0880b00b80004b5952c65289a1202163dc6f0c914e2443f06709c0d80d00004b4262ba5249b11d2123b0688be152250408620960d00e00004b2aa2d45409a91820a3b46a0c314822c378560800bc0a80004b1232e4564a112d2323fc760d61822a4480750a80e80e00004afac2c6528989182083c46c8c21562303a0600940c40b00004ae392b85289891620c3b46d0bb14e2203905b0840a80b80004accf29e4e49090e1e8374658b014020c3785808009c0a00004ab572c05249690f1ee384660ba13e224388590880b40b80004a9e62ae500941111f037c670b91422243905f08c0b40b80004a8712c0524989202103ac6b0bc14a2203805d08a0bc0e00004a6f32c4500949131fe398690bc1502483e0680900d00b80004a5732d25549e1262263fc718c615c2684286a09c0cc0c80004a4152864a48b9001d63445b8a41241f4350560800b00900004a2942d052c9b11e20a3a8678b413420c3605107a0a00a00004a1172d85449a91e202394688b713821c3a86009a0c80c000049f972d45589d11b2063b06c8c516226c430720b60e80e000049e1c2d052c9d9252103d06c0c01462403a85a0880bc0b000049caa2b45089611520439c678ba1502443c86408a09c09800049b392ac50c969101f4390678bf14c2343985e08e0c40e8000499cb2ac508971151fc3b06d0c115a2403c05c0960d80e80004985b2aa504941121f0390660b513c2403c86709e0c80d0000496dc2ce5489b91f2103d46d8c01482383b05c0940cc0d0000495732ac4fc961192003b86b0c31482243a05c0840a40a0000493f92ba51c989182003a0688b81422283a05b08c0bc0b0000492782d25449d1272223e4708cd1602543c0640920c00b8000491032c25149510d1ea370630ac1301f83505407e0a409800048f782e8560a292d2243e4708c816425c400630900c80c000048e1329e4e4951111ec37c660bd1502403b8670a00e40d800048ca22ae504941151fe398660b31402383a05e0920bc0b800048b312ba5149891a2023b4698bb14221c3a05a07e0b0088000489ad2d652c9a9171f438c670bc14c23c3b05c0860b80b80004883b2ba514979161fc398688bd1522483c05e08c0cc0c0000486b72d45409c12321a3d86e0c816a2784206809c0c00d00004853a2c853c9b9202123c46d8c01542443d86008c0a80a8000483cb2ae4f89691620239c688b914222c3985a0800a40c0000482482d85609e1222183d86f0c81582443d05e0900b40b8000480bd2e2564a39302203d4700c815c2583e86a09e0e40d800047f452c05109891c2103c0690be14421c378580860bc0e000047dd42b4510971151f8398680b71442243885a08c0b00c000047c602be50c9611a20e3b06c0bd15025c3f85c0900c40c800047ad32f257ca392f2263ec700c014e2343c85e0900b40a0000479522d25489c1222163c46e8c314a2403805a08a0bc0b0000477ca2e2564a112e2303f4730cd162250408630980bc0c80004765a2b05249911b2083c46b8c515223c3905a08a0c00c8000474dd2c45189711d20c3a8688b613e22c3905f0920b00980004737c29a4e88f9031e436c638af13a2183785808a0b40c0000471fb2da5609f12421a3cc6e8c715c24c3e8670980dc0f0000470952a24e8919101fa3ac660b713620c378520800a409000046f2f2a84fc9610f1f6388638af1302003485607a0a409800046db22c852c9a11d2103d46b0be1442183805808a0ac08000046c312c6520969131f6390640b21382183685507e0a40b800046ab82c65209a92121a3e06d0bd1502443d06108e0c40e80004693e2c85389a91d2063a06a0ba1462183985d0860b0098000467b62e8568a092821c3dc6e0c51542483c05a08c0b40d8000466452b25089691720c3c46c0c215a2503d8610960d80b8000464b92e85609f12a21e3e8720cc17027c4286909a0d80c00004633e2cc5509b1212103c0708c71642543f06509e0d40d8000461ce2bc524981162063b86a0bd14a23c3b05e08c0bc0d0000460562c45249b9222143c86c0bc132214368570880b80b800 else 0x51ae92b2500949132043b46c8be15223c3a8620920c80c8000519772b4520969151fe3a46b8c114e2483d06008c0b80c8000518022ae500941162043a8688ba1482383b85d0980d80e0000516a02884a08b8fd1d2350610ad1282103705d0860a4088000515212ce5309911c2103a86a0c015222c39056080098098000513a72c45209991d2143c06a8be15a2443a86008e0a00a8000512312b650c971142063c4688b513e22c3585908c0b40f0000510ca2aa510969101fc39c660b814c2243a85c0840b80b800050f562b65049811a2143b46a8c31502343c05a0840b00c000050de42ae5189991e2143c46e0c514c2343b05d08c0c40c000050c5b2de570a29252163c86e0be15224c3906008e0a807000050aec2b8524979131e8390670bb14621c3585007608c090000509732c253c9b11f2043b46c0be14822c3b85d08a0bc0d0000507f42c45249a1132083b8680b613a21c3b05e0920c40b80005068b2a24e89390d1fa390650b31342043285107c0b00900005050e2d05449e92120c3b86c8bd15824c3f86509c0e40c8000503892d656ca1933236410748d01722784106609e0d40b00005022a29e4d08f1071de360610ad12e1f8340560840b80c0000500a12ec56ca192b21a3d06f0c11442303b0660980d00f00004ff1b2e25609e12321a3c06c0c715423c3805b0900bc0e00004fda02d05589d12220c3a46a8bf14823c398600880c40b80004fc232cc51c9a12121e3c86d0bc144224370590860b80b00004faa22d455ca012721a3c46c8c916024c3f86409c0d80e80004f9412984e4911081e8368610a912e21c3805708a0cc0d80004f7d72a84f89390d1fa3b46a0ba13e2283c06208a0a80b00004f65c2ce544971171fc38c640b11362203705d08c0b40a80004f4ea2bc5249b11f2063b46a0b713e2203b05d0880c00b00004f37a2a6504929101ea380640b11341fc3305307a0ac0900004f2062b45089390c1e8374630ab1322143985e0840ac0980004f08f2c04fc931121ea374630ac13a2283b85e08c0b00b80004ef1c2b8500921051e2360608a71221e43585307a0980900004ed952d455c9e9272143d4700c614e24c410670960c80b00004ec162c651c981162023b46a8bf14e2383b85d0920c40d00004eab02964e09210e1f4374610b5140220390590840ac0980004e9282d253c9d92d2223d06e8c515e24c3c06709e0c80c80004e7bd2a24e89190b1e6380640b513c214350570800a40900004e6402c6524999151fe394690b714822c3a05c0880c40b80004e4b82da5549e1242183d06e0c31582543f8630940d40d80004e3532a04f0941101fa3a46c0b91462503d06609a0cc0c00004e1c92de5609f12b21e3e0728cc16226c4206c0960b80c00004e05e2a24d88e9041ea374630b11362183885e08e0c40d00004ded72e8574a012721a3d86b8bd14c230370590860bc0a00004dd632b44fc979172043c06c0c615624c3d8630940ac0880004dbe52c852c9b91b20e3c46e0c415c24c3e0640940bc0c00004da7d2a24f8949111f6390650b61442283a05c0940c40d00004d90a2b85189991a2063c06a0bc14e2483985f0900ac0c00004d7972be50c939131f6380660b21442303b05d0940c80d80004d6232ba5349991e2023a86a8bc14a244390600980d00e00004d4ba2ae5089490d1ee37c648b31362243885c08809c0b00004d3492b25189591820c3b06c8c015824c3c8670980cc0d00004d1cd2c2530989182083a0678bd14a2383b05c08a0c00d00004d0612b0500949131fa398640b313e2203705308209c0800004cee72c2520971182023a46b0be14e2483d0600900b80c00004cd572f0570a11262203d06a8bd1462383a85b08a0bc0e80004cbdd2c45289891820c3c46a0c21542443b06408e0b00a80004ca6a2b6508951131f6388660b513c2183885f0840c40b80004c8eb2ca5349b91c20e3c06b0bc14c2343b05f08c0a80a00004c7722d054c9d11f2103c46b0c21502443b85e08c0c80c80004c5f92c653c9811a2023b86b0be14e2443b85f0880b00b00004c47f2c05349911c2083b46b0bc1342143985d08009c0a00004c2fb2d654c9e91f2143c86d8c815c2503e8660980d00b80004c16e2e45749f92a2243d8700c71542383c85f0900b40c00004bffb2b6520991182043a4698be1542303b8630900d80e00004be732e6564a112421a3dc6d8c415e2503d0620940d40c800)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0x578882b04fc9390d1f2384650b412e2043785807a0900900005770c2cc5249811a2063b86c0bd15224c3a85b0900bc0c0000575a02a64f8959152023a46b8bc14e2483c0680960b00d0000574272c45389a92220e3cc6f0c41562483c85d0900c40c8000572aa2d45449d9252243fc710c915a2704106a09e0d40d8000571422a04f4911091e4378640b613c214340580860d80e000056fbb2da5509d12322a3ec708c915a2543f06208c0b009800056e502aa4f09110b1e6388660b11342103605408a0a809800056cd52cc5289b11e2023a8688ba1462403d05e08a0c40d000056b6c2aa500931081e4360628b212e2203b0600980bc0c000056a002a05009411a208390658b213a2203a85d0880c40b0000568882c2514949122003b0690bb1522503c0640900c00c0000567152b651c9891620039c680bb14a2403e05f08c0bc0b80005659f2c2514971141f638c678b614a224390510780ac0a00005641f2c45309b91e2023a46a0bd1502503a8600940e00d0000562a82c45189711a20e3d0710c916025c3e0640960c00d0000561412a24f09110a1f0388638b0128204368520760a009800055fd12ae4f09110c1f23a0660b8140224398600880ac0c000055e452e25509d1222163c86b8c614e2483a8610940c40c000055cda2aa4fc9190c1e8380660b113e2303905d07e0b00d000055b6c2ae514989182043b4698bb14822c3b85b0820b4088000559fa2b65109310d1fa388648b214222c3a8620920c00b00005588a2b8508951151fe3b0660b614423c3b86009a0b80b8000557072dc54ca01262143d06d0c01562403b05d0880b00900005559c2b051c979182003b4688b513c2203705707a0a4098000554292ae4fc949121e8370640b013422c3905a0840a80b0000552b52be51c981161f4398690c11502403a05e08a0a8070000551472ae4fc971171f0390670b71402483e0600880b80c000054fe428e4bc898fe1d034c5f8ad12e204378520760ac0b000054e632ca5489e92321a3d46c0c11582443b05f08c0b00b000054ce02d05449e1242163a8690bd14a2243885907c09009000054b622c65349a12421a3f0720c616025c410690a40cc0d0000549e92be520971161f2388658b91542403d05d08a0b00d0000548732c45349c12621c3d86f8c81582543e0630a40ec0f8000546eb2d65509f12f2243dc6f8c615a2503d85d0860a80d0000545792c25409c12a21e3d06e0c115223c3c0630980d80e0000544082ba510971131f8390670ba1342203805607e0980800005428c2ce5409e1222103bc6c0c014c2183905e082094088000541172b6524971171f83a8678b814623c360550880b40b000053fa02c052497116200394680bc1442343a85a0840bc0c800053e2d2b6504971161fc394668ba14a218370580840b00b000053cad2c65449d11e20e3d06c0c415624c3b85c0860b40b800053b3e29e4d8901101f83a86a0b914823c3c05c0800b40c8000539d12ae510939141f438c670b91422443e06509a0d40c8000538692a44d48e9021da3585f8ac1261f83485508209c098000536d72ee570a49272183d86e8c21582503d8600940d40c0000535512da5509d9292203dc6d8c014e24c3f8670a00e00d0000533cc2d25609c1202103c06c0c01542403e0600940bc0d80005324d2cc53c9d1252183cc6f8c315c2343e06108a0a80a0000530e829e4e09210d1e035c620b1138204368580860b80b800052f6c2d45349911c2023a46a8bf14a2403d0610900c40d000052dea2ca5289a1191fe3ac690c41482183785908c0c40c000052c772c2520981111fe394668b51362183785607e0b40a800052b002c85349911a2083d06d8c51562443c86208c0d00b8000529892c051c969172043a0658b413a21c378580840b00b00005282529c4ec9190c1ec37c650af13421c370580860c40b80005268f2fe584a192b2283f46f8bd14a220378590800bc0d0000525182b6500931141fc3a8698be14e2303c0600920bc0a0000523b32a44f8921142043b86b0be14a2443c8620940b8098000522322d25509e9232143d06e8c515823c3e05d0960c40c8000520c62ae504979181f6388678b7138210378570780a80b000051f512ba52c9a11c2083c06d0c01402383c0610980c40d800051dce2d45349a11c2003b06b0bd14423c3a05f08a0b00a800051c572c65209891820239c658b81402283705a0800bc0b000 else (if i < 15 then 0x5d5632a44ec9110f1e836c638b213e2143a06108e0c40b00005d4042864b88a1071d636c618aa1181d42f84c0720900a00005d28f2b8504941142023a8668b913c21c3605407e09c0b00005d1272a44e49190b1ec384660bb1462183a05e08e0bc0a80005cfab2ca52c981111fc3b06c0be14c22c3c05f0900bc0b80005ce352c05349791b2003a0668b613c2243885e08c0d00b80005ccc52b650c9110c1ec374630b21301f43405307e0b00a00005cb532b4508969101f83a4690bc14c23c3905b08c0c40c80005c9e32ae510979162003a4688b51321f8338520820a00c00005c8722bc50c959131f639c688bb14c2383c0600960d00c00005c70d2924cc8e1091e8380648b31362203685407e0b40c80005c5942d05449991f2083b86d0c21582483d05d0920c80d80005c41a2d0520971202163b4690b914a238390590860a40980005c2a52c2530981192023a86d8c51562583f0650820a00980005c12a2c452c989171fa39c698bb1542443b85e07e0b40b00005bfbe2b451c981192023b86c0bf14e230398620960cc0c00005be4c2b44ec9290b1ec384668bb1522383985d0900b80c00005bcd82c2538991172003946b0bc1422183885d0960c80b80005bb5d2c45209911c20e3ac690be14e2303a85c0880b80980005b9f12984d4931111f839c678b8140234390580820a00a00005b8762b251c981182023a46d0c015a2343985c0960cc0e00005b70a2aa4f8951111e836c640ab136214358590840a80680005b59c2b2518941181fe38c6a0bb14c2303985f0800a00900005b42e2ae4e8941121ee38c650b513a2283b8610940c40e00005b2c52a84f09290f1fa380650b6148230370500760a80b80005b1412dc560a012821c3dc6e0c21502303785807e0ac0a80005afbe2dc564a012521a3e0718c91662483d86108a0c40c80005ae4f2a64f09190e1e436c620b313821c3a85f08a0b80c00005ace729c4d08f10d1ec36c620b1136208358550820ac0a00005ab712c853499919202394668b0134224378580800a80a80005a9f22d05409a11c20c3b46a0bc14c23c3c0670940c40a80005a8892b0500959121fe3a46b0bd1582684206c0ac0ec0e00005a70e2d25489f1262163c06d0c41542543e06309a0d00e00005a5a22b0514969131f4388680b91482303985e08a0a80900005a4292c2518979172003a0690bb146220368540800ac0d00005a2ac2b85089891e2143c86c0be14622c3885c0940c00e00005a1422a04ec911101fc398688c115021c3885808c0d40d000059fcf2b24fc931101fc39c658b213c218388520780a40a800059e692a84f8921171f839c680bc1482343b85e08a0b00a800059ce92d2538999182083b46d8bc14c2343a8590860ac0b800059b6e2c85389b1212103cc6b8c215c2583e0680980d40d0000599ed2da5649e92c2223e0710c41622503c86109c0c80e00005988c2924c08c1011d8368610b11342043705b08e0b00a00005971f2ae518979162003a06a8bb14221c3885f0920cc0e0000595a52ca53c9f12b21c3d06d8c715e260400670960d00e0000594372ac5009390d1f0398698b713c2203a05b0880c00c8000592b92d0528971192103b46b0bc1462383a85a0840c00b00005915d2884b08d1021e036c628ad12c20c3585307c0ac09800058fd22e454c9c12421c3e86f8c515e2483b85f0900a809800058e552c6534979142083b06b8c015624c3985907609809000058cd92c253c9911a20c3b86a8ba14e21c3605707e0ac0b800058b662b451498915206398680b614423c3b86209c0c80e8000589eb2ca5289a91e2083b46b8c11522543f06a0a20e00d80005887e2ae5089711b2063bc6c0be14c2383c05a0800a80b0000586fd2cc5389d12321e3e8710cb15a2503e06509c0e40d0000585a028a4c48d8ff1dc36c618ab12e1f83485307c0b00b00005840c2f2578a11292203e0738cc15a2583e8630920d40c8000582932c25209c1222103d06d8be14e23c3c86309c0d40a0000581272b4508951101f2384638b414222c3b8570800c00c800057fb42b6508969181fa398698c11522383905f0960ac0b800057e4c29c4d49110d1f2384630b1132200350570840a008000057ce72904c88e9091e0370640b31402103505507609c0b800057b682c8520989142023a8690b913e2203985c0860a0090000579f82b65009310d1f6390670b41402343b85f08c0c40b000 else 0x631b02cc5349991e2183dc6f8c414e2303c8610980c80d0000630432ac4f89310a1f438c678b71402103a05f0940c00d800062eb62e4570a21332303e8720cb16e278408690900c00b800062d3d2b6518981182043bc6a0c415224c3d86209e0c40c000062bcf2ae5109791d2143d46c0ba14422c3885b0880b40b800062a592b25189991e20a3a46a0bb1502343b86109a0c40e8000628fb2884c49010b1ee390650b31341f0348540860b40a80006278f2ae4fc96916200390670b81402243a05f0940d40d00006260b2da53c9a1202103d86f0ca1642684087009e0e00e8000624972ae5089611b2103cc6c8bf14c220390590940cc0f80006232d2a24fc9210b1ee384620af13e2203905b08e0d00d8000621b72c85109511620a3dc6d0c41422403d85e0900b80e0000620562964d48e1041da358620aa132200350580840c40b000061ee52b0510971172023b0690b413a224390570840a80a800061d7c2a64fc951131f6394668b21301f8368580800b80a000061c032c65309d11f2063b06a0bf14e2383a0590880bc0c800061a872c451c9991b20a3a0678b11422343b85e07e0a00a00006191c2ae510961141fe388668b713420c3605607c0c00d8000617a72ba518981192023a0680b41402303a85c0840b40c0000616402a24e08f10d1e838c618b213a2183605807e0a00c8000614d02b6500929101ee380638ac14021c3885c08c0bc0b80006135f2b651c9b1172003bc6c0c515a2584006a0ae0dc0e8000611fc2984e88e9061e0368648af132210398570860bc0d8000610932a24f0929101f0378640b51482283905d0860ac0a800060f282a84e8931101f439c680b313c2383905e0960cc0c800060dad2cc5209711c20e3b86c0c114623c3e8620880bc0a800060c412ac4f09390a1f038c670b613e2303a05d08e0b40b800060ac42c0520989192083b06a0b9140220380570800b8090000609612a04e4921091ec37c630b514022c3c8670a20d40d0000607ee2be50c959142003ac6a0c21502503d06308c0b80d8000606862a44e89490b1f8398688bc1402283705807e0ac0a0000605042dc5409c9202063a8690bd14a2303a85c0860c00b00006038b2c0510951141ec37c638b312e20c398580860a40a8000602212a84f0969161f8398690be14a22c3a8610980a80a00006009c2e25589e92721e3e86e8c616424c3f0620960c00d80005ff1f2c4528991182083d06e8c31522443d8680a40e41000005fda82ac4f4941131fa398668bb1422383a85c0900c40a80005fc392ae4f49290e1ea37c628b31342103585b08c0bc0d00005fac82b85149891c2063b0690ba1522443b05a0860c00d80005f9572c2530979141f8390678bc1422303785908e0c00c00005f7ee2ae504941121f63a0680b814a23c3b86809c0b40b80005f6822ae4f89310c1ea37c640b31301fc3505207a0940880005f50e2c052c971151f8384678b713e2303d06609c0bc0d80005f3a02aa4ec909111f63a0690ba1382103585608a0c00c80005f2402964c48e9051dc3605f0ab1302043605607c0a40880005f0cd2bc520979182083a4688bd14a23c3985d08c0a80a80005ef542c250c9991e2083ac698b91482183b06109a0b80d00005edde2c2510969111f83a46b8bd1482243a85c0860b00b80005ec792a44f89210f1f63a0678b7144228388590860bc0b80005eb0b2a64ec911111fe398668bd14e23c3b05e08c0bc0b80005e9902c25289911c2003a86a0b31342183605a0800a40b00005e8262b450c94916200398678b91442343c8660920b00b00005e6af2be51c9611820a3b86b8bc14e23c3d06009c0c40b80005e5452a44f89110d1ea364618ad1262143885c0900cc0d80005e3ce2c252c9a91e2123c06a8bf14e2203985a08a0c00d00005e2682a24e0919051ce3385b8a612c2083505707e0b40b80005e0ed2c051c9992221c3d8710ca1602704106c0a40c80c00005df6e2d65409c11f20a3c86b0bf15021c378580860b00900005ddfd2c05209791a2103bc698b51482383b05c0820ac0d80005dc8d2b05009290f1f838c668b51402383d06308e0d00b00005db1e2ba508951161fe3b0680bc15223c3905808a0b40a80005d9c72824b88b9001da35c5e8a71262043485507c0a00b00005d84b2d05489a91d20c3cc6e0c61522483d0620940d00e80005d6c72c852c981191fe388670b813a224380570880bc0d800)) else (if i < 17 then 0x68de02c25249b11d20c3d06b8bd14a2303a85d0800ac09000068c652be5309a1192183d46e8c61562483c8620900c00c000068aeb2d45509b11d2063ac6a8c716e2683f06a09e0d40f00006898b2944e08f90c1ee384640b313e21c370550820a00a0000688172b850c959172123b46a0b814a2383905c08c0c40d80006869d2ce5489e92521c3e8718cc1642544086509c0e4100000685302c25289a11a2043c46d8c715c2483d8670940c00c0000683c32a85049391820e3a8688b81462303d8610920c00d0000682622984bc8b1061e036c648b01342243a0620940c40c8000680fb2a24ec949111f2380660b61422343e8650940d80e800067f942a44e09010c1f2388648b61402343905908a0ac0b800067e102dc5709e12521a3cc6e8cc164264400660a60d40c800067c9a2c6524961151f638c688b713c21c360560800ac0b800067b3529c4e8939121fe394650b31302203a05d0880b4098000679d72964c48c9051d6340600a812c210388550820bc0c8000678662b451c969131fe39c678b9148234390610940d80b0000676f92b0504969172023a0670bd15023c3c05f09a0cc0b00006757c2d05449b9212083a4698b61442303b05e08e0c40b80006740b2b250c9611b20a3bc6b8ba14a2383905c0960cc0d80006729b2b04fc979172063b06e0c11542644186608e0bc0c0000671262c651c9991c1fe3a0648b61302003405407e0ac0a800066fba2a64e09190f1f839c668b51462283a05d08c0c00b800066e432be51c981181f63a0688b514022c3905b08c0ac09800066cde29e4e89290c1ea37c618af132220370590900b80b000066b692b65089390d1f6394678b41442203905d0900b00c0000669ff2a64f0921081ee388668b9148228390600900c00c00006688c2b4518979171fc390660b713e2303a85e0940d00e80006671b2b2518961151f438c628b2130204378580880b80d0000665a22c65389a11d20c3c86b8be1522483b8610940c80d80006642a2be520949121f8390698b61382183805507c0940c0000662b62b65249b11c20c3b0690b815a2303c0620960d40d8000661522924c48c8fe1ce3305d0a612220c3705b0800a409000065feb2a04f49410c1ec37c660b31382203805007a09409800065e682d25409e91d20c3d06a8c215625c3f06a0a40e00c800065d012a44f0901031de368628ae13221c370580800a00b800065ba12884c48b1001d43485f0a6128208330500820ac0a800065a262ca5149711820c3c06b8bb1502443805b0940b80c0000658ab2c45249b11c20c3b8690b613e214358530820ac0900006574629a4dc9290c1f4394668bb1422343b05f08c0c80c0000655d02b65149711c1fe394658b813e2383b05e08e0b40a00006548726e480868f81ca34c630ae13220c3805d08c0c40c0000653092ce5409c1252203e06f0c5152264400690960c00b00006518f2be5289a1162083a4638b513e2143885b0860b4090000650172c65249911c2003b0690c11502483d8620960d80c000064ea72ae52c9a91f21c3bc6d8be1522383905e08e0cc0d000064d252c65309b11c2063bc6c0c314e22c3785d08a0c80d000064bbc2aa500959151fa390648af12e1f03284e0760a409800064a542a04f4931111ec384678b113a2383c05e0940c80f0000648d52d05409c1222243ec718c815a24c3d86509c0d40e0000647722964d4901081dc358618b21361fc3905a0880b00b0000645f92be5189410d1ee380660b81442383c8640980c80d00006449f2904cc8f10b1de36c638b112e20c3585007e0a4078000643312b0510929111f2384658b213a210360590860b00a8000641c12a44e89010c1ec380620ae1302083505c07a0ac0a00006404b2c0520971171fa39c6b0bc148224398580900cc0d000063ee72a2504921141e837c640ae1342083705407e0b00b000063d732be510971121fa3a0660b913c214378590840b00b800063c002ba4f89290c1f63a86a0ba13c2203905e0900b409000063a8b2b44ec919111fa38c658b51402103805b08e0d0098000639122c65449891d20a3a4698bc14a2343e05f08e09c0b0000637962ca54c9a11d2063c06e8c71502403c0620900c40a80006360f2de558a21292223dc6e0c11562543f0660960c40c00006349d2bc524991172003ac680b613c2343b8610900b00b8000633282ce518991182043ac680ba1442283905e0840a40d000 else (if i < 18 then 0x6e9c72984dc8e1081ea370620b21382183685b0880b00980006e8592ae4ec959111f2380650b412e2143985808209c0800006e6fd28e4c88d1051e4364640b01362183905a0900c00b80006e5772d45489d12b2123cc6e0c51522543e8630a00e00b80006e40b2a6500941141f8380638b313a2183785707a0ac0b80006e28f2cc52c9811420238c690ba1482343c8600900b00c00006e1222ae50c949111f6388658af136218380560760a40b00006dfbd29e4f08f1081de374618a91341e4300510780a80a00006de472b450c9811b20c3b06b8bd14a2483e0630940d40f00006dccc2c65289911a1f83a4668b212e20c350550820a40a00006db572b25149911a200394668b513e220398570860b40c80006d9e82b450c961131f4388658bb1482243885808c0bc0980006d8782b04f0941112003ac6a8bc1542583e8680a00e40e00006d7032b6520939111ee37c618af12e200370550860b40a80006d59e28c4b88d90a1e8374620a611e1f43585908a0a40980006d4262b851c9991a2063a46a8bb1462103605a0900cc0e80006d2bb2aa4f49110c1ec378620b3132214390590820a80900006d15429e4e08c9001d23445f0ac12c204348560800b80a80006cfdb2c251894915202398650b612c1f8350530800ac0a80006ce692b24fc979171f638c658ba1442243a05d0960cc0c00006ccfb2aa50c9611a2043bc6b0ba1442203785307e0a00a80006cb8c2c25149891b20c3a0650b71402283a05d0860a00880006ca282a24d48f10a1d836c640af13e2203885c0900c00a00006c8a32da5449b91f20c3c46c0ba14a2383a85a0900ac0a00006c7362ac4f89310f1ea38c658b41342243905b0920c00d00006c5ca2b85009490f1f236c630b112a1f83605a08a0b80a80006c4562ba5309991d20a39c680bc14a238380590800ac0c00006c2e62b45149691a2043bc6c8bd1482343b05c0920d00c80006c1892904d08f90a1e8374640b5130200350520800a80a00006c0192ae500949131fe39c670b51422203805607c0900800006beaf2a64f49310e1e836c628b11281e43205207609c0a00006bd322c6518991192043b4688bb14a2383a85b08a0c00d00006bbbe2ac4f49110a1ec380668b31382103885c08e0c00b80006ba4e2ba514951141f838c6a0ba14a2303a05d0860ac0a00006b8e82a24d89110b1e435c630b11382203905a0820b00b80006b78b2924d08e1081e8370608b0136218378580800a40900006b6102cc5249c92220a3c86c8c21542403d0640880bc0d80006b4a22b850c971141fa3a86a8bd14a2303d85a0900c00c00006b33c2984dc8f1061e4364610ae12e2003705407c0b80c80006b1cf2a24e0939121f2370648b0136218378520840b40980006b05c2b04f89190b1ec388650b51322103505708c0b80d00006aedf2d053c9a11a2043a8678b914c2443b8600980cc0e80006ad752a64f8931131f8394670b813e234370570800a80900006ac1628e4dc931111f238c670b914022c3885b08e0c00e80006aaac2ae4dc9210e1ee370638af12c214370580840c40f80006a9512944d08f9021d83705f8ab1221f4348530700ac0800006a7e42ae4f4939122083c46b8bd1542443c8600920c80c00006a68128c4d08d1061d435c600ac12e2043785c07c0b00d00006a5092ce53c9891a20a3a4688bb1482303c8630940c00e00006a3952b85209b91c20e3cc6e0c71582583f0610900bc0b00006a2342a4510961121f83a8690bb14c2403b05d08e0c00b00006a0ce2984d09010b1f238c690bc14c23c3785908a0bc0d000069f6429e4e0911051e8388688bb1422303905f0920cc0d800069dea2be51c959192023b8698bc14622c3b85d08c0b00c800069c742c0514951141f6390698be1522203a06008c0ac0b800069b032b6504949121f8384670b312e1f0320540800b00b0000699a12944e0919121ee388648af12c1fc348540840b40c8000698232da54c9d1272183c8708c815e2704086609a0e00e0000696a02d8564a012621a3dc718c715c2503b86409c0c40c00006952b2c05089590c1f2384650b51402403905b0840a40b8000693bc2b450c981161fe398668b313e2203885c0800c00b8000692312e65689f1262243e8708c91502483a05f0900b80b8000690cc2a64f49310e1f6388668b7138210360590940dc0d800068f542c05209691a2063ac6a8b813e2243885b0840a40b800 else 0x7458129e4dc8f90d1e4368630af1322143985c08c0bc0b0000744082bc52c971122003c4698bf14e2303a0570840ac0b80007429c2b2500949172023a0690bd1482283a85e0900b4098000741362964cc9010b1ea370650af1382243905a08c0b40b800073fd62a24dc8f1051e03605f0ac13221c3505708a0a40c800073e5e2c0518949181f238c670b414a23c3b05908a0bc0d000073cf02b85149811d20a3a06b8bf1542544086b0a60c40b000073b852ae4f09090a1ee380640b11342003104c0740940b800073a192ae510969182063c46c8be1582643f86609c0c40b80007388e2e05609f9222143cc718c715e270400690980d00b0000737272a44fc931121f4390680bb1482303b85b0940cc0c0000735b62bc5249a1202183c06b0b714823c3a85908c0c00e00007343b2c4524989171fc390670b614c24c3b8660900c80d0000732df28c4c48c9031d6370618af132214348530880bc0a0000731632d05409a91e2183dc6e8c9164270420660a20ec0e8000730022944c08e1051dc368630ae13221c3785607e0a40a800072e912b0504931121fa3a4698b91382143805a0880b80a800072d232ac4f49090a1e436c678ba14a22c3a8630940c80b800072bbb2a44f8939141f439c688bb1502543f8670960d80d800072a492bc5089911c2123d06d0bf14823c3d8600940d00d8000728dc2ac500951172023ac678bc15a2403d0610920b80c8000727632c85149811920a3a4690ba14223c3d0670920d00c8000725f62ba514989152003a8690b914223c3a85d07e0ac0a00007248a2b45109611a20c3a86c0c01542483e86709a0bc0d80007230b2d25449d9272163d06f0c415e2483a05f08e0bc0a00007218e2ce5349a11d20e3cc6f0c11542543e86409c0cc0c00007201f2b24fc919101e8380658b21362103405007a0900a800071eb22a6508941172063ac678b614e23c3e06108c0cc0b000071d3c2b64ec911121f2394698b71402303a8610960c40d000071bd12b44fc931171fe3a0690bb1482303d05d0900bc0c800071a5e2b45209811820a3b06b0c01542483d8600920b80d0000718f92984d89110b1f4394690b814e2503d06208c0c80f0000717862bc528951131f238c658b413c228390580900c80f0000716172b04fc949141f43a4658b01342083384f072098098000714a32bc508959131f8394690b413e2243785a0900cc0d0000713202ca52c9a9222203dc6f0c81622583d0660960d80d0000711c12904d89190c1e836c628b413e2143405306e098088000710652864cc8e10f1f038c648b413a204388590840ac0b800070ef92ac5049610f1f0388640b31362303b85c08c0b80c800070d8d2a64fc9590e1ee384640b313a208370580880b80c000070c1d2b2500949141fc3b46b0bc14823c3c06008c0c80b000070abe2924cc9010b1ea388670b313a2243885707c09c0a8000709462c05409d9262203d86f8c215023c3c85d0920b40b8000707ce2be5349a918204398688b913e2303e86008a0c00d0000706542be5309c1222123dc6d8c61522483e0620980dc0f0000704f02a84dc8f9091da36c630b313e210388540800a40d0000703872a4500951121f8394670b7142218380580860b0088000702192a24ec9190c1f0380620af13021c360540860bc0b8000700a32b45089811d20a3cc6b8b814623c3c0610920b40b00006ff3a2a44d08f1031d235c620ae1342083785908209c0980006fdbe2ba528969181fe38c640b513a2243905e08e0b40a00006fc3b2da5489e12620c3c46e8c315825c3f05e08a0c40c00006fad02b0504951161fc39c678b7144224368580880a00a80006f95a2ba5209a9171f4398688b713e2203885e08e0c80b80006f7e42c65289591920038c668b61462243905b0860b00b00006f68429a4d89090c1e036c640b113e214370590880cc0c00006f51e2a04dc919111ec384628b0134220378570840a80a80006f3b12ac50c951121f2384618b013220c3705507c09c0b00006f23c2ba518971131fe39c678b61402283a85d0940c00c00006f0d12ac4fc949111f438c670b513620c3605207c0a40900006ef6e2a44e8921111ec378660b813a214370590800a40d80006ee0a2a04bc8e9031dc360618b313621c3b05f09c0c40d80006ec972b2510989152023a0698bf14623c3b06209a0d00d80006eb242ba514949111f0394688bd14a2283b0580880cc0e000))) else (if i < 22 then (if i < 20 then 0x7a0b42964d08e1071e4384660b41442203685708209c09000079f402ac4f09110f1ea380648b9142220398600900d40e000079dd02a64ec949121f639c690c014622c3a85f08e0bc0c000079c5e2ac4f49510f1f6398670b51362103585407e0a409000079af02b050c9510c1e437c660b1136218370590820a4088000799942924e09310f1e835c620af1322143585607809c0980007982c2ac4f89711b2043c06b8b914021c3805a08c0b00a8000796c32a44fc949101f4398670bb1522383b05d08c0bc0b8000795592b0500959121fa384640b113a20c3785a08a0c4100000793db2cc5449b91f2123cc708ce17027c4386909a0c40c00007928a276484860f61bc3345c8a51181e0320500760880680007910f2c052098119200394680ba14824c3a05e0940d40c800078fb32904cc8b9021da35c5f0ab12e208378590860b80b800078e452ae5149510f1f6374648b01342203a85f0880c80c800078cca2be5249791b2043b46b0bf14c22c380570800b008800078b6429e4d88e9091ec384658af13620c3505006e098098000789f42ae500979142023a86b0bd1462343b0630920c00b0000788822be514961172043a0660b713e220388560860b40a0000787142b45109811d206398680be14623c3b8600900cc0c8000785a32ae500951131f438c680b4132200328550800b40c0000784392a64f8941151fa394690be14c22c3985a0860c40d8000782cb2ac5149891e2083a8668b714a23c3b85f08a0b00c0000781572b65189991d20a3a4688b714a2383a8610900c00c000077fec2a04f49290b1ec388678b412e200370570820b00d000077e832a24e08f9091de358620a91321f03305a0860b80e800077d172a24f0931162063b46a0bb1442343d06108c0c00a800077bad2ac4f89210b1e8370630af13021c3a8590800a408000077a3f2ac4f49310f1f4380658b81422303b8590880b00d0000778d62a24e08f90b1ee374640b012e2243705b07e0a0090000777642be5209711c2083a8668b91482443a85f0940d8100000775f02be51095113200398690bc1482383885a08a0b40a00007748d29e4f4941141fc3a0660b31362083585407409c0980007731b2b04f0969141fe388668ba14e230388580820a00a0000771a92c25309a91f20c3a86a0bd14c2503d06008e0c80c80007705b2824bc9110d1f0380640b21281fc3505507e0b40c000076ee52b6504961131f63b0668b413c2303b85d0860a80b000076d812a04cc8e1041d43585f0a31281fc3505307a0980b000076c102ae5009190c1ec380650ae12c1f83485307c0a00b800076a9f2ae508969171fc390678b413a2183985a0780940a00007692d2b2508949121f63a4670bb1442483c0670a00c80b0000767ca2a44d08e1061d63405a8a31281fc3485507e0a8090000766562b65089390f1ea388668b01382283a05d0820ac0a00007650b26e47c870fc1c23385b8a51261ec330500780a40a00007639b2b4500929121f2384650b213820435856080098080000762312a4500979131fc3c46b8c415c2584106509c0d00f0000760d029e4e09090c1f0380660b613e22c3905808009c09000075f552c652c9991a2083bc6f8c515e2543e06409a0cc0f000075dd72d85509e9192083a06b0bf14a2383905c0920bc0b000075c7828c4c88f9081e8384638ab12e20c388610900b80a800075afa2d052c999141f8398678b71442303c85d08c0c40f0000759942a24e09290c1ec374658b112c20c358580860c40c00007581f2b251c9911520039c658bc1382283a85f08a0b00a8000756ab2bc510971161fa38c648b41262003585a0820b80a80007555627e4b08c1031da3405e0a51181ec3204a0740880a8000753ed2a24f49290f1f8398670b613a2283a05f08e0c80a8000752852ae4f09410a1ea378650b113c220398590880ac080000751072d253c9a9252143e86f0c51542403d06408e0c80c800074f972b2510969152043ac6a0bc1442183585707e0a407800074e1d2be508951191fe3a0698be14822c3c85e08a0a809800074c9d2ce5489f1262103d06c8c415a2704186709a0b009000074b312ae4f8929121f2380640b614022c3985807e0a80a8000749b22d25589d91e2123d86e8c615624c3b8610920b40a8000748552884d08d9011dc37c630ad12c1f4338550880b4098000746ed2a64d89110e1ee36c638ae12a1f83505207c0a00b000 else (if i < 21 then 0x7fb882944c48c9001d8354608ac11c1f0338540800b80d80007fa2329a4c88b1031da360608b212e2043685908a0b00a80007f8c52864b88c1051d2354620a912a1fc3385507e0b40880007f74b2c4520979181fa394690c11522403d05e0980ac0d00007f5de2a84f4941121f237c650ae138224378540820b40d00007f4702b250c9210a1ea36c620b013420c3685a0720900880007f31028e4cc8f10b1ec374638b113a2203885c08c0b40800007f1a42ae4fc939101ec388660b41422283985a08c0bc0c00007f02a2bc5289a11e20e3bc6b8bd14c2343d06409a0c40d80007eebe2b4504971171fa398670b214a230360580860a00700007ed522a850c941131e6370618b01362103605a08a0c00b00007ebee29e4e8901091dc374648b314422c3a06008c0b80b00007ea7e2a84fc9210e1ee374648b213c21c3605a0800ac0b00007e9152a24dc9010a1e8370638af1382003805c0860b80c00007e7a92aa4f8929101ee374618ae126204368530880c40d00007e63d2a44f09190e1e636c640ae1321f8360580820b00a80007e4c52bc524969151f6394680b913c2183685e09a0d00c80007e35f29c4d49190d1e8374610ac13020c3705707a09c0a00007e1fd2944dc909081e4380648ad12c2083184f0740b40c80007e0882c05309d9232123b46b8c41622603f06709e0d00c80007df172b850c951101ec360608a91161e4320500720a00900007ddbb2884c48d9041de35c618af1221e03104c0720880800007dc552984d8909131f838c650b41482183705b0800b00a00007dad42ca52c9b1222063b86d0be14e2343a0590840ac0c00007d9622bc50c949121fc398680b813c22c3985c0840a40a80007d7e82c05249691720a3b0690bb14e23c3785407e0a80980007d6712c05209911d20a3b46a8c01562543a8580800a40980007d50e2a04e89190e1e6384620af1322183b85e0900c80c80007d3ad2984d08f1071ee360628b012a200348530760a80980007d23c2be5149791b2043cc718ca16826c4186d0a20d80b80007d0ec2744a08a0fc1ca3585f8a81181f83505708a0ac0a00007cf7f2aa4e492114200398650bc1402143605e08e0b80b80007ce0f2ac4ec9290d1f6384658b51402283b06208c0c00b80007cc992b8508971182043b8698bb1442343b05e0860b40c00007cb1e2c85289811f20e3d06f0c11622683e8670920c40d00007c9ba2924d88e9051f0388668b3136204378510800a40b00007c8382d05449c12721c3e46f0c61622503e85d09c0b80a80007c6e82764a4890ff1d8358620b1136204338550800a80a00007c57a2b0504969111f8380670ba1482383f8690b00e00f00007c40c2b4508959131f83986a0bb13a20c360520880bc0b00007c2b02924d8921131fc380648b012e2003705b0980cc0d80007c14a2984d88f1011d436c620ac1281e83385507209c0a00007bfe129a4d48d1031d435c5f0a511e1ec3185207e0b80c00007be852904b48b9041ee368610b2136210360540800c00a00007bd112b64fc959151f6398678b71442343a85c08e0bc0a00007bba32ae504949181fc3a0698ba14823c3a05f0960d40d00007ba2f2b851c9510e1ea3605f8ab11e1e83284f0740ac0980007b8ce28e4cc8d1051d83505f0a31221f03484f07c0a40980007b77128c4bc8c9011ce334598a212a208378530800a80a00007b60b2964d49010c1ec374658b212e200360560860b40b80007b49d2c2514969171fc3a06a8c01562483e0620a20c00c80007b3242c65109811b20c3b06a0c114c21c3a85f0860a80b80007b1c02904cc8d1041e0364608a81201d8318510740900b80007b04d2ae4fc941121f2398678b813e22c3b85f0820ac0b00007aed82ae518989192043a0678bd15e25c3e0600900b40a80007ad6b2b2510969141fc3bc680b91522583d86108c0c00f80007abfb2b450c989192043bc6e0c71522503c85c0900ac0b00007aa932964d08e10a1ec378638ae130204350540880a00d00007a92f2944c88c9051dc370640b213a2143a0580820c00d80007a7c32aa4f89310e1ee380660b313a2203985c08e0b00900007a66528e4bc8b9001d635c608a812c2083605608e0b00900007a5092824b48a8fc1be3205c8a71241f83585707e0ac0b80007a3942ba520971131ee388648b31402383685608a0b80c00007a20f2d45549c1242203e46f0c715c2703f86609a0c80c000 else 0x855ed2aa4f08f1021e237c648b013220c360560780940a0000854832a64f49190d1f2398678b71402383a8620940b80b8000853242984e09210f1f23ac688bb1402183985b0920b00c0000851cb28a4d08f1061ec378668b81482383b05c0820ac0b0000850682904b88f1091ec368610a612a1e83305107e0ac0a800084f062964d48e90c1ea380640b0134204368570800b40d000084d9f2aa4f8949131fc3b0698bd14a2383d86508e0c00a800084c402924c08e10a1f2378610ad13621c3885408009809000084acc2bc520961141f638c648b31342183785e08e0bc0c8000849482e0558a012821c3ac6a0b81482443c8640a00cc090000847ed2804a48a9001d03545f8a912c2043485707c0b00c8000846782c0528981171fa390668b013a2203a0580840a40980008450e2984c08c8fe1d23545e8ae1342183785707e0a40c0000843b12884b88d1031d8364620ae134208338570860c00b80008424a2ac4f09290f1f03a0688b81442343905b0800a4098000840dc2ae4fc959151f637c660b21362183705c0860c40c000083f7a2964d89290b1ec37c648b11362143805a0860bc0c800083e122a24f8941141fe3a46b8be14a2203885f0880b40b000083cab2a24f49210f1ee390648af13621c3805b0820c80f800083b422a24e49190e200388690bb14c2203785808e0bc0b8000839e82904c48b9001c834c608ad1281f43104c0720a40b00008386c2d45389d1262163d06b0c41562503d86609e0d80d80008370829c4c49110b1ec374650b713c2183a06008c0b80d8000835912c4528999161fe3b8688ba1482383d8620920b40c00008342c2a04e4921101ec378608b012e208360570820ac0b8000832c52a84ec9310d1f238c680b313820c3585807a0a80c8000831602844b88c1001ce35c608ab1241f0338560820a0088000830032924e08e10a1e2364628b213e224390510860b40b800082e842d054c9e1252183c86d0c516425c3c06309c0d40f000082d1b2b04fc959121f239c698b914222c380580900c40c800082bb429e4e4949121fa39c690ba13c22c3b86008409809800082a442a6504979161fc3a0690bb1482383d86008c0ac0b0000828dd29e4e8939181f437c648b3142214370570840c40c80008277a2a24e09090e1f0390668b01322103805f08a0c80c00008260b2b04fc941121f038c678ba14422c3c0630980c00b80008249b2ae50c9390f1e6378610a912c1f03084b0700a40c00008234428a4b88d9021de36c638b113220c348520780a0088000821d72ae4e8959111fa388650b414c2383b06408a0b80b80008206e2a24ec9390e1e8388680b41301f83305107608809000081efa2b450c9791a20c3a8688b41442243905e08a0c80b000081d862ae5049490c1ec36c650b314021c3a86008e0d40e000081c122bc504971182063a0678b414821c3985c08e0c009800081ab02924e09410f1ee36c658b51442383d0620880b40a0000819402ae500959101ee37c670b714a2103685c0900a80a8000817d02be5389a91b20c3a8688bd14c2403d8680940c80c0000816652b05009511a20e3b86d8c51602443d06008c0d80e0000814eb2c6530989182043ac6a0bb13c2183785908c0c00d80008136e2bc5289a1182003a0698c01502443a85f0860b00b0000812092a04e0931152043a4658b61462283e0600860cc0d0000810ad2904c49110b1f2388648ba1482403b05f0880a80a800080f472964c08c9061de35c600ad1222043685708a0c00c800080dd32bc514999222083bc6e8c414a228368550840a00b000080c5f2c0500939151fe398698b91482303c85f0940d80c800080af529c4d48d9081e238c670b613821c3685a08a0ac0a00008097d2b25049811c2063b0690bd1422383a0600980c00c00008081c2904d09010d1ea388660b21362143605a0840bc0c0000806cc27c4a08a9031da368640aa12c228388590880ac0b8000805602a64f49510c1e2368600aa1281f43004b0700a0088000803e22dc554a11292223cc6e8bf14a2443b86108e0c40b80008028d2764a08a1051dc358610aa12e1f8330530800a80b00008011c2b04e4901101f8388660b61362083705707c0b40d80007ffbb29e4e4911071da364638b5132208350550820c00b80007fe422ba5049290f1f638c678b914a23c3c85d08a0ac0a00007fceb2864c88d8ff1de378630ae130204358520800a808800)) else (if i < 24 then (if i < 23 then 0x8b0352b0500951151fa390690c114e2303b8610940c00a80008aed82864b88c9001d6364620ac12a1ec3285107009c0800008ad722a04f89390e1f0390640b113c2243b85f0940d00e00008ac092a8504939121fa39c690b5146218368580860b40c00008aa972b0510959171f6388670b813c220370580840b00a00008a93329e4d49390f1f2370608a712820c3484d0780b00a00008a7e427e498878fa1ce3445e8ab12c1f4338560800a40b00008a67b2a44f09210b1e8374628ae1261f0360590880bc0e00008a5172964c88b1031e436c638b21302203985a0860b00a80008a3b92924d48e1091e839c690b613c2243a85e0800ac0700008a25129c4e4929151ee38c678b41262003785e0920c00e00008a0e22a64f4941131f6394650b513421c3785507c09c08800089f7f29a4d88f9081da36c5d8a31201f43505107209807800089e122b05189a11920e3b86b8ba13c2203a05d08e0ac0c000089cb029a4ec8f9081e837c648b413c220388530780a40b000089b4b29c4dc9090b1e4370618aa12a1f4328560800a8080000899d82b851c941131ee390638b71362143805607009c090000898642bc518969142063b86a0b713e20c3605708e0b80e00008970429a4c08d1021e0374610ab130208360560840c40d0000895982a64f09210e1e838c650b813e2183705b0820b80c0000894452824ac8b1021d6368620b013c2183b05a08e0b0090000892e328e4d48f1071de378648b113e20c3685808a0c00d8000891652c652c9791b2123d06e0c71582483e0650a20e00c000088fef2c05309811a20e3bc6d0c81582543f0620900ac0b000088e852a84f8901111f839c648b214421c3885a08c0a00a000088d272884c88e9051e235c5f0a912a1f8350550880b80c800088bc029a4d88e1081de368628b01321fc3505a08e0b80b000088a522ac4f8919112003ac698c01582503b05c0860940a8000888e92a64fc931132003a0670bb14a2303a8610960c8098000887812a24e88e9051e6368630af1262003605a0880c40c00008860c2be5289811b2083c46d0c014e2443e06509e0d00d0000884a72a84e4931121f4388678b814822c3a85c0840b00b0000883492924c88e1071e237c648af1361ec3284f07c0980b0000881d92b050c9811b20e3dc710cc1662644006308c0b40a80008806a2ac4f0949131fa390650b313821c388550800b00b800087efc2a8500949191fe39c668b813a20c3905e0840ac0a800087d8f2b050895915204390638ad12e2143805a0860b80a800087c372864a48c1021e2354620af12a1e83305007a0ac0a000087ad329a4f09190b1dc3645f8ac1342183705507e0ac0b80008796d29c4e09210b1ec398678b61402243885d0860ac0a8000878062964e8921141fa3a46a0bc1522483c06108e0bc0c0000876932bc510971131f6394660b71382043685d0900cc0d00008751f2ba5209711b2083c06e0c514e2443b85b08a0d00d0000873b32ae4f8961162063ac6b8c214e2203685707e0a80a00008725529e4d08f1061ec388648b21322103485507e0a0098000870ed2a44fc941131fe3ac678b41382203a05d0960c40b000086f7c2b25049391320238c678bb14222c3785c0860940c800086e062c45249791320238c658b21362103785908c0ac0a000086c972a84e8911131fc3a8698b11342083885c0900d80e800086b3a28e4c08d1041d6354618ac1281e8338530760a80a8000869d32a44fc9410d1de378638ae1302103885707c0b00b8000868502de56ca112221a3d06e8c71522503d86609c0d80d8000866ec2a64f8919071dc3685f0b013a2143585407e0a40b8000865942924d88d1031d035c5f8a71201e83384b06a08c088000864172c45289b9222143c86d0c315425c3f0680a20d80f0000862b02a44f8949171f6390678ba14c2383c8640940b40c8000861392c2520999182023a8690bc1462283b06409e0c40c800085fd029e4c48c9031d83545f0a71281f83385608c0bc0d000085e6b29c4d08f10d1f2370648b11322083805707e0bc0a800085d112844b88d90d1ea388650b2140220360560880a80b000085bb828e4b48f1041d03505c8a5128214360560860c80d000085a2a2e4578a492922c3f0728c81502383b85d0920d80d8000858ba2b6524959192063ac6b0c11542483d0660960dc0d80008575329c4d8929111f839c668bd14a2443a05b0880bc0a800 else 0x90ac22984d48e90b1ea37c620b112e208350550840c40b8000909602a24ec9290b1e8384630b013c2303b0590820b00a8000908082824ac899011d8368628b113020c3485807a09c088000906882d455ca092a2203f4750d3172270418670960d00d8000905352824b0880fa1c63485c8a91201d43084c076090070000903ba2c653c9c91e20c3bc6c0c81642744106409a0d4100000902622964d49090e1f838c680b713a2203885a0880ac080000900fc2b2500939142083c06c8bb14622c3905d08c0bc0c80008ff9e2984f8919071d8374630b512e2183685c0860a40900008fe432844ac8b1001e03585d8a31141e43204f07008c0a00008fcd22b45189911c20e3a8698ba14a24c3d0680a40d00d80008fb582ce538981171fe3a0680b5138220350520880ac0c00008f9f92a24e4959161f239c678b41482243c86008a0c80b00008f88c2ae514959151fe3cc6c0c014a2443c85f08a0ac0c00008f71f2ae4fc969181fc3a4690ba144220388570880ac0c00008f59d2d25409b9212123b8698bc1542583d0630940b80c80008f44128e4e49390f1ec378670b61442303a05a08809c0980008f2e32924c48c9021ce3505e0a71202083685a0840b00d00008f17829e4e8941111f4398678b813c210360580840b80b80008f01d2864b0898fd1d43445e8af13a210380590840b40b80008eeac2a84ec909081ec378638b41302043685e08a0c40c00008ed412a84f89210a1ea36c618b213a218390570860b40c00008ebcd2b0508971181fc39c688b11402343b06008c0ac0c80008ea572c85289891b2023b06c8bd142224398590800b00b80008e8f32ae4fc961131fe39c690b71402283805507c0a80b80008e7862ae510969151fe394678ba1482243a85c08a0c00d00008e61d2ac5009390c1ee390668b51482303b0600940c40b00008e4b32a64e4921101f0390668b414422c3885f0820b80e80008e3392c45189891b2103b06a0b71402343985f0900b40a00008e1e826c4988a0ff1cc3505c8a812a1f43404c0720900880008e08429a4ec959151f4384660bb13c2203985b0880c40b00008df2c2804a8870f61cc3485c89f1161d42e84c0720940780008ddb82be524969131f6380638ad1302043805507c0b00b80008dc382e05609d91b2083c06d8c41562403e0600900c80b80008dacf2a04f4901081e235c5f0a61281f83585707a0a00900008d9792844b08b1021de360620a9132224380570820b00a00008d7fe2c65309711d1fe3ac6b0be1462283a85e08e0c40c00008d6a72784a0890fe1ce3345c8a711e1dc3485207a0bc0a80008d53b2aa4f0901081e6384630b513a2103a85f0880b40d80008d3db2984d08b9041d8354610ad1342083585707409c0b00008d2682b2504941151fc39c668b813a2303b85908e0dc0e00008d0f52be5309711a1f638c668b2140220368530840a00900008cf8d2a44f09290e1f037c628b31362143685708009c0880008ce1f2ac4ec9311420639c6a0b5138210378570840ac0b80008ccb52ac5149310e1fa3ac680bb1442243985d08a0b80a80008cb5d28a4bc8d9071d234c5f8ab12e200348510800ac0b00008c9e72be51c981171f8394668ba14c2343c06108c0d00e00008c8642ca5389d1272163d86e8ca1522403f86609e0d40d80008c6fb2a84f09510e1ec374618aa11e1fc3605307c0980900008c59f28a4cc8d9061ea370610a812c20c3705507c0a40b80008c43a2a44dc9010c1ea380628b31462283b0650960d80c80008c2c12ba518969101f6380628a91261f8360590980d40d80008c15d2a04f89490a1ee388660b514c23c3b85d0880b40a80008bff22b2518969131ec378648b61382083605a0880b40b80008be832b451898119204398660b41402183985a08a0b00980008bd1b2a44f4941162003b06d0c214e2343b8600940b80d80008bba92aa508969101ee380640b21302103705808409c0a80008ba3e2a64e0911111e8374610ad12e2003585c08c0c00c00008b8c32cc5289b11c2043b06a8bc15a24c3d8630960c40b80008b75f2a44e8951121fa380640b61342283c05d0860a00980008b5fc2924e48e9081da36c658b61402103605b0840ac0a80008b4862be5249891a206398688bc14c2243b0630900c80c00008b3212a04dc8f1081ee390670b914222c3c0600920b80a80008b1a72c251c961151fa3ac6a8c215224c3b85c0860b00c000) else (if i < 25 then 0x964712ba5249d91d20a3c86c8c01482403a05d0900c80b0000963082a64f8949101f63a0680bb1442143785608a0b80d0000961b527c4ac8c9051e8368638b113a20c3785907c0b40c0000960462a2500961131f8394658b412c1f4350530800ac09000095edd2a04e49010a1e6378640b8142224350550780b00f000095d732a44f09210d1e6370628ae132208358540760bc0c000095bf72c25349e92521c3cc6c8bf1502443e0650940d40d800095a9a2924d88d1041e2370610ae1302043285408a0d00d8000959242c050c9811b2083b86d0c91562503d85c08a0bc0d8000957c62964d49090c1f2390658b614222c3805b0900c00a00009567127a4a0880fe1d434c5f8a612c1e8340560820b80c0000955112904bc8c8ff1ca35c5e0a51161d8340510860a40b00009539d2b45189711a2083ac6a8bb13c2103885d0900cc0c0000952212d65409b91e20a3b86e0c01502383d86108c0bc0d0000950b929c4ec939121f4384658b313a2043705907e0a80a800094f562a44f0919101ee36c640b213621c378540720bc0b800094df52924d09110d1f638c678b814622c3885607c0a40b000094c992824a4898fb1d034c628ad12c2003584c07a0b00c000094b4228e4c88d1051d234c620ac1322103485b08c0c00d0000949d02be5109791b2103c06c0bf1502383b0620900b80c00009486a2964e48c9011d435c620ae12821c3985a0860b00b8000947062924c08e90a1e4374648b613c21c3985c08a0c40c0000945932b84f8961131fe390650ad1322243905908a0c00c8000944262b24ec8f9041da3545f0ac12c1f4360580800b40a8000942c428a4a8899011d635c600b01322083605507c0980900009414f2bc514981141fe3a46b8bd14623c3c05f08c0bc0c800093fe82ac5109610f1f83a4670b51422303b05d08e0c00d800093e852a44e8901051e2384650b71362243c05a08a0c40b000093d3127a4ac880fe1cc3345a89d11e1f8358570820b40a800093bc12b45289b11e20e3ac6b0c014a2303885708a0a80a000093a532a64f0959142063bc690bb1402303b8610980dc0e8000938f62944c89110c1e6388660b713e20c360560880b40b80009379728c4c48a1031d83505e0a311e1f03405107c0ac0b0000936302a64e4929111f63a0678b21362103a05e08e0c00d0000934ca2a04c48e9041da3605f0ab1202003705a0860a80880009336f2844b48a9021d8350600a61261dc330530780a40b0000932142984dc8d0fe1c83445e0aa12e2003405007808c098000930c427a4ac8c1051e4360638b21362043585507609809000092f4a2c2524991172003a4680be14c2383985c0840ac0c800092ddb2b051c9991e2003b86c8bd1522503d05f0880b40d000092c692b2514979141fe3a8688b91482243705a0820a40a000092b032a24dc8f90e1ea390688b81442183605707e0ac0a8000929a728e4c48c9031e636c610ab12e1ec3284f07c0a0090000928362b2514971181fc39c6a0bf14e24c3a85a07e0ac0a0000926eb2784a48a0fc1c833c5a8a011a1e43085307a0a00b00009257c2b250c949132023b46a0be1502443d8620960b80d00009241329c4e09190e1fc39c6a0bc1442183b05f08e0bc0b0000922b32904d49010d1e4374638b713a22c3a05c0960c8098000921442b2504971161fc39c678ba144220378580880bc0b000091fdf2924c88c1041e0368650b413e22c3986008c0c80d800091e632d25389c92721c3d06d0c414e2343e86309a0e00f000091cfd2a04e49110f1f83a4678b71382043705a07e0b80b800091b8f2aa508949111ee394680b513e214388540800a40a800091a1a2be500959121f6390668b113a20c3705407609c090000918cb27248c899001cc3445c8a41201ec348500800ac0b80009175a2b250c951111f6390658b91482343b8610900ac0a0000915fb2864b48a8fc1d03445e0a61201f03605a08a0b00b00009148c2a84f0901061e23645d0a71322103905a08c0a80b0000913222ac508979151fe3a86b0bd1542443c05908c0a8098000911ac2c65389c9252223d46e8c114e2443b85f0920cc0d0000910522964c88c9041e035c610ac128200360580840b40c000090eef2a04e89410f1fa394680b513a2183905d0820a00a800090d912964d49110a1f038c688bc1562643e86209c0d810800090c262b450c951111f238c6a0c015024c3d0670a20dc10000 else 0x9675100000000000000000000000000003c0610940b80c8000965e42b4514979161f237c638b5144224378580840ac0b800)))))

private def checkpoint (i : ℕ) : ℕ :=
  let word := (packet (i/1024) >>> (200*((i%1024)/16))) % (2^200)
  (word >>> 176) + ((word >>> (11*(i%16))) % 2048)

private def raw (j : ℕ) : ℕ := fromBlocks checkpoint (fun r => quick (number r)) j

private def small (n : ℕ) : ℕ := if 5≤n then 3 else if 3≤n then 2 else if 2≤n then 1 else 0


def fast (n : ℕ) : ℕ := raw (index n) + small n

private def step (i : ℕ) := checkpoint (i+1) == checkpoint i + tally (fun r => quick (number r)) (96*i) 96

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

private theorem batch0 : covered 0 50 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch50 : covered 50 100 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch100 : covered 100 150 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch150 : covered 150 200 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch200 : covered 200 250 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch250 : covered 250 300 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch300 : covered 300 350 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch350 : covered 350 400 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch400 : covered 400 450 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch450 : covered 450 500 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch500 : covered 500 550 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch550 : covered 550 600 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch600 : covered 600 650 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch650 : covered 650 700 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch700 : covered 700 750 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch750 : covered 750 800 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch800 : covered 800 850 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch850 : covered 850 900 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch900 : covered 900 950 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch950 : covered 950 1000 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1000 : covered 1000 1050 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1050 : covered 1050 1100 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1100 : covered 1100 1150 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1150 : covered 1150 1200 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1200 : covered 1200 1250 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1250 : covered 1250 1300 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1300 : covered 1300 1350 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1350 : covered 1350 1400 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1400 : covered 1400 1450 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1450 : covered 1450 1500 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1500 : covered 1500 1550 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1550 : covered 1550 1601 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1601 : covered 1601 1651 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1651 : covered 1651 1701 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1701 : covered 1701 1751 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1751 : covered 1751 1801 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1801 : covered 1801 1851 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1851 : covered 1851 1901 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1901 : covered 1901 1951 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch1951 : covered 1951 2001 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2001 : covered 2001 2051 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2051 : covered 2051 2101 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2101 : covered 2101 2151 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2151 : covered 2151 2201 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2201 : covered 2201 2251 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2251 : covered 2251 2301 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2301 : covered 2301 2351 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2351 : covered 2351 2401 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2401 : covered 2401 2451 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2451 : covered 2451 2501 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2501 : covered 2501 2551 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2551 : covered 2551 2601 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2601 : covered 2601 2651 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2651 : covered 2651 2701 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2701 : covered 2701 2751 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2751 : covered 2751 2801 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2801 : covered 2801 2851 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2851 : covered 2851 2901 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2901 : covered 2901 2951 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch2951 : covered 2951 3001 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3001 : covered 3001 3051 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3051 : covered 3051 3101 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3101 : covered 3101 3151 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3151 : covered 3151 3202 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3202 : covered 3202 3252 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3252 : covered 3252 3302 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3302 : covered 3302 3352 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3352 : covered 3352 3402 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3402 : covered 3402 3452 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3452 : covered 3452 3502 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3502 : covered 3502 3552 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3552 : covered 3552 3602 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3602 : covered 3602 3652 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3652 : covered 3652 3702 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3702 : covered 3702 3752 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3752 : covered 3752 3802 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3802 : covered 3802 3852 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3852 : covered 3852 3902 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3902 : covered 3902 3952 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch3952 : covered 3952 4002 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4002 : covered 4002 4052 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4052 : covered 4052 4102 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4102 : covered 4102 4152 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4152 : covered 4152 4202 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4202 : covered 4202 4252 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4252 : covered 4252 4302 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4302 : covered 4302 4352 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4352 : covered 4352 4402 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4402 : covered 4402 4452 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4452 : covered 4452 4502 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4502 : covered 4502 4552 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4552 : covered 4552 4602 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4602 : covered 4602 4652 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4652 : covered 4652 4702 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4702 : covered 4702 4752 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4752 : covered 4752 4803 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4803 : covered 4803 4853 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4853 : covered 4853 4903 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4903 : covered 4903 4953 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch4953 : covered 4953 5003 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5003 : covered 5003 5053 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5053 : covered 5053 5103 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5103 : covered 5103 5153 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5153 : covered 5153 5203 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5203 : covered 5203 5253 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5253 : covered 5253 5303 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5303 : covered 5303 5353 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5353 : covered 5353 5403 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5403 : covered 5403 5453 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5453 : covered 5453 5503 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5503 : covered 5503 5553 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5553 : covered 5553 5604 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5604 : covered 5604 5654 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5654 : covered 5654 5704 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5704 : covered 5704 5754 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5754 : covered 5754 5804 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5804 : covered 5804 5854 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5854 : covered 5854 5904 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5904 : covered 5904 5954 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch5954 : covered 5954 6004 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6004 : covered 6004 6054 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6054 : covered 6054 6104 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6104 : covered 6104 6154 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6154 : covered 6154 6204 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6204 : covered 6204 6254 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6254 : covered 6254 6304 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6304 : covered 6304 6354 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6354 : covered 6354 6405 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6405 : covered 6405 6455 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6455 : covered 6455 6505 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6505 : covered 6505 6555 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6555 : covered 6555 6605 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6605 : covered 6605 6655 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6655 : covered 6655 6705 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6705 : covered 6705 6755 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6755 : covered 6755 6805 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6805 : covered 6805 6855 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6855 : covered 6855 6905 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6905 : covered 6905 6955 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch6955 : covered 6955 7005 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7005 : covered 7005 7055 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7055 : covered 7055 7105 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7105 : covered 7105 7155 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7155 : covered 7155 7205 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7205 : covered 7205 7255 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7255 : covered 7255 7305 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7305 : covered 7305 7355 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7355 : covered 7355 7405 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7405 : covered 7405 7455 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7455 : covered 7455 7505 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7505 : covered 7505 7555 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7555 : covered 7555 7605 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7605 : covered 7605 7655 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7655 : covered 7655 7705 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7705 : covered 7705 7755 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7755 : covered 7755 7805 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7805 : covered 7805 7855 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7855 : covered 7855 7905 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7905 : covered 7905 7955 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch7955 : covered 7955 8006 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8006 : covered 8006 8056 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8056 : covered 8056 8106 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8106 : covered 8106 8156 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8156 : covered 8156 8206 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8206 : covered 8206 8256 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8256 : covered 8256 8306 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8306 : covered 8306 8356 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8356 : covered 8356 8406 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8406 : covered 8406 8456 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8456 : covered 8456 8506 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8506 : covered 8506 8556 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8556 : covered 8556 8606 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8606 : covered 8606 8656 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8656 : covered 8656 8706 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8706 : covered 8706 8756 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8756 : covered 8756 8806 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8806 : covered 8806 8856 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8856 : covered 8856 8906 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8906 : covered 8906 8956 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch8956 : covered 8956 9006 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9006 : covered 9006 9056 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9056 : covered 9056 9106 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9106 : covered 9106 9156 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9156 : covered 9156 9206 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9206 : covered 9206 9256 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9256 : covered 9256 9306 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9306 : covered 9306 9356 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9356 : covered 9356 9406 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9406 : covered 9406 9456 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9456 : covered 9456 9506 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9506 : covered 9506 9556 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9556 : covered 9556 9607 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9607 : covered 9607 9657 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9657 : covered 9657 9707 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9707 : covered 9707 9757 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9757 : covered 9757 9807 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9807 : covered 9807 9857 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9857 : covered 9857 9907 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9907 : covered 9907 9957 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch9957 : covered 9957 10007 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10007 : covered 10007 10057 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10057 : covered 10057 10107 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10107 : covered 10107 10157 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10157 : covered 10157 10207 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10207 : covered 10207 10257 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10257 : covered 10257 10307 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10307 : covered 10307 10357 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10357 : covered 10357 10407 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10407 : covered 10407 10457 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10457 : covered 10457 10507 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10507 : covered 10507 10557 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10557 : covered 10557 10607 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10607 : covered 10607 10657 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10657 : covered 10657 10707 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10707 : covered 10707 10757 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10757 : covered 10757 10807 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10807 : covered 10807 10857 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10857 : covered 10857 10907 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10907 : covered 10907 10957 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch10957 : covered 10957 11007 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11007 : covered 11007 11057 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11057 : covered 11057 11107 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11107 : covered 11107 11157 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11157 : covered 11157 11208 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11208 : covered 11208 11258 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11258 : covered 11258 11308 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11308 : covered 11308 11358 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11358 : covered 11358 11408 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11408 : covered 11408 11458 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11458 : covered 11458 11508 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11508 : covered 11508 11558 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11558 : covered 11558 11608 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11608 : covered 11608 11658 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11658 : covered 11658 11708 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11708 : covered 11708 11758 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11758 : covered 11758 11808 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11808 : covered 11808 11858 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11858 : covered 11858 11908 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11908 : covered 11908 11958 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch11958 : covered 11958 12009 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12009 : covered 12009 12059 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12059 : covered 12059 12109 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12109 : covered 12109 12159 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12159 : covered 12159 12209 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12209 : covered 12209 12259 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12259 : covered 12259 12309 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12309 : covered 12309 12359 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12359 : covered 12359 12409 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12409 : covered 12409 12459 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12459 : covered 12459 12509 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12509 : covered 12509 12559 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12559 : covered 12559 12609 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12609 : covered 12609 12659 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12659 : covered 12659 12709 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12709 : covered 12709 12759 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12759 : covered 12759 12810 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12810 : covered 12810 12860 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12860 : covered 12860 12910 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12910 : covered 12910 12960 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch12960 : covered 12960 13010 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13010 : covered 13010 13060 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13060 : covered 13060 13110 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13110 : covered 13110 13160 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13160 : covered 13160 13210 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13210 : covered 13210 13260 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13260 : covered 13260 13310 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13310 : covered 13310 13360 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13360 : covered 13360 13410 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13410 : covered 13410 13460 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13460 : covered 13460 13510 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13510 : covered 13510 13560 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13560 : covered 13560 13610 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13610 : covered 13610 13660 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13660 : covered 13660 13710 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13710 : covered 13710 13760 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13760 : covered 13760 13810 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13810 : covered 13810 13860 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13860 : covered 13860 13910 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13910 : covered 13910 13960 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch13960 : covered 13960 14010 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14010 : covered 14010 14060 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14060 : covered 14060 14110 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14110 : covered 14110 14160 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14160 : covered 14160 14210 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14210 : covered 14210 14260 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14260 : covered 14260 14310 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14310 : covered 14310 14360 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14360 : covered 14360 14411 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14411 : covered 14411 14461 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14461 : covered 14461 14511 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14511 : covered 14511 14561 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14561 : covered 14561 14611 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14611 : covered 14611 14661 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14661 : covered 14661 14711 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14711 : covered 14711 14761 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14761 : covered 14761 14811 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14811 : covered 14811 14861 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14861 : covered 14861 14911 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14911 : covered 14911 14961 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch14961 : covered 14961 15011 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15011 : covered 15011 15061 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15061 : covered 15061 15111 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15111 : covered 15111 15161 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15161 : covered 15161 15211 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15211 : covered 15211 15261 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15261 : covered 15261 15311 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15311 : covered 15311 15361 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15361 : covered 15361 15411 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15411 : covered 15411 15461 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15461 : covered 15461 15511 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15511 : covered 15511 15561 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15561 : covered 15561 15611 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15611 : covered 15611 15661 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15661 : covered 15661 15711 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15711 : covered 15711 15761 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15761 : covered 15761 15811 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15811 : covered 15811 15861 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15861 : covered 15861 15911 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15911 : covered 15911 15961 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch15961 : covered 15961 16012 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16012 : covered 16012 16062 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16062 : covered 16062 16112 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16112 : covered 16112 16162 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16162 : covered 16162 16212 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16212 : covered 16212 16262 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16262 : covered 16262 16312 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16312 : covered 16312 16362 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16362 : covered 16362 16412 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16412 : covered 16412 16462 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16462 : covered 16462 16512 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16512 : covered 16512 16562 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16562 : covered 16562 16612 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16612 : covered 16612 16662 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16662 : covered 16662 16712 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16712 : covered 16712 16762 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16762 : covered 16762 16812 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16812 : covered 16812 16862 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16862 : covered 16862 16912 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16912 : covered 16912 16962 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch16962 : covered 16962 17012 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17012 : covered 17012 17062 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17062 : covered 17062 17112 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17112 : covered 17112 17162 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17162 : covered 17162 17212 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17212 : covered 17212 17262 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17262 : covered 17262 17312 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17312 : covered 17312 17362 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17362 : covered 17362 17412 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17412 : covered 17412 17462 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17462 : covered 17462 17512 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17512 : covered 17512 17562 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17562 : covered 17562 17613 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17613 : covered 17613 17663 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17663 : covered 17663 17713 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17713 : covered 17713 17763 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17763 : covered 17763 17813 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17813 : covered 17813 17863 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17863 : covered 17863 17913 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17913 : covered 17913 17963 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch17963 : covered 17963 18013 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18013 : covered 18013 18063 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18063 : covered 18063 18113 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18113 : covered 18113 18163 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18163 : covered 18163 18213 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18213 : covered 18213 18263 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18263 : covered 18263 18313 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18313 : covered 18313 18363 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18363 : covered 18363 18414 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18414 : covered 18414 18464 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18464 : covered 18464 18514 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18514 : covered 18514 18564 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18564 : covered 18564 18614 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18614 : covered 18614 18664 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18664 : covered 18664 18714 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18714 : covered 18714 18764 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18764 : covered 18764 18814 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18814 : covered 18814 18864 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18864 : covered 18864 18914 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18914 : covered 18914 18964 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch18964 : covered 18964 19014 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19014 : covered 19014 19064 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19064 : covered 19064 19114 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19114 : covered 19114 19164 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19164 : covered 19164 19215 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19215 : covered 19215 19265 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19265 : covered 19265 19315 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19315 : covered 19315 19365 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19365 : covered 19365 19415 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19415 : covered 19415 19465 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19465 : covered 19465 19515 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19515 : covered 19515 19565 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19565 : covered 19565 19615 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19615 : covered 19615 19665 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19665 : covered 19665 19715 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19715 : covered 19715 19765 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19765 : covered 19765 19815 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19815 : covered 19815 19865 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19865 : covered 19865 19915 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19915 : covered 19915 19965 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch19965 : covered 19965 20015 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20015 : covered 20015 20065 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20065 : covered 20065 20115 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20115 : covered 20115 20165 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20165 : covered 20165 20215 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20215 : covered 20215 20265 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20265 : covered 20265 20315 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20315 : covered 20315 20365 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20365 : covered 20365 20415 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20415 : covered 20415 20465 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20465 : covered 20465 20515 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20515 : covered 20515 20565 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20565 : covered 20565 20615 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20615 : covered 20615 20665 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20665 : covered 20665 20715 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20715 : covered 20715 20765 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20765 : covered 20765 20816 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20816 : covered 20816 20866 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20866 : covered 20866 20916 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20916 : covered 20916 20966 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch20966 : covered 20966 21016 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21016 : covered 21016 21066 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21066 : covered 21066 21116 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21116 : covered 21116 21166 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21166 : covered 21166 21216 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21216 : covered 21216 21266 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21266 : covered 21266 21316 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21316 : covered 21316 21366 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21366 : covered 21366 21416 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21416 : covered 21416 21466 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21466 : covered 21466 21516 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21516 : covered 21516 21566 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21566 : covered 21566 21617 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21617 : covered 21617 21667 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21667 : covered 21667 21717 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21717 : covered 21717 21767 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21767 : covered 21767 21817 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21817 : covered 21817 21867 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21867 : covered 21867 21917 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21917 : covered 21917 21967 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch21967 : covered 21967 22017 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22017 : covered 22017 22067 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22067 : covered 22067 22117 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22117 : covered 22117 22167 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22167 : covered 22167 22217 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22217 : covered 22217 22267 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22267 : covered 22267 22317 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22317 : covered 22317 22367 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22367 : covered 22367 22418 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22418 : covered 22418 22468 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22468 : covered 22468 22518 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22518 : covered 22518 22568 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22568 : covered 22568 22618 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22618 : covered 22618 22668 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22668 : covered 22668 22718 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22718 : covered 22718 22768 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22768 : covered 22768 22818 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22818 : covered 22818 22868 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22868 : covered 22868 22918 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22918 : covered 22918 22968 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch22968 : covered 22968 23018 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23018 : covered 23018 23068 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23068 : covered 23068 23118 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23118 : covered 23118 23168 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23168 : covered 23168 23218 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23218 : covered 23218 23268 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23268 : covered 23268 23318 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23318 : covered 23318 23368 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23368 : covered 23368 23418 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23418 : covered 23418 23468 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23468 : covered 23468 23518 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23518 : covered 23518 23568 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23568 : covered 23568 23618 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23618 : covered 23618 23668 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23668 : covered 23668 23718 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23718 : covered 23718 23768 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23768 : covered 23768 23818 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23818 : covered 23818 23868 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23868 : covered 23868 23918 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23918 : covered 23918 23968 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch23968 : covered 23968 24019 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24019 : covered 24019 24069 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24069 : covered 24069 24119 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24119 : covered 24119 24169 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24169 : covered 24169 24219 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24219 : covered 24219 24269 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24269 : covered 24269 24319 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24319 : covered 24319 24369 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24369 : covered 24369 24419 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24419 : covered 24419 24469 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24469 : covered 24469 24519 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24519 : covered 24519 24569 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24569 : covered 24569 24619 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24619 : covered 24619 24669 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24669 : covered 24669 24719 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24719 : covered 24719 24769 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24769 : covered 24769 24820 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24820 : covered 24820 24870 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24870 : covered 24870 24920 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24920 : covered 24920 24970 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch24970 : covered 24970 25020 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25020 : covered 25020 25070 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25070 : covered 25070 25120 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25120 : covered 25120 25170 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25170 : covered 25170 25220 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25220 : covered 25220 25270 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25270 : covered 25270 25320 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25320 : covered 25320 25370 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25370 : covered 25370 25420 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25420 : covered 25420 25470 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25470 : covered 25470 25520 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25520 : covered 25520 25570 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem batch25570 : covered 25570 25621 := checked (by apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 15000 in
private theorem allrows : covered 0 25621 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch0 batch50) (joinCoverage batch100 batch150)) (joinCoverage (joinCoverage batch200 batch250) (joinCoverage batch300 batch350))) (joinCoverage (joinCoverage (joinCoverage batch400 batch450) (joinCoverage batch500 batch550)) (joinCoverage (joinCoverage batch600 batch650) (joinCoverage batch700 batch750)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch800 batch850) (joinCoverage batch900 batch950)) (joinCoverage (joinCoverage batch1000 batch1050) (joinCoverage batch1100 batch1150))) (joinCoverage (joinCoverage (joinCoverage batch1200 batch1250) (joinCoverage batch1300 batch1350)) (joinCoverage (joinCoverage batch1400 batch1450) (joinCoverage batch1500 batch1550))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch1601 batch1651) (joinCoverage batch1701 batch1751)) (joinCoverage (joinCoverage batch1801 batch1851) (joinCoverage batch1901 batch1951))) (joinCoverage (joinCoverage (joinCoverage batch2001 batch2051) (joinCoverage batch2101 batch2151)) (joinCoverage (joinCoverage batch2201 batch2251) (joinCoverage batch2301 batch2351)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch2401 batch2451) (joinCoverage batch2501 batch2551)) (joinCoverage (joinCoverage batch2601 batch2651) (joinCoverage batch2701 batch2751))) (joinCoverage (joinCoverage (joinCoverage batch2801 batch2851) (joinCoverage batch2901 batch2951)) (joinCoverage (joinCoverage batch3001 batch3051) (joinCoverage batch3101 batch3151)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch3202 batch3252) (joinCoverage batch3302 batch3352)) (joinCoverage (joinCoverage batch3402 batch3452) (joinCoverage batch3502 batch3552))) (joinCoverage (joinCoverage (joinCoverage batch3602 batch3652) (joinCoverage batch3702 batch3752)) (joinCoverage (joinCoverage batch3802 batch3852) (joinCoverage batch3902 batch3952)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch4002 batch4052) (joinCoverage batch4102 batch4152)) (joinCoverage (joinCoverage batch4202 batch4252) (joinCoverage batch4302 batch4352))) (joinCoverage (joinCoverage (joinCoverage batch4402 batch4452) (joinCoverage batch4502 batch4552)) (joinCoverage (joinCoverage batch4602 batch4652) (joinCoverage batch4702 batch4752))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch4803 batch4853) (joinCoverage batch4903 batch4953)) (joinCoverage (joinCoverage batch5003 batch5053) (joinCoverage batch5103 batch5153))) (joinCoverage (joinCoverage (joinCoverage batch5203 batch5253) (joinCoverage batch5303 batch5353)) (joinCoverage (joinCoverage batch5403 batch5453) (joinCoverage batch5503 batch5553)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch5604 batch5654) (joinCoverage batch5704 batch5754)) (joinCoverage (joinCoverage batch5804 batch5854) (joinCoverage batch5904 batch5954))) (joinCoverage (joinCoverage (joinCoverage batch6004 batch6054) (joinCoverage batch6104 batch6154)) (joinCoverage (joinCoverage batch6204 batch6254) (joinCoverage batch6304 batch6354))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch6405 batch6455) (joinCoverage batch6505 batch6555)) (joinCoverage (joinCoverage batch6605 batch6655) (joinCoverage batch6705 batch6755))) (joinCoverage (joinCoverage (joinCoverage batch6805 batch6855) (joinCoverage batch6905 batch6955)) (joinCoverage (joinCoverage batch7005 batch7055) (joinCoverage batch7105 batch7155)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch7205 batch7255) (joinCoverage batch7305 batch7355)) (joinCoverage (joinCoverage batch7405 batch7455) (joinCoverage batch7505 batch7555))) (joinCoverage (joinCoverage (joinCoverage batch7605 batch7655) (joinCoverage batch7705 batch7755)) (joinCoverage (joinCoverage batch7805 batch7855) (joinCoverage batch7905 batch7955))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch8006 batch8056) (joinCoverage batch8106 batch8156)) (joinCoverage (joinCoverage batch8206 batch8256) (joinCoverage batch8306 batch8356))) (joinCoverage (joinCoverage (joinCoverage batch8406 batch8456) (joinCoverage batch8506 batch8556)) (joinCoverage (joinCoverage batch8606 batch8656) (joinCoverage batch8706 batch8756)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch8806 batch8856) (joinCoverage batch8906 batch8956)) (joinCoverage (joinCoverage batch9006 batch9056) (joinCoverage batch9106 batch9156))) (joinCoverage (joinCoverage (joinCoverage batch9206 batch9256) (joinCoverage batch9306 batch9356)) (joinCoverage (joinCoverage batch9406 batch9456) (joinCoverage batch9506 batch9556)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch9607 batch9657) (joinCoverage batch9707 batch9757)) (joinCoverage (joinCoverage batch9807 batch9857) (joinCoverage batch9907 batch9957))) (joinCoverage (joinCoverage (joinCoverage batch10007 batch10057) (joinCoverage batch10107 batch10157)) (joinCoverage (joinCoverage batch10207 batch10257) (joinCoverage batch10307 batch10357)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch10407 batch10457) (joinCoverage batch10507 batch10557)) (joinCoverage (joinCoverage batch10607 batch10657) (joinCoverage batch10707 batch10757))) (joinCoverage (joinCoverage (joinCoverage batch10807 batch10857) (joinCoverage batch10907 batch10957)) (joinCoverage (joinCoverage batch11007 batch11057) (joinCoverage batch11107 batch11157))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch11208 batch11258) (joinCoverage batch11308 batch11358)) (joinCoverage (joinCoverage batch11408 batch11458) (joinCoverage batch11508 batch11558))) (joinCoverage (joinCoverage (joinCoverage batch11608 batch11658) (joinCoverage batch11708 batch11758)) (joinCoverage (joinCoverage batch11808 batch11858) (joinCoverage batch11908 batch11958)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch12009 batch12059) (joinCoverage batch12109 batch12159)) (joinCoverage (joinCoverage batch12209 batch12259) (joinCoverage batch12309 batch12359))) (joinCoverage (joinCoverage (joinCoverage batch12409 batch12459) (joinCoverage batch12509 batch12559)) (joinCoverage (joinCoverage batch12609 batch12659) (joinCoverage batch12709 batch12759)))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch12810 batch12860) (joinCoverage batch12910 batch12960)) (joinCoverage (joinCoverage batch13010 batch13060) (joinCoverage batch13110 batch13160))) (joinCoverage (joinCoverage (joinCoverage batch13210 batch13260) (joinCoverage batch13310 batch13360)) (joinCoverage (joinCoverage batch13410 batch13460) (joinCoverage batch13510 batch13560)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch13610 batch13660) (joinCoverage batch13710 batch13760)) (joinCoverage (joinCoverage batch13810 batch13860) (joinCoverage batch13910 batch13960))) (joinCoverage (joinCoverage (joinCoverage batch14010 batch14060) (joinCoverage batch14110 batch14160)) (joinCoverage (joinCoverage batch14210 batch14260) (joinCoverage batch14310 batch14360))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch14411 batch14461) (joinCoverage batch14511 batch14561)) (joinCoverage (joinCoverage batch14611 batch14661) (joinCoverage batch14711 batch14761))) (joinCoverage (joinCoverage (joinCoverage batch14811 batch14861) (joinCoverage batch14911 batch14961)) (joinCoverage (joinCoverage batch15011 batch15061) (joinCoverage batch15111 batch15161)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch15211 batch15261) (joinCoverage batch15311 batch15361)) (joinCoverage (joinCoverage batch15411 batch15461) (joinCoverage batch15511 batch15561))) (joinCoverage (joinCoverage (joinCoverage batch15611 batch15661) (joinCoverage batch15711 batch15761)) (joinCoverage (joinCoverage batch15811 batch15861) (joinCoverage batch15911 batch15961)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch16012 batch16062) (joinCoverage batch16112 batch16162)) (joinCoverage (joinCoverage batch16212 batch16262) (joinCoverage batch16312 batch16362))) (joinCoverage (joinCoverage (joinCoverage batch16412 batch16462) (joinCoverage batch16512 batch16562)) (joinCoverage (joinCoverage batch16612 batch16662) (joinCoverage batch16712 batch16762)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch16812 batch16862) (joinCoverage batch16912 batch16962)) (joinCoverage (joinCoverage batch17012 batch17062) (joinCoverage batch17112 batch17162))) (joinCoverage (joinCoverage (joinCoverage batch17212 batch17262) (joinCoverage batch17312 batch17362)) (joinCoverage (joinCoverage batch17412 batch17462) (joinCoverage batch17512 batch17562))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch17613 batch17663) (joinCoverage batch17713 batch17763)) (joinCoverage (joinCoverage batch17813 batch17863) (joinCoverage batch17913 batch17963))) (joinCoverage (joinCoverage (joinCoverage batch18013 batch18063) (joinCoverage batch18113 batch18163)) (joinCoverage (joinCoverage batch18213 batch18263) (joinCoverage batch18313 batch18363)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch18414 batch18464) (joinCoverage batch18514 batch18564)) (joinCoverage (joinCoverage batch18614 batch18664) (joinCoverage batch18714 batch18764))) (joinCoverage (joinCoverage (joinCoverage batch18814 batch18864) (joinCoverage batch18914 batch18964)) (joinCoverage (joinCoverage batch19014 batch19064) (joinCoverage batch19114 batch19164))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch19215 batch19265) (joinCoverage batch19315 batch19365)) (joinCoverage (joinCoverage batch19415 batch19465) (joinCoverage batch19515 batch19565))) (joinCoverage (joinCoverage (joinCoverage batch19615 batch19665) (joinCoverage batch19715 batch19765)) (joinCoverage (joinCoverage batch19815 batch19865) (joinCoverage batch19915 batch19965)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch20015 batch20065) (joinCoverage batch20115 batch20165)) (joinCoverage (joinCoverage batch20215 batch20265) (joinCoverage batch20315 batch20365))) (joinCoverage (joinCoverage (joinCoverage batch20415 batch20465) (joinCoverage batch20515 batch20565)) (joinCoverage (joinCoverage batch20615 batch20665) (joinCoverage batch20715 batch20765))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch20816 batch20866) (joinCoverage batch20916 batch20966)) (joinCoverage (joinCoverage batch21016 batch21066) (joinCoverage batch21116 batch21166))) (joinCoverage (joinCoverage (joinCoverage batch21216 batch21266) (joinCoverage batch21316 batch21366)) (joinCoverage (joinCoverage batch21416 batch21466) (joinCoverage batch21516 batch21566)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch21617 batch21667) (joinCoverage batch21717 batch21767)) (joinCoverage (joinCoverage batch21817 batch21867) (joinCoverage batch21917 batch21967))) (joinCoverage (joinCoverage (joinCoverage batch22017 batch22067) (joinCoverage batch22117 batch22167)) (joinCoverage (joinCoverage batch22217 batch22267) (joinCoverage batch22317 batch22367)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch22418 batch22468) (joinCoverage batch22518 batch22568)) (joinCoverage (joinCoverage batch22618 batch22668) (joinCoverage batch22718 batch22768))) (joinCoverage (joinCoverage (joinCoverage batch22818 batch22868) (joinCoverage batch22918 batch22968)) (joinCoverage (joinCoverage batch23018 batch23068) (joinCoverage batch23118 batch23168)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch23218 batch23268) (joinCoverage batch23318 batch23368)) (joinCoverage (joinCoverage batch23418 batch23468) (joinCoverage batch23518 batch23568))) (joinCoverage (joinCoverage (joinCoverage batch23618 batch23668) (joinCoverage batch23718 batch23768)) (joinCoverage (joinCoverage batch23818 batch23868) (joinCoverage batch23918 batch23968))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch24019 batch24069) (joinCoverage batch24119 batch24169)) (joinCoverage (joinCoverage batch24219 batch24269) (joinCoverage batch24319 batch24369))) (joinCoverage (joinCoverage (joinCoverage batch24419 batch24469) (joinCoverage batch24519 batch24569)) (joinCoverage (joinCoverage batch24619 batch24669) (joinCoverage batch24719 batch24769)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage batch24820 batch24870) (joinCoverage batch24920 batch24970)) (joinCoverage (joinCoverage batch25020 batch25070) (joinCoverage batch25120 batch25170))) (joinCoverage (joinCoverage (joinCoverage batch25220 batch25270) (joinCoverage batch25320 batch25370)) (joinCoverage (joinCoverage batch25420 batch25470) (joinCoverage batch25520 batch25570)))))))))

theorem fast_correct (n : ℕ) (bound : n ≤ 9223368) : fast n = Nat.primeCounting n := by
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
      · have ix := index_bound (show n≤9223368 by omega)
        have within : index n / 96 < 25621 := by omega
        have chk := beq_iff_eq.mp (allrows _ (Nat.zero_le _) within)
        change checkpoint (index n/96+1) = checkpoint (index n/96) +
          tally (fun j => quick (number j)) (96*(index n/96)) 96 at chk
        have h := fromBlocks_succ checkpoint (fun j => quick (number j)) (index n) chk
        change raw (index n+1) = raw (index n) + (if quick (number (index n)) then 1 else 0) at h
        rw [whose] at h
        simp only [fast,e,h,unchanged]
        by_cases hp : (n+1).Prime
        · simp [hp,(quick_ok bound).mpr hp,Nat.add_right_comm]
        · simp [hp,mt (quick_ok bound).mp hp]
def prime (n : ℕ) : Bool := quick n

theorem prime_ok (n : ℕ) (hn : n≤9223368) : prime n=true ↔ n.Prime := quick_ok hn

end CheckpointA28006Slim


namespace HybridBound28006

def fast (n : ℕ) : ℕ :=
  if n≤206781 then WheelTableA94.fast n else CheckpointA28006Slim.fast n

theorem fast_correct (n : ℕ) (hn : n≤9223368) : fast n=Nat.primeCounting n := by
  unfold fast
  split_ifs with small
  · exact WheelTableA94.fast_correct n small
  · exact CheckpointA28006Slim.fast_correct n hn

end HybridBound28006


/- The Legendre and Meissel identities below are the public Physbuzz reduction
for OEIS A247824, itself crediting Daniel Veljjanoski and rleshner. The numerical proof below certifies one of the residual ranks. -/
open Finset
namespace Endpoint28006

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


private abbrev tab := HybridBound28006.fast
private abbrev F := evalPhi tab

private abbrev prime := CheckpointA28006Slim.prime
private theorem prime_ok (n : ℕ) (hn : n≤9223368) : prime n=true ↔ n.Prime := CheckpointA28006Slim.prime_ok n hn


private theorem takeStep {ps : List ℕ} {p q prev cut ans : ℕ}
    (notWheel : p≠11) (base : F ps 28006150079=prev) (part : F ps q=cut) (div : 28006150079/p=q)
    (le : p≤28006150079) (sq : (p+1)^2≤28006150079) (sub : prev-cut=ans) :
    F (p::ps) 28006150079=ans := eval_delta tab ps p 28006150079 q prev cut ans notWheel le sq div base part sub


private def ps0 : List ℕ := []
private theorem v0 : F ps0 28006150079=28006150079 := rfl

private def ps1 : List ℕ := 2::ps0
private theorem c1 : F ps0 14003075039=14003075039 := by decide +kernel
private theorem v1 : F ps1 28006150079=14003075040 :=
  takeStep (p:=2) (by decide) v0 c1 rfl (by decide) (by decide) rfl

private def ps2 : List ℕ := 3::ps1
private theorem c2 : F ps1 9335383359=4667691680 := by decide +kernel
private theorem v2 : F ps2 28006150079=9335383360 :=
  takeStep (p:=3) (by decide) v1 c2 rfl (by decide) (by decide) rfl

private def ps3 : List ℕ := 5::ps2
private theorem c3 : F ps2 5601230015=1867076672 := by decide +kernel
private theorem v3 : F ps3 28006150079=7468306688 :=
  takeStep (p:=5) (by decide) v2 c3 rfl (by decide) (by decide) rfl

private def ps4 : List ℕ := 7::ps3
private theorem c4 : F ps3 4000878582=1066900955 := by decide +kernel
private theorem v4 : F ps4 28006150079=6401405733 :=
  takeStep (p:=7) (by decide) v3 c4 rfl (by decide) (by decide) rfl

private def ps5 : List ℕ := 11::ps4
private theorem c5 : F ps4 2546013643=581945976 := by decide +kernel
private theorem v5 : F ps5 28006150079=5819459757 := by decide +kernel

private def ps6 : List ℕ := 13::ps5
private theorem c6 : F ps5 2154319236=447650750 := by decide +kernel
private theorem v6 : F ps6 28006150079=5371809007 :=
  takeStep (p:=13) (by decide) v5 c6 rfl (by decide) (by decide) rfl

private def ps7 : List ℕ := 17::ps6
private theorem c7 : F ps6 1647420592=315988767 := by decide +kernel
private theorem v7 : F ps7 28006150079=5055820240 :=
  takeStep (p:=17) (by decide) v6 c7 rfl (by decide) (by decide) rfl

private def ps8 : List ℕ := 19::ps7
private theorem c8 : F ps7 1474007898=266095804 := by decide +kernel
private theorem v8 : F ps8 28006150079=4789724436 :=
  takeStep (p:=19) (by decide) v7 c8 rfl (by decide) (by decide) rfl

private def ps9 : List ℕ := 23::ps8
private theorem c9 : F ps8 1217658699=208248888 := by decide +kernel
private theorem v9 : F ps9 28006150079=4581475548 :=
  takeStep (p:=23) (by decide) v8 c9 rfl (by decide) (by decide) rfl

private def ps10 : List ℕ := 29::ps9
private theorem c10 : F ps9 965729313=157981915 := by decide +kernel
private theorem v10 : F ps10 28006150079=4423493633 :=
  takeStep (p:=29) (by decide) v9 c10 rfl (by decide) (by decide) rfl

private def ps11 : List ℕ := 31::ps10
private theorem c11 : F ps10 903424196=142693341 := by decide +kernel
private theorem v11 : F ps11 28006150079=4280800292 :=
  takeStep (p:=31) (by decide) v10 c11 rfl (by decide) (by decide) rfl

private def ps12 : List ℕ := 37::ps11
private theorem c12 : F ps11 756922975=115697293 := by decide +kernel
private theorem v12 : F ps12 28006150079=4165102999 :=
  takeStep (p:=37) (by decide) v11 c12 rfl (by decide) (by decide) rfl

private def ps13 : List ℕ := 41::ps12
private theorem c13 : F ps12 683076831=101587869 := by decide +kernel
private theorem v13 : F ps13 28006150079=4063515130 :=
  takeStep (p:=41) (by decide) v12 c13 rfl (by decide) (by decide) rfl

private def ps14 : List ℕ := 43::ps13
private theorem c14 : F ps13 651305815=94500331 := by decide +kernel
private theorem v14 : F ps14 28006150079=3969014799 :=
  takeStep (p:=43) (by decide) v13 c14 rfl (by decide) (by decide) rfl

private def ps15 : List ℕ := 47::ps14
private theorem c15 : F ps14 595875533=84447096 := by decide +kernel
private theorem v15 : F ps15 28006150079=3884567703 :=
  takeStep (p:=47) (by decide) v14 c15 rfl (by decide) (by decide) rfl

private def ps16 : List ℕ := 53::ps15
private theorem c16 : F ps15 528417926=73293780 := by decide +kernel
private theorem v16 : F ps16 28006150079=3811273923 :=
  takeStep (p:=53) (by decide) v15 c16 rfl (by decide) (by decide) rfl

private def ps17 : List ℕ := 59::ps16
private theorem c17 : F ps16 474680509=64598051 := by decide +kernel
private theorem v17 : F ps17 28006150079=3746675872 :=
  takeStep (p:=59) (by decide) v16 c17 rfl (by decide) (by decide) rfl

private def ps18 : List ℕ := 61::ps17
private theorem c18 : F ps17 459117214=61421253 := by decide +kernel
private theorem v18 : F ps18 28006150079=3685254619 :=
  takeStep (p:=61) (by decide) v17 c18 rfl (by decide) (by decide) rfl

private def ps19 : List ℕ := 67::ps18
private theorem c19 : F ps18 418002239=55004334 := by decide +kernel
private theorem v19 : F ps19 28006150079=3630250285 :=
  takeStep (p:=67) (by decide) v18 c19 rfl (by decide) (by decide) rfl

private def ps20 : List ℕ := 71::ps19
private theorem c20 : F ps19 394452818=51131007 := by decide +kernel
private theorem v20 : F ps20 28006150079=3579119278 :=
  takeStep (p:=71) (by decide) v19 c20 rfl (by decide) (by decide) rfl

private def ps21 : List ℕ := 73::ps20
private theorem c21 : F ps20 383645891=49029788 := by decide +kernel
private theorem v21 : F ps21 28006150079=3530089490 :=
  takeStep (p:=73) (by decide) v20 c21 rfl (by decide) (by decide) rfl

private def ps22 : List ℕ := 79::ps21
private theorem c22 : F ps21 354508228=44685355 := by decide +kernel
private theorem v22 : F ps22 28006150079=3485404135 :=
  takeStep (p:=79) (by decide) v21 c22 rfl (by decide) (by decide) rfl

private def ps23 : List ℕ := 83::ps22
private theorem c23 : F ps22 337423494=41993213 := by decide +kernel
private theorem v23 : F ps23 28006150079=3443410922 :=
  takeStep (p:=83) (by decide) v22 c23 rfl (by decide) (by decide) rfl

private def ps24 : List ℕ := 89::ps23
private theorem c24 : F ps23 314675843=38689986 := by decide +kernel
private theorem v24 : F ps24 28006150079=3404720936 :=
  takeStep (p:=89) (by decide) v23 c24 rfl (by decide) (by decide) rfl

private def ps25 : List ℕ := 97::ps24
private theorem c25 : F ps24 288723196=35099558 := by decide +kernel
private theorem v25 : F ps25 28006150079=3369621378 :=
  takeStep (p:=97) (by decide) v24 c25 rfl (by decide) (by decide) rfl

private def ps26 : List ℕ := 101::ps25
private theorem c26 : F ps25 277288614=33361194 := by decide +kernel
private theorem v26 : F ps26 28006150079=3336260184 :=
  takeStep (p:=101) (by decide) v25 c26 rfl (by decide) (by decide) rfl

private def ps27 : List ℕ := 103::ps26
private theorem c27 : F ps26 271904369=32388666 := by decide +kernel
private theorem v27 : F ps27 28006150079=3303871518 :=
  takeStep (p:=103) (by decide) v26 c27 rfl (by decide) (by decide) rfl

private def ps28 : List ℕ := 107::ps27
private theorem c28 : F ps27 261739720=30874184 := by decide +kernel
private theorem v28 : F ps28 28006150079=3272997334 :=
  takeStep (p:=107) (by decide) v27 c28 rfl (by decide) (by decide) rfl

private def ps29 : List ℕ := 109::ps28
private theorem c29 : F ps28 256937156=30023400 := by decide +kernel
private theorem v29 : F ps29 28006150079=3242973934 :=
  takeStep (p:=109) (by decide) v28 c29 rfl (by decide) (by decide) rfl

private def ps30 : List ℕ := 113::ps29
private theorem c30 : F ps29 247842036=28693756 := by decide +kernel
private theorem v30 : F ps30 28006150079=3214280178 :=
  takeStep (p:=113) (by decide) v29 c30 rfl (by decide) (by decide) rfl

private def ps31 : List ℕ := 127::ps30
private theorem c31 : F ps30 220520866=25303141 := by decide +kernel
private theorem v31 : F ps31 28006150079=3188977037 :=
  takeStep (p:=127) (by decide) v30 c31 rfl (by decide) (by decide) rfl

private def ps32 : List ℕ := 131::ps31
private theorem c32 : F ps31 213787405=24336421 := by decide +kernel
private theorem v32 : F ps32 28006150079=3164640616 :=
  takeStep (p:=131) (by decide) v31 c32 rfl (by decide) (by decide) rfl

private def ps33 : List ℕ := 137::ps32
private theorem c33 : F ps32 204424453=23091971 := by decide +kernel
private theorem v33 : F ps33 28006150079=3141548645 :=
  takeStep (p:=137) (by decide) v32 c33 rfl (by decide) (by decide) rfl

private def ps34 : List ℕ := 139::ps33
private theorem c34 : F ps33 201483094=22592917 := by decide +kernel
private theorem v34 : F ps34 28006150079=3118955728 :=
  takeStep (p:=139) (by decide) v33 c34 rfl (by decide) (by decide) rfl

private def ps35 : List ℕ := 149::ps34
private theorem c35 : F ps34 187960738=20924324 := by decide +kernel
private theorem v35 : F ps35 28006150079=3098031404 :=
  takeStep (p:=149) (by decide) v34 c35 rfl (by decide) (by decide) rfl

private def ps36 : List ℕ := 151::ps35
private theorem c36 : F ps35 185471192=20508307 := by decide +kernel
private theorem v36 : F ps36 28006150079=3077523097 :=
  takeStep (p:=151) (by decide) v35 c36 rfl (by decide) (by decide) rfl

private def ps37 : List ℕ := 157::ps36
private theorem c37 : F ps36 178383121=19593639 := by decide +kernel
private theorem v37 : F ps37 28006150079=3057929458 :=
  takeStep (p:=157) (by decide) v36 c37 rfl (by decide) (by decide) rfl

private def ps38 : List ℕ := 163::ps37
private theorem c38 : F ps37 171816871=18752257 := by decide +kernel
private theorem v38 : F ps38 28006150079=3039177201 :=
  takeStep (p:=163) (by decide) v37 c38 rfl (by decide) (by decide) rfl

private def ps39 : List ℕ := 167::ps38
private theorem c39 : F ps38 167701497=18191012 := by decide +kernel
private theorem v39 : F ps39 28006150079=3020986189 :=
  takeStep (p:=167) (by decide) v38 c39 rfl (by decide) (by decide) rfl

private def ps40 : List ℕ := 173::ps39
private theorem c40 : F ps39 161885260=17455378 := by decide +kernel
private theorem v40 : F ps40 28006150079=3003530811 :=
  takeStep (p:=173) (by decide) v39 c40 rfl (by decide) (by decide) rfl

private def ps41 : List ℕ := 179::ps40
private theorem c41 : F ps40 156458938=16773373 := by decide +kernel
private theorem v41 : F ps41 28006150079=2986757438 :=
  takeStep (p:=179) (by decide) v40 c41 rfl (by decide) (by decide) rfl

private def ps42 : List ℕ := 181::ps41
private theorem c42 : F ps41 154730110=16496023 := by decide +kernel
private theorem v42 : F ps42 28006150079=2970261415 :=
  takeStep (p:=181) (by decide) v41 c42 rfl (by decide) (by decide) rfl

private def ps43 : List ℕ := 191::ps42
private theorem c43 : F ps42 146629058=15547128 := by decide +kernel
private theorem v43 : F ps43 28006150079=2954714287 :=
  takeStep (p:=191) (by decide) v42 c43 rfl (by decide) (by decide) rfl

private def ps44 : List ℕ := 193::ps43
private theorem c44 : F ps43 145109585=15306387 := by decide +kernel
private theorem v44 : F ps44 28006150079=2939407900 :=
  takeStep (p:=193) (by decide) v43 c44 rfl (by decide) (by decide) rfl

private def ps45 : List ℕ := 197::ps44
private theorem c45 : F ps44 142163198=14919037 := by decide +kernel
private theorem v45 : F ps45 28006150079=2924488863 :=
  takeStep (p:=197) (by decide) v44 c45 rfl (by decide) (by decide) rfl

private def ps46 : List ℕ := 199::ps45
private theorem c46 : F ps45 140734422=14695313 := by decide +kernel
private theorem v46 : F ps46 28006150079=2909793550 :=
  takeStep (p:=199) (by decide) v45 c46 rfl (by decide) (by decide) rfl

private def ps47 : List ℕ := 211::ps46
private theorem c47 : F ps46 132730569=13791721 := by decide +kernel
private theorem v47 : F ps47 28006150079=2896001829 :=
  takeStep (p:=211) (by decide) v46 c47 rfl (by decide) (by decide) rfl

private def ps48 : List ℕ := 223::ps47
private theorem c48 : F ps47 125588116=12989710 := by decide +kernel
private theorem v48 : F ps48 28006150079=2883012119 :=
  takeStep (p:=223) (by decide) v47 c48 rfl (by decide) (by decide) rfl

private def ps49 : List ℕ := 227::ps48
private theorem c49 : F ps48 123375110=12705130 := by decide +kernel
private theorem v49 : F ps49 28006150079=2870306989 :=
  takeStep (p:=227) (by decide) v48 c49 rfl (by decide) (by decide) rfl

private def ps50 : List ℕ := 229::ps49
private theorem c50 : F ps49 122297598=12540155 := by decide +kernel
private theorem v50 : F ps50 28006150079=2857766834 :=
  takeStep (p:=229) (by decide) v49 c50 rfl (by decide) (by decide) rfl

private def ps51 : List ℕ := 233::ps50
private theorem c51 : F ps50 120198069=12272781 := by decide +kernel
private theorem v51 : F ps51 28006150079=2845494053 :=
  takeStep (p:=233) (by decide) v50 c51 rfl (by decide) (by decide) rfl

private def ps52 : List ℕ := 239::ps51
private theorem c52 : F ps51 117180544=11915255 := by decide +kernel
private theorem v52 : F ps52 28006150079=2833578798 :=
  takeStep (p:=239) (by decide) v51 c52 rfl (by decide) (by decide) rfl

private def ps53 : List ℕ := 241::ps52
private theorem c53 : F ps52 116208091=11768576 := by decide +kernel
private theorem v53 : F ps53 28006150079=2821810222 :=
  takeStep (p:=241) (by decide) v52 c53 rfl (by decide) (by decide) rfl

private def ps54 : List ℕ := 251::ps53
private theorem c54 : F ps53 111578287=11255216 := by decide +kernel
private theorem v54 : F ps54 28006150079=2810555006 :=
  takeStep (p:=251) (by decide) v53 c54 rfl (by decide) (by decide) rfl

private def ps55 : List ℕ := 257::ps54
private theorem c55 : F ps54 108973346=10950644 := by decide +kernel
private theorem v55 : F ps55 28006150079=2799604362 :=
  takeStep (p:=257) (by decide) v54 c55 rfl (by decide) (by decide) rfl

private def ps56 : List ℕ := 263::ps55
private theorem c56 : F ps55 106487262=10661186 := by decide +kernel
private theorem v56 : F ps56 28006150079=2788943176 :=
  takeStep (p:=263) (by decide) v55 c56 rfl (by decide) (by decide) rfl

private def ps57 : List ℕ := 269::ps56
private theorem c57 : F ps56 104112082=10385835 := by decide +kernel
private theorem v57 : F ps57 28006150079=2778557341 :=
  takeStep (p:=269) (by decide) v56 c57 rfl (by decide) (by decide) rfl

private def ps58 : List ℕ := 271::ps57
private theorem c58 : F ps57 103343727=10272630 := by decide +kernel
private theorem v58 : F ps58 28006150079=2768284711 :=
  takeStep (p:=271) (by decide) v57 c58 rfl (by decide) (by decide) rfl

private def ps59 : List ℕ := 277::ps58
private theorem c59 : F ps58 101105234=10015026 := by decide +kernel
private theorem v59 : F ps59 28006150079=2758269685 :=
  takeStep (p:=277) (by decide) v58 c59 rfl (by decide) (by decide) rfl

private def ps60 : List ℕ := 281::ps59
private theorem c60 : F ps59 99666014=9838706 := by decide +kernel
private theorem v60 : F ps60 28006150079=2748430979 :=
  takeStep (p:=281) (by decide) v59 c60 rfl (by decide) (by decide) rfl

private def ps61 : List ℕ := 283::ps60
private theorem c61 : F ps60 98961661=9736144 := by decide +kernel
private theorem v61 : F ps61 28006150079=2738694835 :=
  takeStep (p:=283) (by decide) v60 c61 rfl (by decide) (by decide) rfl

private def ps62 : List ℕ := 293::ps61
private theorem c62 : F ps61 95584129=9372988 := by decide +kernel
private theorem v62 : F ps62 28006150079=2729321847 :=
  takeStep (p:=293) (by decide) v61 c62 rfl (by decide) (by decide) rfl

private def ps63 : List ℕ := 307::ps62
private theorem c63 : F ps62 91225244=8917647 := by decide +kernel
private theorem v63 : F ps63 28006150079=2720404200 :=
  takeStep (p:=307) (by decide) v62 c63 rfl (by decide) (by decide) rfl

private def ps64 : List ℕ := 311::ps63
private theorem c64 : F ps63 90051929=8775977 := by decide +kernel
private theorem v64 : F ps64 28006150079=2711628223 :=
  takeStep (p:=311) (by decide) v63 c64 rfl (by decide) (by decide) rfl

private def ps65 : List ℕ := 313::ps64
private theorem c65 : F ps64 89476517=8693497 := by decide +kernel
private theorem v65 : F ps65 28006150079=2702934726 :=
  takeStep (p:=313) (by decide) v64 c65 rfl (by decide) (by decide) rfl

private def ps66 : List ℕ := 317::ps65
private theorem c66 : F ps65 88347476=8558089 := by decide +kernel
private theorem v66 : F ps66 28006150079=2694376637 :=
  takeStep (p:=317) (by decide) v65 c66 rfl (by decide) (by decide) rfl

private def ps67 : List ℕ := 331::ps66
private theorem c67 : F ps66 84610725=8172587 := by decide +kernel
private theorem v67 : F ps67 28006150079=2686204050 :=
  takeStep (p:=331) (by decide) v66 c67 rfl (by decide) (by decide) rfl

private def ps68 : List ℕ := 337::ps67
private theorem c68 : F ps67 83104302=8004472 := by decide +kernel
private theorem v68 : F ps68 28006150079=2678199578 :=
  takeStep (p:=337) (by decide) v67 c68 rfl (by decide) (by decide) rfl

private def ps69 : List ℕ := 347::ps68
private theorem c69 : F ps68 80709366=7752494 := by decide +kernel
private theorem v69 : F ps69 28006150079=2670447084 :=
  takeStep (p:=347) (by decide) v68 c69 rfl (by decide) (by decide) rfl

private def ps70 : List ℕ := 349::ps69
private theorem c70 : F ps69 80246848=7687118 := by decide +kernel
private theorem v70 : F ps70 28006150079=2662759966 :=
  takeStep (p:=349) (by decide) v69 c70 rfl (by decide) (by decide) rfl

private def ps71 : List ℕ := 353::ps70
private theorem c71 : F ps70 79337535=7579573 := by decide +kernel
private theorem v71 : F ps71 28006150079=2655180393 :=
  takeStep (p:=353) (by decide) v70 c71 rfl (by decide) (by decide) rfl

private def ps72 : List ℕ := 359::ps71
private theorem c72 : F ps71 78011560=7433179 := by decide +kernel
private theorem v72 : F ps72 28006150079=2647747214 :=
  takeStep (p:=359) (by decide) v71 c72 rfl (by decide) (by decide) rfl

private def ps73 : List ℕ := 367::ps72
private theorem c73 : F ps72 76311035=7252325 := by decide +kernel
private theorem v73 : F ps73 28006150079=2640494889 :=
  takeStep (p:=367) (by decide) v72 c73 rfl (by decide) (by decide) rfl

private def ps74 : List ℕ := 373::ps73
private theorem c74 : F ps73 75083512=7117438 := by decide +kernel
private theorem v74 : F ps74 28006150079=2633377451 :=
  takeStep (p:=373) (by decide) v73 c74 rfl (by decide) (by decide) rfl

private def ps75 : List ℕ := 379::ps74
private theorem c75 : F ps74 73894855=6987116 := by decide +kernel
private theorem v75 : F ps75 28006150079=2626390335 :=
  takeStep (p:=379) (by decide) v74 c75 rfl (by decide) (by decide) rfl

private def ps76 : List ℕ := 383::ps75
private theorem c76 : F ps75 73123107=6896778 := by decide +kernel
private theorem v76 : F ps76 28006150079=2619493557 :=
  takeStep (p:=383) (by decide) v75 c76 rfl (by decide) (by decide) rfl

private def ps77 : List ℕ := 389::ps76
private theorem c77 : F ps76 71995244=6773610 := by decide +kernel
private theorem v77 : F ps77 28006150079=2612719947 :=
  takeStep (p:=389) (by decide) v76 c77 rfl (by decide) (by decide) rfl

private def ps78 : List ℕ := 397::ps77
private theorem c78 : F ps77 70544458=6620994 := by decide +kernel
private theorem v78 : F ps78 28006150079=2606098953 :=
  takeStep (p:=397) (by decide) v77 c78 rfl (by decide) (by decide) rfl

private def ps79 : List ℕ := 401::ps78
private theorem c79 : F ps78 69840773=6539137 := by decide +kernel
private theorem v79 : F ps79 28006150079=2599559816 :=
  takeStep (p:=401) (by decide) v78 c79 rfl (by decide) (by decide) rfl

private def ps80 : List ℕ := 409::ps79
private theorem c80 : F ps79 68474694=6395895 := by decide +kernel
private theorem v80 : F ps80 28006150079=2593163921 :=
  takeStep (p:=409) (by decide) v79 c80 rfl (by decide) (by decide) rfl

private def ps81 : List ℕ := 419::ps80
private theorem c81 : F ps80 66840453=6228506 := by decide +kernel
private theorem v81 : F ps81 28006150079=2586935415 :=
  takeStep (p:=419) (by decide) v80 c81 rfl (by decide) (by decide) rfl

private def ps82 : List ℕ := 421::ps81
private theorem c82 : F ps81 66522921=6184478 := by decide +kernel
private theorem v82 : F ps82 28006150079=2580750937 :=
  takeStep (p:=421) (by decide) v81 c82 rfl (by decide) (by decide) rfl

private def ps83 : List ℕ := 431::ps82
private theorem c83 : F ps82 64979466=6026834 := by decide +kernel
private theorem v83 : F ps83 28006150079=2574724103 :=
  takeStep (p:=431) (by decide) v82 c83 rfl (by decide) (by decide) rfl

private def ps84 : List ℕ := 433::ps83
private theorem c84 : F ps83 64679330=5985251 := by decide +kernel
private theorem v84 : F ps84 28006150079=2568738852 :=
  takeStep (p:=433) (by decide) v83 c84 rfl (by decide) (by decide) rfl

private def ps85 : List ℕ := 439::ps84
private theorem c85 : F ps84 63795330=5889965 := by decide +kernel
private theorem v85 : F ps85 28006150079=2562848887 :=
  takeStep (p:=439) (by decide) v84 c85 rfl (by decide) (by decide) rfl

private def ps86 : List ℕ := 443::ps85
private theorem c86 : F ps85 63219300=5823527 := by decide +kernel
private theorem v86 : F ps86 28006150079=2557025360 :=
  takeStep (p:=443) (by decide) v85 c86 rfl (by decide) (by decide) rfl

private def ps87 : List ℕ := 449::ps86
private theorem c87 : F ps86 62374499=5732649 := by decide +kernel
private theorem v87 : F ps87 28006150079=2551292711 :=
  takeStep (p:=449) (by decide) v86 c87 rfl (by decide) (by decide) rfl

private def ps88 : List ℕ := 457::ps87
private theorem c88 : F ps87 61282604=5619631 := by decide +kernel
private theorem v88 : F ps88 28006150079=2545673080 :=
  takeStep (p:=457) (by decide) v87 c88 rfl (by decide) (by decide) rfl

private def ps89 : List ℕ := 461::ps88
private theorem c89 : F ps88 60750867=5558480 := by decide +kernel
private theorem v89 : F ps89 28006150079=2540114600 :=
  takeStep (p:=461) (by decide) v88 c89 rfl (by decide) (by decide) rfl

private def ps90 : List ℕ := 463::ps89
private theorem c90 : F ps89 60488445=5522271 := by decide +kernel
private theorem v90 : F ps90 28006150079=2534592329 :=
  takeStep (p:=463) (by decide) v89 c90 rfl (by decide) (by decide) rfl

private def ps91 : List ℕ := 467::ps90
private theorem c91 : F ps90 59970342=5462821 := by decide +kernel
private theorem v91 : F ps91 28006150079=2529129508 :=
  takeStep (p:=467) (by decide) v90 c91 rfl (by decide) (by decide) rfl

private def ps92 : List ℕ := 479::ps91
private theorem c92 : F ps91 58467954=5314108 := by decide +kernel
private theorem v92 : F ps92 28006150079=2523815400 :=
  takeStep (p:=479) (by decide) v91 c92 rfl (by decide) (by decide) rfl

private def ps93 : List ℕ := 487::ps92
private theorem c93 : F ps92 57507495=5215419 := by decide +kernel
private theorem v93 : F ps93 28006150079=2518599981 :=
  takeStep (p:=487) (by decide) v92 c93 rfl (by decide) (by decide) rfl

private def ps94 : List ℕ := 491::ps93
private theorem c94 : F ps93 57039002=5161899 := by decide +kernel
private theorem v94 : F ps94 28006150079=2513438082 :=
  takeStep (p:=491) (by decide) v93 c94 rfl (by decide) (by decide) rfl

private def ps95 : List ℕ := 499::ps94
private theorem c95 : F ps94 56124549=5068205 := by decide +kernel
private theorem v95 : F ps95 28006150079=2508369877 :=
  takeStep (p:=499) (by decide) v94 c95 rfl (by decide) (by decide) rfl

private def ps96 : List ℕ := 503::ps95
private theorem c96 : F ps95 55678230=5017298 := by decide +kernel
private theorem v96 : F ps96 28006150079=2503352579 :=
  takeStep (p:=503) (by decide) v95 c96 rfl (by decide) (by decide) rfl

private def ps97 : List ℕ := 509::ps96
private theorem c97 : F ps96 55021905=4947645 := by decide +kernel
private theorem v97 : F ps97 28006150079=2498404934 :=
  takeStep (p:=509) (by decide) v96 c97 rfl (by decide) (by decide) rfl

private def ps98 : List ℕ := 521::ps97
private theorem c98 : F ps97 53754606=4823367 := by decide +kernel
private theorem v98 : F ps98 28006150079=2493581567 :=
  takeStep (p:=521) (by decide) v97 c98 rfl (by decide) (by decide) rfl

private def ps99 : List ℕ := 523::ps98
private theorem c99 : F ps98 53549044=4795130 := by decide +kernel
private theorem v99 : F ps99 28006150079=2488786437 :=
  takeStep (p:=523) (by decide) v98 c99 rfl (by decide) (by decide) rfl

private def ps100 : List ℕ := 541::ps99
private theorem c100 : F ps99 51767375=4625563 := by decide +kernel
private theorem v100 : F ps100 28006150079=2484160874 :=
  takeStep (p:=541) (by decide) v99 c100 rfl (by decide) (by decide) rfl

private def ps101 : List ℕ := 547::ps100
private theorem c101 : F ps100 51199543=4565581 := by decide +kernel
private theorem v101 : F ps101 28006150079=2479595293 :=
  takeStep (p:=547) (by decide) v100 c101 rfl (by decide) (by decide) rfl

private def ps102 : List ℕ := 557::ps101
private theorem c102 : F ps101 50280341=4474483 := by decide +kernel
private theorem v102 : F ps102 28006150079=2475120810 :=
  takeStep (p:=557) (by decide) v101 c102 rfl (by decide) (by decide) rfl

private def ps103 : List ℕ := 563::ps102
private theorem c103 : F ps102 49744493=4418008 := by decide +kernel
private theorem v103 : F ps103 28006150079=2470702802 :=
  takeStep (p:=563) (by decide) v102 c103 rfl (by decide) (by decide) rfl

private def ps104 : List ℕ := 569::ps103
private theorem c104 : F ps103 49219947=4362790 := by decide +kernel
private theorem v104 : F ps104 28006150079=2466340012 :=
  takeStep (p:=569) (by decide) v103 c104 rfl (by decide) (by decide) rfl

private def ps105 : List ℕ := 571::ps104
private theorem c105 : F ps104 49047548=4339115 := by decide +kernel
private theorem v105 : F ps105 28006150079=2462000897 :=
  takeStep (p:=571) (by decide) v104 c105 rfl (by decide) (by decide) rfl

private def ps106 : List ℕ := 577::ps105
private theorem c106 : F ps105 48537521=4285600 := by decide +kernel
private theorem v106 : F ps106 28006150079=2457715297 :=
  takeStep (p:=577) (by decide) v105 c106 rfl (by decide) (by decide) rfl

private def ps107 : List ℕ := 587::ps106
private theorem c107 : F ps106 47710647=4204215 := by decide +kernel
private theorem v107 : F ps107 28006150079=2453511082 :=
  takeStep (p:=587) (by decide) v106 c107 rfl (by decide) (by decide) rfl

private def ps108 : List ℕ := 593::ps107
private theorem c108 : F ps107 47227909=4153747 := by decide +kernel
private theorem v108 : F ps108 28006150079=2449357335 :=
  takeStep (p:=593) (by decide) v107 c108 rfl (by decide) (by decide) rfl

private def ps109 : List ℕ := 599::ps108
private theorem c109 : F ps108 46754841=4104246 := by decide +kernel
private theorem v109 : F ps109 28006150079=2445253089 :=
  takeStep (p:=599) (by decide) v108 c109 rfl (by decide) (by decide) rfl

private def ps110 : List ℕ := 601::ps109
private theorem c110 : F ps109 46599251=4082930 := by decide +kernel
private theorem v110 : F ps110 28006150079=2441170159 :=
  takeStep (p:=601) (by decide) v109 c110 rfl (by decide) (by decide) rfl

private def ps111 : List ℕ := 607::ps110
private theorem c111 : F ps110 46138632=4034904 := by decide +kernel
private theorem v111 : F ps111 28006150079=2437135255 :=
  takeStep (p:=607) (by decide) v110 c111 rfl (by decide) (by decide) rfl

private def ps112 : List ℕ := 613::ps111
private theorem c112 : F ps111 45687031=3987840 := by decide +kernel
private theorem v112 : F ps112 28006150079=2433147415 :=
  takeStep (p:=613) (by decide) v111 c112 rfl (by decide) (by decide) rfl

private def ps113 : List ℕ := 617::ps112
private theorem c113 : F ps112 45390842=3954577 := by decide +kernel
private theorem v113 : F ps113 28006150079=2429192838 :=
  takeStep (p:=617) (by decide) v112 c113 rfl (by decide) (by decide) rfl

private def ps114 : List ℕ := 619::ps113
private theorem c114 : F ps113 45244184=3934553 := by decide +kernel
private theorem v114 : F ps114 28006150079=2425258285 :=
  takeStep (p:=619) (by decide) v113 c114 rfl (by decide) (by decide) rfl

private def ps115 : List ℕ := 631::ps114
private theorem c115 : F ps114 44383756=3852147 := by decide +kernel
private theorem v115 : F ps115 28006150079=2421406138 :=
  takeStep (p:=631) (by decide) v114 c115 rfl (by decide) (by decide) rfl

private def ps116 : List ℕ := 641::ps115
private theorem c116 : F ps115 43691341=3784858 := by decide +kernel
private theorem v116 : F ps116 28006150079=2417621280 :=
  takeStep (p:=641) (by decide) v115 c116 rfl (by decide) (by decide) rfl

private def ps117 : List ℕ := 643::ps116
private theorem c117 : F ps116 43555443=3766396 := by decide +kernel
private theorem v117 : F ps117 28006150079=2413854884 :=
  takeStep (p:=643) (by decide) v116 c117 rfl (by decide) (by decide) rfl

private def ps118 : List ℕ := 647::ps117
private theorem c118 : F ps117 43286167=3736300 := by decide +kernel
private theorem v118 : F ps118 28006150079=2410118584 :=
  takeStep (p:=647) (by decide) v117 c118 rfl (by decide) (by decide) rfl

private def ps119 : List ℕ := 653::ps118
private theorem c119 : F ps118 42888438=3695191 := by decide +kernel
private theorem v119 : F ps119 28006150079=2406423393 :=
  takeStep (p:=653) (by decide) v118 c119 rfl (by decide) (by decide) rfl

private def ps120 : List ℕ := 659::ps119
private theorem c120 : F ps119 42497951=3654931 := by decide +kernel
private theorem v120 : F ps120 28006150079=2402768462 :=
  takeStep (p:=659) (by decide) v119 c120 rfl (by decide) (by decide) rfl

private def ps121 : List ℕ := 661::ps120
private theorem c121 : F ps120 42369364=3637468 := by decide +kernel
private theorem v121 : F ps121 28006150079=2399130994 :=
  takeStep (p:=661) (by decide) v120 c121 rfl (by decide) (by decide) rfl

private def ps122 : List ℕ := 673::ps121
private theorem c122 : F ps121 41613893=3565794 := by decide +kernel
private theorem v122 : F ps122 28006150079=2395565200 :=
  takeStep (p:=673) (by decide) v121 c122 rfl (by decide) (by decide) rfl

private def ps123 : List ℕ := 677::ps122
private theorem c123 : F ps122 41368020=3538527 := by decide +kernel
private theorem v123 : F ps123 28006150079=2392026673 :=
  takeStep (p:=677) (by decide) v122 c123 rfl (by decide) (by decide) rfl

private def ps124 : List ℕ := 683::ps123
private theorem c124 : F ps123 41004612=3501114 := by decide +kernel
private theorem v124 : F ps124 28006150079=2388525559 :=
  takeStep (p:=683) (by decide) v123 c124 rfl (by decide) (by decide) rfl

private def ps125 : List ℕ := 691::ps124
private theorem c125 : F ps124 40529884=3454321 := by decide +kernel
private theorem v125 : F ps125 28006150079=2385071238 :=
  takeStep (p:=691) (by decide) v124 c125 rfl (by decide) (by decide) rfl

private def ps126 : List ℕ := 701::ps125
private theorem c126 : F ps125 39951711=3398814 := by decide +kernel
private theorem v126 : F ps126 28006150079=2381672424 :=
  takeStep (p:=701) (by decide) v125 c126 rfl (by decide) (by decide) rfl

private def ps127 : List ℕ := 709::ps126
private theorem c127 : F ps126 39500916=3354485 := by decide +kernel
private theorem v127 : F ps127 28006150079=2378317939 :=
  takeStep (p:=709) (by decide) v126 c127 rfl (by decide) (by decide) rfl

private def ps128 : List ℕ := 719::ps127
private theorem c128 : F ps127 38951530=3301873 := by decide +kernel
private theorem v128 : F ps128 28006150079=2375016066 :=
  takeStep (p:=719) (by decide) v127 c128 rfl (by decide) (by decide) rfl

private def ps129 : List ℕ := 727::ps128
private theorem c129 : F ps128 38522902=3259787 := by decide +kernel
private theorem v129 : F ps129 28006150079=2371756279 :=
  takeStep (p:=727) (by decide) v128 c129 rfl (by decide) (by decide) rfl

private def ps130 : List ℕ := 733::ps129
private theorem c130 : F ps129 38207571=3227551 := by decide +kernel
private theorem v130 : F ps130 28006150079=2368528728 :=
  takeStep (p:=733) (by decide) v129 c130 rfl (by decide) (by decide) rfl

private def ps131 : List ℕ := 739::ps130
private theorem c131 : F ps130 37897361=3195864 := by decide +kernel
private theorem v131 : F ps131 28006150079=2365332864 :=
  takeStep (p:=739) (by decide) v130 c131 rfl (by decide) (by decide) rfl

private def ps132 : List ℕ := 743::ps131
private theorem c132 : F ps131 37693337=3173391 := by decide +kernel
private theorem v132 : F ps132 28006150079=2362159473 :=
  takeStep (p:=743) (by decide) v131 c132 rfl (by decide) (by decide) rfl

private def ps133 : List ℕ := 751::ps132
private theorem c133 : F ps132 37291811=3134177 := by decide +kernel
private theorem v133 : F ps133 28006150079=2359025296 :=
  takeStep (p:=751) (by decide) v132 c133 rfl (by decide) (by decide) rfl

private def ps134 : List ℕ := 757::ps133
private theorem c134 : F ps133 36996235=3104091 := by decide +kernel
private theorem v134 : F ps134 28006150079=2355921205 :=
  takeStep (p:=757) (by decide) v133 c134 rfl (by decide) (by decide) rfl

private def ps135 : List ℕ := 761::ps134
private theorem c135 : F ps134 36801774=3082746 := by decide +kernel
private theorem v135 : F ps135 28006150079=2352838459 :=
  takeStep (p:=761) (by decide) v134 c135 rfl (by decide) (by decide) rfl

private def ps136 : List ℕ := 769::ps135
private theorem c136 : F ps135 36418920=3045494 := by decide +kernel
private theorem v136 : F ps136 28006150079=2349792965 :=
  takeStep (p:=769) (by decide) v135 c136 rfl (by decide) (by decide) rfl

private def ps137 : List ℕ := 773::ps136
private theorem c137 : F ps136 36230465=3024799 := by decide +kernel
private theorem v137 : F ps137 28006150079=2346768166 :=
  takeStep (p:=773) (by decide) v136 c137 rfl (by decide) (by decide) rfl

private def ps138 : List ℕ := 787::ps137
private theorem c138 : F ps137 35585959=2965712 := by decide +kernel
private theorem v138 : F ps138 28006150079=2343802454 :=
  takeStep (p:=787) (by decide) v137 c138 rfl (by decide) (by decide) rfl

private def ps139 : List ℕ := 797::ps138
private theorem c139 : F ps138 35139460=2923520 := by decide +kernel
private theorem v139 : F ps139 28006150079=2340878934 :=
  takeStep (p:=797) (by decide) v138 c139 rfl (by decide) (by decide) rfl

private def ps140 : List ℕ := 809::ps139
private theorem c140 : F ps139 34618232=2875260 := by decide +kernel
private theorem v140 : F ps140 28006150079=2338003674 :=
  takeStep (p:=809) (by decide) v139 c140 rfl (by decide) (by decide) rfl

private def ps141 : List ℕ := 811::ps140
private theorem c141 : F ps140 34532860=2863757 := by decide +kernel
private theorem v141 : F ps141 28006150079=2335139917 :=
  takeStep (p:=811) (by decide) v140 c141 rfl (by decide) (by decide) rfl

private def ps142 : List ℕ := 821::ps141
private theorem c142 : F ps141 34112241=2824202 := by decide +kernel
private theorem v142 : F ps142 28006150079=2332315715 :=
  takeStep (p:=821) (by decide) v141 c142 rfl (by decide) (by decide) rfl

private def ps143 : List ℕ := 823::ps142
private theorem c143 : F ps142 34029343=2813039 := by decide +kernel
private theorem v143 : F ps143 28006150079=2329502676 :=
  takeStep (p:=823) (by decide) v142 c143 rfl (by decide) (by decide) rfl

private def ps144 : List ℕ := 827::ps143
private theorem c144 : F ps143 33864752=2795138 := by decide +kernel
private theorem v144 : F ps144 28006150079=2326707538 :=
  takeStep (p:=827) (by decide) v143 c144 rfl (by decide) (by decide) rfl

private def ps145 : List ℕ := 829::ps144
private theorem c145 : F ps144 33783051=2784173 := by decide +kernel
private theorem v145 : F ps145 28006150079=2323923365 :=
  takeStep (p:=829) (by decide) v144 c145 rfl (by decide) (by decide) rfl

private def ps146 : List ℕ := 839::ps145
private theorem c146 : F ps145 33380393=2746438 := by decide +kernel
private theorem v146 : F ps146 28006150079=2321176927 :=
  takeStep (p:=839) (by decide) v145 c146 rfl (by decide) (by decide) rfl

private def ps147 : List ℕ := 853::ps146
private theorem c147 : F ps146 32832532=2696694 := by decide +kernel
private theorem v147 : F ps147 28006150079=2318480233 :=
  takeStep (p:=853) (by decide) v146 c147 rfl (by decide) (by decide) rfl

private def ps148 : List ℕ := 857::ps147
private theorem c148 : F ps147 32679288=2680053 := by decide +kernel
private theorem v148 : F ps148 28006150079=2315800180 :=
  takeStep (p:=857) (by decide) v147 c148 rfl (by decide) (by decide) rfl

private def ps149 : List ℕ := 859::ps148
private theorem c149 : F ps148 32603201=2669864 := by decide +kernel
private theorem v149 : F ps149 28006150079=2313130316 :=
  takeStep (p:=859) (by decide) v148 c149 rfl (by decide) (by decide) rfl

private def ps150 : List ℕ := 863::ps149
private theorem c150 : F ps149 32452085=2653413 := by decide +kernel
private theorem v150 : F ps150 28006150079=2310476903 :=
  takeStep (p:=863) (by decide) v149 c150 rfl (by decide) (by decide) rfl

private def ps151 : List ℕ := 877::ps150
private theorem c151 : F ps150 31934036=2606695 := by decide +kernel
private theorem v151 : F ps151 28006150079=2307870208 :=
  takeStep (p:=877) (by decide) v150 c151 rfl (by decide) (by decide) rfl

private def ps152 : List ℕ := 881::ps151
private theorem c152 : F ps151 31789046=2590959 := by decide +kernel
private theorem v152 : F ps152 28006150079=2305279249 :=
  takeStep (p:=881) (by decide) v151 c152 rfl (by decide) (by decide) rfl

private def ps153 : List ℕ := 883::ps152
private theorem c153 : F ps152 31717044=2581344 := by decide +kernel
private theorem v153 : F ps153 28006150079=2302697905 :=
  takeStep (p:=883) (by decide) v152 c153 rfl (by decide) (by decide) rfl

private def ps154 : List ℕ := 887::ps153
private theorem c154 : F ps153 31574013=2565882 := by decide +kernel
private theorem v154 : F ps154 28006150079=2300132023 :=
  takeStep (p:=887) (by decide) v153 c154 rfl (by decide) (by decide) rfl

private def ps155 : List ℕ := 907::ps154
private theorem c155 : F ps154 30877783=2504946 := by decide +kernel
private theorem v155 : F ps155 28006150079=2297627077 :=
  takeStep (p:=907) (by decide) v154 c155 rfl (by decide) (by decide) rfl

private def ps156 : List ℕ := 911::ps155
private theorem c156 : F ps155 30742206=2490304 := by decide +kernel
private theorem v156 : F ps156 28006150079=2295136773 :=
  takeStep (p:=911) (by decide) v155 c156 rfl (by decide) (by decide) rfl

private def ps157 : List ℕ := 919::ps156
private theorem c157 : F ps156 30474592=2464764 := by decide +kernel
private theorem v157 : F ps157 28006150079=2292672009 :=
  takeStep (p:=919) (by decide) v156 c157 rfl (by decide) (by decide) rfl

private def ps158 : List ℕ := 929::ps157
private theorem c158 : F ps157 30146555=2434482 := by decide +kernel
private theorem v158 : F ps158 28006150079=2290237527 :=
  takeStep (p:=929) (by decide) v157 c158 rfl (by decide) (by decide) rfl

private def ps159 : List ℕ := 937::ps158
private theorem c159 : F ps158 29889167=2410010 := by decide +kernel
private theorem v159 : F ps159 28006150079=2287827517 :=
  takeStep (p:=937) (by decide) v158 c159 rfl (by decide) (by decide) rfl

private def ps160 : List ℕ := 941::ps159
private theorem c160 : F ps159 29762114=2396329 := by decide +kernel
private theorem v160 : F ps160 28006150079=2285431188 :=
  takeStep (p:=941) (by decide) v159 c160 rfl (by decide) (by decide) rfl

private def ps161 : List ℕ := 947::ps160
private theorem c161 : F ps160 29573548=2377633 := by decide +kernel
private theorem v161 : F ps161 28006150079=2283053555 :=
  takeStep (p:=947) (by decide) v160 c161 rfl (by decide) (by decide) rfl

private def ps162 : List ℕ := 953::ps161
private theorem c162 : F ps161 29387355=2359303 := by decide +kernel
private theorem v162 : F ps162 28006150079=2280694252 :=
  takeStep (p:=953) (by decide) v161 c162 rfl (by decide) (by decide) rfl

private def ps163 : List ℕ := 967::ps162
private theorem c163 : F ps162 28961892=2321428 := by decide +kernel
private theorem v163 : F ps163 28006150079=2278372824 :=
  takeStep (p:=967) (by decide) v162 c163 rfl (by decide) (by decide) rfl

private def ps164 : List ℕ := 971::ps163
private theorem c164 : F ps163 28842585=2308616 := by decide +kernel
private theorem v164 : F ps164 28006150079=2276064208 :=
  takeStep (p:=971) (by decide) v163 c164 rfl (by decide) (by decide) rfl

private def ps165 : List ℕ := 977::ps164
private theorem c165 : F ps164 28665455=2291186 := by decide +kernel
private theorem v165 : F ps165 28006150079=2273773022 :=
  takeStep (p:=977) (by decide) v164 c165 rfl (by decide) (by decide) rfl

private def ps166 : List ℕ := 983::ps165
private theorem c166 : F ps165 28490488=2273933 := by decide +kernel
private theorem v166 : F ps166 28006150079=2271499089 :=
  takeStep (p:=983) (by decide) v165 c166 rfl (by decide) (by decide) rfl

private def ps167 : List ℕ := 991::ps166
private theorem c167 : F ps166 28260494=2252308 := by decide +kernel
private theorem v167 : F ps167 28006150079=2269246781 :=
  takeStep (p:=991) (by decide) v166 c167 rfl (by decide) (by decide) rfl

private def ps168 : List ℕ := 997::ps167
private theorem c168 : F ps167 28090421=2235592 := by decide +kernel
private theorem v168 : F ps168 28006150079=2267011189 :=
  takeStep (p:=997) (by decide) v167 c168 rfl (by decide) (by decide) rfl

private def ps169 : List ℕ := 1009::ps168
private theorem c169 : F ps168 27756342=2205672 := by decide +kernel
private theorem v169 : F ps169 28006150079=2264805517 :=
  takeStep (p:=1009) (by decide) v168 c169 rfl (by decide) (by decide) rfl

private def ps170 : List ℕ := 1013::ps169
private theorem c170 : F ps169 27646742=2193979 := by decide +kernel
private theorem v170 : F ps170 28006150079=2262611538 :=
  takeStep (p:=1013) (by decide) v169 c170 rfl (by decide) (by decide) rfl

private def ps171 : List ℕ := 1019::ps170
private theorem c171 : F ps170 27483954=2177998 := by decide +kernel
private theorem v171 : F ps171 28006150079=2260433540 :=
  takeStep (p:=1019) (by decide) v170 c171 rfl (by decide) (by decide) rfl

private def ps172 : List ℕ := 1021::ps171
private theorem c172 : F ps171 27430117=2170871 := by decide +kernel
private theorem v172 : F ps172 28006150079=2258262669 :=
  takeStep (p:=1021) (by decide) v171 c172 rfl (by decide) (by decide) rfl

private def ps173 : List ℕ := 1031::ps172
private theorem c173 : F ps172 27164064=2146749 := by decide +kernel
private theorem v173 : F ps173 28006150079=2256115920 :=
  takeStep (p:=1031) (by decide) v172 c173 rfl (by decide) (by decide) rfl

private def ps174 : List ℕ := 1033::ps173
private theorem c174 : F ps173 27111471=2139778 := by decide +kernel
private theorem v174 : F ps174 28006150079=2253976142 :=
  takeStep (p:=1033) (by decide) v173 c174 rfl (by decide) (by decide) rfl

private def ps175 : List ℕ := 1039::ps174
private theorem c175 : F ps174 26954908=2124492 := by decide +kernel
private theorem v175 : F ps175 28006150079=2251851650 :=
  takeStep (p:=1039) (by decide) v174 c175 rfl (by decide) (by decide) rfl

private def ps176 : List ℕ := 1049::ps175
private theorem c176 : F ps175 26697950=2101228 := by decide +kernel
private theorem v176 : F ps176 28006150079=2249750422 :=
  takeStep (p:=1049) (by decide) v175 c176 rfl (by decide) (by decide) rfl

private def ps177 : List ℕ := 1051::ps176
private theorem c177 : F ps176 26647145=2094535 := by decide +kernel
private theorem v177 : F ps177 28006150079=2247655887 :=
  takeStep (p:=1051) (by decide) v176 c177 rfl (by decide) (by decide) rfl

private def ps178 : List ℕ := 1061::ps177
private theorem c178 : F ps177 26395994=2071770 := by decide +kernel
private theorem v178 : F ps178 28006150079=2245584117 :=
  takeStep (p:=1061) (by decide) v177 c178 rfl (by decide) (by decide) rfl

private def ps179 : List ℕ := 1063::ps178
private theorem c179 : F ps178 26346331=2065236 := by decide +kernel
private theorem v179 : F ps179 28006150079=2243518881 :=
  takeStep (p:=1063) (by decide) v178 c179 rfl (by decide) (by decide) rfl

private def ps180 : List ℕ := 1069::ps179
private theorem c180 : F ps179 26198456=2050835 := by decide +kernel
private theorem v180 : F ps180 28006150079=2241468046 :=
  takeStep (p:=1069) (by decide) v179 c180 rfl (by decide) (by decide) rfl

private def ps181 : List ℕ := 1087::ps180
private theorem c181 : F ps180 25764627=2013687 := by decide +kernel
private theorem v181 : F ps181 28006150079=2239454359 :=
  takeStep (p:=1087) (by decide) v180 c181 rfl (by decide) (by decide) rfl

private def ps182 : List ℕ := 1091::ps181
private theorem c182 : F ps181 25670165=2003701 := by decide +kernel
private theorem v182 : F ps182 28006150079=2237450658 :=
  takeStep (p:=1091) (by decide) v181 c182 rfl (by decide) (by decide) rfl

private def ps183 : List ℕ := 1093::ps182
private theorem c183 : F ps182 25623193=1997538 := by decide +kernel
private theorem v183 : F ps183 28006150079=2235453120 :=
  takeStep (p:=1093) (by decide) v182 c183 rfl (by decide) (by decide) rfl

private def ps184 : List ℕ := 1097::ps183
private theorem c184 : F ps183 25529763=1987663 := by decide +kernel
private theorem v184 : F ps184 28006150079=2233465457 :=
  takeStep (p:=1097) (by decide) v183 c184 rfl (by decide) (by decide) rfl

private def ps185 : List ℕ := 1103::ps184
private theorem c185 : F ps184 25390888=1974261 := by decide +kernel
private theorem v185 : F ps185 28006150079=2231491196 :=
  takeStep (p:=1103) (by decide) v184 c185 rfl (by decide) (by decide) rfl

private def ps186 : List ℕ := 1109::ps185
private theorem c186 : F ps185 25253516=1960980 := by decide +kernel
private theorem v186 : F ps186 28006150079=2229530216 :=
  takeStep (p:=1109) (by decide) v185 c186 rfl (by decide) (by decide) rfl

private def ps187 : List ℕ := 1117::ps186
private theorem c187 : F ps186 25072650=1944403 := by decide +kernel
private theorem v187 : F ps187 28006150079=2227585813 :=
  takeStep (p:=1117) (by decide) v186 c187 rfl (by decide) (by decide) rfl

private def ps188 : List ℕ := 1123::ps187
private theorem c188 : F ps187 24938691=1931458 := by decide +kernel
private theorem v188 : F ps188 28006150079=2225654355 :=
  takeStep (p:=1123) (by decide) v187 c188 rfl (by decide) (by decide) rfl

private def ps189 : List ℕ := 1129::ps188
private theorem c189 : F ps188 24806155=1918735 := by decide +kernel
private theorem v189 : F ps189 28006150079=2223735620 :=
  takeStep (p:=1129) (by decide) v188 c189 rfl (by decide) (by decide) rfl

private def ps190 : List ℕ := 1151::ps189
private theorem c190 : F ps189 24332015=1879112 := by decide +kernel
private theorem v190 : F ps190 28006150079=2221856508 :=
  takeStep (p:=1151) (by decide) v189 c190 rfl (by decide) (by decide) rfl

private def ps191 : List ℕ := 1153::ps190
private theorem c191 : F ps190 24289809=1873608 := by decide +kernel
private theorem v191 : F ps191 28006150079=2219982900 :=
  takeStep (p:=1153) (by decide) v190 c191 rfl (by decide) (by decide) rfl

private def ps192 : List ℕ := 1163::ps191
private theorem c192 : F ps191 24080954=1854988 := by decide +kernel
private theorem v192 : F ps192 28006150079=2218127912 :=
  takeStep (p:=1163) (by decide) v191 c192 rfl (by decide) (by decide) rfl

private def ps193 : List ℕ := 1171::ps192
private theorem c193 : F ps192 23916439=1839922 := by decide +kernel
private theorem v193 : F ps193 28006150079=2216287990 :=
  takeStep (p:=1171) (by decide) v192 c193 rfl (by decide) (by decide) rfl

private def ps194 : List ℕ := 1181::ps193
private theorem c194 : F ps193 23713928=1821938 := by decide +kernel
private theorem v194 : F ps194 28006150079=2214466052 :=
  takeStep (p:=1181) (by decide) v193 c194 rfl (by decide) (by decide) rfl

private def ps195 : List ℕ := 1187::ps194
private theorem c195 : F ps194 23594060=1810465 := by decide +kernel
private theorem v195 : F ps195 28006150079=2212655587 :=
  takeStep (p:=1187) (by decide) v194 c195 rfl (by decide) (by decide) rfl

private def ps196 : List ℕ := 1193::ps195
private theorem c196 : F ps195 23475398=1799161 := by decide +kernel
private theorem v196 : F ps196 28006150079=2210856426 :=
  takeStep (p:=1193) (by decide) v195 c196 rfl (by decide) (by decide) rfl

private def ps197 : List ℕ := 1201::ps196
private theorem c197 : F ps196 23319025=1784894 := by decide +kernel
private theorem v197 : F ps197 28006150079=2209071532 :=
  takeStep (p:=1201) (by decide) v196 c197 rfl (by decide) (by decide) rfl

private def ps198 : List ℕ := 1213::ps197
private theorem c198 : F ps197 23088334=1764865 := by decide +kernel
private theorem v198 : F ps198 28006150079=2207306667 :=
  takeStep (p:=1213) (by decide) v197 c198 rfl (by decide) (by decide) rfl

private def ps199 : List ℕ := 1217::ps198
private theorem c199 : F ps198 23012448=1756995 := by decide +kernel
private theorem v199 : F ps199 28006150079=2205549672 :=
  takeStep (p:=1217) (by decide) v198 c199 rfl (by decide) (by decide) rfl

private def ps200 : List ℕ := 1223::ps199
private theorem c200 : F ps199 22899550=1746243 := by decide +kernel
private theorem v200 : F ps200 28006150079=2203803429 :=
  takeStep (p:=1223) (by decide) v199 c200 rfl (by decide) (by decide) rfl

private def ps201 : List ℕ := 1229::ps200
private theorem c201 : F ps200 22787754=1735588 := by decide +kernel
private theorem v201 : F ps201 28006150079=2202067841 :=
  takeStep (p:=1229) (by decide) v200 c201 rfl (by decide) (by decide) rfl

private def ps202 : List ℕ := 1231::ps201
private theorem c202 : F ps201 22750731=1730810 := by decide +kernel
private theorem v202 : F ps202 28006150079=2200337031 :=
  takeStep (p:=1231) (by decide) v201 c202 rfl (by decide) (by decide) rfl

private def ps203 : List ℕ := 1237::ps202
private theorem c203 : F ps202 22640380=1720309 := by decide +kernel
private theorem v203 : F ps203 28006150079=2198616722 :=
  takeStep (p:=1237) (by decide) v202 c203 rfl (by decide) (by decide) rfl

private def ps204 : List ℕ := 1249::ps203
private theorem c204 : F ps203 22422858=1701521 := by decide +kernel
private theorem v204 : F ps204 28006150079=2196915201 :=
  takeStep (p:=1249) (by decide) v203 c204 rfl (by decide) (by decide) rfl

private def ps205 : List ℕ := 1259::ps204
private theorem c205 : F ps204 22244757=1685887 := by decide +kernel
private theorem v205 : F ps205 28006150079=2195229314 :=
  takeStep (p:=1259) (by decide) v204 c205 rfl (by decide) (by decide) rfl

private def ps206 : List ℕ := 1277::ps205
private theorem c206 : F ps205 21931206=1659871 := by decide +kernel
private theorem v206 : F ps206 28006150079=2193569443 :=
  takeStep (p:=1277) (by decide) v205 c206 rfl (by decide) (by decide) rfl

private def ps207 : List ℕ := 1279::ps206
private theorem c207 : F ps206 21896911=1655435 := by decide +kernel
private theorem v207 : F ps207 28006150079=2191914008 :=
  takeStep (p:=1279) (by decide) v206 c207 rfl (by decide) (by decide) rfl

private def ps208 : List ℕ := 1283::ps207
private theorem c208 : F ps207 21828643=1648415 := by decide +kernel
private theorem v208 : F ps208 28006150079=2190265593 :=
  takeStep (p:=1283) (by decide) v207 c208 rfl (by decide) (by decide) rfl

private def ps209 : List ℕ := 1289::ps208
private theorem c209 : F ps208 21727036=1638799 := by decide +kernel
private theorem v209 : F ps209 28006150079=2188626794 :=
  takeStep (p:=1289) (by decide) v208 c209 rfl (by decide) (by decide) rfl

private def ps210 : List ℕ := 1291::ps209
private theorem c210 : F ps209 21693377=1634471 := by decide +kernel
private theorem v210 : F ps210 28006150079=2186992323 :=
  takeStep (p:=1291) (by decide) v209 c210 rfl (by decide) (by decide) rfl

private def ps211 : List ℕ := 1297::ps210
private theorem c211 : F ps210 21593022=1625024 := by decide +kernel
private theorem v211 : F ps211 28006150079=2185367299 :=
  takeStep (p:=1297) (by decide) v210 c211 rfl (by decide) (by decide) rfl

private def ps212 : List ℕ := 1301::ps211
private theorem c212 : F ps211 21526633=1618214 := by decide +kernel
private theorem v212 : F ps212 28006150079=2183749085 :=
  takeStep (p:=1301) (by decide) v211 c212 rfl (by decide) (by decide) rfl

private def ps213 : List ℕ := 1303::ps212
private theorem c213 : F ps212 21493591=1614000 := by decide +kernel
private theorem v213 : F ps213 28006150079=2182135085 :=
  takeStep (p:=1303) (by decide) v212 c213 rfl (by decide) (by decide) rfl

private def ps214 : List ℕ := 1307::ps213
private theorem c214 : F ps213 21427811=1607209 := by decide +kernel
private theorem v214 : F ps214 28006150079=2180527876 :=
  takeStep (p:=1307) (by decide) v213 c214 rfl (by decide) (by decide) rfl

private def ps215 : List ℕ := 1319::ps214
private theorem c215 : F ps214 21232865=1590587 := by decide +kernel
private theorem v215 : F ps215 28006150079=2178937289 :=
  takeStep (p:=1319) (by decide) v214 c215 rfl (by decide) (by decide) rfl

private def ps216 : List ℕ := 1321::ps215
private theorem c216 : F ps215 21200719=1586485 := by decide +kernel
private theorem v216 : F ps216 28006150079=2177350804 :=
  takeStep (p:=1321) (by decide) v215 c216 rfl (by decide) (by decide) rfl

private def ps217 : List ℕ := 1327::ps216
private theorem c217 : F ps216 21104860=1577530 := by decide +kernel
private theorem v217 : F ps217 28006150079=2175773274 :=
  takeStep (p:=1327) (by decide) v216 c217 rfl (by decide) (by decide) rfl

private def ps218 : List ℕ := 1361::ps217
private theorem c218 : F ps217 20577626=1535647 := by decide +kernel
private theorem v218 : F ps218 28006150079=2174237627 :=
  takeStep (p:=1361) (by decide) v217 c218 rfl (by decide) (by decide) rfl

private def ps219 : List ℕ := 1367::ps218
private theorem c219 : F ps218 20487308=1527170 := by decide +kernel
private theorem v219 : F ps219 28006150079=2172710457 :=
  takeStep (p:=1367) (by decide) v218 c219 rfl (by decide) (by decide) rfl

private def ps220 : List ℕ := 1373::ps219
private theorem c220 : F ps219 20397778=1518862 := by decide +kernel
private theorem v220 : F ps220 28006150079=2171191595 :=
  takeStep (p:=1373) (by decide) v219 c220 rfl (by decide) (by decide) rfl

private def ps221 : List ℕ := 1381::ps220
private theorem c221 : F ps220 20279616=1508375 := by decide +kernel
private theorem v221 : F ps221 28006150079=2169683220 :=
  takeStep (p:=1381) (by decide) v220 c221 rfl (by decide) (by decide) rfl

private def ps222 : List ℕ := 1399::ps221
private theorem c222 : F ps221 20018691=1487078 := by decide +kernel
private theorem v222 : F ps222 28006150079=2168196142 :=
  takeStep (p:=1399) (by decide) v221 c222 rfl (by decide) (by decide) rfl

private def ps223 : List ℕ := 1409::ps222
private theorem c223 : F ps222 19876614=1474826 := by decide +kernel
private theorem v223 : F ps223 28006150079=2166721316 :=
  takeStep (p:=1409) (by decide) v222 c223 rfl (by decide) (by decide) rfl

private def ps224 : List ℕ := 1423::ps223
private theorem c224 : F ps223 19681061=1458541 := by decide +kernel
private theorem v224 : F ps224 28006150079=2165262775 :=
  takeStep (p:=1423) (by decide) v223 c224 rfl (by decide) (by decide) rfl

private def ps225 : List ℕ := 1427::ps224
private theorem c225 : F ps224 19625893=1452978 := by decide +kernel
private theorem v225 : F ps225 28006150079=2163809797 :=
  takeStep (p:=1427) (by decide) v224 c225 rfl (by decide) (by decide) rfl

private def ps226 : List ℕ := 1429::ps225
private theorem c226 : F ps225 19598425=1449471 := by decide +kernel
private theorem v226 : F ps226 28006150079=2162360326 :=
  takeStep (p:=1429) (by decide) v225 c226 rfl (by decide) (by decide) rfl

private def ps227 : List ℕ := 1433::ps226
private theorem c227 : F ps226 19543719=1443978 := by decide +kernel
private theorem v227 : F ps227 28006150079=2160916348 :=
  takeStep (p:=1433) (by decide) v226 c227 rfl (by decide) (by decide) rfl

private def ps228 : List ℕ := 1439::ps227
private theorem c228 : F ps227 19462230=1436500 := by decide +kernel
private theorem v228 : F ps228 28006150079=2159479848 :=
  takeStep (p:=1439) (by decide) v227 c228 rfl (by decide) (by decide) rfl

private def ps229 : List ℕ := 1447::ps228
private theorem c229 : F ps228 19354630=1426962 := by decide +kernel
private theorem v229 : F ps229 28006150079=2158052886 :=
  takeStep (p:=1447) (by decide) v228 c229 rfl (by decide) (by decide) rfl

private def ps230 : List ℕ := 1451::ps229
private theorem c230 : F ps229 19301275=1421557 := by decide +kernel
private theorem v230 : F ps230 28006150079=2156631329 :=
  takeStep (p:=1451) (by decide) v229 c230 rfl (by decide) (by decide) rfl

private def ps231 : List ℕ := 1453::ps230
private theorem c231 : F ps230 19274707=1418222 := by decide +kernel
private theorem v231 : F ps231 28006150079=2155213107 :=
  takeStep (p:=1453) (by decide) v230 c231 rfl (by decide) (by decide) rfl

private def ps232 : List ℕ := 1459::ps231
private theorem c232 : F ps231 19195442=1410931 := by decide +kernel
private theorem v232 : F ps232 28006150079=2153802176 :=
  takeStep (p:=1459) (by decide) v231 c232 rfl (by decide) (by decide) rfl

private def ps233 : List ℕ := 1471::ps232
private theorem c233 : F ps232 19038851=1397854 := by decide +kernel
private theorem v233 : F ps233 28006150079=2152404322 :=
  takeStep (p:=1471) (by decide) v232 c233 rfl (by decide) (by decide) rfl

private def ps234 : List ℕ := 1481::ps233
private theorem c234 : F ps233 18910297=1386912 := by decide +kernel
private theorem v234 : F ps234 28006150079=2151017410 :=
  takeStep (p:=1481) (by decide) v233 c234 rfl (by decide) (by decide) rfl

private def ps235 : List ℕ := 1483::ps234
private theorem c235 : F ps234 18884794=1383742 := by decide +kernel
private theorem v235 : F ps235 28006150079=2149633668 :=
  takeStep (p:=1483) (by decide) v234 c235 rfl (by decide) (by decide) rfl

private def ps236 : List ℕ := 1487::ps235
private theorem c236 : F ps235 18833994=1378655 := by decide +kernel
private theorem v236 : F ps236 28006150079=2148255013 :=
  takeStep (p:=1487) (by decide) v235 c236 rfl (by decide) (by decide) rfl

private def ps237 : List ℕ := 1489::ps236
private theorem c237 : F ps236 18808697=1375490 := by decide +kernel
private theorem v237 : F ps237 28006150079=2146879523 :=
  takeStep (p:=1489) (by decide) v236 c237 rfl (by decide) (by decide) rfl

private def ps238 : List ℕ := 1493::ps237
private theorem c238 : F ps237 18758305=1370465 := by decide +kernel
private theorem v238 : F ps238 28006150079=2145509058 :=
  takeStep (p:=1493) (by decide) v237 c238 rfl (by decide) (by decide) rfl

private def ps239 : List ℕ := 1499::ps238
private theorem c239 : F ps238 18683222=1363608 := by decide +kernel
private theorem v239 : F ps239 28006150079=2144145450 :=
  takeStep (p:=1499) (by decide) v238 c239 rfl (by decide) (by decide) rfl

private def ps240 : List ℕ := 1511::ps239
private theorem c240 : F ps239 18534844=1351253 := by decide +kernel
private theorem v240 : F ps240 28006150079=2142794197 :=
  takeStep (p:=1511) (by decide) v239 c240 rfl (by decide) (by decide) rfl

private def ps241 : List ℕ := 1523::ps240
private theorem c241 : F ps240 18388805=1339200 := by decide +kernel
private theorem v241 : F ps241 28006150079=2141454997 :=
  takeStep (p:=1523) (by decide) v240 c241 rfl (by decide) (by decide) rfl

private def ps242 : List ℕ := 1531::ps241
private theorem c242 : F ps241 18292717=1330867 := by decide +kernel
private theorem v242 : F ps242 28006150079=2140124130 :=
  takeStep (p:=1531) (by decide) v241 c242 rfl (by decide) (by decide) rfl

private def ps243 : List ℕ := 1543::ps242
private theorem c243 : F ps242 18150453=1319105 := by decide +kernel
private theorem v243 : F ps243 28006150079=2138805025 :=
  takeStep (p:=1543) (by decide) v242 c243 rfl (by decide) (by decide) rfl

private def ps244 : List ℕ := 1549::ps243
private theorem c244 : F ps243 18080148=1312734 := by decide +kernel
private theorem v244 : F ps244 28006150079=2137492291 :=
  takeStep (p:=1549) (by decide) v243 c244 rfl (by decide) (by decide) rfl

private def ps245 : List ℕ := 1553::ps244
private theorem c245 : F ps244 18033580=1308137 := by decide +kernel
private theorem v245 : F ps245 28006150079=2136184154 :=
  takeStep (p:=1553) (by decide) v244 c245 rfl (by decide) (by decide) rfl

private def ps246 : List ℕ := 1559::ps245
private theorem c246 : F ps245 17964175=1301851 := by decide +kernel
private theorem v246 : F ps246 28006150079=2134882303 :=
  takeStep (p:=1559) (by decide) v245 c246 rfl (by decide) (by decide) rfl

private def ps247 : List ℕ := 1567::ps246
private theorem c247 : F ps246 17872463=1293888 := by decide +kernel
private theorem v247 : F ps247 28006150079=2133588415 :=
  takeStep (p:=1567) (by decide) v246 c247 rfl (by decide) (by decide) rfl

private def ps248 : List ℕ := 1571::ps247
private theorem c248 : F ps247 17826957=1289428 := by decide +kernel
private theorem v248 : F ps248 28006150079=2132298987 :=
  takeStep (p:=1571) (by decide) v247 c248 rfl (by decide) (by decide) rfl

private def ps249 : List ℕ := 1579::ps248
private theorem c249 : F ps248 17736637=1281654 := by decide +kernel
private theorem v249 : F ps249 28006150079=2131017333 :=
  takeStep (p:=1579) (by decide) v248 c249 rfl (by decide) (by decide) rfl

private def ps250 : List ℕ := 1583::ps249
private theorem c250 : F ps249 17691819=1277243 := by decide +kernel
private theorem v250 : F ps250 28006150079=2129740090 :=
  takeStep (p:=1583) (by decide) v249 c250 rfl (by decide) (by decide) rfl

private def ps251 : List ℕ := 1597::ps250
private theorem c251 : F ps250 17536725=1264719 := by decide +kernel
private theorem v251 : F ps251 28006150079=2128475371 :=
  takeStep (p:=1597) (by decide) v250 c251 rfl (by decide) (by decide) rfl

private def ps252 : List ℕ := 1601::ps251
private theorem c252 : F ps251 17492910=1260396 := by decide +kernel
private theorem v252 : F ps252 28006150079=2127214975 :=
  takeStep (p:=1601) (by decide) v251 c252 rfl (by decide) (by decide) rfl

private def ps253 : List ℕ := 1607::ps252
private theorem c253 : F ps252 17427598=1254485 := by decide +kernel
private theorem v253 : F ps253 28006150079=2125960490 :=
  takeStep (p:=1607) (by decide) v252 c253 rfl (by decide) (by decide) rfl

private def ps254 : List ℕ := 1609::ps253
private theorem c254 : F ps253 17405935=1251824 := by decide +kernel
private theorem v254 : F ps254 28006150079=2124708666 :=
  takeStep (p:=1609) (by decide) v253 c254 rfl (by decide) (by decide) rfl

private def ps255 : List ℕ := 1613::ps254
private theorem c255 : F ps254 17362771=1247577 := by decide +kernel
private theorem v255 : F ps255 28006150079=2123461089 :=
  takeStep (p:=1613) (by decide) v254 c255 rfl (by decide) (by decide) rfl

private def ps256 : List ℕ := 1619::ps255
private theorem c256 : F ps255 17298425=1241777 := by decide +kernel
private theorem v256 : F ps256 28006150079=2122219312 :=
  takeStep (p:=1619) (by decide) v255 c256 rfl (by decide) (by decide) rfl

private def ps257 : List ℕ := 1621::ps256
private theorem c257 : F ps256 17277082=1239141 := by decide +kernel
private theorem v257 : F ps257 28006150079=2120980171 :=
  takeStep (p:=1621) (by decide) v256 c257 rfl (by decide) (by decide) rfl

private def ps258 : List ℕ := 1627::ps257
private theorem c258 : F ps257 17213368=1233420 := by decide +kernel
private theorem v258 : F ps258 28006150079=2119746751 :=
  takeStep (p:=1627) (by decide) v257 c258 rfl (by decide) (by decide) rfl

private def ps259 : List ℕ := 1637::ps258
private theorem c259 : F ps258 17108216=1224792 := by decide +kernel
private theorem v259 : F ps259 28006150079=2118521959 :=
  takeStep (p:=1637) (by decide) v258 c259 rfl (by decide) (by decide) rfl

private def ps260 : List ℕ := 1657::ps259
private theorem c260 : F ps259 16901720=1208628 := by decide +kernel
private theorem v260 : F ps260 28006150079=2117313331 :=
  takeStep (p:=1657) (by decide) v259 c260 rfl (by decide) (by decide) rfl

private def ps261 : List ℕ := 1663::ps260
private theorem c261 : F ps260 16840739=1203195 := by decide +kernel
private theorem v261 : F ps261 28006150079=2116110136 :=
  takeStep (p:=1663) (by decide) v260 c261 rfl (by decide) (by decide) rfl

private def ps262 : List ℕ := 1667::ps261
private theorem c262 : F ps261 16800329=1199281 := by decide +kernel
private theorem v262 : F ps262 28006150079=2114910855 :=
  takeStep (p:=1667) (by decide) v261 c262 rfl (by decide) (by decide) rfl

private def ps263 : List ℕ := 1669::ps262
private theorem c263 : F ps262 16780197=1196818 := by decide +kernel
private theorem v263 : F ps263 28006150079=2113714037 :=
  takeStep (p:=1669) (by decide) v262 c263 rfl (by decide) (by decide) rfl

private def ps264 : List ℕ := 1693::ps263
private theorem c264 : F ps263 16542321=1178500 := by decide +kernel
private theorem v264 : F ps264 28006150079=2112535537 :=
  takeStep (p:=1693) (by decide) v263 c264 rfl (by decide) (by decide) rfl

private def ps265 : List ℕ := 1697::ps264
private theorem c265 : F ps264 16503329=1174760 := by decide +kernel
private theorem v265 : F ps265 28006150079=2111360777 :=
  takeStep (p:=1697) (by decide) v264 c265 rfl (by decide) (by decide) rfl

private def ps266 : List ℕ := 1699::ps265
private theorem c266 : F ps265 16483902=1172398 := by decide +kernel
private theorem v266 : F ps266 28006150079=2110188379 :=
  takeStep (p:=1699) (by decide) v265 c266 rfl (by decide) (by decide) rfl

private def ps267 : List ℕ := 1709::ps266
private theorem c267 : F ps266 16387448=1164435 := by decide +kernel
private theorem v267 : F ps267 28006150079=2109023944 :=
  takeStep (p:=1709) (by decide) v266 c267 rfl (by decide) (by decide) rfl

private def ps268 : List ℕ := 1721::ps267
private theorem c268 : F ps267 16273184=1155303 := by decide +kernel
private theorem v268 : F ps268 28006150079=2107868641 :=
  takeStep (p:=1721) (by decide) v267 c268 rfl (by decide) (by decide) rfl

private def ps269 : List ℕ := 1723::ps268
private theorem c269 : F ps268 16254294=1153023 := by decide +kernel
private theorem v269 : F ps269 28006150079=2106715618 :=
  takeStep (p:=1723) (by decide) v268 c269 rfl (by decide) (by decide) rfl

private def ps270 : List ℕ := 1733::ps269
private theorem c270 : F ps269 16160502=1145342 := by decide +kernel
private theorem v270 : F ps270 28006150079=2105570276 :=
  takeStep (p:=1733) (by decide) v269 c270 rfl (by decide) (by decide) rfl

private def ps271 : List ℕ := 1741::ps270
private theorem c271 : F ps270 16086243=1139112 := by decide +kernel
private theorem v271 : F ps271 28006150079=2104431164 :=
  takeStep (p:=1741) (by decide) v270 c271 rfl (by decide) (by decide) rfl

private def ps272 : List ℕ := 1747::ps271
private theorem c272 : F ps271 16030996=1134270 := by decide +kernel
private theorem v272 : F ps272 28006150079=2103296894 :=
  takeStep (p:=1747) (by decide) v271 c272 rfl (by decide) (by decide) rfl

private def ps273 : List ℕ := 1753::ps272
private theorem c273 : F ps272 15976126=1129463 := by decide +kernel
private theorem v273 : F ps273 28006150079=2102167431 :=
  takeStep (p:=1753) (by decide) v272 c273 rfl (by decide) (by decide) rfl

private def ps274 : List ℕ := 1759::ps273
private theorem c274 : F ps273 15921631=1124678 := by decide +kernel
private theorem v274 : F ps274 28006150079=2101042753 :=
  takeStep (p:=1759) (by decide) v273 c274 rfl (by decide) (by decide) rfl

private def ps275 : List ℕ := 1777::ps274
private theorem c275 : F ps274 15760354=1112232 := by decide +kernel
private theorem v275 : F ps275 28006150079=2099930521 :=
  takeStep (p:=1777) (by decide) v274 c275 rfl (by decide) (by decide) rfl

private def ps276 : List ℕ := 1783::ps275
private theorem c276 : F ps275 15707319=1107594 := by decide +kernel
private theorem v276 : F ps276 28006150079=2098822927 :=
  takeStep (p:=1783) (by decide) v275 c276 rfl (by decide) (by decide) rfl

private def ps277 : List ℕ := 1787::ps276
private theorem c277 : F ps276 15672160=1104256 := by decide +kernel
private theorem v277 : F ps277 28006150079=2097718671 :=
  takeStep (p:=1787) (by decide) v276 c277 rfl (by decide) (by decide) rfl

private def ps278 : List ℕ := 1789::ps277
private theorem c278 : F ps277 15654639=1102156 := by decide +kernel
private theorem v278 : F ps278 28006150079=2096616515 :=
  takeStep (p:=1789) (by decide) v277 c278 rfl (by decide) (by decide) rfl

private def ps279 : List ℕ := 1801::ps278
private theorem c279 : F ps278 15550333=1093859 := by decide +kernel
private theorem v279 : F ps279 28006150079=2095522656 :=
  takeStep (p:=1801) (by decide) v278 c279 rfl (by decide) (by decide) rfl

private def ps280 : List ℕ := 1811::ps279
private theorem c280 : F ps279 15464467=1086906 := by decide +kernel
private theorem v280 : F ps280 28006150079=2094435750 :=
  takeStep (p:=1811) (by decide) v279 c280 rfl (by decide) (by decide) rfl

private def ps281 : List ℕ := 1823::ps280
private theorem c281 : F ps280 15362671=1078909 := by decide +kernel
private theorem v281 : F ps281 28006150079=2093356841 :=
  takeStep (p:=1823) (by decide) v280 c281 rfl (by decide) (by decide) rfl

private def ps282 : List ℕ := 1831::ps281
private theorem c282 : F ps281 15295548=1073332 := by decide +kernel
private theorem v282 : F ps282 28006150079=2092283509 :=
  takeStep (p:=1831) (by decide) v281 c282 rfl (by decide) (by decide) rfl

private def ps283 : List ℕ := 1847::ps282
private theorem c283 : F ps282 15163048=1063125 := by decide +kernel
private theorem v283 : F ps283 28006150079=2091220384 :=
  takeStep (p:=1847) (by decide) v282 c283 rfl (by decide) (by decide) rfl

private def ps284 : List ℕ := 1861::ps283
private theorem c284 : F ps283 15048979=1054257 := by decide +kernel
private theorem v284 : F ps284 28006150079=2090166127 :=
  takeStep (p:=1861) (by decide) v283 c284 rfl (by decide) (by decide) rfl

private def ps285 : List ℕ := 1867::ps284
private theorem c285 : F ps284 15000616=1050086 := by decide +kernel
private theorem v285 : F ps285 28006150079=2089116041 :=
  takeStep (p:=1867) (by decide) v284 c285 rfl (by decide) (by decide) rfl

private def ps286 : List ℕ := 1871::ps285
private theorem c286 : F ps285 14968546=1047067 := by decide +kernel
private theorem v286 : F ps286 28006150079=2088068974 :=
  takeStep (p:=1871) (by decide) v285 c286 rfl (by decide) (by decide) rfl

private def ps287 : List ℕ := 1873::ps286
private theorem c287 : F ps286 14952562=1045245 := by decide +kernel
private theorem v287 : F ps287 28006150079=2087023729 :=
  takeStep (p:=1873) (by decide) v286 c287 rfl (by decide) (by decide) rfl

private def ps288 : List ℕ := 1877::ps287
private theorem c288 : F ps287 14920697=1042246 := by decide +kernel
private theorem v288 : F ps288 28006150079=2085981483 :=
  takeStep (p:=1877) (by decide) v287 c288 rfl (by decide) (by decide) rfl

private def ps289 : List ℕ := 1879::ps288
private theorem c289 : F ps288 14904816=1040416 := by decide +kernel
private theorem v289 : F ps289 28006150079=2084941067 :=
  takeStep (p:=1879) (by decide) v288 c289 rfl (by decide) (by decide) rfl

private def ps290 : List ℕ := 1889::ps289
private theorem c290 : F ps289 14825913=1034142 := by decide +kernel
private theorem v290 : F ps290 28006150079=2083906925 :=
  takeStep (p:=1889) (by decide) v289 c290 rfl (by decide) (by decide) rfl

private def ps291 : List ℕ := 1901::ps290
private theorem c291 : F ps290 14732325=1026789 := by decide +kernel
private theorem v291 : F ps291 28006150079=2082880136 :=
  takeStep (p:=1901) (by decide) v290 c291 rfl (by decide) (by decide) rfl

private def ps292 : List ℕ := 1907::ps291
private theorem c292 : F ps291 14685972=1022806 := by decide +kernel
private theorem v292 : F ps292 28006150079=2081857330 :=
  takeStep (p:=1907) (by decide) v291 c292 rfl (by decide) (by decide) rfl

private def ps293 : List ℕ := 1913::ps292
private theorem c293 : F ps292 14639911=1018883 := by decide +kernel
private theorem v293 : F ps293 28006150079=2080838447 :=
  takeStep (p:=1913) (by decide) v292 c293 rfl (by decide) (by decide) rfl

private def ps294 : List ℕ := 1931::ps293
private theorem c294 : F ps293 14503443=1008609 := by decide +kernel
private theorem v294 : F ps294 28006150079=2079829838 :=
  takeStep (p:=1931) (by decide) v293 c294 rfl (by decide) (by decide) rfl

private def ps295 : List ℕ := 1933::ps294
private theorem c295 : F ps294 14488437=1006887 := by decide +kernel
private theorem v295 : F ps295 28006150079=2078822951 :=
  takeStep (p:=1933) (by decide) v294 c295 rfl (by decide) (by decide) rfl

private def ps296 : List ℕ := 1949::ps295
private theorem c296 : F ps295 14369497=997855 := by decide +kernel
private theorem v296 : F ps296 28006150079=2077825096 :=
  takeStep (p:=1949) (by decide) v295 c296 rfl (by decide) (by decide) rfl

private def ps297 : List ℕ := 1951::ps296
private theorem c297 : F ps296 14354766=996176 := by decide +kernel
private theorem v297 : F ps297 28006150079=2076828920 :=
  takeStep (p:=1951) (by decide) v296 c297 rfl (by decide) (by decide) rfl

private def ps298 : List ℕ := 1973::ps297
private theorem c298 : F ps297 14194703=984225 := by decide +kernel
private theorem v298 : F ps298 28006150079=2075844695 :=
  takeStep (p:=1973) (by decide) v297 c298 rfl (by decide) (by decide) rfl

private def ps299 : List ℕ := 1979::ps298
private theorem c299 : F ps298 14151667=980615 := by decide +kernel
private theorem v299 : F ps299 28006150079=2074864080 :=
  takeStep (p:=1979) (by decide) v298 c299 rfl (by decide) (by decide) rfl

private def ps300 : List ℕ := 1987::ps299
private theorem c300 : F ps299 14094690=975995 := by decide +kernel
private theorem v300 : F ps300 28006150079=2073888085 :=
  takeStep (p:=1987) (by decide) v299 c300 rfl (by decide) (by decide) rfl

private def ps301 : List ℕ := 1993::ps300
private theorem c301 : F ps300 14052257=972409 := by decide +kernel
private theorem v301 : F ps301 28006150079=2072915676 :=
  takeStep (p:=1993) (by decide) v300 c301 rfl (by decide) (by decide) rfl

private def ps302 : List ℕ := 1997::ps301
private theorem c302 : F ps301 14024111=969846 := by decide +kernel
private theorem v302 : F ps302 28006150079=2071945830 :=
  takeStep (p:=1997) (by decide) v301 c302 rfl (by decide) (by decide) rfl

private def ps303 : List ℕ := 1999::ps302
private theorem c303 : F ps302 14010080=968255 := by decide +kernel
private theorem v303 : F ps303 28006150079=2070977575 :=
  takeStep (p:=1999) (by decide) v302 c303 rfl (by decide) (by decide) rfl

private def ps304 : List ℕ := 2003::ps303
private theorem c304 : F ps303 13982101=965714 := by decide +kernel
private theorem v304 : F ps304 28006150079=2070011861 :=
  takeStep (p:=2003) (by decide) v303 c304 rfl (by decide) (by decide) rfl

private def ps305 : List ℕ := 2011::ps304
private theorem c305 : F ps304 13926479=961298 := by decide +kernel
private theorem v305 : F ps305 28006150079=2069050563 :=
  takeStep (p:=2011) (by decide) v304 c305 rfl (by decide) (by decide) rfl

private def ps306 : List ℕ := 2017::ps305
private theorem c306 : F ps305 13885052=957779 := by decide +kernel
private theorem v306 : F ps306 28006150079=2068092784 :=
  takeStep (p:=2017) (by decide) v305 c306 rfl (by decide) (by decide) rfl

private def ps307 : List ℕ := 2027::ps306
private theorem c307 : F ps306 13816551=952395 := by decide +kernel
private theorem v307 : F ps307 28006150079=2067140389 :=
  takeStep (p:=2027) (by decide) v306 c307 rfl (by decide) (by decide) rfl

private def ps308 : List ℕ := 2029::ps307
private theorem c308 : F ps307 13802932=950872 := by decide +kernel
private theorem v308 : F ps308 28006150079=2066189517 :=
  takeStep (p:=2029) (by decide) v307 c308 rfl (by decide) (by decide) rfl

private def ps309 : List ℕ := 2039::ps308
private theorem c309 : F ps308 13735237=945588 := by decide +kernel
private theorem v309 : F ps309 28006150079=2065243929 :=
  takeStep (p:=2039) (by decide) v308 c309 rfl (by decide) (by decide) rfl

private def ps310 : List ℕ := 2053::ps309
private theorem c310 : F ps309 13641573=938511 := by decide +kernel
private theorem v310 : F ps310 28006150079=2064305418 :=
  takeStep (p:=2053) (by decide) v309 c310 rfl (by decide) (by decide) rfl

private def ps311 : List ℕ := 2063::ps310
private theorem c311 : F ps310 13575448=933341 := by decide +kernel
private theorem v311 : F ps311 28006150079=2063372077 :=
  takeStep (p:=2063) (by decide) v310 c311 rfl (by decide) (by decide) rfl

private def ps312 : List ℕ := 2069::ps311
private theorem c312 : F ps311 13536080=930084 := by decide +kernel
private theorem v312 : F ps312 28006150079=2062441993 :=
  takeStep (p:=2069) (by decide) v311 c312 rfl (by decide) (by decide) rfl

private def ps313 : List ℕ := 2081::ps312
private theorem c313 : F ps312 13458025=924155 := by decide +kernel
private theorem v313 : F ps313 28006150079=2061517838 :=
  takeStep (p:=2081) (by decide) v312 c313 rfl (by decide) (by decide) rfl

private def ps314 : List ℕ := 2083::ps313
private theorem c314 : F ps313 13445103=922750 := by decide +kernel
private theorem v314 : F ps314 28006150079=2060595088 :=
  takeStep (p:=2083) (by decide) v313 c314 rfl (by decide) (by decide) rfl

private def ps315 : List ℕ := 2087::ps314
private theorem c315 : F ps314 13419334=920444 := by decide +kernel
private theorem v315 : F ps315 28006150079=2059674644 :=
  takeStep (p:=2087) (by decide) v314 c315 rfl (by decide) (by decide) rfl

private def ps316 : List ℕ := 2089::ps315
private theorem c316 : F ps315 13406486=919058 := by decide +kernel
private theorem v316 : F ps316 28006150079=2058755586 :=
  takeStep (p:=2089) (by decide) v315 c316 rfl (by decide) (by decide) rfl

private def ps317 : List ℕ := 2099::ps316
private theorem c317 : F ps316 13342615=914099 := by decide +kernel
private theorem v317 : F ps317 28006150079=2057841487 :=
  takeStep (p:=2099) (by decide) v316 c317 rfl (by decide) (by decide) rfl

private def ps318 : List ℕ := 2111::ps317
private theorem c318 : F ps317 13266769=908344 := by decide +kernel
private theorem v318 : F ps318 28006150079=2056933143 :=
  takeStep (p:=2111) (by decide) v317 c318 rfl (by decide) (by decide) rfl

private def ps319 : List ℕ := 2113::ps318
private theorem c319 : F ps318 13254212=906984 := by decide +kernel
private theorem v319 : F ps319 28006150079=2056026159 :=
  takeStep (p:=2113) (by decide) v318 c319 rfl (by decide) (by decide) rfl

private def ps320 : List ℕ := 2129::ps319
private theorem c320 : F ps319 13154603=899620 := by decide +kernel
private theorem v320 : F ps320 28006150079=2055126539 :=
  takeStep (p:=2129) (by decide) v319 c320 rfl (by decide) (by decide) rfl

private def ps321 : List ℕ := 2131::ps320
private theorem c321 : F ps320 13142257=898295 := by decide +kernel
private theorem v321 : F ps321 28006150079=2054228244 :=
  takeStep (p:=2131) (by decide) v320 c321 rfl (by decide) (by decide) rfl

private def ps322 : List ℕ := 2137::ps321
private theorem c322 : F ps321 13105358=895275 := by decide +kernel
private theorem v322 : F ps322 28006150079=2053332969 :=
  takeStep (p:=2137) (by decide) v321 c322 rfl (by decide) (by decide) rfl

private def ps323 : List ℕ := 2141::ps322
private theorem c323 : F ps322 13080873=893150 := by decide +kernel
private theorem v323 : F ps323 28006150079=2052439819 :=
  takeStep (p:=2141) (by decide) v322 c323 rfl (by decide) (by decide) rfl

private def ps324 : List ℕ := 2143::ps323
private theorem c324 : F ps323 13068665=891830 := by decide +kernel
private theorem v324 : F ps324 28006150079=2051547989 :=
  takeStep (p:=2143) (by decide) v323 c324 rfl (by decide) (by decide) rfl

private def ps325 : List ℕ := 2153::ps324
private theorem c325 : F ps324 13007965=887232 := by decide +kernel
private theorem v325 : F ps325 28006150079=2050660757 :=
  takeStep (p:=2153) (by decide) v324 c325 rfl (by decide) (by decide) rfl

private def ps326 : List ℕ := 2161::ps325
private theorem c326 : F ps325 12959810=883469 := by decide +kernel
private theorem v326 : F ps326 28006150079=2049777288 :=
  takeStep (p:=2161) (by decide) v325 c326 rfl (by decide) (by decide) rfl

private def ps327 : List ℕ := 2179::ps326
private theorem c327 : F ps326 12852753=875734 := by decide +kernel
private theorem v327 : F ps327 28006150079=2048901554 :=
  takeStep (p:=2179) (by decide) v326 c327 rfl (by decide) (by decide) rfl

private def ps328 : List ℕ := 2203::ps327
private theorem c328 : F ps327 12712732=865644 := by decide +kernel
private theorem v328 : F ps328 28006150079=2048035910 :=
  takeStep (p:=2203) (by decide) v327 c328 rfl (by decide) (by decide) rfl

private def ps329 : List ℕ := 2207::ps328
private theorem c329 : F ps328 12689691=863650 := by decide +kernel
private theorem v329 : F ps329 28006150079=2047172260 :=
  takeStep (p:=2207) (by decide) v328 c329 rfl (by decide) (by decide) rfl

private def ps330 : List ℕ := 2213::ps329
private theorem c330 : F ps329 12655286=860877 := by decide +kernel
private theorem v330 : F ps330 28006150079=2046311383 :=
  takeStep (p:=2213) (by decide) v329 c330 rfl (by decide) (by decide) rfl

private def ps331 : List ℕ := 2221::ps330
private theorem c331 : F ps330 12609702=857339 := by decide +kernel
private theorem v331 : F ps331 28006150079=2045454044 :=
  takeStep (p:=2221) (by decide) v330 c331 rfl (by decide) (by decide) rfl

private def ps332 : List ℕ := 2237::ps331
private theorem c332 : F ps331 12519512=850802 := by decide +kernel
private theorem v332 : F ps332 28006150079=2044603242 :=
  takeStep (p:=2237) (by decide) v331 c332 rfl (by decide) (by decide) rfl

private def ps333 : List ℕ := 2239::ps332
private theorem c333 : F ps332 12508329=849610 := by decide +kernel
private theorem v333 : F ps333 28006150079=2043753632 :=
  takeStep (p:=2239) (by decide) v332 c333 rfl (by decide) (by decide) rfl

private def ps334 : List ℕ := 2243::ps333
private theorem c334 : F ps333 12486023=847737 := by decide +kernel
private theorem v334 : F ps334 28006150079=2042905895 :=
  takeStep (p:=2243) (by decide) v333 c334 rfl (by decide) (by decide) rfl

private def ps335 : List ℕ := 2251::ps334
private theorem c335 : F ps334 12441648=844311 := by decide +kernel
private theorem v335 : F ps335 28006150079=2042061584 :=
  takeStep (p:=2251) (by decide) v334 c335 rfl (by decide) (by decide) rfl

private def ps336 : List ℕ := 2267::ps335
private theorem c336 : F ps335 12353837=837917 := by decide +kernel
private theorem v336 : F ps336 28006150079=2041223667 :=
  takeStep (p:=2267) (by decide) v335 c336 rfl (by decide) (by decide) rfl

private def ps337 : List ℕ := 2269::ps336
private theorem c337 : F ps336 12342948=836773 := by decide +kernel
private theorem v337 : F ps337 28006150079=2040386894 :=
  takeStep (p:=2269) (by decide) v336 c337 rfl (by decide) (by decide) rfl

private def ps338 : List ℕ := 2273::ps337
private theorem c338 : F ps337 12321227=834971 := by decide +kernel
private theorem v338 : F ps338 28006150079=2039551923 :=
  takeStep (p:=2273) (by decide) v337 c338 rfl (by decide) (by decide) rfl

private def ps339 : List ℕ := 2281::ps338
private theorem c339 : F ps338 12278014=831649 := by decide +kernel
private theorem v339 : F ps339 28006150079=2038720274 :=
  takeStep (p:=2281) (by decide) v338 c339 rfl (by decide) (by decide) rfl

private def ps340 : List ℕ := 2287::ps339
private theorem c340 : F ps339 12245802=829101 := by decide +kernel
private theorem v340 : F ps340 28006150079=2037891173 :=
  takeStep (p:=2287) (by decide) v339 c340 rfl (by decide) (by decide) rfl

private def ps341 : List ℕ := 2293::ps340
private theorem c341 : F ps340 12213759=826556 := by decide +kernel
private theorem v341 : F ps341 28006150079=2037064617 :=
  takeStep (p:=2293) (by decide) v340 c341 rfl (by decide) (by decide) rfl

private def ps342 : List ℕ := 2297::ps341
private theorem c342 : F ps341 12192490=824751 := by decide +kernel
private theorem v342 : F ps342 28006150079=2036239866 :=
  takeStep (p:=2297) (by decide) v341 c342 rfl (by decide) (by decide) rfl

private def ps343 : List ℕ := 2309::ps342
private theorem c343 : F ps342 12129125=820124 := by decide +kernel
private theorem v343 : F ps343 28006150079=2035419742 :=
  takeStep (p:=2309) (by decide) v342 c343 rfl (by decide) (by decide) rfl

private def ps344 : List ℕ := 2311::ps343
private theorem c344 : F ps343 12118628=819070 := by decide +kernel
private theorem v344 : F ps344 28006150079=2034600672 :=
  takeStep (p:=2311) (by decide) v343 c344 rfl (by decide) (by decide) rfl

private def ps345 : List ℕ := 2333::ps344
private theorem c345 : F ps344 12004350=811023 := by decide +kernel
private theorem v345 : F ps345 28006150079=2033789649 :=
  takeStep (p:=2333) (by decide) v344 c345 rfl (by decide) (by decide) rfl

private def ps346 : List ℕ := 2339::ps345
private theorem c346 : F ps345 11973557=808626 := by decide +kernel
private theorem v346 : F ps346 28006150079=2032981023 :=
  takeStep (p:=2339) (by decide) v345 c346 rfl (by decide) (by decide) rfl

private def ps347 : List ℕ := 2341::ps346
private theorem c347 : F ps346 11963327=807622 := by decide +kernel
private theorem v347 : F ps347 28006150079=2032173401 :=
  takeStep (p:=2341) (by decide) v346 c347 rfl (by decide) (by decide) rfl

private def ps348 : List ℕ := 2347::ps347
private theorem c348 : F ps347 11932743=805204 := by decide +kernel
private theorem v348 : F ps348 28006150079=2031368197 :=
  takeStep (p:=2347) (by decide) v347 c348 rfl (by decide) (by decide) rfl

private def ps349 : List ℕ := 2351::ps348
private theorem c349 : F ps348 11912441=803501 := by decide +kernel
private theorem v349 : F ps349 28006150079=2030564696 :=
  takeStep (p:=2351) (by decide) v348 c349 rfl (by decide) (by decide) rfl

private def ps350 : List ℕ := 2357::ps349
private theorem c350 : F ps349 11882117=801137 := by decide +kernel
private theorem v350 : F ps350 28006150079=2029763559 :=
  takeStep (p:=2357) (by decide) v349 c350 rfl (by decide) (by decide) rfl

private def ps351 : List ℕ := 2371::ps350
private theorem c351 : F ps350 11811957=796110 := by decide +kernel
private theorem v351 : F ps351 28006150079=2028967449 :=
  takeStep (p:=2371) (by decide) v350 c351 rfl (by decide) (by decide) rfl

private def ps352 : List ℕ := 2377::ps351
private theorem c352 : F ps351 11782141=793764 := by decide +kernel
private theorem v352 : F ps352 28006150079=2028173685 :=
  takeStep (p:=2377) (by decide) v351 c352 rfl (by decide) (by decide) rfl

private def ps353 : List ℕ := 2381::ps352
private theorem c353 : F ps352 11762347=792139 := by decide +kernel
private theorem v353 : F ps353 28006150079=2027381546 :=
  takeStep (p:=2381) (by decide) v352 c353 rfl (by decide) (by decide) rfl

private def ps354 : List ℕ := 2383::ps353
private theorem c354 : F ps353 11752475=791182 := by decide +kernel
private theorem v354 : F ps354 28006150079=2026590364 :=
  takeStep (p:=2383) (by decide) v353 c354 rfl (by decide) (by decide) rfl

private def ps355 : List ℕ := 2389::ps354
private theorem c355 : F ps354 11722959=788918 := by decide +kernel
private theorem v355 : F ps355 28006150079=2025801446 :=
  takeStep (p:=2389) (by decide) v354 c355 rfl (by decide) (by decide) rfl

private def ps356 : List ℕ := 2393::ps355
private theorem c356 : F ps355 11703364=787326 := by decide +kernel
private theorem v356 : F ps356 28006150079=2025014120 :=
  takeStep (p:=2393) (by decide) v355 c356 rfl (by decide) (by decide) rfl

private def ps357 : List ℕ := 2399::ps356
private theorem c357 : F ps356 11674093=785081 := by decide +kernel
private theorem v357 : F ps357 28006150079=2024229039 :=
  takeStep (p:=2399) (by decide) v356 c357 rfl (by decide) (by decide) rfl

private def ps358 : List ℕ := 2411::ps357
private theorem c358 : F ps357 11615989=780920 := by decide +kernel
private theorem v358 : F ps358 28006150079=2023448119 :=
  takeStep (p:=2411) (by decide) v357 c358 rfl (by decide) (by decide) rfl

private def ps359 : List ℕ := 2417::ps358
private theorem c359 : F ps358 11587153=778672 := by decide +kernel
private theorem v359 : F ps359 28006150079=2022669447 :=
  takeStep (p:=2417) (by decide) v358 c359 rfl (by decide) (by decide) rfl

private def ps360 : List ℕ := 2423::ps359
private theorem c360 : F ps359 11558460=776489 := by decide +kernel
private theorem v360 : F ps360 28006150079=2021892958 :=
  takeStep (p:=2423) (by decide) v359 c360 rfl (by decide) (by decide) rfl

private def ps361 : List ℕ := 2437::ps360
private theorem c361 : F ps360 11492059=771764 := by decide +kernel
private theorem v361 : F ps361 28006150079=2021121194 :=
  takeStep (p:=2437) (by decide) v360 c361 rfl (by decide) (by decide) rfl

private def ps362 : List ℕ := 2441::ps361
private theorem c362 : F ps361 11473228=770267 := by decide +kernel
private theorem v362 : F ps362 28006150079=2020350927 :=
  takeStep (p:=2441) (by decide) v361 c362 rfl (by decide) (by decide) rfl

private def ps363 : List ℕ := 2447::ps362
private theorem c363 : F ps362 11445096=768079 := by decide +kernel
private theorem v363 : F ps363 28006150079=2019582848 :=
  takeStep (p:=2447) (by decide) v362 c363 rfl (by decide) (by decide) rfl

private def ps364 : List ℕ := 2459::ps363
private theorem c364 : F ps363 11389243=764111 := by decide +kernel
private theorem v364 : F ps364 28006150079=2018818737 :=
  takeStep (p:=2459) (by decide) v363 c364 rfl (by decide) (by decide) rfl

private def ps365 : List ℕ := 2467::ps364
private theorem c365 : F ps364 11352310=761436 := by decide +kernel
private theorem v365 : F ps365 28006150079=2018057301 :=
  takeStep (p:=2467) (by decide) v364 c365 rfl (by decide) (by decide) rfl

private def ps366 : List ℕ := 2473::ps365
private theorem c366 : F ps365 11324767=759361 := by decide +kernel
private theorem v366 : F ps366 28006150079=2017297940 :=
  takeStep (p:=2473) (by decide) v365 c366 rfl (by decide) (by decide) rfl

private def ps367 : List ℕ := 2477::ps366
private theorem c367 : F ps366 11306479=757890 := by decide +kernel
private theorem v367 : F ps367 28006150079=2016540050 :=
  takeStep (p:=2477) (by decide) v366 c367 rfl (by decide) (by decide) rfl

private def ps368 : List ℕ := 2503::ps367
private theorem c368 : F ps367 11189033=749924 := by decide +kernel
private theorem v368 : F ps368 28006150079=2015790126 :=
  takeStep (p:=2503) (by decide) v367 c368 rfl (by decide) (by decide) rfl

private def ps369 : List ℕ := 2521::ps368
private theorem c369 : F ps368 11109143=744429 := by decide +kernel
private theorem v369 : F ps369 28006150079=2015045697 :=
  takeStep (p:=2521) (by decide) v368 c369 rfl (by decide) (by decide) rfl

private def ps370 : List ℕ := 2531::ps369
private theorem c370 : F ps369 11065250=741283 := by decide +kernel
private theorem v370 : F ps370 28006150079=2014304414 :=
  takeStep (p:=2531) (by decide) v369 c370 rfl (by decide) (by decide) rfl

private def ps371 : List ℕ := 2539::ps370
private theorem c371 : F ps370 11030386=738728 := by decide +kernel
private theorem v371 : F ps371 28006150079=2013565686 :=
  takeStep (p:=2539) (by decide) v370 c371 rfl (by decide) (by decide) rfl

private def ps372 : List ℕ := 2543::ps371
private theorem c372 : F ps371 11013035=737372 := by decide +kernel
private theorem v372 : F ps372 28006150079=2012828314 :=
  takeStep (p:=2543) (by decide) v371 c372 rfl (by decide) (by decide) rfl

private def ps373 : List ℕ := 2549::ps372
private theorem c373 : F ps372 10987112=735471 := by decide +kernel
private theorem v373 : F ps373 28006150079=2012092843 :=
  takeStep (p:=2549) (by decide) v372 c373 rfl (by decide) (by decide) rfl

private def ps374 : List ℕ := 2551::ps373
private theorem c374 : F ps373 10978498=734677 := by decide +kernel
private theorem v374 : F ps374 28006150079=2011358166 :=
  takeStep (p:=2551) (by decide) v373 c374 rfl (by decide) (by decide) rfl

private def ps375 : List ℕ := 2557::ps374
private theorem c375 : F ps374 10952737=732777 := by decide +kernel
private theorem v375 : F ps375 28006150079=2010625389 :=
  takeStep (p:=2557) (by decide) v374 c375 rfl (by decide) (by decide) rfl

private def ps376 : List ℕ := 2579::ps375
private theorem c376 : F ps375 10859305=726423 := by decide +kernel
private theorem v376 : F ps376 28006150079=2009898966 :=
  takeStep (p:=2579) (by decide) v375 c376 rfl (by decide) (by decide) rfl

private def ps377 : List ℕ := 2591::ps376
private theorem c377 : F ps376 10809011=722925 := by decide +kernel
private theorem v377 : F ps377 28006150079=2009176041 :=
  takeStep (p:=2591) (by decide) v376 c377 rfl (by decide) (by decide) rfl

private def ps378 : List ℕ := 2593::ps377
private theorem c378 : F ps377 10800674=722181 := by decide +kernel
private theorem v378 : F ps378 28006150079=2008453860 :=
  takeStep (p:=2593) (by decide) v377 c378 rfl (by decide) (by decide) rfl

private def ps379 : List ℕ := 2609::ps378
private theorem c379 : F ps378 10734438=717683 := by decide +kernel
private theorem v379 : F ps379 28006150079=2007736177 :=
  takeStep (p:=2609) (by decide) v378 c379 rfl (by decide) (by decide) rfl

private def ps380 : List ℕ := 2617::ps379
private theorem c380 : F ps379 10701624=715338 := by decide +kernel
private theorem v380 : F ps380 28006150079=2007020839 :=
  takeStep (p:=2617) (by decide) v379 c380 rfl (by decide) (by decide) rfl

private def ps381 : List ℕ := 2621::ps380
private theorem c381 : F ps380 10685291=714098 := by decide +kernel
private theorem v381 : F ps381 28006150079=2006306741 :=
  takeStep (p:=2621) (by decide) v380 c381 rfl (by decide) (by decide) rfl

private def ps382 : List ℕ := 2633::ps381
private theorem c382 : F ps381 10636593=710693 := by decide +kernel
private theorem v382 : F ps382 28006150079=2005596048 :=
  takeStep (p:=2633) (by decide) v381 c382 rfl (by decide) (by decide) rfl

private def ps383 : List ℕ := 2647::ps382
private theorem c383 : F ps382 10580336=706862 := by decide +kernel
private theorem v383 : F ps383 28006150079=2004889186 :=
  takeStep (p:=2647) (by decide) v382 c383 rfl (by decide) (by decide) rfl

private def ps384 : List ℕ := 2657::ps383
private theorem c384 : F ps383 10540515=704091 := by decide +kernel
private theorem v384 : F ps384 28006150079=2004185095 :=
  takeStep (p:=2657) (by decide) v383 c384 rfl (by decide) (by decide) rfl

private def ps385 : List ℕ := 2659::ps384
private theorem c385 : F ps384 10532587=703403 := by decide +kernel
private theorem v385 : F ps385 28006150079=2003481692 :=
  takeStep (p:=2659) (by decide) v384 c385 rfl (by decide) (by decide) rfl

private def ps386 : List ℕ := 2663::ps385
private theorem c386 : F ps385 10516766=702235 := by decide +kernel
private theorem v386 : F ps386 28006150079=2002779457 :=
  takeStep (p:=2663) (by decide) v385 c386 rfl (by decide) (by decide) rfl

private def ps387 : List ℕ := 2671::ps386
private theorem c387 : F ps386 10485267=700001 := by decide +kernel
private theorem v387 : F ps387 28006150079=2002079456 :=
  takeStep (p:=2671) (by decide) v386 c387 rfl (by decide) (by decide) rfl

private def ps388 : List ℕ := 2677::ps387
private theorem c388 : F ps387 10461766=698307 := by decide +kernel
private theorem v388 : F ps388 28006150079=2001381149 :=
  takeStep (p:=2677) (by decide) v387 c388 rfl (by decide) (by decide) rfl

private def ps389 : List ℕ := 2683::ps388
private theorem c389 : F ps388 10438371=696635 := by decide +kernel
private theorem v389 : F ps389 28006150079=2000684514 :=
  takeStep (p:=2683) (by decide) v388 c389 rfl (by decide) (by decide) rfl

private def ps390 : List ℕ := 2687::ps389
private theorem c390 : F ps389 10422832=695469 := by decide +kernel
private theorem v390 : F ps390 28006150079=1999989045 :=
  takeStep (p:=2687) (by decide) v389 c390 rfl (by decide) (by decide) rfl

private def ps391 : List ℕ := 2689::ps390
private theorem c391 : F ps390 10415079=694823 := by decide +kernel
private theorem v391 : F ps391 28006150079=1999294222 :=
  takeStep (p:=2689) (by decide) v390 c391 rfl (by decide) (by decide) rfl

private def ps392 : List ℕ := 2693::ps391
private theorem c392 : F ps391 10399610=693671 := by decide +kernel
private theorem v392 : F ps392 28006150079=1998600551 :=
  takeStep (p:=2693) (by decide) v391 c392 rfl (by decide) (by decide) rfl

private def ps393 : List ℕ := 2699::ps392
private theorem c393 : F ps392 10376491=692012 := by decide +kernel
private theorem v393 : F ps393 28006150079=1997908539 :=
  takeStep (p:=2699) (by decide) v392 c393 rfl (by decide) (by decide) rfl

private def ps394 : List ℕ := 2707::ps393
private theorem c394 : F ps393 10345825=689891 := by decide +kernel
private theorem v394 : F ps394 28006150079=1997218648 :=
  takeStep (p:=2707) (by decide) v393 c394 rfl (by decide) (by decide) rfl

private def ps395 : List ℕ := 2711::ps394
private theorem c395 : F ps394 10330560=688778 := by decide +kernel
private theorem v395 : F ps395 28006150079=1996529870 :=
  takeStep (p:=2711) (by decide) v394 c395 rfl (by decide) (by decide) rfl

private def ps396 : List ℕ := 2713::ps395
private theorem c396 : F ps395 10322945=688143 := by decide +kernel
private theorem v396 : F ps396 28006150079=1995841727 :=
  takeStep (p:=2713) (by decide) v395 c396 rfl (by decide) (by decide) rfl

private def ps397 : List ℕ := 2719::ps396
private theorem c397 : F ps396 10300165=686542 := by decide +kernel
private theorem v397 : F ps397 28006150079=1995155185 :=
  takeStep (p:=2719) (by decide) v396 c397 rfl (by decide) (by decide) rfl

private def ps398 : List ℕ := 2729::ps397
private theorem c398 : F ps397 10262422=683996 := by decide +kernel
private theorem v398 : F ps398 28006150079=1994471189 :=
  takeStep (p:=2729) (by decide) v397 c398 rfl (by decide) (by decide) rfl

private def ps399 : List ℕ := 2731::ps398
private theorem c399 : F ps398 10254906=683375 := by decide +kernel
private theorem v399 : F ps399 28006150079=1993787814 :=
  takeStep (p:=2731) (by decide) v398 c399 rfl (by decide) (by decide) rfl

private def ps400 : List ℕ := 2741::ps399
private theorem c400 : F ps399 10217493=680826 := by decide +kernel
private theorem v400 : F ps400 28006150079=1993106988 :=
  takeStep (p:=2741) (by decide) v399 c400 rfl (by decide) (by decide) rfl

private def ps401 : List ℕ := 2749::ps400
private theorem c401 : F ps400 10187759=678833 := by decide +kernel
private theorem v401 : F ps401 28006150079=1992428155 :=
  takeStep (p:=2749) (by decide) v400 c401 rfl (by decide) (by decide) rfl

private def ps402 : List ℕ := 2753::ps401
private theorem c402 : F ps401 10172956=677767 := by decide +kernel
private theorem v402 : F ps402 28006150079=1991750388 :=
  takeStep (p:=2753) (by decide) v401 c402 rfl (by decide) (by decide) rfl

private def ps403 : List ℕ := 2767::ps402
private theorem c403 : F ps402 10121485=674366 := by decide +kernel
private theorem v403 : F ps403 28006150079=1991076022 :=
  takeStep (p:=2767) (by decide) v402 c403 rfl (by decide) (by decide) rfl

private def ps404 : List ℕ := 2777::ps403
private theorem c404 : F ps403 10085037=671934 := by decide +kernel
private theorem v404 : F ps404 28006150079=1990404088 :=
  takeStep (p:=2777) (by decide) v403 c404 rfl (by decide) (by decide) rfl

private def ps405 : List ℕ := 2789::ps404
private theorem c405 : F ps404 10041645=669027 := by decide +kernel
private theorem v405 : F ps405 28006150079=1989735061 :=
  takeStep (p:=2789) (by decide) v404 c405 rfl (by decide) (by decide) rfl

private def ps406 : List ℕ := 2791::ps405
private theorem c406 : F ps405 10034450=668464 := by decide +kernel
private theorem v406 : F ps406 28006150079=1989066597 :=
  takeStep (p:=2791) (by decide) v405 c406 rfl (by decide) (by decide) rfl

private def ps407 : List ℕ := 2797::ps406
private theorem c407 : F ps406 10012924=666970 := by decide +kernel
private theorem v407 : F ps407 28006150079=1988399627 :=
  takeStep (p:=2797) (by decide) v406 c407 rfl (by decide) (by decide) rfl

private def ps408 : List ℕ := 2801::ps407
private theorem c408 : F ps407 9998625=665973 := by decide +kernel
private theorem v408 : F ps408 28006150079=1987733654 :=
  takeStep (p:=2801) (by decide) v407 c408 rfl (by decide) (by decide) rfl

private def ps409 : List ℕ := 2803::ps408
private theorem c409 : F ps408 9991491=665423 := by decide +kernel
private theorem v409 : F ps409 28006150079=1987068231 :=
  takeStep (p:=2803) (by decide) v408 c409 rfl (by decide) (by decide) rfl

private def ps410 : List ℕ := 2819::ps409
private theorem c410 : F ps409 9934781=661775 := by decide +kernel
private theorem v410 : F ps410 28006150079=1986406456 :=
  takeStep (p:=2819) (by decide) v409 c410 rfl (by decide) (by decide) rfl

private def ps411 : List ℕ := 2833::ps410
private theorem c411 : F ps410 9885686=658582 := by decide +kernel
private theorem v411 : F ps411 28006150079=1985747874 :=
  takeStep (p:=2833) (by decide) v410 c411 rfl (by decide) (by decide) rfl

private def ps412 : List ℕ := 2837::ps411
private theorem c412 : F ps411 9871748=657627 := by decide +kernel
private theorem v412 : F ps412 28006150079=1985090247 :=
  takeStep (p:=2837) (by decide) v411 c412 rfl (by decide) (by decide) rfl

private def ps413 : List ℕ := 2843::ps412
private theorem c413 : F ps412 9850914=656239 := by decide +kernel
private theorem v413 : F ps413 28006150079=1984434008 :=
  takeStep (p:=2843) (by decide) v412 c413 rfl (by decide) (by decide) rfl

private def ps414 : List ℕ := 2851::ps413
private theorem c414 : F ps413 9823272=654443 := by decide +kernel
private theorem v414 : F ps414 28006150079=1983779565 :=
  takeStep (p:=2851) (by decide) v413 c414 rfl (by decide) (by decide) rfl

private def ps415 : List ℕ := 2857::ps414
private theorem c415 : F ps414 9802642=653057 := by decide +kernel
private theorem v415 : F ps415 28006150079=1983126508 :=
  takeStep (p:=2857) (by decide) v414 c415 rfl (by decide) (by decide) rfl

private def ps416 : List ℕ := 2861::ps415
private theorem c416 : F ps415 9788937=652098 := by decide +kernel
private theorem v416 : F ps416 28006150079=1982474410 :=
  takeStep (p:=2861) (by decide) v415 c416 rfl (by decide) (by decide) rfl

private def ps417 : List ℕ := 2879::ps416
private theorem c417 : F ps416 9727735=648170 := by decide +kernel
private theorem v417 : F ps417 28006150079=1981826240 :=
  takeStep (p:=2879) (by decide) v416 c417 rfl (by decide) (by decide) rfl

private def ps418 : List ℕ := 2887::ps417
private theorem c418 : F ps417 9700779=646415 := by decide +kernel
private theorem v418 : F ps418 28006150079=1981179825 :=
  takeStep (p:=2887) (by decide) v417 c418 rfl (by decide) (by decide) rfl

private def ps419 : List ℕ := 2897::ps418
private theorem c419 : F ps418 9667293=644257 := by decide +kernel
private theorem v419 : F ps419 28006150079=1980535568 :=
  takeStep (p:=2897) (by decide) v418 c419 rfl (by decide) (by decide) rfl

private def ps420 : List ℕ := 2903::ps419
private theorem c420 : F ps419 9647313=642934 := by decide +kernel
private theorem v420 : F ps420 28006150079=1979892634 :=
  takeStep (p:=2903) (by decide) v419 c420 rfl (by decide) (by decide) rfl

private def ps421 : List ℕ := 2909::ps420
private theorem c421 : F ps420 9627414=641629 := by decide +kernel
private theorem v421 : F ps421 28006150079=1979251005 :=
  takeStep (p:=2909) (by decide) v420 c421 rfl (by decide) (by decide) rfl

private def ps422 : List ℕ := 2917::ps421
private theorem c422 : F ps421 9601011=639923 := by decide +kernel
private theorem v422 : F ps422 28006150079=1978611082 :=
  takeStep (p:=2917) (by decide) v421 c422 rfl (by decide) (by decide) rfl

private def ps423 : List ℕ := 2927::ps422
private theorem c423 : F ps422 9568209=637770 := by decide +kernel
private theorem v423 : F ps423 28006150079=1977973312 :=
  takeStep (p:=2927) (by decide) v422 c423 rfl (by decide) (by decide) rfl

private def ps424 : List ℕ := 2939::ps423
private theorem c424 : F ps423 9529142=635269 := by decide +kernel
private theorem v424 : F ps424 28006150079=1977338043 :=
  takeStep (p:=2939) (by decide) v423 c424 rfl (by decide) (by decide) rfl

private def ps425 : List ℕ := 2953::ps424
private theorem c425 : F ps424 9483965=632401 := by decide +kernel
private theorem v425 : F ps425 28006150079=1976705642 :=
  takeStep (p:=2953) (by decide) v424 c425 rfl (by decide) (by decide) rfl

private def ps426 : List ℕ := 2957::ps425
private theorem c426 : F ps425 9471136=631575 := by decide +kernel
private theorem v426 : F ps426 28006150079=1976074067 :=
  takeStep (p:=2957) (by decide) v425 c426 rfl (by decide) (by decide) rfl

private def ps427 : List ℕ := 2963::ps426
private theorem c427 : F ps426 9451957=630364 := by decide +kernel
private theorem v427 : F ps427 28006150079=1975443703 :=
  takeStep (p:=2963) (by decide) v426 c427 rfl (by decide) (by decide) rfl

private def ps428 : List ℕ := 2969::ps427
private theorem c428 : F ps427 9432856=629139 := by decide +kernel
private theorem v428 : F ps428 28006150079=1974814564 :=
  takeStep (p:=2969) (by decide) v427 c428 rfl (by decide) (by decide) rfl

private def ps429 : List ℕ := 2971::ps428
private theorem c429 : F ps428 9426506=628722 := by decide +kernel
private theorem v429 : F ps429 28006150079=1974185842 :=
  takeStep (p:=2971) (by decide) v428 c429 rfl (by decide) (by decide) rfl

private def ps430 : List ℕ := 2999::ps429
private theorem c430 : F ps429 9338496=623214 := by decide +kernel
private theorem v430 : F ps430 28006150079=1973562628 :=
  takeStep (p:=2999) (by decide) v429 c430 rfl (by decide) (by decide) rfl

private def ps431 : List ℕ := 3001::ps430
private theorem c431 : F ps430 9332272=622796 := by decide +kernel
private theorem v431 : F ps431 28006150079=1972939832 :=
  takeStep (p:=3001) (by decide) v430 c431 rfl (by decide) (by decide) rfl

private def ps432 : List ℕ := 3011::ps431
private theorem c432 : F ps431 9301278=620856 := by decide +kernel
private theorem v432 : F ps432 28006150079=1972318976 :=
  takeStep (p:=3011) (by decide) v431 c432 rfl (by decide) (by decide) rfl

private def ps433 : List ℕ := 3019::ps432
private theorem c433 : F ps432 9276631=619303 := by decide +kernel
private theorem v433 : F ps433 28006150079=1971699673 :=
  takeStep (p:=3019) (by decide) v432 c433 rfl (by decide) (by decide) rfl

private def ps434 : List ℕ := 3023::ps433
private theorem c434 : F ps433 9264356=618523 := by decide +kernel
private theorem v434 : F ps434 28006150079=1971081150 :=
  takeStep (p:=3023) (by decide) v433 c434 rfl (by decide) (by decide) rfl

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

private def l0_94 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]
private theorem l0_94ok : (List.range' 0 94).filter prime = l0_94 :=
  by decide +kernel

private def l94_189 : List ℕ := [97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181]
private theorem l94_189ok : (List.range' 94 95).filter prime = l94_189 :=
  by decide +kernel

private def l0_189 : List ℕ := l0_94 ++ l94_189
private theorem l0_189ok : (List.range' 0 189).filter prime = l0_189 :=
  merge_filter _ 0 94 95 _ _ l0_94ok l94_189ok

private def l189_284 : List ℕ := [191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283]
private theorem l189_284ok : (List.range' 189 95).filter prime = l189_284 :=
  by decide +kernel

private def l284_379 : List ℕ := [293,307,311,313,317,331,337,347,349,353,359,367,373]
private theorem l284_379ok : (List.range' 284 95).filter prime = l284_379 :=
  by decide +kernel

private def l189_379 : List ℕ := l189_284 ++ l284_379
private theorem l189_379ok : (List.range' 189 190).filter prime = l189_379 :=
  merge_filter _ 189 95 95 _ _ l189_284ok l284_379ok

private def l0_379 : List ℕ := l0_189 ++ l189_379
private theorem l0_379ok : (List.range' 0 379).filter prime = l0_379 :=
  merge_filter _ 0 189 190 _ _ l0_189ok l189_379ok

private def l379_474 : List ℕ := [379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467]
private theorem l379_474ok : (List.range' 379 95).filter prime = l379_474 :=
  by decide +kernel

private def l474_569 : List ℕ := [479,487,491,499,503,509,521,523,541,547,557,563]
private theorem l474_569ok : (List.range' 474 95).filter prime = l474_569 :=
  by decide +kernel

private def l379_569 : List ℕ := l379_474 ++ l474_569
private theorem l379_569ok : (List.range' 379 190).filter prime = l379_569 :=
  merge_filter _ 379 95 95 _ _ l379_474ok l474_569ok

private def l569_664 : List ℕ := [569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661]
private theorem l569_664ok : (List.range' 569 95).filter prime = l569_664 :=
  by decide +kernel

private def l664_759 : List ℕ := [673,677,683,691,701,709,719,727,733,739,743,751,757]
private theorem l664_759ok : (List.range' 664 95).filter prime = l664_759 :=
  by decide +kernel

private def l569_759 : List ℕ := l569_664 ++ l664_759
private theorem l569_759ok : (List.range' 569 190).filter prime = l569_759 :=
  merge_filter _ 569 95 95 _ _ l569_664ok l664_759ok

private def l379_759 : List ℕ := l379_569 ++ l569_759
private theorem l379_759ok : (List.range' 379 380).filter prime = l379_759 :=
  merge_filter _ 379 190 190 _ _ l379_569ok l569_759ok

private def l0_759 : List ℕ := l0_379 ++ l379_759
private theorem l0_759ok : (List.range' 0 759).filter prime = l0_759 :=
  merge_filter _ 0 379 380 _ _ l0_379ok l379_759ok

private def l759_853 : List ℕ := [761,769,773,787,797,809,811,821,823,827,829,839]
private theorem l759_853ok : (List.range' 759 94).filter prime = l759_853 :=
  by decide +kernel

private def l853_948 : List ℕ := [853,857,859,863,877,881,883,887,907,911,919,929,937,941,947]
private theorem l853_948ok : (List.range' 853 95).filter prime = l853_948 :=
  by decide +kernel

private def l759_948 : List ℕ := l759_853 ++ l853_948
private theorem l759_948ok : (List.range' 759 189).filter prime = l759_948 :=
  merge_filter _ 759 94 95 _ _ l759_853ok l853_948ok

private def l948_1043 : List ℕ := [953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039]
private theorem l948_1043ok : (List.range' 948 95).filter prime = l948_1043 :=
  by decide +kernel

private def l1043_1138 : List ℕ := [1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129]
private theorem l1043_1138ok : (List.range' 1043 95).filter prime = l1043_1138 :=
  by decide +kernel

private def l948_1138 : List ℕ := l948_1043 ++ l1043_1138
private theorem l948_1138ok : (List.range' 948 190).filter prime = l948_1138 :=
  merge_filter _ 948 95 95 _ _ l948_1043ok l1043_1138ok

private def l759_1138 : List ℕ := l759_948 ++ l948_1138
private theorem l759_1138ok : (List.range' 759 379).filter prime = l759_1138 :=
  merge_filter _ 759 189 190 _ _ l759_948ok l948_1138ok

private def l1138_1233 : List ℕ := [1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231]
private theorem l1138_1233ok : (List.range' 1138 95).filter prime = l1138_1233 :=
  by decide +kernel

private def l1233_1328 : List ℕ := [1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327]
private theorem l1233_1328ok : (List.range' 1233 95).filter prime = l1233_1328 :=
  by decide +kernel

private def l1138_1328 : List ℕ := l1138_1233 ++ l1233_1328
private theorem l1138_1328ok : (List.range' 1138 190).filter prime = l1138_1328 :=
  merge_filter _ 1138 95 95 _ _ l1138_1233ok l1233_1328ok

private def l1328_1423 : List ℕ := [1361,1367,1373,1381,1399,1409]
private theorem l1328_1423ok : (List.range' 1328 95).filter prime = l1328_1423 :=
  by decide +kernel

private def l1423_1518 : List ℕ := [1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511]
private theorem l1423_1518ok : (List.range' 1423 95).filter prime = l1423_1518 :=
  by decide +kernel

private def l1328_1518 : List ℕ := l1328_1423 ++ l1423_1518
private theorem l1328_1518ok : (List.range' 1328 190).filter prime = l1328_1518 :=
  merge_filter _ 1328 95 95 _ _ l1328_1423ok l1423_1518ok

private def l1138_1518 : List ℕ := l1138_1328 ++ l1328_1518
private theorem l1138_1518ok : (List.range' 1138 380).filter prime = l1138_1518 :=
  merge_filter _ 1138 190 190 _ _ l1138_1328ok l1328_1518ok

private def l759_1518 : List ℕ := l759_1138 ++ l1138_1518
private theorem l759_1518ok : (List.range' 759 759).filter prime = l759_1518 :=
  merge_filter _ 759 379 380 _ _ l759_1138ok l1138_1518ok

private def l0_1518 : List ℕ := l0_759 ++ l759_1518
private theorem l0_1518ok : (List.range' 0 1518).filter prime = l0_1518 :=
  merge_filter _ 0 759 759 _ _ l0_759ok l759_1518ok

private def l1518_1612 : List ℕ := [1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609]
private theorem l1518_1612ok : (List.range' 1518 94).filter prime = l1518_1612 :=
  by decide +kernel

private def l1612_1707 : List ℕ := [1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699]
private theorem l1612_1707ok : (List.range' 1612 95).filter prime = l1612_1707 :=
  by decide +kernel

private def l1518_1707 : List ℕ := l1518_1612 ++ l1612_1707
private theorem l1518_1707ok : (List.range' 1518 189).filter prime = l1518_1707 :=
  merge_filter _ 1518 94 95 _ _ l1518_1612ok l1612_1707ok

private def l1707_1802 : List ℕ := [1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801]
private theorem l1707_1802ok : (List.range' 1707 95).filter prime = l1707_1802 :=
  by decide +kernel

private def l1802_1897 : List ℕ := [1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889]
private theorem l1802_1897ok : (List.range' 1802 95).filter prime = l1802_1897 :=
  by decide +kernel

private def l1707_1897 : List ℕ := l1707_1802 ++ l1802_1897
private theorem l1707_1897ok : (List.range' 1707 190).filter prime = l1707_1897 :=
  merge_filter _ 1707 95 95 _ _ l1707_1802ok l1802_1897ok

private def l1518_1897 : List ℕ := l1518_1707 ++ l1707_1897
private theorem l1518_1897ok : (List.range' 1518 379).filter prime = l1518_1897 :=
  merge_filter _ 1518 189 190 _ _ l1518_1707ok l1707_1897ok

private def l1897_1992 : List ℕ := [1901,1907,1913,1931,1933,1949,1951,1973,1979,1987]
private theorem l1897_1992ok : (List.range' 1897 95).filter prime = l1897_1992 :=
  by decide +kernel

private def l1992_2087 : List ℕ := [1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083]
private theorem l1992_2087ok : (List.range' 1992 95).filter prime = l1992_2087 :=
  by decide +kernel

private def l1897_2087 : List ℕ := l1897_1992 ++ l1992_2087
private theorem l1897_2087ok : (List.range' 1897 190).filter prime = l1897_2087 :=
  merge_filter _ 1897 95 95 _ _ l1897_1992ok l1992_2087ok

private def l2087_2182 : List ℕ := [2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179]
private theorem l2087_2182ok : (List.range' 2087 95).filter prime = l2087_2182 :=
  by decide +kernel

private def l2182_2277 : List ℕ := [2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273]
private theorem l2182_2277ok : (List.range' 2182 95).filter prime = l2182_2277 :=
  by decide +kernel

private def l2087_2277 : List ℕ := l2087_2182 ++ l2182_2277
private theorem l2087_2277ok : (List.range' 2087 190).filter prime = l2087_2277 :=
  merge_filter _ 2087 95 95 _ _ l2087_2182ok l2182_2277ok

private def l1897_2277 : List ℕ := l1897_2087 ++ l2087_2277
private theorem l1897_2277ok : (List.range' 1897 380).filter prime = l1897_2277 :=
  merge_filter _ 1897 190 190 _ _ l1897_2087ok l2087_2277ok

private def l1518_2277 : List ℕ := l1518_1897 ++ l1897_2277
private theorem l1518_2277ok : (List.range' 1518 759).filter prime = l1518_2277 :=
  merge_filter _ 1518 379 380 _ _ l1518_1897ok l1897_2277ok

private def l2277_2372 : List ℕ := [2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371]
private theorem l2277_2372ok : (List.range' 2277 95).filter prime = l2277_2372 :=
  by decide +kernel

private def l2372_2467 : List ℕ := [2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459]
private theorem l2372_2467ok : (List.range' 2372 95).filter prime = l2372_2467 :=
  by decide +kernel

private def l2277_2467 : List ℕ := l2277_2372 ++ l2372_2467
private theorem l2277_2467ok : (List.range' 2277 190).filter prime = l2277_2467 :=
  merge_filter _ 2277 95 95 _ _ l2277_2372ok l2372_2467ok

private def l2467_2562 : List ℕ := [2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557]
private theorem l2467_2562ok : (List.range' 2467 95).filter prime = l2467_2562 :=
  by decide +kernel

private def l2562_2657 : List ℕ := [2579,2591,2593,2609,2617,2621,2633,2647]
private theorem l2562_2657ok : (List.range' 2562 95).filter prime = l2562_2657 :=
  by decide +kernel

private def l2467_2657 : List ℕ := l2467_2562 ++ l2562_2657
private theorem l2467_2657ok : (List.range' 2467 190).filter prime = l2467_2657 :=
  merge_filter _ 2467 95 95 _ _ l2467_2562ok l2562_2657ok

private def l2277_2657 : List ℕ := l2277_2467 ++ l2467_2657
private theorem l2277_2657ok : (List.range' 2277 380).filter prime = l2277_2657 :=
  merge_filter _ 2277 190 190 _ _ l2277_2467ok l2467_2657ok

private def l2657_2752 : List ℕ := [2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749]
private theorem l2657_2752ok : (List.range' 2657 95).filter prime = l2657_2752 :=
  by decide +kernel

private def l2752_2847 : List ℕ := [2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843]
private theorem l2752_2847ok : (List.range' 2752 95).filter prime = l2752_2847 :=
  by decide +kernel

private def l2657_2847 : List ℕ := l2657_2752 ++ l2752_2847
private theorem l2657_2847ok : (List.range' 2657 190).filter prime = l2657_2847 :=
  merge_filter _ 2657 95 95 _ _ l2657_2752ok l2752_2847ok

private def l2847_2942 : List ℕ := [2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939]
private theorem l2847_2942ok : (List.range' 2847 95).filter prime = l2847_2942 :=
  by decide +kernel

private def l2942_3037 : List ℕ := [2953,2957,2963,2969,2971,2999,3001,3011,3019,3023]
private theorem l2942_3037ok : (List.range' 2942 95).filter prime = l2942_3037 :=
  by decide +kernel

private def l2847_3037 : List ℕ := l2847_2942 ++ l2942_3037
private theorem l2847_3037ok : (List.range' 2847 190).filter prime = l2847_3037 :=
  merge_filter _ 2847 95 95 _ _ l2847_2942ok l2942_3037ok

private def l2657_3037 : List ℕ := l2657_2847 ++ l2847_3037
private theorem l2657_3037ok : (List.range' 2657 380).filter prime = l2657_3037 :=
  merge_filter _ 2657 190 190 _ _ l2657_2847ok l2847_3037ok

private def l2277_3037 : List ℕ := l2277_2657 ++ l2657_3037
private theorem l2277_3037ok : (List.range' 2277 760).filter prime = l2277_3037 :=
  merge_filter _ 2277 380 380 _ _ l2277_2657ok l2657_3037ok

private def l1518_3037 : List ℕ := l1518_2277 ++ l2277_3037
private theorem l1518_3037ok : (List.range' 1518 1519).filter prime = l1518_3037 :=
  merge_filter _ 1518 759 760 _ _ l1518_2277ok l2277_3037ok

private def l0_3037 : List ℕ := l0_1518 ++ l1518_3037
private theorem l0_3037ok : (List.range' 0 3037).filter prime = l0_3037 :=
  merge_filter _ 0 1518 1519 _ _ l0_1518ok l1518_3037ok

set_option maxRecDepth 8000 in
private theorem last_row :
    ((List.range (3036+1)).filter (fun p => decide p.Prime)).reverse = ps434 := by
  rw [filter_from_test prime prime_ok 3036 (by decide),List.range_eq_range',l0_3037ok]
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
    (((List.range (3036+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id 28006150079) +
    (Nat.primesLE 3036).card = 1971081584 := by
  exact left_from_rows tab HybridBound28006.fast_correct ps434 (by decide) (by decide) last_row (show evalPhi tab ps434 28006150079 = 1971081150 from v434) (by decide +kernel)

private abbrev term := contribution 28006150079 3036 tab prime

private theorem s0 : blockSum term 0 326 0 := by unfold blockSum; decide +kernel

private theorem s326 : blockSum term 326 327 0 := by unfold blockSum; decide +kernel

private theorem s653 : blockSum term 653 327 0 := by unfold blockSum; decide +kernel

private theorem s980 : blockSum term 980 327 0 := by unfold blockSum; decide +kernel

private theorem s1307 : blockSum term 1307 326 0 := by unfold blockSum; decide +kernel

private theorem s1633 : blockSum term 1633 327 0 := by unfold blockSum; decide +kernel

private theorem s1960 : blockSum term 1960 327 0 := by unfold blockSum; decide +kernel

private theorem s2287 : blockSum term 2287 327 0 := by unfold blockSum; decide +kernel

private theorem s2614 : blockSum term 2614 326 0 := by unfold blockSum; decide +kernel

private theorem s2940 : blockSum term 2940 327 16060285 := by unfold blockSum; decide +kernel

private theorem s3267 : blockSum term 3267 327 23047323 := by unfold blockSum; decide +kernel

private theorem s3594 : blockSum term 3594 327 20188544 := by unfold blockSum; decide +kernel

private theorem s3921 : blockSum term 3921 327 18210648 := by unfold blockSum; decide +kernel

private theorem s4248 : blockSum term 4248 327 16087560 := by unfold blockSum; decide +kernel

private theorem s4575 : blockSum term 4575 327 14266142 := by unfold blockSum; decide +kernel

private theorem s4902 : blockSum term 4902 327 15332730 := by unfold blockSum; decide +kernel

private theorem s5229 : blockSum term 5229 326 13690123 := by unfold blockSum; decide +kernel

private theorem s5555 : blockSum term 5555 327 14638287 := by unfold blockSum; decide +kernel

private theorem s5882 : blockSum term 5882 327 10337525 := by unfold blockSum; decide +kernel

private theorem s6209 : blockSum term 6209 327 11441247 := by unfold blockSum; decide +kernel

private theorem s6536 : blockSum term 6536 327 11185023 := by unfold blockSum; decide +kernel

private theorem s6863 : blockSum term 6863 327 10149489 := by unfold blockSum; decide +kernel

private theorem s7190 : blockSum term 7190 327 8906521 := by unfold blockSum; decide +kernel

private theorem s7517 : blockSum term 7517 327 10381440 := by unfold blockSum; decide +kernel

private theorem s7844 : blockSum term 7844 326 8469585 := by unfold blockSum; decide +kernel

private theorem s8170 : blockSum term 8170 327 8170967 := by unfold blockSum; decide +kernel

private theorem s8497 : blockSum term 8497 327 9253702 := by unfold blockSum; decide +kernel

private theorem s8824 : blockSum term 8824 327 7604060 := by unfold blockSum; decide +kernel

private theorem s9151 : blockSum term 9151 327 8857443 := by unfold blockSum; decide +kernel

private theorem s9478 : blockSum term 9478 327 7317803 := by unfold blockSum; decide +kernel

private theorem s9805 : blockSum term 9805 327 6699409 := by unfold blockSum; decide +kernel

private theorem s10132 : blockSum term 10132 327 7288817 := by unfold blockSum; decide +kernel

private theorem s10459 : blockSum term 10459 326 6496056 := by unfold blockSum; decide +kernel

private theorem s10785 : blockSum term 10785 327 5942661 := by unfold blockSum; decide +kernel

private theorem s11112 : blockSum term 11112 327 6145776 := by unfold blockSum; decide +kernel

private theorem s11439 : blockSum term 11439 327 5280880 := by unfold blockSum; decide +kernel

private theorem s11766 : blockSum term 11766 326 6345765 := by unfold blockSum; decide +kernel

private theorem s12092 : blockSum term 12092 327 6016197 := by unfold blockSum; decide +kernel

private theorem s12419 : blockSum term 12419 327 6356615 := by unfold blockSum; decide +kernel

private theorem s12746 : blockSum term 12746 327 5563714 := by unfold blockSum; decide +kernel

private theorem s13073 : blockSum term 13073 326 4973051 := by unfold blockSum; decide +kernel

private theorem s13399 : blockSum term 13399 327 5461269 := by unfold blockSum; decide +kernel

private theorem s13726 : blockSum term 13726 327 4899239 := by unfold blockSum; decide +kernel

private theorem s14053 : blockSum term 14053 327 3921555 := by unfold blockSum; decide +kernel

private theorem s14380 : blockSum term 14380 327 5120078 := by unfold blockSum; decide +kernel

private theorem s14707 : blockSum term 14707 327 5154954 := by unfold blockSum; decide +kernel

private theorem s15034 : blockSum term 15034 327 5039214 := by unfold blockSum; decide +kernel

private theorem s15361 : blockSum term 15361 327 4938792 := by unfold blockSum; decide +kernel

private theorem s15688 : blockSum term 15688 326 4319863 := by unfold blockSum; decide +kernel

private theorem s16014 : blockSum term 16014 327 3982300 := by unfold blockSum; decide +kernel

private theorem s16341 : blockSum term 16341 327 4157473 := by unfold blockSum; decide +kernel

private theorem s16668 : blockSum term 16668 327 3954762 := by unfold blockSum; decide +kernel

private theorem s16995 : blockSum term 16995 327 3765223 := by unfold blockSum; decide +kernel

private theorem s17322 : blockSum term 17322 327 4295884 := by unfold blockSum; decide +kernel

private theorem s17649 : blockSum term 17649 327 3866028 := by unfold blockSum; decide +kernel

private theorem s17976 : blockSum term 17976 327 4260833 := by unfold blockSum; decide +kernel

private theorem s18303 : blockSum term 18303 326 3626389 := by unfold blockSum; decide +kernel

private theorem s18629 : blockSum term 18629 327 2895568 := by unfold blockSum; decide +kernel

private theorem s18956 : blockSum term 18956 327 3393760 := by unfold blockSum; decide +kernel

private theorem s19283 : blockSum term 19283 327 4198981 := by unfold blockSum; decide +kernel

private theorem s19610 : blockSum term 19610 327 2965711 := by unfold blockSum; decide +kernel

private theorem s19937 : blockSum term 19937 327 3863014 := by unfold blockSum; decide +kernel

private theorem s20264 : blockSum term 20264 327 3186036 := by unfold blockSum; decide +kernel

private theorem s20591 : blockSum term 20591 327 3136688 := by unfold blockSum; decide +kernel

private theorem s20918 : blockSum term 20918 326 3489324 := by unfold blockSum; decide +kernel

private theorem s21244 : blockSum term 21244 327 3336657 := by unfold blockSum; decide +kernel

private theorem s21571 : blockSum term 21571 327 3387380 := by unfold blockSum; decide +kernel

private theorem s21898 : blockSum term 21898 327 3147672 := by unfold blockSum; decide +kernel

private theorem s22225 : blockSum term 22225 326 3008818 := by unfold blockSum; decide +kernel

private theorem s22551 : blockSum term 22551 327 3151402 := by unfold blockSum; decide +kernel

private theorem s22878 : blockSum term 22878 327 3198838 := by unfold blockSum; decide +kernel

private theorem s23205 : blockSum term 23205 327 2256316 := by unfold blockSum; decide +kernel

private theorem s23532 : blockSum term 23532 326 3383514 := by unfold blockSum; decide +kernel

private theorem s23858 : blockSum term 23858 327 3423470 := by unfold blockSum; decide +kernel

private theorem s24185 : blockSum term 24185 327 2337727 := by unfold blockSum; decide +kernel

private theorem s24512 : blockSum term 24512 327 2223521 := by unfold blockSum; decide +kernel

private theorem s24839 : blockSum term 24839 327 2701827 := by unfold blockSum; decide +kernel

private theorem s25166 : blockSum term 25166 327 2750135 := by unfold blockSum; decide +kernel

private theorem s25493 : blockSum term 25493 327 2631907 := by unfold blockSum; decide +kernel

private theorem s25820 : blockSum term 25820 327 2519071 := by unfold blockSum; decide +kernel

private theorem s26147 : blockSum term 26147 326 2729405 := by unfold blockSum; decide +kernel

private theorem s26473 : blockSum term 26473 327 2537024 := by unfold blockSum; decide +kernel

private theorem s26800 : blockSum term 26800 327 2743018 := by unfold blockSum; decide +kernel

private theorem s27127 : blockSum term 27127 327 2012803 := by unfold blockSum; decide +kernel

private theorem s27454 : blockSum term 27454 327 2447147 := by unfold blockSum; decide +kernel

private theorem s27781 : blockSum term 27781 327 2571387 := by unfold blockSum; decide +kernel

private theorem s28108 : blockSum term 28108 327 2092289 := by unfold blockSum; decide +kernel

private theorem s28435 : blockSum term 28435 327 2881654 := by unfold blockSum; decide +kernel

private theorem s28762 : blockSum term 28762 326 2119474 := by unfold blockSum; decide +kernel

private theorem s29088 : blockSum term 29088 327 2456424 := by unfold blockSum; decide +kernel

private theorem s29415 : blockSum term 29415 327 2001609 := by unfold blockSum; decide +kernel

private theorem s29742 : blockSum term 29742 327 1838624 := by unfold blockSum; decide +kernel

private theorem s30069 : blockSum term 30069 327 2379064 := by unfold blockSum; decide +kernel

private theorem s30396 : blockSum term 30396 327 2074634 := by unfold blockSum; decide +kernel

private theorem s30723 : blockSum term 30723 327 2053413 := by unfold blockSum; decide +kernel

private theorem s31050 : blockSum term 31050 327 2438597 := by unfold blockSum; decide +kernel

private theorem s31377 : blockSum term 31377 326 1943134 := by unfold blockSum; decide +kernel

private theorem s31703 : blockSum term 31703 327 1790604 := by unfold blockSum; decide +kernel

private theorem s32030 : blockSum term 32030 327 2231503 := by unfold blockSum; decide +kernel

private theorem s32357 : blockSum term 32357 327 2274457 := by unfold blockSum; decide +kernel

private theorem s32684 : blockSum term 32684 327 2121331 := by unfold blockSum; decide +kernel

private theorem s33011 : blockSum term 33011 327 1973487 := by unfold blockSum; decide +kernel

private theorem s33338 : blockSum term 33338 327 2394089 := by unfold blockSum; decide +kernel

private theorem s33665 : blockSum term 33665 327 1871830 := by unfold blockSum; decide +kernel

private theorem s33992 : blockSum term 33992 326 1851873 := by unfold blockSum; decide +kernel

private theorem s34318 : blockSum term 34318 327 1957509 := by unfold blockSum; decide +kernel

private theorem s34645 : blockSum term 34645 327 1938943 := by unfold blockSum; decide +kernel

private theorem s34972 : blockSum term 34972 327 1739543 := by unfold blockSum; decide +kernel

private theorem s35299 : blockSum term 35299 327 1960450 := by unfold blockSum; decide +kernel

private theorem s35626 : blockSum term 35626 327 1469990 := by unfold blockSum; decide +kernel

private theorem s35953 : blockSum term 35953 327 1865960 := by unfold blockSum; decide +kernel

private theorem s36280 : blockSum term 36280 327 1789960 := by unfold blockSum; decide +kernel

private theorem s36607 : blockSum term 36607 326 2115947 := by unfold blockSum; decide +kernel

private theorem s36933 : blockSum term 36933 327 1586941 := by unfold blockSum; decide +kernel

private theorem s37260 : blockSum term 37260 327 1964563 := by unfold blockSum; decide +kernel

private theorem s37587 : blockSum term 37587 327 1558669 := by unfold blockSum; decide +kernel

private theorem s37914 : blockSum term 37914 327 1544046 := by unfold blockSum; decide +kernel

private theorem s38241 : blockSum term 38241 327 1421990 := by unfold blockSum; decide +kernel

private theorem s38568 : blockSum term 38568 327 1842590 := by unfold blockSum; decide +kernel

private theorem s38895 : blockSum term 38895 327 1718328 := by unfold blockSum; decide +kernel

private theorem s39222 : blockSum term 39222 326 1650984 := by unfold blockSum; decide +kernel

private theorem s39548 : blockSum term 39548 327 1687851 := by unfold blockSum; decide +kernel

private theorem s39875 : blockSum term 39875 327 1621086 := by unfold blockSum; decide +kernel

private theorem s40202 : blockSum term 40202 327 1295981 := by unfold blockSum; decide +kernel

private theorem s40529 : blockSum term 40529 327 1593343 := by unfold blockSum; decide +kernel

private theorem s40856 : blockSum term 40856 327 1528953 := by unfold blockSum; decide +kernel

private theorem s41183 : blockSum term 41183 327 1567347 := by unfold blockSum; decide +kernel

private theorem s41510 : blockSum term 41510 327 1604172 := by unfold blockSum; decide +kernel

private theorem s41837 : blockSum term 41837 326 1690165 := by unfold blockSum; decide +kernel

private theorem s42163 : blockSum term 42163 327 1921125 := by unfold blockSum; decide +kernel

private theorem s42490 : blockSum term 42490 327 1514142 := by unfold blockSum; decide +kernel

private theorem s42817 : blockSum term 42817 327 1453908 := by unfold blockSum; decide +kernel

private theorem s43144 : blockSum term 43144 326 1201339 := by unfold blockSum; decide +kernel

private theorem s43470 : blockSum term 43470 327 1524660 := by unfold blockSum; decide +kernel

private theorem s43797 : blockSum term 43797 327 1417759 := by unfold blockSum; decide +kernel

private theorem s44124 : blockSum term 44124 327 1267035 := by unfold blockSum; decide +kernel

private theorem s44451 : blockSum term 44451 326 1535902 := by unfold blockSum; decide +kernel

private theorem s44777 : blockSum term 44777 327 1293578 := by unfold blockSum; decide +kernel

private theorem s45104 : blockSum term 45104 327 1420536 := by unfold blockSum; decide +kernel

private theorem s45431 : blockSum term 45431 327 1272455 := by unfold blockSum; decide +kernel

private theorem s45758 : blockSum term 45758 327 1217725 := by unfold blockSum; decide +kernel

private theorem s46085 : blockSum term 46085 327 1342455 := by unfold blockSum; decide +kernel

private theorem s46412 : blockSum term 46412 327 1420276 := by unfold blockSum; decide +kernel

private theorem s46739 : blockSum term 46739 327 1189544 := by unfold blockSum; decide +kernel

private theorem s47066 : blockSum term 47066 326 1354317 := by unfold blockSum; decide +kernel

private theorem s47392 : blockSum term 47392 327 1430783 := by unfold blockSum; decide +kernel

private theorem s47719 : blockSum term 47719 327 1247718 := by unfold blockSum; decide +kernel

private theorem s48046 : blockSum term 48046 327 1152710 := by unfold blockSum; decide +kernel

private theorem s48373 : blockSum term 48373 327 1355836 := by unfold blockSum; decide +kernel

private theorem s48700 : blockSum term 48700 327 1261438 := by unfold blockSum; decide +kernel

private theorem s49027 : blockSum term 49027 327 1335344 := by unfold blockSum; decide +kernel

private theorem s49354 : blockSum term 49354 327 1325166 := by unfold blockSum; decide +kernel

private theorem s49681 : blockSum term 49681 326 1274134 := by unfold blockSum; decide +kernel

private theorem s50007 : blockSum term 50007 327 1346175 := by unfold blockSum; decide +kernel

private theorem s50334 : blockSum term 50334 327 1133723 := by unfold blockSum; decide +kernel

private theorem s50661 : blockSum term 50661 327 1044846 := by unfold blockSum; decide +kernel

private theorem s50988 : blockSum term 50988 327 1157030 := by unfold blockSum; decide +kernel

private theorem s51315 : blockSum term 51315 327 1426003 := by unfold blockSum; decide +kernel

private theorem s51642 : blockSum term 51642 327 1179648 := by unfold blockSum; decide +kernel

private theorem s51969 : blockSum term 51969 327 1210110 := by unfold blockSum; decide +kernel

private theorem s52296 : blockSum term 52296 326 1007511 := by unfold blockSum; decide +kernel

private theorem s52622 : blockSum term 52622 327 1116129 := by unfold blockSum; decide +kernel

private theorem s52949 : blockSum term 52949 327 1261019 := by unfold blockSum; decide +kernel

private theorem s53276 : blockSum term 53276 327 1024077 := by unfold blockSum; decide +kernel

private theorem s53603 : blockSum term 53603 327 1280165 := by unfold blockSum; decide +kernel

private theorem s53930 : blockSum term 53930 327 897245 := by unfold blockSum; decide +kernel

private theorem s54257 : blockSum term 54257 327 1372482 := by unfold blockSum; decide +kernel

private theorem s54584 : blockSum term 54584 327 957889 := by unfold blockSum; decide +kernel

private theorem s54911 : blockSum term 54911 326 1097471 := by unfold blockSum; decide +kernel

private theorem s55237 : blockSum term 55237 327 908318 := by unfold blockSum; decide +kernel

private theorem s55564 : blockSum term 55564 327 1262623 := by unfold blockSum; decide +kernel

private theorem s55891 : blockSum term 55891 327 1110535 := by unfold blockSum; decide +kernel

private theorem s56218 : blockSum term 56218 327 1173130 := by unfold blockSum; decide +kernel

private theorem s56545 : blockSum term 56545 327 1023772 := by unfold blockSum; decide +kernel

private theorem s56872 : blockSum term 56872 327 1262357 := by unfold blockSum; decide +kernel

private theorem s57199 : blockSum term 57199 327 940229 := by unfold blockSum; decide +kernel

private theorem s57526 : blockSum term 57526 326 1140735 := by unfold blockSum; decide +kernel

private theorem s57852 : blockSum term 57852 327 1030122 := by unfold blockSum; decide +kernel

private theorem s58179 : blockSum term 58179 327 1057373 := by unfold blockSum; decide +kernel

private theorem s58506 : blockSum term 58506 327 914512 := by unfold blockSum; decide +kernel

private theorem s58833 : blockSum term 58833 327 1109335 := by unfold blockSum; decide +kernel

private theorem s59160 : blockSum term 59160 327 1101808 := by unfold blockSum; decide +kernel

private theorem s59487 : blockSum term 59487 327 1027669 := by unfold blockSum; decide +kernel

private theorem s59814 : blockSum term 59814 327 855509 := by unfold blockSum; decide +kernel

private theorem s60141 : blockSum term 60141 326 850322 := by unfold blockSum; decide +kernel

private theorem s60467 : blockSum term 60467 327 1006699 := by unfold blockSum; decide +kernel

private theorem s60794 : blockSum term 60794 327 807052 := by unfold blockSum; decide +kernel

private theorem s61121 : blockSum term 61121 327 833861 := by unfold blockSum; decide +kernel

private theorem s61448 : blockSum term 61448 327 1083230 := by unfold blockSum; decide +kernel

private theorem s61775 : blockSum term 61775 327 886045 := by unfold blockSum; decide +kernel

private theorem s62102 : blockSum term 62102 327 848947 := by unfold blockSum; decide +kernel

private theorem s62429 : blockSum term 62429 327 905727 := by unfold blockSum; decide +kernel

private theorem s62756 : blockSum term 62756 326 869002 := by unfold blockSum; decide +kernel

private theorem s63082 : blockSum term 63082 327 862731 := by unfold blockSum; decide +kernel

private theorem s63409 : blockSum term 63409 327 1132505 := by unfold blockSum; decide +kernel

private theorem s63736 : blockSum term 63736 327 821268 := by unfold blockSum; decide +kernel

private theorem s64063 : blockSum term 64063 326 785820 := by unfold blockSum; decide +kernel

private theorem s64389 : blockSum term 64389 327 810223 := by unfold blockSum; decide +kernel

private theorem s64716 : blockSum term 64716 327 804609 := by unfold blockSum; decide +kernel

private theorem s65043 : blockSum term 65043 327 888323 := by unfold blockSum; decide +kernel

private theorem s65370 : blockSum term 65370 326 970447 := by unfold blockSum; decide +kernel

private theorem s65696 : blockSum term 65696 327 876915 := by unfold blockSum; decide +kernel

private theorem s66023 : blockSum term 66023 327 725952 := by unfold blockSum; decide +kernel

private theorem s66350 : blockSum term 66350 327 836500 := by unfold blockSum; decide +kernel

private theorem s66677 : blockSum term 66677 327 888199 := by unfold blockSum; decide +kernel

private theorem s67004 : blockSum term 67004 327 853852 := by unfold blockSum; decide +kernel

private theorem s67331 : blockSum term 67331 327 961248 := by unfold blockSum; decide +kernel

private theorem s67658 : blockSum term 67658 327 898546 := by unfold blockSum; decide +kernel

private theorem s67985 : blockSum term 67985 326 669757 := by unfold blockSum; decide +kernel

private theorem s68311 : blockSum term 68311 327 720739 := by unfold blockSum; decide +kernel

private theorem s68638 : blockSum term 68638 327 853787 := by unfold blockSum; decide +kernel

private theorem s68965 : blockSum term 68965 327 738865 := by unfold blockSum; decide +kernel

private theorem s69292 : blockSum term 69292 327 680255 := by unfold blockSum; decide +kernel

private theorem s69619 : blockSum term 69619 327 729869 := by unfold blockSum; decide +kernel

private theorem s69946 : blockSum term 69946 327 886492 := by unfold blockSum; decide +kernel

private theorem s70273 : blockSum term 70273 327 773962 := by unfold blockSum; decide +kernel

private theorem s70600 : blockSum term 70600 326 769118 := by unfold blockSum; decide +kernel

private theorem s70926 : blockSum term 70926 327 790784 := by unfold blockSum; decide +kernel

private theorem s71253 : blockSum term 71253 327 942330 := by unfold blockSum; decide +kernel

private theorem s71580 : blockSum term 71580 327 727597 := by unfold blockSum; decide +kernel

private theorem s71907 : blockSum term 71907 327 852092 := by unfold blockSum; decide +kernel

private theorem s72234 : blockSum term 72234 327 692888 := by unfold blockSum; decide +kernel

private theorem s72561 : blockSum term 72561 327 688547 := by unfold blockSum; decide +kernel

private theorem s72888 : blockSum term 72888 327 760476 := by unfold blockSum; decide +kernel

private theorem s73215 : blockSum term 73215 326 654530 := by unfold blockSum; decide +kernel

private theorem s73541 : blockSum term 73541 327 775782 := by unfold blockSum; decide +kernel

private theorem s73868 : blockSum term 73868 327 695935 := by unfold blockSum; decide +kernel

private theorem s74195 : blockSum term 74195 327 765906 := by unfold blockSum; decide +kernel

private theorem s74522 : blockSum term 74522 327 736165 := by unfold blockSum; decide +kernel

private theorem s74849 : blockSum term 74849 327 658450 := by unfold blockSum; decide +kernel

private theorem s75176 : blockSum term 75176 327 678633 := by unfold blockSum; decide +kernel

private theorem s75503 : blockSum term 75503 327 842974 := by unfold blockSum; decide +kernel

private theorem s75830 : blockSum term 75830 326 622393 := by unfold blockSum; decide +kernel

private theorem s76156 : blockSum term 76156 327 642391 := by unfold blockSum; decide +kernel

private theorem s76483 : blockSum term 76483 327 661916 := by unfold blockSum; decide +kernel

private theorem s76810 : blockSum term 76810 327 610801 := by unfold blockSum; decide +kernel

private theorem s77137 : blockSum term 77137 327 723596 := by unfold blockSum; decide +kernel

private theorem s77464 : blockSum term 77464 327 881080 := by unfold blockSum; decide +kernel

private theorem s77791 : blockSum term 77791 327 553197 := by unfold blockSum; decide +kernel

private theorem s78118 : blockSum term 78118 327 641360 := by unfold blockSum; decide +kernel

private theorem s78445 : blockSum term 78445 326 591934 := by unfold blockSum; decide +kernel

private theorem s78771 : blockSum term 78771 327 611137 := by unfold blockSum; decide +kernel

private theorem s79098 : blockSum term 79098 327 741569 := by unfold blockSum; decide +kernel

private theorem s79425 : blockSum term 79425 327 580523 := by unfold blockSum; decide +kernel

private theorem s79752 : blockSum term 79752 327 709950 := by unfold blockSum; decide +kernel

private theorem s80079 : blockSum term 80079 327 639216 := by unfold blockSum; decide +kernel

private theorem s80406 : blockSum term 80406 327 635003 := by unfold blockSum; decide +kernel

private theorem s80733 : blockSum term 80733 327 761400 := by unfold blockSum; decide +kernel

private theorem s81060 : blockSum term 81060 326 626774 := by unfold blockSum; decide +kernel

private theorem s81386 : blockSum term 81386 327 622590 := by unfold blockSum; decide +kernel

private theorem s81713 : blockSum term 81713 327 682580 := by unfold blockSum; decide +kernel

private theorem s82040 : blockSum term 82040 327 593485 := by unfold blockSum; decide +kernel

private theorem s82367 : blockSum term 82367 327 590018 := by unfold blockSum; decide +kernel

private theorem s82694 : blockSum term 82694 327 565612 := by unfold blockSum; decide +kernel

private theorem s83021 : blockSum term 83021 327 582569 := by unfold blockSum; decide +kernel

private theorem s83348 : blockSum term 83348 327 620263 := by unfold blockSum; decide +kernel

private theorem s83675 : blockSum term 83675 326 493058 := by unfold blockSum; decide +kernel

private theorem s84001 : blockSum term 84001 327 612447 := by unfold blockSum; decide +kernel

private theorem s84328 : blockSum term 84328 327 588416 := by unfold blockSum; decide +kernel

private theorem s84655 : blockSum term 84655 327 544286 := by unfold blockSum; decide +kernel

private theorem s84982 : blockSum term 84982 326 580842 := by unfold blockSum; decide +kernel

private theorem s85308 : blockSum term 85308 327 577048 := by unfold blockSum; decide +kernel

private theorem s85635 : blockSum term 85635 327 514234 := by unfold blockSum; decide +kernel

private theorem s85962 : blockSum term 85962 327 569568 := by unfold blockSum; decide +kernel

private theorem s86289 : blockSum term 86289 326 624567 := by unfold blockSum; decide +kernel

private theorem s86615 : blockSum term 86615 327 465377 := by unfold blockSum; decide +kernel

private theorem s86942 : blockSum term 86942 327 539594 := by unfold blockSum; decide +kernel

private theorem s87269 : blockSum term 87269 327 612566 := by unfold blockSum; decide +kernel

private theorem s87596 : blockSum term 87596 327 589536 := by unfold blockSum; decide +kernel

private theorem s87923 : blockSum term 87923 327 434555 := by unfold blockSum; decide +kernel

private theorem s88250 : blockSum term 88250 327 394192 := by unfold blockSum; decide +kernel

private theorem s88577 : blockSum term 88577 327 615146 := by unfold blockSum; decide +kernel

private theorem s88904 : blockSum term 88904 326 537212 := by unfold blockSum; decide +kernel

private theorem s89230 : blockSum term 89230 327 533602 := by unfold blockSum; decide +kernel

private theorem s89557 : blockSum term 89557 327 548506 := by unfold blockSum; decide +kernel

private theorem s89884 : blockSum term 89884 327 653788 := by unfold blockSum; decide +kernel

private theorem s90211 : blockSum term 90211 327 523123 := by unfold blockSum; decide +kernel

private theorem s90538 : blockSum term 90538 327 448043 := by unfold blockSum; decide +kernel

private theorem s90865 : blockSum term 90865 327 498804 := by unfold blockSum; decide +kernel

private theorem s91192 : blockSum term 91192 327 531022 := by unfold blockSum; decide +kernel

private theorem s91519 : blockSum term 91519 326 457132 := by unfold blockSum; decide +kernel

private theorem s91845 : blockSum term 91845 327 419246 := by unfold blockSum; decide +kernel

private theorem s92172 : blockSum term 92172 327 624577 := by unfold blockSum; decide +kernel

private theorem s92499 : blockSum term 92499 327 568357 := by unfold blockSum; decide +kernel

private theorem s92826 : blockSum term 92826 327 513326 := by unfold blockSum; decide +kernel

private theorem s93153 : blockSum term 93153 327 458937 := by unfold blockSum; decide +kernel

private theorem s93480 : blockSum term 93480 327 422466 := by unfold blockSum; decide +kernel

private theorem s93807 : blockSum term 93807 327 537047 := by unfold blockSum; decide +kernel

private theorem s94134 : blockSum term 94134 326 466763 := by unfold blockSum; decide +kernel

private theorem s94460 : blockSum term 94460 327 463841 := by unfold blockSum; decide +kernel

private theorem s94787 : blockSum term 94787 327 526598 := by unfold blockSum; decide +kernel

private theorem s95114 : blockSum term 95114 327 474019 := by unfold blockSum; decide +kernel

private theorem s95441 : blockSum term 95441 327 487406 := by unfold blockSum; decide +kernel

private theorem s95768 : blockSum term 95768 327 484214 := by unfold blockSum; decide +kernel

private theorem s96095 : blockSum term 96095 327 416850 := by unfold blockSum; decide +kernel

private theorem s96422 : blockSum term 96422 327 430039 := by unfold blockSum; decide +kernel

private theorem s96749 : blockSum term 96749 326 474550 := by unfold blockSum; decide +kernel

private theorem s97075 : blockSum term 97075 327 408408 := by unfold blockSum; decide +kernel

private theorem s97402 : blockSum term 97402 327 406086 := by unfold blockSum; decide +kernel

private theorem s97729 : blockSum term 97729 327 449973 := by unfold blockSum; decide +kernel

private theorem s98056 : blockSum term 98056 327 354556 := by unfold blockSum; decide +kernel

private theorem s98383 : blockSum term 98383 327 428871 := by unfold blockSum; decide +kernel

private theorem s98710 : blockSum term 98710 327 517120 := by unfold blockSum; decide +kernel

private theorem s99037 : blockSum term 99037 327 407998 := by unfold blockSum; decide +kernel

private theorem s99364 : blockSum term 99364 326 435030 := by unfold blockSum; decide +kernel

private theorem s99690 : blockSum term 99690 327 431962 := by unfold blockSum; decide +kernel

private theorem s100017 : blockSum term 100017 327 369831 := by unfold blockSum; decide +kernel

private theorem s100344 : blockSum term 100344 327 426340 := by unfold blockSum; decide +kernel

private theorem s100671 : blockSum term 100671 327 365017 := by unfold blockSum; decide +kernel

private theorem s100998 : blockSum term 100998 327 449657 := by unfold blockSum; decide +kernel

private theorem s101325 : blockSum term 101325 327 446418 := by unfold blockSum; decide +kernel

private theorem s101652 : blockSum term 101652 327 428815 := by unfold blockSum; decide +kernel

private theorem s101979 : blockSum term 101979 326 496740 := by unfold blockSum; decide +kernel

private theorem s102305 : blockSum term 102305 327 380609 := by unfold blockSum; decide +kernel

private theorem s102632 : blockSum term 102632 327 350106 := by unfold blockSum; decide +kernel

private theorem s102959 : blockSum term 102959 327 292222 := by unfold blockSum; decide +kernel

private theorem s103286 : blockSum term 103286 327 386933 := by unfold blockSum; decide +kernel

private theorem s103613 : blockSum term 103613 327 329395 := by unfold blockSum; decide +kernel

private theorem s103940 : blockSum term 103940 327 449731 := by unfold blockSum; decide +kernel

private theorem s104267 : blockSum term 104267 327 378801 := by unfold blockSum; decide +kernel

private theorem s104594 : blockSum term 104594 326 429506 := by unfold blockSum; decide +kernel

private theorem s104920 : blockSum term 104920 327 306476 := by unfold blockSum; decide +kernel

private theorem s105247 : blockSum term 105247 327 436566 := by unfold blockSum; decide +kernel

private theorem s105574 : blockSum term 105574 327 302109 := by unfold blockSum; decide +kernel

private theorem s105901 : blockSum term 105901 326 365228 := by unfold blockSum; decide +kernel

private theorem s106227 : blockSum term 106227 327 414356 := by unfold blockSum; decide +kernel

private theorem s106554 : blockSum term 106554 327 411133 := by unfold blockSum; decide +kernel

private theorem s106881 : blockSum term 106881 327 344497 := by unfold blockSum; decide +kernel

private theorem s107208 : blockSum term 107208 326 266261 := by unfold blockSum; decide +kernel

private theorem s107534 : blockSum term 107534 327 327310 := by unfold blockSum; decide +kernel

private theorem s107861 : blockSum term 107861 327 362607 := by unfold blockSum; decide +kernel

private theorem s108188 : blockSum term 108188 327 360006 := by unfold blockSum; decide +kernel

private theorem s108515 : blockSum term 108515 327 320298 := by unfold blockSum; decide +kernel

private theorem s108842 : blockSum term 108842 327 415862 := by unfold blockSum; decide +kernel

private theorem s109169 : blockSum term 109169 327 352097 := by unfold blockSum; decide +kernel

private theorem s109496 : blockSum term 109496 327 313430 := by unfold blockSum; decide +kernel

private theorem s109823 : blockSum term 109823 326 335008 := by unfold blockSum; decide +kernel

private theorem s110149 : blockSum term 110149 327 249434 := by unfold blockSum; decide +kernel

private theorem s110476 : blockSum term 110476 327 365573 := by unfold blockSum; decide +kernel

private theorem s110803 : blockSum term 110803 327 374511 := by unfold blockSum; decide +kernel

private theorem s111130 : blockSum term 111130 327 278754 := by unfold blockSum; decide +kernel

private theorem s111457 : blockSum term 111457 327 334119 := by unfold blockSum; decide +kernel

private theorem s111784 : blockSum term 111784 327 320429 := by unfold blockSum; decide +kernel

private theorem s112111 : blockSum term 112111 327 363432 := by unfold blockSum; decide +kernel

private theorem s112438 : blockSum term 112438 326 247887 := by unfold blockSum; decide +kernel

private theorem s112764 : blockSum term 112764 327 346423 := by unfold blockSum; decide +kernel

private theorem s113091 : blockSum term 113091 327 354929 := by unfold blockSum; decide +kernel

private theorem s113418 : blockSum term 113418 327 231065 := by unfold blockSum; decide +kernel

private theorem s113745 : blockSum term 113745 327 316741 := by unfold blockSum; decide +kernel

private theorem s114072 : blockSum term 114072 327 292658 := by unfold blockSum; decide +kernel

private theorem s114399 : blockSum term 114399 327 290186 := by unfold blockSum; decide +kernel

private theorem s114726 : blockSum term 114726 327 277411 := by unfold blockSum; decide +kernel

private theorem s115053 : blockSum term 115053 326 328086 := by unfold blockSum; decide +kernel

private theorem s115379 : blockSum term 115379 327 252014 := by unfold blockSum; decide +kernel

private theorem s115706 : blockSum term 115706 327 375064 := by unfold blockSum; decide +kernel

private theorem s116033 : blockSum term 116033 327 268428 := by unfold blockSum; decide +kernel

private theorem s116360 : blockSum term 116360 327 245978 := by unfold blockSum; decide +kernel

private theorem s116687 : blockSum term 116687 327 294777 := by unfold blockSum; decide +kernel

private theorem s117014 : blockSum term 117014 327 292408 := by unfold blockSum; decide +kernel

private theorem s117341 : blockSum term 117341 327 250074 := by unfold blockSum; decide +kernel

private theorem s117668 : blockSum term 117668 326 356961 := by unfold blockSum; decide +kernel

private theorem s117994 : blockSum term 117994 327 236091 := by unfold blockSum; decide +kernel

private theorem s118321 : blockSum term 118321 327 244045 := by unfold blockSum; decide +kernel

private theorem s118648 : blockSum term 118648 327 290606 := by unfold blockSum; decide +kernel

private theorem s118975 : blockSum term 118975 327 269022 := by unfold blockSum; decide +kernel

private theorem s119302 : blockSum term 119302 327 209575 := by unfold blockSum; decide +kernel

private theorem s119629 : blockSum term 119629 327 302490 := by unfold blockSum; decide +kernel

private theorem s119956 : blockSum term 119956 327 262580 := by unfold blockSum; decide +kernel

private theorem s120283 : blockSum term 120283 326 232544 := by unfold blockSum; decide +kernel

private theorem s120609 : blockSum term 120609 327 313658 := by unfold blockSum; decide +kernel

private theorem s120936 : blockSum term 120936 327 237885 := by unfold blockSum; decide +kernel

private theorem s121263 : blockSum term 121263 327 317364 := by unfold blockSum; decide +kernel

private theorem s121590 : blockSum term 121590 327 197745 := by unfold blockSum; decide +kernel

private theorem s121917 : blockSum term 121917 327 293746 := by unfold blockSum; decide +kernel

private theorem s122244 : blockSum term 122244 327 264458 := by unfold blockSum; decide +kernel

private theorem s122571 : blockSum term 122571 327 235721 := by unfold blockSum; decide +kernel

private theorem s122898 : blockSum term 122898 326 216546 := by unfold blockSum; decide +kernel

private theorem s123224 : blockSum term 123224 327 248895 := by unfold blockSum; decide +kernel

private theorem s123551 : blockSum term 123551 327 255269 := by unfold blockSum; decide +kernel

private theorem s123878 : blockSum term 123878 327 227633 := by unfold blockSum; decide +kernel

private theorem s124205 : blockSum term 124205 327 233938 := by unfold blockSum; decide +kernel

private theorem s124532 : blockSum term 124532 327 248275 := by unfold blockSum; decide +kernel

private theorem s124859 : blockSum term 124859 327 196815 := by unfold blockSum; decide +kernel

private theorem s125186 : blockSum term 125186 327 235855 := by unfold blockSum; decide +kernel

private theorem s125513 : blockSum term 125513 326 233448 := by unfold blockSum; decide +kernel

private theorem s125839 : blockSum term 125839 327 223401 := by unfold blockSum; decide +kernel

private theorem s126166 : blockSum term 126166 327 221244 := by unfold blockSum; decide +kernel

private theorem s126493 : blockSum term 126493 327 195782 := by unfold blockSum; decide +kernel

private theorem s126820 : blockSum term 126820 326 178462 := by unfold blockSum; decide +kernel

private theorem s127146 : blockSum term 127146 327 200001 := by unfold blockSum; decide +kernel

private theorem s127473 : blockSum term 127473 327 251036 := by unfold blockSum; decide +kernel

private theorem s127800 : blockSum term 127800 327 188376 := by unfold blockSum; decide +kernel

private theorem s128127 : blockSum term 128127 326 231111 := by unfold blockSum; decide +kernel

private theorem s128453 : blockSum term 128453 327 214224 := by unfold blockSum; decide +kernel

private theorem s128780 : blockSum term 128780 327 219253 := by unfold blockSum; decide +kernel

private theorem s129107 : blockSum term 129107 327 188184 := by unfold blockSum; decide +kernel

private theorem s129434 : blockSum term 129434 327 229430 := by unfold blockSum; decide +kernel

private theorem s129761 : blockSum term 129761 327 184455 := by unfold blockSum; decide +kernel

private theorem s130088 : blockSum term 130088 327 196783 := by unfold blockSum; decide +kernel

private theorem s130415 : blockSum term 130415 327 208706 := by unfold blockSum; decide +kernel

private theorem s130742 : blockSum term 130742 326 158339 := by unfold blockSum; decide +kernel

private theorem s131068 : blockSum term 131068 327 170462 := by unfold blockSum; decide +kernel

private theorem s131395 : blockSum term 131395 327 188934 := by unfold blockSum; decide +kernel

private theorem s131722 : blockSum term 131722 327 180502 := by unfold blockSum; decide +kernel

private theorem s132049 : blockSum term 132049 327 185254 := by unfold blockSum; decide +kernel

private theorem s132376 : blockSum term 132376 327 196277 := by unfold blockSum; decide +kernel

private theorem s132703 : blockSum term 132703 327 174812 := by unfold blockSum; decide +kernel

private theorem s133030 : blockSum term 133030 327 204832 := by unfold blockSum; decide +kernel

private theorem s133357 : blockSum term 133357 326 151799 := by unfold blockSum; decide +kernel

private theorem s133683 : blockSum term 133683 327 156405 := by unfold blockSum; decide +kernel

private theorem s134010 : blockSum term 134010 327 179452 := by unfold blockSum; decide +kernel

private theorem s134337 : blockSum term 134337 327 146914 := by unfold blockSum; decide +kernel

private theorem s134664 : blockSum term 134664 327 157326 := by unfold blockSum; decide +kernel

private theorem s134991 : blockSum term 134991 327 167352 := by unfold blockSum; decide +kernel

private theorem s135318 : blockSum term 135318 327 200819 := by unfold blockSum; decide +kernel

private theorem s135645 : blockSum term 135645 327 151792 := by unfold blockSum; decide +kernel

private theorem s135972 : blockSum term 135972 326 149962 := by unfold blockSum; decide +kernel

private theorem s136298 : blockSum term 136298 327 216384 := by unfold blockSum; decide +kernel

private theorem s136625 : blockSum term 136625 327 151773 := by unfold blockSum; decide +kernel

private theorem s136952 : blockSum term 136952 327 150012 := by unfold blockSum; decide +kernel

private theorem s137279 : blockSum term 137279 327 159200 := by unfold blockSum; decide +kernel

private theorem s137606 : blockSum term 137606 327 130199 := by unfold blockSum; decide +kernel

private theorem s137933 : blockSum term 137933 327 160787 := by unfold blockSum; decide +kernel

private theorem s138260 : blockSum term 138260 327 158755 := by unfold blockSum; decide +kernel

private theorem s138587 : blockSum term 138587 326 135850 := by unfold blockSum; decide +kernel

private theorem s138913 : blockSum term 138913 327 103211 := by unfold blockSum; decide +kernel

private theorem s139240 : blockSum term 139240 327 158081 := by unfold blockSum; decide +kernel

private theorem s139567 : blockSum term 139567 327 140978 := by unfold blockSum; decide +kernel

private theorem s139894 : blockSum term 139894 327 129241 := by unfold blockSum; decide +kernel

private theorem s140221 : blockSum term 140221 327 142215 := by unfold blockSum; decide +kernel

private theorem s140548 : blockSum term 140548 327 164444 := by unfold blockSum; decide +kernel

private theorem s140875 : blockSum term 140875 327 114445 := by unfold blockSum; decide +kernel

private theorem s141202 : blockSum term 141202 326 131760 := by unfold blockSum; decide +kernel

private theorem s141528 : blockSum term 141528 327 152948 := by unfold blockSum; decide +kernel

private theorem s141855 : blockSum term 141855 327 123273 := by unfold blockSum; decide +kernel

private theorem s142182 : blockSum term 142182 327 103644 := by unfold blockSum; decide +kernel

private theorem s142509 : blockSum term 142509 327 120047 := by unfold blockSum; decide +kernel

private theorem s142836 : blockSum term 142836 327 109552 := by unfold blockSum; decide +kernel

private theorem s143163 : blockSum term 143163 327 103690 := by unfold blockSum; decide +kernel

private theorem s143490 : blockSum term 143490 327 127735 := by unfold blockSum; decide +kernel

private theorem s143817 : blockSum term 143817 326 92306 := by unfold blockSum; decide +kernel

private theorem s144143 : blockSum term 144143 327 115940 := by unfold blockSum; decide +kernel

private theorem s144470 : blockSum term 144470 327 114032 := by unfold blockSum; decide +kernel

private theorem s144797 : blockSum term 144797 327 104270 := by unfold blockSum; decide +kernel

private theorem s145124 : blockSum term 145124 327 90799 := by unfold blockSum; decide +kernel

private theorem s145451 : blockSum term 145451 327 132031 := by unfold blockSum; decide +kernel

private theorem s145778 : blockSum term 145778 327 110587 := by unfold blockSum; decide +kernel

private theorem s146105 : blockSum term 146105 327 101197 := by unfold blockSum; decide +kernel

private theorem s146432 : blockSum term 146432 326 88601 := by unfold blockSum; decide +kernel

private theorem s146758 : blockSum term 146758 327 98020 := by unfold blockSum; decide +kernel

private theorem s147085 : blockSum term 147085 327 110640 := by unfold blockSum; decide +kernel

private theorem s147412 : blockSum term 147412 327 91199 := by unfold blockSum; decide +kernel

private theorem s147739 : blockSum term 147739 326 82758 := by unfold blockSum; decide +kernel

private theorem s148065 : blockSum term 148065 327 88035 := by unfold blockSum; decide +kernel

private theorem s148392 : blockSum term 148392 327 89747 := by unfold blockSum; decide +kernel

private theorem s148719 : blockSum term 148719 327 97878 := by unfold blockSum; decide +kernel

private theorem s149046 : blockSum term 149046 326 102498 := by unfold blockSum; decide +kernel

private theorem s149372 : blockSum term 149372 327 87962 := by unfold blockSum; decide +kernel

private theorem s149699 : blockSum term 149699 327 89150 := by unfold blockSum; decide +kernel

private theorem s150026 : blockSum term 150026 327 87380 := by unfold blockSum; decide +kernel

private theorem s150353 : blockSum term 150353 327 79695 := by unfold blockSum; decide +kernel

private theorem s150680 : blockSum term 150680 327 77806 := by unfold blockSum; decide +kernel

private theorem s151007 : blockSum term 151007 327 76217 := by unfold blockSum; decide +kernel

private theorem s151334 : blockSum term 151334 327 93726 := by unfold blockSum; decide +kernel

private theorem s151661 : blockSum term 151661 326 78132 := by unfold blockSum; decide +kernel

private theorem s151987 : blockSum term 151987 327 73687 := by unfold blockSum; decide +kernel

private theorem s152314 : blockSum term 152314 327 69479 := by unfold blockSum; decide +kernel

private theorem s152641 : blockSum term 152641 327 75255 := by unfold blockSum; decide +kernel

private theorem s152968 : blockSum term 152968 327 56436 := by unfold blockSum; decide +kernel

private theorem s153295 : blockSum term 153295 327 71761 := by unfold blockSum; decide +kernel

private theorem s153622 : blockSum term 153622 327 53604 := by unfold blockSum; decide +kernel

private theorem s153949 : blockSum term 153949 327 63586 := by unfold blockSum; decide +kernel

private theorem s154276 : blockSum term 154276 326 59811 := by unfold blockSum; decide +kernel

private theorem s154602 : blockSum term 154602 327 60500 := by unfold blockSum; decide +kernel

private theorem s154929 : blockSum term 154929 327 56928 := by unfold blockSum; decide +kernel

private theorem s155256 : blockSum term 155256 327 57370 := by unfold blockSum; decide +kernel

private theorem s155583 : blockSum term 155583 327 67477 := by unfold blockSum; decide +kernel

private theorem s155910 : blockSum term 155910 327 36449 := by unfold blockSum; decide +kernel

private theorem s156237 : blockSum term 156237 327 41145 := by unfold blockSum; decide +kernel

private theorem s156564 : blockSum term 156564 327 50685 := by unfold blockSum; decide +kernel

private theorem s156891 : blockSum term 156891 326 48909 := by unfold blockSum; decide +kernel

private theorem s157217 : blockSum term 157217 327 55706 := by unfold blockSum; decide +kernel

private theorem s157544 : blockSum term 157544 327 40724 := by unfold blockSum; decide +kernel

private theorem s157871 : blockSum term 157871 327 36357 := by unfold blockSum; decide +kernel

private theorem s158198 : blockSum term 158198 327 39736 := by unfold blockSum; decide +kernel

private theorem s158525 : blockSum term 158525 327 41111 := by unfold blockSum; decide +kernel

private theorem s158852 : blockSum term 158852 327 32266 := by unfold blockSum; decide +kernel

private theorem s159179 : blockSum term 159179 327 38948 := by unfold blockSum; decide +kernel

private theorem s159506 : blockSum term 159506 326 39848 := by unfold blockSum; decide +kernel

private theorem s159832 : blockSum term 159832 327 32128 := by unfold blockSum; decide +kernel

private theorem s160159 : blockSum term 160159 327 30720 := by unfold blockSum; decide +kernel

private theorem s160486 : blockSum term 160486 327 33709 := by unfold blockSum; decide +kernel

private theorem s160813 : blockSum term 160813 327 28794 := by unfold blockSum; decide +kernel

private theorem s161140 : blockSum term 161140 327 25188 := by unfold blockSum; decide +kernel

private theorem s161467 : blockSum term 161467 327 28622 := by unfold blockSum; decide +kernel

private theorem s161794 : blockSum term 161794 327 23381 := by unfold blockSum; decide +kernel

private theorem s162121 : blockSum term 162121 326 16060 := by unfold blockSum; decide +kernel

private theorem s162447 : blockSum term 162447 327 25276 := by unfold blockSum; decide +kernel

private theorem s162774 : blockSum term 162774 327 19819 := by unfold blockSum; decide +kernel

private theorem s163101 : blockSum term 163101 327 19523 := by unfold blockSum; decide +kernel

private theorem s163428 : blockSum term 163428 327 16094 := by unfold blockSum; decide +kernel

private theorem s163755 : blockSum term 163755 327 15814 := by unfold blockSum; decide +kernel

private theorem s164082 : blockSum term 164082 327 14230 := by unfold blockSum; decide +kernel

private theorem s164409 : blockSum term 164409 327 12150 := by unfold blockSum; decide +kernel

private theorem s164736 : blockSum term 164736 326 8664 := by unfold blockSum; decide +kernel

private theorem s165062 : blockSum term 165062 327 8195 := by unfold blockSum; decide +kernel

private theorem s165389 : blockSum term 165389 327 8886 := by unfold blockSum; decide +kernel

private theorem s165716 : blockSum term 165716 327 5372 := by unfold blockSum; decide +kernel

private theorem s166043 : blockSum term 166043 327 4595 := by unfold blockSum; decide +kernel

private theorem s166370 : blockSum term 166370 327 3617 := by unfold blockSum; decide +kernel

private theorem s166697 : blockSum term 166697 327 2373 := by unfold blockSum; decide +kernel

private theorem s167024 : blockSum term 167024 327 897 := by unfold blockSum; decide +kernel

private theorem rows : blockSum term 0 167351 753837725 := (join_sums term (lo:=0) (a:=83675) (b:=83676) (join_sums term (lo:=0) (a:=41837) (b:=41838) (join_sums term (lo:=0) (a:=20918) (b:=20919) (join_sums term (lo:=0) (a:=10459) (b:=10459) (join_sums term (lo:=0) (a:=5229) (b:=5230) (join_sums term (lo:=0) (a:=2614) (b:=2615) (join_sums term (lo:=0) (a:=1307) (b:=1307) (join_sums term (lo:=0) (a:=653) (b:=654) (join_sums term (lo:=0) (a:=326) (b:=327) s0 s326) (join_sums term (lo:=653) (a:=327) (b:=327) s653 s980)) (join_sums term (lo:=1307) (a:=653) (b:=654) (join_sums term (lo:=1307) (a:=326) (b:=327) s1307 s1633) (join_sums term (lo:=1960) (a:=327) (b:=327) s1960 s2287))) (join_sums term (lo:=2614) (a:=1307) (b:=1308) (join_sums term (lo:=2614) (a:=653) (b:=654) (join_sums term (lo:=2614) (a:=326) (b:=327) s2614 s2940) (join_sums term (lo:=3267) (a:=327) (b:=327) s3267 s3594)) (join_sums term (lo:=3921) (a:=654) (b:=654) (join_sums term (lo:=3921) (a:=327) (b:=327) s3921 s4248) (join_sums term (lo:=4575) (a:=327) (b:=327) s4575 s4902)))) (join_sums term (lo:=5229) (a:=2615) (b:=2615) (join_sums term (lo:=5229) (a:=1307) (b:=1308) (join_sums term (lo:=5229) (a:=653) (b:=654) (join_sums term (lo:=5229) (a:=326) (b:=327) s5229 s5555) (join_sums term (lo:=5882) (a:=327) (b:=327) s5882 s6209)) (join_sums term (lo:=6536) (a:=654) (b:=654) (join_sums term (lo:=6536) (a:=327) (b:=327) s6536 s6863) (join_sums term (lo:=7190) (a:=327) (b:=327) s7190 s7517))) (join_sums term (lo:=7844) (a:=1307) (b:=1308) (join_sums term (lo:=7844) (a:=653) (b:=654) (join_sums term (lo:=7844) (a:=326) (b:=327) s7844 s8170) (join_sums term (lo:=8497) (a:=327) (b:=327) s8497 s8824)) (join_sums term (lo:=9151) (a:=654) (b:=654) (join_sums term (lo:=9151) (a:=327) (b:=327) s9151 s9478) (join_sums term (lo:=9805) (a:=327) (b:=327) s9805 s10132))))) (join_sums term (lo:=10459) (a:=5229) (b:=5230) (join_sums term (lo:=10459) (a:=2614) (b:=2615) (join_sums term (lo:=10459) (a:=1307) (b:=1307) (join_sums term (lo:=10459) (a:=653) (b:=654) (join_sums term (lo:=10459) (a:=326) (b:=327) s10459 s10785) (join_sums term (lo:=11112) (a:=327) (b:=327) s11112 s11439)) (join_sums term (lo:=11766) (a:=653) (b:=654) (join_sums term (lo:=11766) (a:=326) (b:=327) s11766 s12092) (join_sums term (lo:=12419) (a:=327) (b:=327) s12419 s12746))) (join_sums term (lo:=13073) (a:=1307) (b:=1308) (join_sums term (lo:=13073) (a:=653) (b:=654) (join_sums term (lo:=13073) (a:=326) (b:=327) s13073 s13399) (join_sums term (lo:=13726) (a:=327) (b:=327) s13726 s14053)) (join_sums term (lo:=14380) (a:=654) (b:=654) (join_sums term (lo:=14380) (a:=327) (b:=327) s14380 s14707) (join_sums term (lo:=15034) (a:=327) (b:=327) s15034 s15361)))) (join_sums term (lo:=15688) (a:=2615) (b:=2615) (join_sums term (lo:=15688) (a:=1307) (b:=1308) (join_sums term (lo:=15688) (a:=653) (b:=654) (join_sums term (lo:=15688) (a:=326) (b:=327) s15688 s16014) (join_sums term (lo:=16341) (a:=327) (b:=327) s16341 s16668)) (join_sums term (lo:=16995) (a:=654) (b:=654) (join_sums term (lo:=16995) (a:=327) (b:=327) s16995 s17322) (join_sums term (lo:=17649) (a:=327) (b:=327) s17649 s17976))) (join_sums term (lo:=18303) (a:=1307) (b:=1308) (join_sums term (lo:=18303) (a:=653) (b:=654) (join_sums term (lo:=18303) (a:=326) (b:=327) s18303 s18629) (join_sums term (lo:=18956) (a:=327) (b:=327) s18956 s19283)) (join_sums term (lo:=19610) (a:=654) (b:=654) (join_sums term (lo:=19610) (a:=327) (b:=327) s19610 s19937) (join_sums term (lo:=20264) (a:=327) (b:=327) s20264 s20591)))))) (join_sums term (lo:=20918) (a:=10459) (b:=10460) (join_sums term (lo:=20918) (a:=5229) (b:=5230) (join_sums term (lo:=20918) (a:=2614) (b:=2615) (join_sums term (lo:=20918) (a:=1307) (b:=1307) (join_sums term (lo:=20918) (a:=653) (b:=654) (join_sums term (lo:=20918) (a:=326) (b:=327) s20918 s21244) (join_sums term (lo:=21571) (a:=327) (b:=327) s21571 s21898)) (join_sums term (lo:=22225) (a:=653) (b:=654) (join_sums term (lo:=22225) (a:=326) (b:=327) s22225 s22551) (join_sums term (lo:=22878) (a:=327) (b:=327) s22878 s23205))) (join_sums term (lo:=23532) (a:=1307) (b:=1308) (join_sums term (lo:=23532) (a:=653) (b:=654) (join_sums term (lo:=23532) (a:=326) (b:=327) s23532 s23858) (join_sums term (lo:=24185) (a:=327) (b:=327) s24185 s24512)) (join_sums term (lo:=24839) (a:=654) (b:=654) (join_sums term (lo:=24839) (a:=327) (b:=327) s24839 s25166) (join_sums term (lo:=25493) (a:=327) (b:=327) s25493 s25820)))) (join_sums term (lo:=26147) (a:=2615) (b:=2615) (join_sums term (lo:=26147) (a:=1307) (b:=1308) (join_sums term (lo:=26147) (a:=653) (b:=654) (join_sums term (lo:=26147) (a:=326) (b:=327) s26147 s26473) (join_sums term (lo:=26800) (a:=327) (b:=327) s26800 s27127)) (join_sums term (lo:=27454) (a:=654) (b:=654) (join_sums term (lo:=27454) (a:=327) (b:=327) s27454 s27781) (join_sums term (lo:=28108) (a:=327) (b:=327) s28108 s28435))) (join_sums term (lo:=28762) (a:=1307) (b:=1308) (join_sums term (lo:=28762) (a:=653) (b:=654) (join_sums term (lo:=28762) (a:=326) (b:=327) s28762 s29088) (join_sums term (lo:=29415) (a:=327) (b:=327) s29415 s29742)) (join_sums term (lo:=30069) (a:=654) (b:=654) (join_sums term (lo:=30069) (a:=327) (b:=327) s30069 s30396) (join_sums term (lo:=30723) (a:=327) (b:=327) s30723 s31050))))) (join_sums term (lo:=31377) (a:=5230) (b:=5230) (join_sums term (lo:=31377) (a:=2615) (b:=2615) (join_sums term (lo:=31377) (a:=1307) (b:=1308) (join_sums term (lo:=31377) (a:=653) (b:=654) (join_sums term (lo:=31377) (a:=326) (b:=327) s31377 s31703) (join_sums term (lo:=32030) (a:=327) (b:=327) s32030 s32357)) (join_sums term (lo:=32684) (a:=654) (b:=654) (join_sums term (lo:=32684) (a:=327) (b:=327) s32684 s33011) (join_sums term (lo:=33338) (a:=327) (b:=327) s33338 s33665))) (join_sums term (lo:=33992) (a:=1307) (b:=1308) (join_sums term (lo:=33992) (a:=653) (b:=654) (join_sums term (lo:=33992) (a:=326) (b:=327) s33992 s34318) (join_sums term (lo:=34645) (a:=327) (b:=327) s34645 s34972)) (join_sums term (lo:=35299) (a:=654) (b:=654) (join_sums term (lo:=35299) (a:=327) (b:=327) s35299 s35626) (join_sums term (lo:=35953) (a:=327) (b:=327) s35953 s36280)))) (join_sums term (lo:=36607) (a:=2615) (b:=2615) (join_sums term (lo:=36607) (a:=1307) (b:=1308) (join_sums term (lo:=36607) (a:=653) (b:=654) (join_sums term (lo:=36607) (a:=326) (b:=327) s36607 s36933) (join_sums term (lo:=37260) (a:=327) (b:=327) s37260 s37587)) (join_sums term (lo:=37914) (a:=654) (b:=654) (join_sums term (lo:=37914) (a:=327) (b:=327) s37914 s38241) (join_sums term (lo:=38568) (a:=327) (b:=327) s38568 s38895))) (join_sums term (lo:=39222) (a:=1307) (b:=1308) (join_sums term (lo:=39222) (a:=653) (b:=654) (join_sums term (lo:=39222) (a:=326) (b:=327) s39222 s39548) (join_sums term (lo:=39875) (a:=327) (b:=327) s39875 s40202)) (join_sums term (lo:=40529) (a:=654) (b:=654) (join_sums term (lo:=40529) (a:=327) (b:=327) s40529 s40856) (join_sums term (lo:=41183) (a:=327) (b:=327) s41183 s41510))))))) (join_sums term (lo:=41837) (a:=20919) (b:=20919) (join_sums term (lo:=41837) (a:=10459) (b:=10460) (join_sums term (lo:=41837) (a:=5229) (b:=5230) (join_sums term (lo:=41837) (a:=2614) (b:=2615) (join_sums term (lo:=41837) (a:=1307) (b:=1307) (join_sums term (lo:=41837) (a:=653) (b:=654) (join_sums term (lo:=41837) (a:=326) (b:=327) s41837 s42163) (join_sums term (lo:=42490) (a:=327) (b:=327) s42490 s42817)) (join_sums term (lo:=43144) (a:=653) (b:=654) (join_sums term (lo:=43144) (a:=326) (b:=327) s43144 s43470) (join_sums term (lo:=43797) (a:=327) (b:=327) s43797 s44124))) (join_sums term (lo:=44451) (a:=1307) (b:=1308) (join_sums term (lo:=44451) (a:=653) (b:=654) (join_sums term (lo:=44451) (a:=326) (b:=327) s44451 s44777) (join_sums term (lo:=45104) (a:=327) (b:=327) s45104 s45431)) (join_sums term (lo:=45758) (a:=654) (b:=654) (join_sums term (lo:=45758) (a:=327) (b:=327) s45758 s46085) (join_sums term (lo:=46412) (a:=327) (b:=327) s46412 s46739)))) (join_sums term (lo:=47066) (a:=2615) (b:=2615) (join_sums term (lo:=47066) (a:=1307) (b:=1308) (join_sums term (lo:=47066) (a:=653) (b:=654) (join_sums term (lo:=47066) (a:=326) (b:=327) s47066 s47392) (join_sums term (lo:=47719) (a:=327) (b:=327) s47719 s48046)) (join_sums term (lo:=48373) (a:=654) (b:=654) (join_sums term (lo:=48373) (a:=327) (b:=327) s48373 s48700) (join_sums term (lo:=49027) (a:=327) (b:=327) s49027 s49354))) (join_sums term (lo:=49681) (a:=1307) (b:=1308) (join_sums term (lo:=49681) (a:=653) (b:=654) (join_sums term (lo:=49681) (a:=326) (b:=327) s49681 s50007) (join_sums term (lo:=50334) (a:=327) (b:=327) s50334 s50661)) (join_sums term (lo:=50988) (a:=654) (b:=654) (join_sums term (lo:=50988) (a:=327) (b:=327) s50988 s51315) (join_sums term (lo:=51642) (a:=327) (b:=327) s51642 s51969))))) (join_sums term (lo:=52296) (a:=5230) (b:=5230) (join_sums term (lo:=52296) (a:=2615) (b:=2615) (join_sums term (lo:=52296) (a:=1307) (b:=1308) (join_sums term (lo:=52296) (a:=653) (b:=654) (join_sums term (lo:=52296) (a:=326) (b:=327) s52296 s52622) (join_sums term (lo:=52949) (a:=327) (b:=327) s52949 s53276)) (join_sums term (lo:=53603) (a:=654) (b:=654) (join_sums term (lo:=53603) (a:=327) (b:=327) s53603 s53930) (join_sums term (lo:=54257) (a:=327) (b:=327) s54257 s54584))) (join_sums term (lo:=54911) (a:=1307) (b:=1308) (join_sums term (lo:=54911) (a:=653) (b:=654) (join_sums term (lo:=54911) (a:=326) (b:=327) s54911 s55237) (join_sums term (lo:=55564) (a:=327) (b:=327) s55564 s55891)) (join_sums term (lo:=56218) (a:=654) (b:=654) (join_sums term (lo:=56218) (a:=327) (b:=327) s56218 s56545) (join_sums term (lo:=56872) (a:=327) (b:=327) s56872 s57199)))) (join_sums term (lo:=57526) (a:=2615) (b:=2615) (join_sums term (lo:=57526) (a:=1307) (b:=1308) (join_sums term (lo:=57526) (a:=653) (b:=654) (join_sums term (lo:=57526) (a:=326) (b:=327) s57526 s57852) (join_sums term (lo:=58179) (a:=327) (b:=327) s58179 s58506)) (join_sums term (lo:=58833) (a:=654) (b:=654) (join_sums term (lo:=58833) (a:=327) (b:=327) s58833 s59160) (join_sums term (lo:=59487) (a:=327) (b:=327) s59487 s59814))) (join_sums term (lo:=60141) (a:=1307) (b:=1308) (join_sums term (lo:=60141) (a:=653) (b:=654) (join_sums term (lo:=60141) (a:=326) (b:=327) s60141 s60467) (join_sums term (lo:=60794) (a:=327) (b:=327) s60794 s61121)) (join_sums term (lo:=61448) (a:=654) (b:=654) (join_sums term (lo:=61448) (a:=327) (b:=327) s61448 s61775) (join_sums term (lo:=62102) (a:=327) (b:=327) s62102 s62429)))))) (join_sums term (lo:=62756) (a:=10459) (b:=10460) (join_sums term (lo:=62756) (a:=5229) (b:=5230) (join_sums term (lo:=62756) (a:=2614) (b:=2615) (join_sums term (lo:=62756) (a:=1307) (b:=1307) (join_sums term (lo:=62756) (a:=653) (b:=654) (join_sums term (lo:=62756) (a:=326) (b:=327) s62756 s63082) (join_sums term (lo:=63409) (a:=327) (b:=327) s63409 s63736)) (join_sums term (lo:=64063) (a:=653) (b:=654) (join_sums term (lo:=64063) (a:=326) (b:=327) s64063 s64389) (join_sums term (lo:=64716) (a:=327) (b:=327) s64716 s65043))) (join_sums term (lo:=65370) (a:=1307) (b:=1308) (join_sums term (lo:=65370) (a:=653) (b:=654) (join_sums term (lo:=65370) (a:=326) (b:=327) s65370 s65696) (join_sums term (lo:=66023) (a:=327) (b:=327) s66023 s66350)) (join_sums term (lo:=66677) (a:=654) (b:=654) (join_sums term (lo:=66677) (a:=327) (b:=327) s66677 s67004) (join_sums term (lo:=67331) (a:=327) (b:=327) s67331 s67658)))) (join_sums term (lo:=67985) (a:=2615) (b:=2615) (join_sums term (lo:=67985) (a:=1307) (b:=1308) (join_sums term (lo:=67985) (a:=653) (b:=654) (join_sums term (lo:=67985) (a:=326) (b:=327) s67985 s68311) (join_sums term (lo:=68638) (a:=327) (b:=327) s68638 s68965)) (join_sums term (lo:=69292) (a:=654) (b:=654) (join_sums term (lo:=69292) (a:=327) (b:=327) s69292 s69619) (join_sums term (lo:=69946) (a:=327) (b:=327) s69946 s70273))) (join_sums term (lo:=70600) (a:=1307) (b:=1308) (join_sums term (lo:=70600) (a:=653) (b:=654) (join_sums term (lo:=70600) (a:=326) (b:=327) s70600 s70926) (join_sums term (lo:=71253) (a:=327) (b:=327) s71253 s71580)) (join_sums term (lo:=71907) (a:=654) (b:=654) (join_sums term (lo:=71907) (a:=327) (b:=327) s71907 s72234) (join_sums term (lo:=72561) (a:=327) (b:=327) s72561 s72888))))) (join_sums term (lo:=73215) (a:=5230) (b:=5230) (join_sums term (lo:=73215) (a:=2615) (b:=2615) (join_sums term (lo:=73215) (a:=1307) (b:=1308) (join_sums term (lo:=73215) (a:=653) (b:=654) (join_sums term (lo:=73215) (a:=326) (b:=327) s73215 s73541) (join_sums term (lo:=73868) (a:=327) (b:=327) s73868 s74195)) (join_sums term (lo:=74522) (a:=654) (b:=654) (join_sums term (lo:=74522) (a:=327) (b:=327) s74522 s74849) (join_sums term (lo:=75176) (a:=327) (b:=327) s75176 s75503))) (join_sums term (lo:=75830) (a:=1307) (b:=1308) (join_sums term (lo:=75830) (a:=653) (b:=654) (join_sums term (lo:=75830) (a:=326) (b:=327) s75830 s76156) (join_sums term (lo:=76483) (a:=327) (b:=327) s76483 s76810)) (join_sums term (lo:=77137) (a:=654) (b:=654) (join_sums term (lo:=77137) (a:=327) (b:=327) s77137 s77464) (join_sums term (lo:=77791) (a:=327) (b:=327) s77791 s78118)))) (join_sums term (lo:=78445) (a:=2615) (b:=2615) (join_sums term (lo:=78445) (a:=1307) (b:=1308) (join_sums term (lo:=78445) (a:=653) (b:=654) (join_sums term (lo:=78445) (a:=326) (b:=327) s78445 s78771) (join_sums term (lo:=79098) (a:=327) (b:=327) s79098 s79425)) (join_sums term (lo:=79752) (a:=654) (b:=654) (join_sums term (lo:=79752) (a:=327) (b:=327) s79752 s80079) (join_sums term (lo:=80406) (a:=327) (b:=327) s80406 s80733))) (join_sums term (lo:=81060) (a:=1307) (b:=1308) (join_sums term (lo:=81060) (a:=653) (b:=654) (join_sums term (lo:=81060) (a:=326) (b:=327) s81060 s81386) (join_sums term (lo:=81713) (a:=327) (b:=327) s81713 s82040)) (join_sums term (lo:=82367) (a:=654) (b:=654) (join_sums term (lo:=82367) (a:=327) (b:=327) s82367 s82694) (join_sums term (lo:=83021) (a:=327) (b:=327) s83021 s83348)))))))) (join_sums term (lo:=83675) (a:=41838) (b:=41838) (join_sums term (lo:=83675) (a:=20919) (b:=20919) (join_sums term (lo:=83675) (a:=10459) (b:=10460) (join_sums term (lo:=83675) (a:=5229) (b:=5230) (join_sums term (lo:=83675) (a:=2614) (b:=2615) (join_sums term (lo:=83675) (a:=1307) (b:=1307) (join_sums term (lo:=83675) (a:=653) (b:=654) (join_sums term (lo:=83675) (a:=326) (b:=327) s83675 s84001) (join_sums term (lo:=84328) (a:=327) (b:=327) s84328 s84655)) (join_sums term (lo:=84982) (a:=653) (b:=654) (join_sums term (lo:=84982) (a:=326) (b:=327) s84982 s85308) (join_sums term (lo:=85635) (a:=327) (b:=327) s85635 s85962))) (join_sums term (lo:=86289) (a:=1307) (b:=1308) (join_sums term (lo:=86289) (a:=653) (b:=654) (join_sums term (lo:=86289) (a:=326) (b:=327) s86289 s86615) (join_sums term (lo:=86942) (a:=327) (b:=327) s86942 s87269)) (join_sums term (lo:=87596) (a:=654) (b:=654) (join_sums term (lo:=87596) (a:=327) (b:=327) s87596 s87923) (join_sums term (lo:=88250) (a:=327) (b:=327) s88250 s88577)))) (join_sums term (lo:=88904) (a:=2615) (b:=2615) (join_sums term (lo:=88904) (a:=1307) (b:=1308) (join_sums term (lo:=88904) (a:=653) (b:=654) (join_sums term (lo:=88904) (a:=326) (b:=327) s88904 s89230) (join_sums term (lo:=89557) (a:=327) (b:=327) s89557 s89884)) (join_sums term (lo:=90211) (a:=654) (b:=654) (join_sums term (lo:=90211) (a:=327) (b:=327) s90211 s90538) (join_sums term (lo:=90865) (a:=327) (b:=327) s90865 s91192))) (join_sums term (lo:=91519) (a:=1307) (b:=1308) (join_sums term (lo:=91519) (a:=653) (b:=654) (join_sums term (lo:=91519) (a:=326) (b:=327) s91519 s91845) (join_sums term (lo:=92172) (a:=327) (b:=327) s92172 s92499)) (join_sums term (lo:=92826) (a:=654) (b:=654) (join_sums term (lo:=92826) (a:=327) (b:=327) s92826 s93153) (join_sums term (lo:=93480) (a:=327) (b:=327) s93480 s93807))))) (join_sums term (lo:=94134) (a:=5230) (b:=5230) (join_sums term (lo:=94134) (a:=2615) (b:=2615) (join_sums term (lo:=94134) (a:=1307) (b:=1308) (join_sums term (lo:=94134) (a:=653) (b:=654) (join_sums term (lo:=94134) (a:=326) (b:=327) s94134 s94460) (join_sums term (lo:=94787) (a:=327) (b:=327) s94787 s95114)) (join_sums term (lo:=95441) (a:=654) (b:=654) (join_sums term (lo:=95441) (a:=327) (b:=327) s95441 s95768) (join_sums term (lo:=96095) (a:=327) (b:=327) s96095 s96422))) (join_sums term (lo:=96749) (a:=1307) (b:=1308) (join_sums term (lo:=96749) (a:=653) (b:=654) (join_sums term (lo:=96749) (a:=326) (b:=327) s96749 s97075) (join_sums term (lo:=97402) (a:=327) (b:=327) s97402 s97729)) (join_sums term (lo:=98056) (a:=654) (b:=654) (join_sums term (lo:=98056) (a:=327) (b:=327) s98056 s98383) (join_sums term (lo:=98710) (a:=327) (b:=327) s98710 s99037)))) (join_sums term (lo:=99364) (a:=2615) (b:=2615) (join_sums term (lo:=99364) (a:=1307) (b:=1308) (join_sums term (lo:=99364) (a:=653) (b:=654) (join_sums term (lo:=99364) (a:=326) (b:=327) s99364 s99690) (join_sums term (lo:=100017) (a:=327) (b:=327) s100017 s100344)) (join_sums term (lo:=100671) (a:=654) (b:=654) (join_sums term (lo:=100671) (a:=327) (b:=327) s100671 s100998) (join_sums term (lo:=101325) (a:=327) (b:=327) s101325 s101652))) (join_sums term (lo:=101979) (a:=1307) (b:=1308) (join_sums term (lo:=101979) (a:=653) (b:=654) (join_sums term (lo:=101979) (a:=326) (b:=327) s101979 s102305) (join_sums term (lo:=102632) (a:=327) (b:=327) s102632 s102959)) (join_sums term (lo:=103286) (a:=654) (b:=654) (join_sums term (lo:=103286) (a:=327) (b:=327) s103286 s103613) (join_sums term (lo:=103940) (a:=327) (b:=327) s103940 s104267)))))) (join_sums term (lo:=104594) (a:=10459) (b:=10460) (join_sums term (lo:=104594) (a:=5229) (b:=5230) (join_sums term (lo:=104594) (a:=2614) (b:=2615) (join_sums term (lo:=104594) (a:=1307) (b:=1307) (join_sums term (lo:=104594) (a:=653) (b:=654) (join_sums term (lo:=104594) (a:=326) (b:=327) s104594 s104920) (join_sums term (lo:=105247) (a:=327) (b:=327) s105247 s105574)) (join_sums term (lo:=105901) (a:=653) (b:=654) (join_sums term (lo:=105901) (a:=326) (b:=327) s105901 s106227) (join_sums term (lo:=106554) (a:=327) (b:=327) s106554 s106881))) (join_sums term (lo:=107208) (a:=1307) (b:=1308) (join_sums term (lo:=107208) (a:=653) (b:=654) (join_sums term (lo:=107208) (a:=326) (b:=327) s107208 s107534) (join_sums term (lo:=107861) (a:=327) (b:=327) s107861 s108188)) (join_sums term (lo:=108515) (a:=654) (b:=654) (join_sums term (lo:=108515) (a:=327) (b:=327) s108515 s108842) (join_sums term (lo:=109169) (a:=327) (b:=327) s109169 s109496)))) (join_sums term (lo:=109823) (a:=2615) (b:=2615) (join_sums term (lo:=109823) (a:=1307) (b:=1308) (join_sums term (lo:=109823) (a:=653) (b:=654) (join_sums term (lo:=109823) (a:=326) (b:=327) s109823 s110149) (join_sums term (lo:=110476) (a:=327) (b:=327) s110476 s110803)) (join_sums term (lo:=111130) (a:=654) (b:=654) (join_sums term (lo:=111130) (a:=327) (b:=327) s111130 s111457) (join_sums term (lo:=111784) (a:=327) (b:=327) s111784 s112111))) (join_sums term (lo:=112438) (a:=1307) (b:=1308) (join_sums term (lo:=112438) (a:=653) (b:=654) (join_sums term (lo:=112438) (a:=326) (b:=327) s112438 s112764) (join_sums term (lo:=113091) (a:=327) (b:=327) s113091 s113418)) (join_sums term (lo:=113745) (a:=654) (b:=654) (join_sums term (lo:=113745) (a:=327) (b:=327) s113745 s114072) (join_sums term (lo:=114399) (a:=327) (b:=327) s114399 s114726))))) (join_sums term (lo:=115053) (a:=5230) (b:=5230) (join_sums term (lo:=115053) (a:=2615) (b:=2615) (join_sums term (lo:=115053) (a:=1307) (b:=1308) (join_sums term (lo:=115053) (a:=653) (b:=654) (join_sums term (lo:=115053) (a:=326) (b:=327) s115053 s115379) (join_sums term (lo:=115706) (a:=327) (b:=327) s115706 s116033)) (join_sums term (lo:=116360) (a:=654) (b:=654) (join_sums term (lo:=116360) (a:=327) (b:=327) s116360 s116687) (join_sums term (lo:=117014) (a:=327) (b:=327) s117014 s117341))) (join_sums term (lo:=117668) (a:=1307) (b:=1308) (join_sums term (lo:=117668) (a:=653) (b:=654) (join_sums term (lo:=117668) (a:=326) (b:=327) s117668 s117994) (join_sums term (lo:=118321) (a:=327) (b:=327) s118321 s118648)) (join_sums term (lo:=118975) (a:=654) (b:=654) (join_sums term (lo:=118975) (a:=327) (b:=327) s118975 s119302) (join_sums term (lo:=119629) (a:=327) (b:=327) s119629 s119956)))) (join_sums term (lo:=120283) (a:=2615) (b:=2615) (join_sums term (lo:=120283) (a:=1307) (b:=1308) (join_sums term (lo:=120283) (a:=653) (b:=654) (join_sums term (lo:=120283) (a:=326) (b:=327) s120283 s120609) (join_sums term (lo:=120936) (a:=327) (b:=327) s120936 s121263)) (join_sums term (lo:=121590) (a:=654) (b:=654) (join_sums term (lo:=121590) (a:=327) (b:=327) s121590 s121917) (join_sums term (lo:=122244) (a:=327) (b:=327) s122244 s122571))) (join_sums term (lo:=122898) (a:=1307) (b:=1308) (join_sums term (lo:=122898) (a:=653) (b:=654) (join_sums term (lo:=122898) (a:=326) (b:=327) s122898 s123224) (join_sums term (lo:=123551) (a:=327) (b:=327) s123551 s123878)) (join_sums term (lo:=124205) (a:=654) (b:=654) (join_sums term (lo:=124205) (a:=327) (b:=327) s124205 s124532) (join_sums term (lo:=124859) (a:=327) (b:=327) s124859 s125186))))))) (join_sums term (lo:=125513) (a:=20919) (b:=20919) (join_sums term (lo:=125513) (a:=10459) (b:=10460) (join_sums term (lo:=125513) (a:=5229) (b:=5230) (join_sums term (lo:=125513) (a:=2614) (b:=2615) (join_sums term (lo:=125513) (a:=1307) (b:=1307) (join_sums term (lo:=125513) (a:=653) (b:=654) (join_sums term (lo:=125513) (a:=326) (b:=327) s125513 s125839) (join_sums term (lo:=126166) (a:=327) (b:=327) s126166 s126493)) (join_sums term (lo:=126820) (a:=653) (b:=654) (join_sums term (lo:=126820) (a:=326) (b:=327) s126820 s127146) (join_sums term (lo:=127473) (a:=327) (b:=327) s127473 s127800))) (join_sums term (lo:=128127) (a:=1307) (b:=1308) (join_sums term (lo:=128127) (a:=653) (b:=654) (join_sums term (lo:=128127) (a:=326) (b:=327) s128127 s128453) (join_sums term (lo:=128780) (a:=327) (b:=327) s128780 s129107)) (join_sums term (lo:=129434) (a:=654) (b:=654) (join_sums term (lo:=129434) (a:=327) (b:=327) s129434 s129761) (join_sums term (lo:=130088) (a:=327) (b:=327) s130088 s130415)))) (join_sums term (lo:=130742) (a:=2615) (b:=2615) (join_sums term (lo:=130742) (a:=1307) (b:=1308) (join_sums term (lo:=130742) (a:=653) (b:=654) (join_sums term (lo:=130742) (a:=326) (b:=327) s130742 s131068) (join_sums term (lo:=131395) (a:=327) (b:=327) s131395 s131722)) (join_sums term (lo:=132049) (a:=654) (b:=654) (join_sums term (lo:=132049) (a:=327) (b:=327) s132049 s132376) (join_sums term (lo:=132703) (a:=327) (b:=327) s132703 s133030))) (join_sums term (lo:=133357) (a:=1307) (b:=1308) (join_sums term (lo:=133357) (a:=653) (b:=654) (join_sums term (lo:=133357) (a:=326) (b:=327) s133357 s133683) (join_sums term (lo:=134010) (a:=327) (b:=327) s134010 s134337)) (join_sums term (lo:=134664) (a:=654) (b:=654) (join_sums term (lo:=134664) (a:=327) (b:=327) s134664 s134991) (join_sums term (lo:=135318) (a:=327) (b:=327) s135318 s135645))))) (join_sums term (lo:=135972) (a:=5230) (b:=5230) (join_sums term (lo:=135972) (a:=2615) (b:=2615) (join_sums term (lo:=135972) (a:=1307) (b:=1308) (join_sums term (lo:=135972) (a:=653) (b:=654) (join_sums term (lo:=135972) (a:=326) (b:=327) s135972 s136298) (join_sums term (lo:=136625) (a:=327) (b:=327) s136625 s136952)) (join_sums term (lo:=137279) (a:=654) (b:=654) (join_sums term (lo:=137279) (a:=327) (b:=327) s137279 s137606) (join_sums term (lo:=137933) (a:=327) (b:=327) s137933 s138260))) (join_sums term (lo:=138587) (a:=1307) (b:=1308) (join_sums term (lo:=138587) (a:=653) (b:=654) (join_sums term (lo:=138587) (a:=326) (b:=327) s138587 s138913) (join_sums term (lo:=139240) (a:=327) (b:=327) s139240 s139567)) (join_sums term (lo:=139894) (a:=654) (b:=654) (join_sums term (lo:=139894) (a:=327) (b:=327) s139894 s140221) (join_sums term (lo:=140548) (a:=327) (b:=327) s140548 s140875)))) (join_sums term (lo:=141202) (a:=2615) (b:=2615) (join_sums term (lo:=141202) (a:=1307) (b:=1308) (join_sums term (lo:=141202) (a:=653) (b:=654) (join_sums term (lo:=141202) (a:=326) (b:=327) s141202 s141528) (join_sums term (lo:=141855) (a:=327) (b:=327) s141855 s142182)) (join_sums term (lo:=142509) (a:=654) (b:=654) (join_sums term (lo:=142509) (a:=327) (b:=327) s142509 s142836) (join_sums term (lo:=143163) (a:=327) (b:=327) s143163 s143490))) (join_sums term (lo:=143817) (a:=1307) (b:=1308) (join_sums term (lo:=143817) (a:=653) (b:=654) (join_sums term (lo:=143817) (a:=326) (b:=327) s143817 s144143) (join_sums term (lo:=144470) (a:=327) (b:=327) s144470 s144797)) (join_sums term (lo:=145124) (a:=654) (b:=654) (join_sums term (lo:=145124) (a:=327) (b:=327) s145124 s145451) (join_sums term (lo:=145778) (a:=327) (b:=327) s145778 s146105)))))) (join_sums term (lo:=146432) (a:=10459) (b:=10460) (join_sums term (lo:=146432) (a:=5229) (b:=5230) (join_sums term (lo:=146432) (a:=2614) (b:=2615) (join_sums term (lo:=146432) (a:=1307) (b:=1307) (join_sums term (lo:=146432) (a:=653) (b:=654) (join_sums term (lo:=146432) (a:=326) (b:=327) s146432 s146758) (join_sums term (lo:=147085) (a:=327) (b:=327) s147085 s147412)) (join_sums term (lo:=147739) (a:=653) (b:=654) (join_sums term (lo:=147739) (a:=326) (b:=327) s147739 s148065) (join_sums term (lo:=148392) (a:=327) (b:=327) s148392 s148719))) (join_sums term (lo:=149046) (a:=1307) (b:=1308) (join_sums term (lo:=149046) (a:=653) (b:=654) (join_sums term (lo:=149046) (a:=326) (b:=327) s149046 s149372) (join_sums term (lo:=149699) (a:=327) (b:=327) s149699 s150026)) (join_sums term (lo:=150353) (a:=654) (b:=654) (join_sums term (lo:=150353) (a:=327) (b:=327) s150353 s150680) (join_sums term (lo:=151007) (a:=327) (b:=327) s151007 s151334)))) (join_sums term (lo:=151661) (a:=2615) (b:=2615) (join_sums term (lo:=151661) (a:=1307) (b:=1308) (join_sums term (lo:=151661) (a:=653) (b:=654) (join_sums term (lo:=151661) (a:=326) (b:=327) s151661 s151987) (join_sums term (lo:=152314) (a:=327) (b:=327) s152314 s152641)) (join_sums term (lo:=152968) (a:=654) (b:=654) (join_sums term (lo:=152968) (a:=327) (b:=327) s152968 s153295) (join_sums term (lo:=153622) (a:=327) (b:=327) s153622 s153949))) (join_sums term (lo:=154276) (a:=1307) (b:=1308) (join_sums term (lo:=154276) (a:=653) (b:=654) (join_sums term (lo:=154276) (a:=326) (b:=327) s154276 s154602) (join_sums term (lo:=154929) (a:=327) (b:=327) s154929 s155256)) (join_sums term (lo:=155583) (a:=654) (b:=654) (join_sums term (lo:=155583) (a:=327) (b:=327) s155583 s155910) (join_sums term (lo:=156237) (a:=327) (b:=327) s156237 s156564))))) (join_sums term (lo:=156891) (a:=5230) (b:=5230) (join_sums term (lo:=156891) (a:=2615) (b:=2615) (join_sums term (lo:=156891) (a:=1307) (b:=1308) (join_sums term (lo:=156891) (a:=653) (b:=654) (join_sums term (lo:=156891) (a:=326) (b:=327) s156891 s157217) (join_sums term (lo:=157544) (a:=327) (b:=327) s157544 s157871)) (join_sums term (lo:=158198) (a:=654) (b:=654) (join_sums term (lo:=158198) (a:=327) (b:=327) s158198 s158525) (join_sums term (lo:=158852) (a:=327) (b:=327) s158852 s159179))) (join_sums term (lo:=159506) (a:=1307) (b:=1308) (join_sums term (lo:=159506) (a:=653) (b:=654) (join_sums term (lo:=159506) (a:=326) (b:=327) s159506 s159832) (join_sums term (lo:=160159) (a:=327) (b:=327) s160159 s160486)) (join_sums term (lo:=160813) (a:=654) (b:=654) (join_sums term (lo:=160813) (a:=327) (b:=327) s160813 s161140) (join_sums term (lo:=161467) (a:=327) (b:=327) s161467 s161794)))) (join_sums term (lo:=162121) (a:=2615) (b:=2615) (join_sums term (lo:=162121) (a:=1307) (b:=1308) (join_sums term (lo:=162121) (a:=653) (b:=654) (join_sums term (lo:=162121) (a:=326) (b:=327) s162121 s162447) (join_sums term (lo:=162774) (a:=327) (b:=327) s162774 s163101)) (join_sums term (lo:=163428) (a:=654) (b:=654) (join_sums term (lo:=163428) (a:=327) (b:=327) s163428 s163755) (join_sums term (lo:=164082) (a:=327) (b:=327) s164082 s164409))) (join_sums term (lo:=164736) (a:=1307) (b:=1308) (join_sums term (lo:=164736) (a:=653) (b:=654) (join_sums term (lo:=164736) (a:=326) (b:=327) s164736 s165062) (join_sums term (lo:=165389) (a:=327) (b:=327) s165389 s165716)) (join_sums term (lo:=166043) (a:=654) (b:=654) (join_sums term (lo:=166043) (a:=327) (b:=327) s166043 s166370) (join_sums term (lo:=166697) (a:=327) (b:=327) s166697 s167024)))))))))

set_option maxRecDepth 8000 in
private theorem right_part :
    (∑ p ∈ (Nat.primesLE 167350).filter (3036 < ·),
      (Nat.primeCounting (28006150079/p) - Nat.primeCounting (p-1))) = 753837725 :=
  right_from_blocks tab prime HybridBound28006.fast_correct prime_ok (by decide) (by decide) rows

set_option maxRecDepth 12000 in
theorem exact_count : Nat.primeCounting 28006150079 = 1217243858 :=
  assemble (x:=28006150079) (y:=3036) (z:=167350) (a:=1971081584) (b:=753837725) (r:=1217243858)
    (by decide) (by decide) (by decide) (by decide) (by decide) left_part right_part (by decide)
end Endpoint28006
